-- Prove2me | solution 1 for NumberField.SUnits.finrank_groupCohomology_zero_sUnitsRep_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/475cdaf8-1051-5b24-9d5a-1548437bed09

import Mathlib
import Definitions.Def_NumberField_SUnitsModule
import Theorems.Thm_NumberField_SUnits_sUnits_eq_unit
import Theorems.Thm_M4aHerbrand_finrank_sUnit_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_finrank_groupCohomology_zero_sUnitsRep_add_one

set_option autoImplicit false
open IsDedekindDomain NumberField

namespace P2mS26C2a

open IsDedekindDomain NumberField UniqueFactorizationMonoid

theorem numberField_of_algebra (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K] : NumberField E := by
  haveI : CharZero E := RingHom.charZero (algebraMap E K)
  exact { to_charZero := inferInstance,
          to_finiteDimensional :=
            FiniteDimensional.of_injective (algebraMap E K).toRatAlgHom.toLinearMap (algebraMap E K).injective }

theorem algebraMap_ringOfIntegers_injective (A B : Type*) [Field A] [Field B] [Algebra A B] :
    Function.Injective (algebraMap (𝓞 A) (𝓞 B)) := fun x y hxy => by
  apply IsIntegralClosure.algebraMap_injective (𝓞 A) ℤ A
  apply (algebraMap A B).injective
  have := congrArg (algebraMap (𝓞 B) B) hxy
  rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 A) A B, IsScalarTower.algebraMap_apply (𝓞 A) A B] at this

section count
variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S] [Algebra R S]

open scoped Classical in

theorem pow_dvd_iff_le_count {P I : Ideal S} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hI : I ≠ ⊥) (k : ℕ) :
    P ^ k ∣ I ↔ k ≤ (normalizedFactors I).count P := by
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_eq_count_normalizedFactors (Ideal.prime_of_isPrime hP0 hP).irreducible hI,
    normalize_eq, Nat.cast_le]

open scoped Classical in

theorem count_map_eq (hinj : Function.Injective (algebraMap R S))
    {I : Ideal R} (hI : I ≠ ⊥) (P : Ideal S) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hp0 : Ideal.comap (algebraMap R S) P ≠ ⊥) :
    (normalizedFactors (I.map (algebraMap R S))).count P =
      Ideal.ramificationIdx' (P.comap (algebraMap R S)) P *
        (normalizedFactors I).count (P.comap (algebraMap R S)) := by
  set p := P.comap (algebraMap R S) with hpdef
  have hpP : p.IsPrime := hP.comap (algebraMap R S)
  set a := (normalizedFactors I).count p with hadef
  set e := Ideal.ramificationIdx' p P with hedef
  have hmapI : I.map (algebraMap R S) ≠ ⊥ := fun h => hI ((Ideal.map_eq_bot_iff_of_injective hinj).1 h)
  have hmapp : p.map (algebraMap R S) ≠ ⊥ := fun h => hp0 ((Ideal.map_eq_bot_iff_of_injective hinj).1 h)
  obtain ⟨J, hJ⟩ : p ^ a ∣ I := (pow_dvd_iff_le_count hpP hp0 hI a).2 le_rfl
  have hpJ : ¬ p ∣ J := fun h => by
    have : p ^ (a + 1) ∣ I := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ h
    exact Nat.not_succ_le_self a ((pow_dvd_iff_le_count hpP hp0 hI (a + 1)).1 this)
  have hmap : I.map (algebraMap R S) = (p.map (algebraMap R S)) ^ a * J.map (algebraMap R S) := by
    rw [hJ, Ideal.map_mul, Ideal.map_pow]
  have hPprime : Prime P := Ideal.prime_of_isPrime hP0 hP
  have hPJ : ¬ P ∣ J.map (algebraMap R S) := fun h => hpJ (by
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at h
    exact Ideal.dvd_iff_le.2 h)
  apply le_antisymm
  · set c := (normalizedFactors (I.map (algebraMap R S))).count P with hcdef
    have h1 : P ^ c ∣ I.map (algebraMap R S) := (pow_dvd_iff_le_count hP hP0 hmapI c).2 le_rfl
    rw [hmap, pow_dvd_iff_le_emultiplicity, emultiplicity_mul hPprime, emultiplicity_pow hPprime,
      emultiplicity_eq_zero.2 hPJ, add_zero,
      emultiplicity_eq_count_normalizedFactors hPprime.irreducible hmapp, normalize_eq,
      ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmapp hP hP0] at h1
    rw [mul_comm]
    exact_mod_cast h1
  · apply (pow_dvd_iff_le_count hP hP0 hmapI _).1
    rw [pow_mul]
    calc (P ^ e) ^ a ∣ (p.map (algebraMap R S)) ^ a := pow_dvd_pow_of_dvd (Ideal.dvd_iff_le.2 Ideal.le_pow_ramificationIdx) a
      _ ∣ I.map (algebraMap R S) := by
        rw [hmap]
        exact dvd_mul_right _ _

end count

theorem pow_eq_one_iff' {y : WithZero (Multiplicative ℤ)} {e : ℕ} (he : e ≠ 0) : y ^ e = 1 ↔ y = 1 := by
  constructor
  · intro h
    rcases eq_or_ne y 0 with rfl | hy
    · rw [zero_pow he] at h
      exact absurd h zero_ne_one
    · obtain ⟨z, rfl⟩ : ∃ z : ℤ, y = WithZero.exp z := ⟨_, (WithZero.exp_log hy).symm⟩
      rw [← WithZero.exp_nsmul, ← WithZero.exp_zero, WithZero.exp_injective.eq_iff] at h
      rw [← WithZero.exp_zero, WithZero.exp_injective.eq_iff]
      rw [nsmul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 he)
  · rintro rfl
    exact one_pow _

section ext
variable (A B : Type*) [Field A] [NumberField A] [Field B] [NumberField B] [Algebra A B]

omit [NumberField A] in

theorem ramificationIdx_under_ne_zero (w : HeightOneSpectrum (𝓞 B)) :
    Ideal.ramificationIdx' (w.under (𝓞 A)).asIdeal w.asIdeal ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx_ne_zero
    (fun h => (w.under (𝓞 A)).ne_bot ((Ideal.map_eq_bot_iff_of_injective (algebraMap_ringOfIntegers_injective A B)).1 h))
    w.isPrime (Ideal.map_le_iff_le_comap.2 le_rfl)

open scoped Classical in
theorem intValuation_algebraMap (w : HeightOneSpectrum (𝓞 B)) (r : 𝓞 A) :
    w.intValuation (algebraMap (𝓞 A) (𝓞 B) r) =
      (w.under (𝓞 A)).intValuation r ^ Ideal.ramificationIdx' (w.under (𝓞 A)).asIdeal w.asIdeal := by
  have hinj := algebraMap_ringOfIntegers_injective A B
  rcases eq_or_ne r 0 with rfl | hr
  · rw [map_zero, Valuation.map_zero, Valuation.map_zero, zero_pow (ramificationIdx_under_ne_zero A B w)]
  have hr' : algebraMap (𝓞 A) (𝓞 B) r ≠ 0 := (map_ne_zero_iff _ hinj).2 hr
  have h0 : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have h0' : Ideal.span {algebraMap (𝓞 A) (𝓞 B) r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [w.intValuation_if_neg hr', (w.under (𝓞 A)).intValuation_if_neg hr, ← WithZero.exp_nsmul, smul_neg, nsmul_eq_mul,
    Ideal.count_associates_factors_eq h0' w.isPrime w.ne_bot,
    Ideal.count_associates_factors_eq h0 (w.under (𝓞 A)).isPrime (w.under (𝓞 A)).ne_bot,
    show Ideal.span {algebraMap (𝓞 A) (𝓞 B) r} = (Ideal.span {r}).map (algebraMap (𝓞 A) (𝓞 B)) by
      rw [Ideal.map_span, Set.image_singleton],
    count_map_eq hinj h0 w.asIdeal w.isPrime w.ne_bot (w.under (𝓞 A)).ne_bot, Nat.cast_mul]
  rfl

theorem valuation_algebraMap (w : HeightOneSpectrum (𝓞 B)) (x : A) :
    w.valuation B (algebraMap A B x) =
      (w.under (𝓞 A)).valuation A x ^ Ideal.ramificationIdx' (w.under (𝓞 A)).asIdeal w.asIdeal := by
  have hinj := algebraMap_ringOfIntegers_injective A B
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 A)) x
  have hs' : algebraMap (𝓞 A) (𝓞 B) s ∈ nonZeroDivisors (𝓞 B) :=
    mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero s.2))
  have hx : algebraMap A B (IsLocalization.mk' A r s) =
      IsLocalization.mk' B (algebraMap (𝓞 A) (𝓞 B) r) ⟨_, hs'⟩ := by
    rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, map_div₀, ← IsScalarTower.algebraMap_apply (𝓞 A) A B,
      ← IsScalarTower.algebraMap_apply (𝓞 A) A B]
    change _ = algebraMap (𝓞 B) B (algebraMap (𝓞 A) (𝓞 B) r) / algebraMap (𝓞 B) B (algebraMap (𝓞 A) (𝓞 B) s)
    rw [← IsScalarTower.algebraMap_apply (𝓞 A) (𝓞 B) B, ← IsScalarTower.algebraMap_apply (𝓞 A) (𝓞 B) B]
  rw [hx, HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.valuation_of_mk', intValuation_algebraMap,
    intValuation_algebraMap, div_pow]

theorem valuation_algebraMap_eq_one_iff (w : HeightOneSpectrum (𝓞 B)) (x : A) :
    w.valuation B (algebraMap A B x) = 1 ↔ (w.under (𝓞 A)).valuation A x = 1 := by
  rw [valuation_algebraMap]
  exact pow_eq_one_iff' (ramificationIdx_under_ne_zero A B w)

end ext

end P2mS26C2a

namespace P2mS26C2a

open IsDedekindDomain NumberField

theorem isScalarTower_ringOfIntegers (E F K : Type*) [Field E] [Field F] [Field K] [NumberField K]
    [Algebra E F] [Algebra F K] [Algebra E K] [IsScalarTower E F K] : IsScalarTower (𝓞 E) (𝓞 F) (𝓞 K) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    apply IsFractionRing.injective (𝓞 K) K
    rw [← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 K) K, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
      IsScalarTower.algebraMap_apply (𝓞 E) E K, IsScalarTower.algebraMap_apply (𝓞 F) F K,
      ← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 F) F, IsScalarTower.algebraMap_apply (𝓞 E) E F,
      ← IsScalarTower.algebraMap_apply E F K]

theorem finite_setOf_under_mem (A B : Type*) [Field A] [NumberField A] [Field B] [NumberField B] [Algebra A B]
    (S : Finset (HeightOneSpectrum (𝓞 A))) :
    Set.Finite {u : HeightOneSpectrum (𝓞 B) | u.under (𝓞 A) ∈ (S : Set (HeightOneSpectrum (𝓞 A)))} := by
  classical
  have hsub : {u : HeightOneSpectrum (𝓞 B) | u.under (𝓞 A) ∈ (S : Set (HeightOneSpectrum (𝓞 A)))} ⊆
      ⋃ v ∈ S, (fun u : HeightOneSpectrum (𝓞 B) => u.asIdeal) ⁻¹' (v.asIdeal.primesOver (𝓞 B)) := by
    intro u hu
    simp only [Set.mem_iUnion, Set.mem_preimage]
    exact ⟨u.under (𝓞 A), hu, u.isPrime, ⟨rfl⟩⟩
  refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun v _ => ?_) hsub
  haveI := v.isMaximal
  exact (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 B)).preimage fun x _ y _ h => HeightOneSpectrum.ext h

section descent

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (H : Subgroup (K ≃ₐ[E] K))

def placesF : Set (HeightOneSpectrum (𝓞 (IntermediateField.fixedField H))) :=
  {u | u.under (𝓞 E) ∈ (S : Set (HeightOneSpectrum (𝓞 E)))}

omit [NumberField E] [NumberField K] in
theorem mem_placesF (u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H))) :
    u ∈ placesF E K S H ↔ u.under (𝓞 E) ∈ S := Iff.rfl

omit [NumberField E] in

theorem under_mem_iff (w : HeightOneSpectrum (𝓞 K)) :
    w.under (𝓞 E) ∈ S ↔ w.under (𝓞 (IntermediateField.fixedField H)) ∈ placesF E K S H := by
  haveI := isScalarTower_ringOfIntegers E (IntermediateField.fixedField H) K
  rw [mem_placesF, show (w.under (𝓞 (IntermediateField.fixedField H))).under (𝓞 E) = w.under (𝓞 E) from
    HeightOneSpectrum.ext (Ideal.under_under _)]

theorem map_mem_sUnits (y : ↥((placesF E K S H).unit (IntermediateField.fixedField H))) :
    Units.map (algebraMap (IntermediateField.fixedField H) K : IntermediateField.fixedField H →* K) (y : (IntermediateField.fixedField H)ˣ) ∈
      NumberField.SUnits.sUnits E K S := by
  rw [NumberField.SUnits.sUnits_eq_unit E K S]
  intro w hw
  rw [NumberField.SUnits.mem_placesAbove, under_mem_iff E K S H] at hw
  change w.valuation K (algebraMap (IntermediateField.fixedField H) K (y : (IntermediateField.fixedField H)ˣ)) = 1
  rw [valuation_algebraMap_eq_one_iff]
  exact y.2 _ hw

omit [NumberField E] [NumberField K] in

theorem smul_map_eq (h : H) (y : (IntermediateField.fixedField H)ˣ) :
    (h : K ≃ₐ[E] K) • Units.map (algebraMap (IntermediateField.fixedField H) K : IntermediateField.fixedField H →* K) y =
      Units.map (algebraMap (IntermediateField.fixedField H) K : IntermediateField.fixedField H →* K) y := by
  apply Units.ext
  change (h : K ≃ₐ[E] K) (((y : IntermediateField.fixedField H) : K)) = ((y : IntermediateField.fixedField H) : K)
  exact (IntermediateField.mem_fixedField_iff H _).1 (y : IntermediateField.fixedField H).2 (h : K ≃ₐ[E] K) h.2

omit [NumberField E] in

theorem coe_val_mem_fixedField (x : NumberField.SUnits.sUnitsRep E K S)
    (hx : x ∈ (Representation.invariants ((NumberField.SUnits.sUnitsRep E K S).ρ.comp H.subtype))) :
    ((NumberField.SUnits.val E K S x : Kˣ) : K) ∈ IntermediateField.fixedField H := by
  rw [IntermediateField.mem_fixedField_iff]
  intro f hf
  have h1 := congrArg (fun z => ((NumberField.SUnits.val E K S z : Kˣ) : K)) (hx ⟨f, hf⟩)
  exact h1

noncomputable def descUnit (x : NumberField.SUnits.sUnitsRep E K S)
    (hx : x ∈ (Representation.invariants ((NumberField.SUnits.sUnitsRep E K S).ρ.comp H.subtype))) : (IntermediateField.fixedField H)ˣ :=
  Units.mk0 ⟨((NumberField.SUnits.val E K S x : Kˣ) : K), coe_val_mem_fixedField E K S H x hx⟩ fun h0 =>
    (NumberField.SUnits.val E K S x).ne_zero (congrArg Subtype.val h0)

omit [NumberField E] in
theorem coe_descUnit (x : NumberField.SUnits.sUnitsRep E K S)
    (hx : x ∈ (Representation.invariants ((NumberField.SUnits.sUnitsRep E K S).ρ.comp H.subtype))) :
    (((descUnit E K S H x hx : (IntermediateField.fixedField H)ˣ) : IntermediateField.fixedField H) : K) =
      ((NumberField.SUnits.val E K S x : Kˣ) : K) := rfl

theorem descUnit_mem (x : NumberField.SUnits.sUnitsRep E K S)
    (hx : x ∈ (Representation.invariants ((NumberField.SUnits.sUnitsRep E K S).ρ.comp H.subtype))) :
    descUnit E K S H x hx ∈ (placesF E K S H).unit (IntermediateField.fixedField H) := by
  intro u hu
  obtain ⟨w, hw⟩ := NumberField.PlaceAbove.exists_above (IntermediateField.fixedField H) K u
  have hwu : w.under (𝓞 (IntermediateField.fixedField H)) = u := HeightOneSpectrum.ext hw
  rw [← hwu, ← valuation_algebraMap_eq_one_iff]
  change w.valuation K ((NumberField.SUnits.val E K S x : Kˣ) : K) = 1
  have hxS := NumberField.SUnits.val_mem E K S x
  rw [NumberField.SUnits.sUnits_eq_unit E K S] at hxS
  apply hxS w
  rw [NumberField.SUnits.mem_placesAbove, under_mem_iff E K S H, hwu]
  exact hu

noncomputable def descentEquiv :
    Additive ↥((placesF E K S H).unit (IntermediateField.fixedField H)) ≃+
      ↥((Representation.invariants ((NumberField.SUnits.sUnitsRep E K S).ρ.comp H.subtype))) where
  toFun a := ⟨⟨Additive.ofMul (Units.map (algebraMap (IntermediateField.fixedField H) K : IntermediateField.fixedField H →* K)
      ((Additive.toMul a : (placesF E K S H).unit (IntermediateField.fixedField H)) : (IntermediateField.fixedField H)ˣ)),
      (NumberField.SUnits.mem_sUnitsSubmodule E K S _).2 (map_mem_sUnits E K S H (Additive.toMul a))⟩, fun h => by
        apply Subtype.ext
        exact congrArg Additive.ofMul (smul_map_eq E K H h _)⟩
  invFun x := Additive.ofMul ⟨descUnit E K S H x.1 x.2, descUnit_mem E K S H x.1 x.2⟩
  left_inv a := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Additive.ofMul (Units.ext rfl)
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change Additive.ofMul (Units.map _ (((Additive.toMul a * Additive.toMul b :
        (placesF E K S H).unit (IntermediateField.fixedField H)) : (IntermediateField.fixedField H)ˣ))) = _
    rw [Subgroup.coe_mul, map_mul, ofMul_mul]
    rfl

end descent

end P2mS26C2a

theorem solution (E K : Type) [Field E] [Field K]
    [NumberField K] [Algebra E K] (S : Finset (HeightOneSpectrum (𝓞 E))) (H : Subgroup (K ≃ₐ[E] K)) :
    Module.finrank ℤ (groupCohomology (Rep.res H.subtype (NumberField.SUnits.sUnitsRep E K S)) 0) + 1 =
      Nat.card {u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) // u.under (𝓞 E) ∈ S} +
        Nat.card (InfinitePlace (IntermediateField.fixedField H)) := by
  classical
  haveI : NumberField E := P2mS26C2a.numberField_of_algebra E K
  haveI : Finite ↥(P2mS26C2a.placesF E K S H) := (P2mS26C2a.finite_setOf_under_mem E (IntermediateField.fixedField H) S).to_subtype
  obtain ⟨-, hrank⟩ := M4aHerbrand.finrank_sUnit_eq (IntermediateField.fixedField H) (P2mS26C2a.placesF E K S H)
  have h0 : Module.finrank ℤ (groupCohomology (Rep.res H.subtype (NumberField.SUnits.sUnitsRep E K S)) 0) =
      Module.finrank ℤ (Additive ↥((P2mS26C2a.placesF E K S H).unit (IntermediateField.fixedField H))) :=
    (LinearEquiv.finrank_eq (groupCohomology.H0Iso (Rep.res H.subtype (NumberField.SUnits.sUnitsRep E K S))).toLinearEquiv).trans
      (LinearEquiv.finrank_eq (P2mS26C2a.descentEquiv E K S H).toIntLinearEquiv).symm
  have hS : Nat.card {u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) // u.under (𝓞 E) ∈ S} =
      Nat.card ↥(P2mS26C2a.placesF E K S H) := rfl
  have hpos : 0 < Fintype.card (InfinitePlace (IntermediateField.fixedField H)) := Fintype.card_pos
  rw [h0, hrank, hS, NumberField.Units.rank, Nat.card_eq_fintype_card (α := InfinitePlace (IntermediateField.fixedField H))]
  omega

end S_NumberField_SUnits_finrank_groupCohomology_zero_sUnitsRep_add_one
end P2MW
export P2MW.S_NumberField_SUnits_finrank_groupCohomology_zero_sUnitsRep_add_one (solution)
