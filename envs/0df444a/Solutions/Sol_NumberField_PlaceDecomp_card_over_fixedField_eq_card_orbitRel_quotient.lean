-- Prove2me | solution 1 for NumberField.PlaceDecomp.card_over_fixedField_eq_card_orbitRel_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f996bd03-0d7d-5846-b041-dadd058cb3df

import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_card_over_fixedField_eq_card_orbitRel_quotient

set_option autoImplicit false
open IsDedekindDomain NumberField

namespace P2mS26C2b

open IsDedekindDomain NumberField
open scoped Pointwise

lemma eq_of_forall_le_exp_neg_iff {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  obtain ⟨α, rfl⟩ : ∃ α : ℤ, a = WithZero.exp α := ⟨_, (WithZero.exp_log ha).symm⟩
  obtain ⟨β, rfl⟩ : ∃ β : ℤ, b = WithZero.exp β := ⟨_, (WithZero.exp_log hb).symm⟩
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
  simp only [WithZero.exp_le_exp] at h
  have h1 := (h (-α).toNat).1 (by omega)
  have h2 := (h (-β).toNat).2 (by omega)
  congr 1
  omega

section comap
variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

theorem intValuation_comap (e : R ≃+* R') (v : HeightOneSpectrum R') (r : R) :
    (HeightOneSpectrum.comap e.toRingHom e.surjective v).intValuation r = v.intValuation (e r) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  apply eq_of_forall_le_exp_neg_iff (HeightOneSpectrum.intValuation_ne_zero _ _ hr)
    (HeightOneSpectrum.intValuation_ne_zero _ _ (by simpa using hr)) (HeightOneSpectrum.intValuation_le_one _ _)
    (HeightOneSpectrum.intValuation_le_one _ _)
  intro n
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
    HeightOneSpectrum.comap_asIdeal]
  change r ∈ Ideal.comap e v.asIdeal ^ n ↔ e r ∈ v.asIdeal ^ n
  rw [← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]

end comap

variable (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]

noncomputable abbrev galInt (σ : K ≃ₐ[E] K) : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (σ : K ≃+* K)

omit [NumberField K] in
theorem coe_galInt (σ : K ≃ₐ[E] K) (x : 𝓞 K) : ((galInt E K σ x : 𝓞 K) : K) = σ (x : K) :=
  RingOfIntegers.mapRingEquiv_apply _ _

noncomputable def pullback (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.comap (galInt E K σ).toRingHom (galInt E K σ).surjective w

theorem valuation_apply_eq_valuation_pullback (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (y : K) :
    w.valuation K (σ y) = (pullback E K σ w).valuation K y := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 K)) y
  have hs : (galInt E K σ s : 𝓞 K) ∈ nonZeroDivisors (𝓞 K) :=
    mem_nonZeroDivisors_of_ne_zero (by simp)
  have hσ : σ (IsLocalization.mk' K r s) = IsLocalization.mk' K (galInt E K σ r) ⟨galInt E K σ s, hs⟩ := by
    rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, map_div₀]
    change σ ((r : 𝓞 K) : K) / σ ((s : 𝓞 K) : K) = ((galInt E K σ r : 𝓞 K) : K) / ((galInt E K σ s : 𝓞 K) : K)
    rw [coe_galInt, coe_galInt]
  rw [hσ, HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.valuation_of_mk', pullback,
    intValuation_comap, intValuation_comap]

theorem inv_smul_valuationSubring (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    σ⁻¹ • (w.valuation K).valuationSubring = ((pullback E K σ w).valuation K).valuationSubring := by
  ext x
  rw [ValuationSubring.mem_inv_pointwise_smul_iff, Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    AlgEquiv.smul_def, valuation_apply_eq_valuation_pullback]

omit [NumberField K] in

theorem inv_smul_asIdeal (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    σ⁻¹ • w.asIdeal = (pullback E K σ w).asIdeal := by
  ext r
  rw [Ideal.mem_inv_pointwise_smul_iff]
  rfl

theorem eq_of_valuationSubring_eq {w w' : HeightOneSpectrum (𝓞 K)}
    (h : (w.valuation K).valuationSubring = (w'.valuation K).valuationSubring) : w = w' := by
  have he := (Valuation.isEquiv_iff_valuationSubring _ _).2 h
  rw [Valuation.isEquiv_iff_val_lt_one] at he
  apply HeightOneSpectrum.ext
  ext r
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  exact he

theorem mem_decomp_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    σ ∈ NumberField.PlaceDecomp.decomp E K w ↔ σ ∈ MulAction.stabilizer (K ≃ₐ[E] K) w.asIdeal := by
  rw [← Subgroup.inv_mem_iff (NumberField.PlaceDecomp.decomp E K w), ← Subgroup.inv_mem_iff (MulAction.stabilizer _ w.asIdeal)]
  change σ⁻¹ • (w.valuation K).valuationSubring = (w.valuation K).valuationSubring ↔ σ⁻¹ • w.asIdeal = w.asIdeal
  rw [inv_smul_valuationSubring, inv_smul_asIdeal]
  constructor
  · intro h
    rw [eq_of_valuationSubring_eq K h]
  · intro h
    rw [HeightOneSpectrum.ext h]

theorem decomp_eq_stabilizer (w : HeightOneSpectrum (𝓞 K)) :
    NumberField.PlaceDecomp.decomp E K w = MulAction.stabilizer (K ≃ₐ[E] K) w.asIdeal :=
  Subgroup.ext fun σ => mem_decomp_iff E K σ w

end P2mS26C2b

namespace P2mS26C2b

open IsDedekindDomain NumberField
open scoped Pointwise

def sigmaOrbitEquiv {G : Type*} [Group G] (H : Subgroup G) {ι : Type*} (X : ι → Type*) [∀ i, MulAction G (X i)] :
    MulAction.orbitRel.Quotient H (Σ i, X i) ≃ Σ i, MulAction.orbitRel.Quotient H (X i) where
  toFun := Quotient.lift (fun x : Σ i, X i => (⟨x.1, (Quotient.mk'' x.2 : MulAction.orbitRel.Quotient H (X x.1))⟩ :
      Σ i, MulAction.orbitRel.Quotient H (X i))) (by
    rintro a ⟨i, x⟩ hab
    obtain ⟨h, rfl⟩ := MulAction.orbitRel_apply.1 hab
    change (⟨i, Quotient.mk'' (h • x)⟩ : Σ i, MulAction.orbitRel.Quotient H (X i)) = ⟨i, Quotient.mk'' x⟩
    exact congrArg (Sigma.mk i) (Quotient.sound' (MulAction.mem_orbit x h)))
  invFun p := Quotient.map' (Sigma.mk p.1) (fun a b hab => by
    obtain ⟨h, rfl⟩ := MulAction.orbitRel_apply.1 hab
    exact MulAction.orbitRel_apply.2 ⟨h, rfl⟩) p.2
  left_inv q := Quotient.inductionOn' q fun x => by rcases x with ⟨i, x⟩; rfl
  right_inv p := by
    rcases p with ⟨i, q⟩
    induction q using Quotient.inductionOn' with
    | h x => rfl

theorem nonempty_orbitQuot_equiv {G : Type*} [Group G] (H : Subgroup G) {α : Type*} [MulAction G α] (a : α) :
    Nonempty (MulAction.orbitRel.Quotient H (MulAction.orbit G a) ≃
      MulAction.orbitRel.Quotient H (G ⧸ MulAction.stabilizer G a)) := by
  let e : MulAction.orbit G a ≃ G ⧸ MulAction.stabilizer G a := MulAction.orbitEquivQuotientStabilizer G a
  have hsymm : ∀ (g : G) (q : G ⧸ MulAction.stabilizer G a), e.symm (g • q) = g • e.symm q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H b =>
      apply Subtype.ext
      change ((MulAction.orbitEquivQuotientStabilizer G a).symm (g • (b : G ⧸ MulAction.stabilizer G a)) : α) =
        g • ((MulAction.orbitEquivQuotientStabilizer G a).symm (b : G ⧸ MulAction.stabilizer G a) : α)
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, MulAction.orbitEquivQuotientStabilizer_symm_apply,
        MulAction.orbitEquivQuotientStabilizer_symm_apply, mul_smul]
  have hsmul : ∀ (g : G) (x : MulAction.orbit G a), e (g • x) = g • e x := by
    intro g x
    apply e.symm.injective
    rw [Equiv.symm_apply_apply, hsymm, Equiv.symm_apply_apply]
  refine ⟨Quotient.congr e fun x y => ?_⟩
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, (hsmul h y).symm⟩
  · rintro ⟨h, hh⟩
    refine ⟨h, e.injective ?_⟩
    rw [← hh]
    exact hsmul h y

def sigmaFibreEquiv {α β : Type*} (f : α → β) (S : Finset β) : {a : α // f a ∈ S} ≃ Σ b : S, {a : α // f a = b} :=
  (Equiv.sigmaSubtypeFiberEquivSubtype f fun _ => Iff.rfl).symm

theorem algebraMap_ringOfIntegers_injective (A B : Type*) [Field A] [Field B] [Algebra A B] :
    Function.Injective (algebraMap (𝓞 A) (𝓞 B)) := fun x y hxy => by
  apply IsIntegralClosure.algebraMap_injective (𝓞 A) ℤ A
  apply (algebraMap A B).injective
  have := congrArg (algebraMap (𝓞 B) B) hxy
  rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 A) A B, IsScalarTower.algebraMap_apply (𝓞 A) A B] at this

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem nonempty_fibre_equiv [IsGalois E K] (H : Subgroup (K ≃ₐ[E] K)) (v : HeightOneSpectrum (𝓞 E)) :
    Nonempty ({u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) // u.under (𝓞 E) = v} ≃
      MulAction.orbitRel.Quotient H
        (MulAction.orbit (K ≃ₐ[E] K) (NumberField.PlaceAbove.above E K v).asIdeal)) := by
  classical
  let G := K ≃ₐ[E] K
  let F := IntermediateField.fixedField H
  let w₀ := NumberField.PlaceAbove.above E K v
  haveI hGal : IsGaloisGroup H F K := IsGaloisGroup.subgroup G E K H
  haveI hGalInt : IsGaloisGroup H (𝓞 F) (𝓞 K) := IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 K) F K
  have hw₀ : Ideal.under (𝓞 E) w₀.asIdeal = v.asIdeal := NumberField.PlaceAbove.comap_above E K v
  haveI : w₀.asIdeal.IsPrime := w₀.isPrime
  haveI : w₀.asIdeal.LiesOver v.asIdeal := (Ideal.liesOver_iff _ _).2 hw₀.symm
  have horb := Algebra.IsInvariant.orbit_eq_primesOver (𝓞 E) (𝓞 K) G v.asIdeal w₀.asIdeal
  have hmem : ∀ P : MulAction.orbit G w₀.asIdeal,
      (P : Ideal (𝓞 K)).IsPrime ∧ v.asIdeal = Ideal.under (𝓞 E) (P : Ideal (𝓞 K)) := fun P => by
    have h := (Set.ext_iff.1 horb (P : Ideal (𝓞 K))).1 P.2
    exact ⟨h.1, (Ideal.liesOver_iff _ _).1 h.2⟩
  have hinjE := algebraMap_ringOfIntegers_injective E F
  have hinjF := algebraMap_ringOfIntegers_injective F K
  haveI : IsScalarTower (𝓞 E) (𝓞 F) (𝓞 K) := IsScalarTower.of_algebraMap_eq fun x => by
    apply IsFractionRing.injective (𝓞 K) K
    rw [← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 K) K, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
      IsScalarTower.algebraMap_apply (𝓞 E) E K, IsScalarTower.algebraMap_apply (𝓞 F) F K,
      ← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 F) F, IsScalarTower.algebraMap_apply (𝓞 E) E F,
      ← IsScalarTower.algebraMap_apply E F K]
  have htower : ∀ P : Ideal (𝓞 K), (P.under (𝓞 F)).under (𝓞 E) = P.under (𝓞 E) := fun P => Ideal.under_under P

  have hfix : ∀ (h : H) (a : 𝓞 F), ((h : G) • (algebraMap (𝓞 F) (𝓞 K) a) : 𝓞 K) = algebraMap (𝓞 F) (𝓞 K) a := by
    intro h a
    apply RingOfIntegers.coe_injective
    have key : ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = ((algebraMap (𝓞 F) F a : F) : K) := by
      rw [show ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) from rfl,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F K]
      rfl
    change (h : G) ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K)
    rw [key]
    exact (IntermediateField.mem_fixedField_iff H _).1 (algebraMap (𝓞 F) F a).2 (h : G) h.2

  let φ : MulAction.orbit G w₀.asIdeal → {u : HeightOneSpectrum (𝓞 F) // u.under (𝓞 E) = v} := fun P =>
    ⟨⟨(P : Ideal (𝓞 K)).under (𝓞 F), (hmem P).1.comap (algebraMap (𝓞 F) (𝓞 K)), fun h0 => v.ne_bot (by
        rw [(hmem P).2, ← htower, h0]
        exact Ideal.comap_bot_of_injective _ hinjE)⟩,
      HeightOneSpectrum.ext (by
        change ((P : Ideal (𝓞 K)).under (𝓞 F)).under (𝓞 E) = v.asIdeal
        rw [htower, (hmem P).2])⟩
  have hφval : ∀ P, ((φ P).1).asIdeal = (P : Ideal (𝓞 K)).under (𝓞 F) := fun P => rfl
  have hφ : ∀ (h : H) (P : MulAction.orbit G w₀.asIdeal), φ (h • P) = φ P := by
    intro h P
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    rw [hφval, hφval]
    change (((h : G) • (P : Ideal (𝓞 K))) : Ideal (𝓞 K)).under (𝓞 F) = (P : Ideal (𝓞 K)).under (𝓞 F)
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      show (h : G)⁻¹ = ((h⁻¹ : H) : G) from rfl, hfix]
  refine ⟨(Equiv.ofBijective (Quotient.lift φ fun P Q hPQ => ?_) ⟨?_, ?_⟩).symm⟩
  · obtain ⟨h, rfl⟩ := MulAction.orbitRel_apply.1 hPQ
    exact hφ h Q
  · rintro ⟨P⟩ ⟨Q⟩ hPQ
    change φ P = φ Q at hPQ
    apply Quotient.sound

    have hq : (P : Ideal (𝓞 K)).under (𝓞 F) = (Q : Ideal (𝓞 K)).under (𝓞 F) := by
      rw [← hφval, ← hφval, hPQ]
    haveI : (Q : Ideal (𝓞 K)).IsPrime := (hmem Q).1
    haveI : (Q : Ideal (𝓞 K)).LiesOver ((Q : Ideal (𝓞 K)).under (𝓞 F)) := ⟨rfl⟩
    have horbH := Algebra.IsInvariant.orbit_eq_primesOver (𝓞 F) (𝓞 K) H ((Q : Ideal (𝓞 K)).under (𝓞 F)) (Q : Ideal (𝓞 K))
    have hP : (P : Ideal (𝓞 K)) ∈ ((Q : Ideal (𝓞 K)).under (𝓞 F)).primesOver (𝓞 K) := ⟨(hmem P).1, ⟨hq.symm⟩⟩
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.1 ((Set.ext_iff.1 horbH (P : Ideal (𝓞 K))).2 hP)
    refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨h, Subtype.ext ?_⟩)
    change (h : G) • (Q : Ideal (𝓞 K)) = (P : Ideal (𝓞 K))
    rw [← hh]
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  · rintro ⟨u, hu⟩
    haveI := u.isMaximal
    obtain ⟨P, hPmax, hPu⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) u.asIdeal
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinjF]; exact bot_le)
    have hPorb : P ∈ MulAction.orbit G w₀.asIdeal := by
      rw [horb]
      refine ⟨hPmax.isPrime, (Ideal.liesOver_iff _ _).2 ?_⟩
      rw [← htower, show P.under (𝓞 F) = u.asIdeal from hPu, ← congrArg HeightOneSpectrum.asIdeal hu]
      rfl
    refine ⟨Quotient.mk'' ⟨P, hPorb⟩, ?_⟩
    change φ ⟨P, hPorb⟩ = ⟨u, hu⟩
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    rw [hφval]
    exact hPu

end P2mS26C2b

open scoped Pointwise in
theorem solution (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E))) (H : Subgroup (K ≃ₐ[E] K)) :
    Nat.card {u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) // u.under (𝓞 E) ∈ S} =
      Nat.card (MulAction.orbitRel.Quotient H
        (Σ v : S, (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) := by
  classical
  refine Nat.card_congr (((P2mS26C2b.sigmaFibreEquiv
    (fun u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) => u.under (𝓞 E)) S).trans
    (Equiv.sigmaCongrRight fun v : S => ?_)).trans
    (P2mS26C2b.sigmaOrbitEquiv H fun v : S =>
      (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)).symm)
  rw [P2mS26C2b.decomp_eq_stabilizer E K]
  exact (P2mS26C2b.nonempty_fibre_equiv E K H v).some.trans
    (P2mS26C2b.nonempty_orbitQuot_equiv H (NumberField.PlaceAbove.above E K (v : HeightOneSpectrum (𝓞 E))).asIdeal).some

end S_NumberField_PlaceDecomp_card_over_fixedField_eq_card_orbitRel_quotient
end P2MW
export P2MW.S_NumberField_PlaceDecomp_card_over_fixedField_eq_card_orbitRel_quotient (solution)
