-- Prove2me | solution 1 for NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/aa88b2e6-54fe-517c-931d-8b191e4b6810

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_GroupCohomology_LevelConstantHom
import Theorems.Thm_NumberField_LevelArith_kummerChar_mul_and_add_and_level
import Theorems.Thm_NumberField_LevelArith_kummerChar_eq_zero_iff
import Theorems.Thm_NumberField_LevelArith_exists_kummerChar_eq_of_continuous
import Theorems.Thm_NumberField_LevelArith_kummerChar_conj_eq_cycloChar_mul
import Theorems.Thm_NumberField_LevelArith_kummerChar_isLevelConstant_iff_forall_dvd_valuation
import Theorems.Thm_NumberField_LevelArith_selmerStable_eq_selmer
import Definitions.Def_GroupCohomology_LevelConstantHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

noncomputable section

namespace CycBaseK2cB

variable {p : ℕ} [Fact p.Prime]

section bridge
variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)

def uL : (↥(levelField K L hKL))ˣ ≃* (↥L)ˣ := Units.mapEquiv (levelFieldEquiv K L hKL).symm.toMulEquiv

omit [Fact p.Prime] in
@[scoped simp] lemma coe_uL (u : (↥(levelField K L hKL))ˣ) :
    (((uL K L hKL u : (↥L)ˣ) : ↥L) : AlgebraicClosure ℚ) = (((u : ↥(levelField K L hKL)) : AlgebraicClosure ℚ)) := rfl

def ι (s : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)) : ↥L.fixingSubgroup :=
  ⟨((s : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), Subgroup.mem_subgroupOf.mp s.2⟩

omit [Fact p.Prime] in
@[scoped simp] lemma coe_ι (s : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)) :
    ((ι K L s : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = ((s : ↥K.fixingSubgroup) : _) := rfl

def ι' (σ : ↥L.fixingSubgroup) : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) :=
  ⟨⟨(σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL σ.2⟩,
    Subgroup.mem_subgroupOf.mpr σ.2⟩

omit [Fact p.Prime] in
lemma ι_ι' (σ : ↥L.fixingSubgroup) : ι K L (ι' K L hKL σ) = σ := rfl

omit [Fact p.Prime] in
lemma ι_mul (s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)) : ι K L (s * t) = ι K L s * ι K L t := rfl

def eO : 𝓞 ↥L ≃+* 𝓞 ↥(levelField K L hKL) := NumberField.RingOfIntegers.mapRingEquiv (levelFieldEquiv K L hKL)

def placeEquiv : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L) ≃ IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) :=
  IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv (eO K L hKL)

omit [Fact p.Prime] in
lemma mem_placeEquiv_asIdeal_iff (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L)) (r : 𝓞 ↥(levelField K L hKL)) :
    r ∈ (placeEquiv K L hKL w).asIdeal ↔ (eO K L hKL).symm r ∈ w.asIdeal := Iff.rfl

omit [Fact p.Prime] in
lemma eO_mem_placeEquiv_pow_iff (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L)) (r : 𝓞 ↥L) (n : ℕ) :
    eO K L hKL r ∈ (placeEquiv K L hKL w).asIdeal ^ n ↔ r ∈ w.asIdeal ^ n := by
  have h : (placeEquiv K L hKL w).asIdeal = Ideal.map (eO K L hKL) w.asIdeal := by
    rw [← Ideal.comap_symm]; rfl
  rw [h, ← Ideal.map_pow, ← Ideal.comap_symm, Ideal.mem_comap, RingEquiv.symm_apply_apply]

omit [Fact p.Prime] in
lemma mem_placesOverPrimes_placeEquiv_iff (S : Set Nat.Primes) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L)) :
    placeEquiv K L hKL w ∈ placesOverPrimes ↥(levelField K L hKL) S ↔ w ∈ placesOverPrimes ↥L S := by
  rw [mem_placesOverPrimes_iff, mem_placesOverPrimes_iff]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  rw [mem_placeEquiv_asIdeal_iff, map_natCast]

variable [FiniteDimensional ℚ ↥L]

omit [Fact p.Prime] in

lemma intValuation_placeEquiv (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L)) (r : 𝓞 ↥L) :
    (placeEquiv K L hKL w).intValuation (eO K L hKL r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [map_zero, Valuation.map_zero, Valuation.map_zero]
  · have hr' : eO K L hKL r ≠ 0 := (EmbeddingLike.map_ne_zero_iff).mpr hr
    apply le_antisymm
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, w.intValuation r = WithZero.exp (-(n : ℤ)) := ⟨_, w.intValuation_if_neg hr⟩
      rw [hn, IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, eO_mem_placeEquiv_pow_iff,
        ← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (placeEquiv K L hKL w).intValuation (eO K L hKL r) = WithZero.exp (-(n : ℤ)) :=
        ⟨_, (placeEquiv K L hKL w).intValuation_if_neg hr'⟩
      rw [hn, IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, ← eO_mem_placeEquiv_pow_iff K L hKL,
        ← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]

omit [Fact p.Prime] in

lemma valuation_placeEquiv (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L)) (z : ↥L) :
    (placeEquiv K L hKL w).valuation (↥(levelField K L hKL)) (levelFieldEquiv K L hKL z) = w.valuation (↥L) z := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 ↥L) z
  have h1 : ∀ c : 𝓞 ↥L, levelFieldEquiv K L hKL (algebraMap (𝓞 ↥L) (↥L) c) =
      algebraMap (𝓞 ↥(levelField K L hKL)) (↥(levelField K L hKL)) (eO K L hKL c) := fun c =>
    (NumberField.RingOfIntegers.mapRingEquiv_apply _ c).symm
  rw [map_div₀, map_div₀, map_div₀, h1, h1, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, intValuation_placeEquiv, intValuation_placeEquiv]

omit [Fact p.Prime] in
lemma valuationOfNeZero_placeEquiv (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L)) (u : (↥(levelField K L hKL))ˣ) :
    (placeEquiv K L hKL w).valuationOfNeZero u = w.valuationOfNeZero (uL K L hKL u) := by
  apply WithZero.coe_injective
  rw [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq, IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
  have h : ((u : ↥(levelField K L hKL)) : ↥(levelField K L hKL)) = levelFieldEquiv K L hKL ((uL K L hKL u : (↥L)ˣ) : ↥L) := rfl
  rw [h, valuation_placeEquiv]

end bridge

lemma kummerChar_pow (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hζF : ζ ∈ F)
    (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) (n : ℕ) : kummerChar p ζ hζ F (x ^ n) σ = n * kummerChar p ζ hζ F x σ := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    have h := (kummerChar_mul_and_add_and_level p ζ hζ F hζF).2.1 1 1 σ
    rw [mul_one] at h
    exact left_eq_add.mp h
  | succ n ih =>
    rw [pow_succ, (kummerChar_mul_and_add_and_level p ζ hζ F hζF).2.1, ih, Nat.cast_succ, add_mul, one_mul]

lemma valuationOfNeZeroMod_mk_eq_one_iff {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : Fˣ) :
    v.valuationOfNeZeroMod p (QuotientGroup.mk u : Fˣ ⧸ (powMonoidHom p : Fˣ →* Fˣ).range) = 1 ↔
      (p : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  simp only [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.coe_comp, Function.comp_apply]
  erw [QuotientGroup.map_mk]
  show (AddEquiv.toMultiplicative (Int.quotientZMultiplesNatEquivZMod p))
      ((v.valuationOfNeZero u : Multiplicative ℤ) : Multiplicative ℤ ⧸ AddSubgroup.toSubgroup (AddSubgroup.zmultiples (p : ℤ))) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  exact (QuotientGroup.eq_one_iff _).trans Int.mem_zmultiples_iff

lemma mem_placesAbove_iff (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField K L hKL))) :
    w ∈ NumberField.SUnits.placesAbove ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) ↔
      w ∈ placesOverPrimes ↥(levelField K L hKL) (S : Set Nat.Primes) := by
  rw [NumberField.SUnits.mem_placesAbove, mem_placesOverPrimesFinset, mem_placesOverPrimes_iff, mem_placesOverPrimes_iff]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  show algebraMap (𝓞 ↥K) (𝓞 ↥(levelField K L hKL)) ((q : ℕ) : 𝓞 ↥K) ∈ w.asIdeal ↔ _
  rw [map_natCast]

section kappa
variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)

def κfun (u : (↥(levelField K L hKL))ˣ) : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p :=
  fun s => kummerChar p ζ hζ L (uL K L hKL u) (ι K L s)

lemma κfun_apply (u : (↥(levelField K L hKL))ˣ) (s : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)) :
    κfun K L hKL ζ hζ u s = kummerChar p ζ hζ L (uL K L hKL u) (ι K L s) := rfl

variable (hζL : ζ ∈ L)
include hζL

lemma κfun_mul (u u' : (↥(levelField K L hKL))ˣ) : κfun K L hKL ζ hζ (u * u') = κfun K L hKL ζ hζ u + κfun K L hKL ζ hζ u' := by
  funext s
  show kummerChar p ζ hζ L (uL K L hKL (u * u')) (ι K L s) = _
  rw [map_mul]
  exact (kummerChar_mul_and_add_and_level p ζ hζ L hζL).2.1 _ _ (ι K L s)

lemma κfun_add (u : (↥(levelField K L hKL))ˣ) (s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)) :
    κfun K L hKL ζ hζ u (s * t) = κfun K L hKL ζ hζ u s + κfun K L hKL ζ hζ u t := by
  show kummerChar p ζ hζ L (uL K L hKL u) (ι K L (s * t)) = _
  rw [ι_mul]
  exact (kummerChar_mul_and_add_and_level p ζ hζ L hζL).1 _ _ _

lemma κfun_one (u : (↥(levelField K L hKL))ˣ) : κfun K L hKL ζ hζ u 1 = 0 := by
  have h := κfun_add K L hKL ζ hζ hζL u 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

lemma κfun_unit_one : κfun K L hKL ζ hζ 1 = 0 := by
  have h := κfun_mul K L hKL ζ hζ hζL 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

lemma κfun_pow_p (u : (↥(levelField K L hKL))ˣ) : κfun K L hKL ζ hζ (u ^ p) = 0 := by
  funext s
  show kummerChar p ζ hζ L (uL K L hKL (u ^ p)) (ι K L s) = 0
  rw [map_pow, kummerChar_pow ζ hζ L hζL, ZMod.natCast_self, zero_mul]

def κhom : (↥(levelField K L hKL))ˣ →* Multiplicative (↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) where
  toFun u := Multiplicative.ofAdd (κfun K L hKL ζ hζ u)
  map_one' := by rw [κfun_unit_one K L hKL ζ hζ hζL]; rfl
  map_mul' u u' := by rw [κfun_mul K L hKL ζ hζ hζL, ofAdd_add]

lemma range_le_ker_κhom :
    (powMonoidHom p : (↥(levelField K L hKL))ˣ →* (↥(levelField K L hKL))ˣ).range ≤ (κhom K L hKL ζ hζ hζL).ker := by
  rintro _ ⟨w, rfl⟩
  rw [MonoidHom.mem_ker, powMonoidHom_apply]
  show Multiplicative.ofAdd (κfun K L hKL ζ hζ (w ^ p)) = 1
  rw [κfun_pow_p K L hKL ζ hζ hζL]; rfl

def κ : unitsModPow (↥(levelField K L hKL)) p →* Multiplicative (↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) :=
  QuotientGroup.lift _ (κhom K L hKL ζ hζ hζL) (range_le_ker_κhom K L hKL ζ hζ hζL)

lemma κ_mk (u : (↥(levelField K L hKL))ˣ) :
    κ K L hKL ζ hζ hζL (unitsModPow.mk (↥(levelField K L hKL)) p u) = Multiplicative.ofAdd (κfun K L hKL ζ hζ u) := rfl

lemma κ_add (q : unitsModPow (↥(levelField K L hKL)) p) (s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)) :
    Multiplicative.toAdd (κ K L hKL ζ hζ hζL q) (s * t) =
      Multiplicative.toAdd (κ K L hKL ζ hζ hζL q) s + Multiplicative.toAdd (κ K L hKL ζ hζ hζL q) t := by
  obtain ⟨u, rfl⟩ := unitsModPow.mk_surjective (↥(levelField K L hKL)) p q
  exact κfun_add K L hKL ζ hζ hζL u s t

lemma isLevelConstant_κfun_iff (S : Finset Nat.Primes) (u : (↥(levelField K L hKL))ˣ) :
    IsLevelConstantSr₁ (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S (κfun K L hKL ζ hζ u) ↔
      ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), F'.IsUnramifiedOutside S ∧
        ∀ σ : ↥L.fixingSubgroup, (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F'.fixingSubgroup →
          kummerChar p ζ hζ L (uL K L hKL u) σ = 0 := by
  constructor
  · rintro ⟨F', hF', h⟩
    refine ⟨F', hF', fun σ hσ => ?_⟩
    have h1 := h 1 (ι' K L hKL σ) hσ
    rw [one_mul, κfun_one K L hKL ζ hζ hζL] at h1
    exact h1
  · rintro ⟨F', hF', h⟩
    refine ⟨F', hF', fun g s hs => ?_⟩
    rw [κfun_add K L hKL ζ hζ hζL, κfun_apply K L hKL ζ hζ u s, h (ι K L s) hs, add_zero]

variable [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] [Normal ↥K ↥(levelField K L hKL)]

omit [Normal ↥K ↥(levelField K L hKL)] in

lemma mk_mem_selmer_iff_isLevelConstant (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (hL : L.IsUnramifiedOutside S)
    (u : (↥(levelField K L hKL))ˣ) :
    unitsModPow.mk (↥(levelField K L hKL)) p u ∈ selmer ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p ↔
      IsLevelConstantSr₁ (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S (κfun K L hKL ζ hζ u) := by
  rw [isLevelConstant_κfun_iff K L hKL ζ hζ hζL S,
    kummerChar_isLevelConstant_iff_forall_dvd_valuation p S hpS ζ hζ L hL hζL (uL K L hKL u),
    NumberField.LevelArith.mem_selmer_iff]
  constructor
  · intro h w hw
    have h1 := h (placeEquiv K L hKL w) (by rwa [mem_placesAbove_iff S K L hKL, mem_placesOverPrimes_placeEquiv_iff])
    rw [← valuationOfNeZero_placeEquiv K L hKL w u, ← valuationOfNeZeroMod_mk_eq_one_iff]
    exact h1
  · intro h v hv
    obtain ⟨w, rfl⟩ := (placeEquiv K L hKL).surjective v
    have h1 := h w (by rwa [mem_placesAbove_iff S K L hKL, mem_placesOverPrimes_placeEquiv_iff] at hv)
    rw [← valuationOfNeZero_placeEquiv K L hKL w u, ← valuationOfNeZeroMod_mk_eq_one_iff] at h1
    exact h1

end kappa

end CycBaseK2cB
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom.CycBaseK2cB"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom.CycBaseK2cB"

noncomputable section

namespace CycBaseK2cB

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
  (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
  [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L] (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)

include hpS hL hζL in
omit [Normal ↥K ↥(levelField K L hKL)] in

lemma mem_selmerStable_iff (q : unitsModPow (↥(levelField K L hKL)) p) :
    q ∈ selmerStable ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p ↔
      Multiplicative.toAdd (κ K L hKL ζ hζ hζL q) ∈
        levelConstantHom (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S (ZMod p) (ZMod p) := by
  obtain ⟨u, rfl⟩ := unitsModPow.mk_surjective _ p q
  rw [selmerStable_eq_selmer, mk_mem_selmer_iff_isLevelConstant K L hKL ζ hζ hζL S hpS hL u, mem_levelConstantHom_iff]
  exact ⟨fun h => ⟨κfun_add K L hKL ζ hζ hζL u, h⟩, fun h => h.2⟩

def cls (x : selmerRep K L hKL S p) : unitsModPow (↥(levelField K L hKL)) p :=
  Additive.toMul (x.1 : Additive (unitsModPow (↥(levelField K L hKL)) p))

lemma cls_add (x y : selmerRep K L hKL S p) : cls S K L hKL (x + y) = cls S K L hKL x * cls S K L hKL y := rfl

lemma cls_zero : cls S K L hKL (0 : selmerRep K L hKL S p) = 1 := rfl

lemma cls_ρ (g : ↥K.fixingSubgroup) (x : selmerRep K L hKL S p) :
    cls S K L hKL ((selmerRep K L hKL S p).ρ g x) = (levelGal K L hKL g) • cls S K L hKL x := rfl

lemma cls_mem (x : selmerRep K L hKL S p) : cls S K L hKL x ∈ selmerStable ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p := x.2

lemma eq_zero_of_cls_eq_one {x : selmerRep K L hKL S p} (h : cls S K L hKL x = 1) : x = 0 :=
  Subtype.ext (by
    change Additive.ofMul (cls S K L hKL x) = (0 : Additive (unitsModPow (↥(levelField K L hKL)) p))
    rw [h]; rfl)

def ofCls (q : unitsModPow (↥(levelField K L hKL)) p)
    (hq : q ∈ selmerStable ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p) : selmerRep K L hKL S p :=
  ⟨Additive.ofMul q, hq⟩

lemma cls_ofCls (q : unitsModPow (↥(levelField K L hKL)) p)
    (hq : q ∈ selmerStable ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p) : cls S K L hKL (ofCls S K L hKL q hq) = q := rfl

def fB₀ : selmerRep K L hKL S p →+
    ↥(levelConstantHom (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S (ZMod p) (ZMod p)) where
  toFun x := ⟨Multiplicative.toAdd (κ K L hKL ζ hζ hζL (cls S K L hKL x)),
    (mem_selmerStable_iff S hpS K L hL hKL ζ hζ hζL _).mp (cls_mem S K L hKL x)⟩
  map_zero' := Subtype.ext (by
    show Multiplicative.toAdd (κ K L hKL ζ hζ hζL (cls S K L hKL 0)) = 0
    rw [cls_zero, map_one, toAdd_one])
  map_add' x y := Subtype.ext (by
    show Multiplicative.toAdd (κ K L hKL ζ hζ hζL (cls S K L hKL (x + y))) =
      Multiplicative.toAdd (κ K L hKL ζ hζ hζL (cls S K L hKL x)) + Multiplicative.toAdd (κ K L hKL ζ hζ hζL (cls S K L hKL y))
    rw [cls_add, map_mul, toAdd_mul])

def fB : selmerRep K L hKL S p →ₗ[ZMod p]
    ↥(levelConstantHom (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S (ZMod p) (ZMod p)) :=
  (fB₀ S hpS K L hL hKL ζ hζ hζL).toZModLinearMap p

lemma fB_apply (x : selmerRep K L hKL S p) (s : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)) :
    (fB S hpS K L hL hKL ζ hζ hζL x : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) s =
      Multiplicative.toAdd (κ K L hKL ζ hζ hζL (cls S K L hKL x)) s := rfl

lemma fB_injective : Function.Injective (fB S hpS K L hL hKL ζ hζ hζL) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨u, hu⟩ := unitsModPow.mk_surjective _ p (cls S K L hKL x)
  have h0 : ∀ σ : ↥L.fixingSubgroup, kummerChar p ζ hζ L (uL K L hKL u) σ = 0 := by
    intro σ
    have h1 := congrArg (fun φ : ↥(levelConstantHom (K.fixingSubgroup.subtype.comp
      (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S (ZMod p) (ZMod p)) =>
        (φ : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) (ι' K L hKL σ)) hx
    simp only at h1
    rw [fB_apply, ← hu, κ_mk, toAdd_ofAdd, κfun_apply] at h1
    exact h1
  obtain ⟨v, hv⟩ := (kummerChar_eq_zero_iff p ζ hζ L hζL (uL K L hKL u)).mp h0
  apply eq_zero_of_cls_eq_one S K L hKL
  rw [← hu]
  apply (QuotientGroup.eq_one_iff u).mpr
  refine ⟨(uL K L hKL).symm v, ?_⟩
  apply (uL K L hKL).injective
  rw [powMonoidHom_apply, map_pow, MulEquiv.apply_symm_apply, ← powMonoidHom_apply, hv]

lemma fB_surjective : Function.Surjective (fB S hpS K L hL hKL ζ hζ hζL) := by
  intro φ
  obtain ⟨hadd, F', hF', hlc⟩ := φ.2
  haveI : FiniteDimensional ℚ ↥F' := hF'.1
  haveI : FiniteDimensional ℚ ↥(L ⊔ F') := IntermediateField.finiteDimensional_sup L F'
  have hφ1 : (φ : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) 1 = 0 := by
    have h := hadd 1 1; rw [mul_one] at h; exact left_eq_add.mp h
  obtain ⟨xL, hxL⟩ := exists_kummerChar_eq_of_continuous p ζ hζ L hζL
    (fun σ => (φ : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) (ι' K L hKL σ))
    (fun σ τ => by
      show (φ : _ → ZMod p) (ι' K L hKL σ * ι' K L hKL τ) = (φ : _ → ZMod p) (ι' K L hKL σ) + (φ : _ → ZMod p) (ι' K L hKL τ)
      exact hadd _ _) (L ⊔ F') le_sup_left (fun σ hσ => by
      have h := hlc 1 (ι' K L hKL σ) (IntermediateField.fixingSubgroup_antitone le_sup_right hσ)
      rw [one_mul, hφ1] at h
      exact h)
  have hu : uL K L hKL ((uL K L hKL).symm xL) = xL := MulEquiv.apply_symm_apply _ _
  have hκ : κfun K L hKL ζ hζ ((uL K L hKL).symm xL) = (φ : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) := by
    funext s; rw [κfun_apply, hu, hxL]; rfl
  have hmem : unitsModPow.mk _ p ((uL K L hKL).symm xL) ∈ selmerStable ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p := by
    rw [mem_selmerStable_iff S hpS K L hL hKL ζ hζ hζL, κ_mk, toAdd_ofAdd, hκ]; exact φ.2
  refine ⟨ofCls S K L hKL _ hmem, ?_⟩
  apply Subtype.ext; funext s
  rw [fB_apply, cls_ofCls, κ_mk, toAdd_ofAdd, hκ]

include hζL in

lemma kummerChar_uL_eq_of_coe_eq (g : ↥K.fixingSubgroup) (u v : (↥(levelField K L hKL))ˣ)
    (hv : (((v : ↥(levelField K L hKL)) : AlgebraicClosure ℚ)) =
      ((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (((u : ↥(levelField K L hKL)) : AlgebraicClosure ℚ)))
    (s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)) (hst : (g⁻¹ * s * g : ↥K.fixingSubgroup) = t) :
    kummerChar p ζ hζ L (uL K L hKL v) (ι K L s) =
      ((cycloChar p ((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : (ZMod p)ˣ) : ZMod p) *
        kummerChar p ζ hζ L (uL K L hKL u) (ι K L t) := by
  have hγL : ∀ z ∈ L, ((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) z ∈ L := by
    intro z hz
    have h := levelGal_apply_coe K L hKL g ⟨z, (IntermediateField.mem_extendScalars hKL).2 hz⟩
    rw [← h]
    exact (IntermediateField.mem_extendScalars hKL).1 (Subtype.property _)
  have hcalc : ((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) *
      ((ι K L t : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) *
        ((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)⁻¹ =
      ((s : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := by
    rw [coe_ι, ← hst, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hconj : ((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) *
      ((ι K L t : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) *
        ((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)⁻¹ ∈ L.fixingSubgroup := by
    rw [hcalc]; exact Subgroup.mem_subgroupOf.mp s.2
  have hx' : (((uL K L hKL v : (↥L)ˣ) : ↥L) : AlgebraicClosure ℚ) =
      ((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (((uL K L hKL u : (↥L)ˣ) : ↥L) : AlgebraicClosure ℚ) := by
    rw [coe_uL, coe_uL]; exact hv
  have hE := kummerChar_conj_eq_cycloChar_mul p ζ hζ L hζL ((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    hγL (ι K L t) hconj (uL K L hKL u) (uL K L hKL v) hx'
  have hs : (⟨((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) *
      ((ι K L t : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) *
        ((g : ↥K.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)⁻¹, hconj⟩ : ↥L.fixingSubgroup) = ι K L s :=
    Subtype.ext hcalc
  rw [hs] at hE
  exact hE

lemma fB_smul (g : ↥K.fixingSubgroup) (x : selmerRep K L hKL S p) (s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup))
    (hst : (g⁻¹ * s * g : ↥K.fixingSubgroup) = t) :
    (fB S hpS K L hL hKL ζ hζ hζL ((selmerRep K L hKL S p).ρ g x) : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) s =
      ((((cycloChar p).comp K.fixingSubgroup.subtype) g : (ZMod p)ˣ) : ZMod p) *
        (fB S hpS K L hL hKL ζ hζ hζL x : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) t := by
  letI : MulDistribMulAction (LevelGal K L hKL) (↥(levelField K L hKL))ˣ := inferInstance
  rw [fB_apply, fB_apply]
  obtain ⟨u, hu⟩ := unitsModPow.mk_surjective _ p (cls S K L hKL x)
  rw [cls_ρ, ← hu, smul_mk, κ_mk, κ_mk, toAdd_ofAdd, toAdd_ofAdd, κfun_apply, κfun_apply]
  exact kummerChar_uL_eq_of_coe_eq K L hKL ζ hζ hζL g u _ (levelGal_apply_coe K L hKL g (u : ↥(levelField K L hKL))) s t hst

end CycBaseK2cB
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom.CycBaseK2cB"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom.CycBaseK2cB"

open CycBaseK2cB in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L) :
    ∃ e : (selmerRep K L hKL S p) ≃ₗ[ZMod p]
        ↥(levelConstantHom (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S (ZMod p) (ZMod p)),
      ∀ (g : ↥K.fixingSubgroup) (x : selmerRep K L hKL S p) (s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)),
        (g⁻¹ * s * g : ↥K.fixingSubgroup) = t →
          (e ((selmerRep K L hKL S p).ρ g x) : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) s =
            ((((cycloChar p).comp K.fixingSubgroup.subtype) g : (ZMod p)ˣ) : ZMod p) *
              (e x : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) t :=
  ⟨LinearEquiv.ofBijective (fB S hpS K L hL hKL ζ hζ hζL) ⟨fB_injective S hpS K L hL hKL ζ hζ hζL, fB_surjective S hpS K L hL hKL ζ hζ hζL⟩,
    fun g x s t hst => by
      rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply]
      exact fB_smul S hpS K L hL hKL ζ hζ hζL g x s t hst⟩

end S_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom
end P2MW
export P2MW.S_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom (solution)
