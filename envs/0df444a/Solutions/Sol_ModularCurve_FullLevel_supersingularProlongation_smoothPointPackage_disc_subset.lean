-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_disc_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/7f4e6477-67b9-57b9-8061-f5b760a2acc6

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_AlgebraicCurve_RegularProlongation_isResidueDisc_of_etaleChart_of_sections
import Theorems.Thm_AlgebraicCurve_Place_exists_not_mem_range_and_forall_ne_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset.AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ConstantReduction Place Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue Place.evalAt_algebraMap RegularProlongation RegularProlongation.isResidueDisc_of_etaleChart_of_sections Place.exists_not_mem_range_and_forall_ne_ord_nonneg Place.evalAt_eq_zero_iff_one_le_ord"
namespace DiscRigidity
p2m_open "AlgebraicCurve"

attribute [local instance] Classical.propDecidable

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem coe_sub' (v : Place L F) (a b : v.toValuationSubring) : ((a - b : v.toValuationSubring) : F) = a - b := by simp

theorem ord_algebraMap_mul (v : Place L F) {c : L} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) :
    v.ord (algebraMap L F c * f) = v.ord f := by
  have hu : IsUnit (⟨algebraMap L F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) := by
    refine IsUnit.of_mul_eq_one ⟨algebraMap L F c⁻¹, v.algebraMap_mem' c⁻¹⟩ ?_
    apply Subtype.ext
    show algebraMap L F c * algebraMap L F c⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  obtain ⟨u, hu'⟩ := hu
  have h0 : v.ord (algebraMap L F c) = 0 := by
    have := v.ord_coe_unit u
    rwa [hu'] at this
  have hc' : algebraMap L F c ≠ 0 := (map_ne_zero (algebraMap L F)).mpr hc
  rw [v.ord_mul hc' hf, h0, zero_add]

theorem evalAt_sub (v : Place L F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_sub]
  congr 1

theorem isRational_of_isAlgClosed [IsAlgClosed L] [IsCurveOver L F] (v : Place L F) : v.IsRational := by
  haveI : Module.Finite L v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral L v.ResidueField := Algebra.IsIntegral.of_finite L v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := v.ResidueField)).2

theorem degree_eq_sum [IsAlgClosed L] [IsCurveOver L F] (Df : Divisor L F) :
    Divisor.degree Df = ∑ v ∈ Df.support, Df v := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [AddMonoidHom.mulRight_apply, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one]

variable (A : ValuationSubring L) {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]

theorem sum_filter_eq_of_degreeOn (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (D D' : Set (Place L F)) (hD : R.DegreeOn Q D) (hD' : R.DegreeOn Q D')
    (f : F) (hf : f ≠ 0) (Df : Divisor L F) (hDf : ∀ v, Df v = v.ord f) :
    (∑ v ∈ Df.support with v ∈ D, Df v) = ∑ v ∈ Df.support with v ∈ D', Df v := by
  classical
  obtain ⟨c, hcf, hres⟩ := R.exists_smul_mem f hf
  have hc : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : L) • f, hcf⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  have hord : ∀ v : Place L F, v.ord (c • f) = v.ord f := fun v => by
    rw [Algebra.smul_def]; exact ord_algebraMap_mul v hc hf
  have key : ∀ X : Set (Place L F), R.DegreeOn Q X →
      (Df.filter (· ∈ X)).sum (fun _ n => n) = Q.ord (R.residue ⟨c • f, hcf⟩) := fun X hX =>
    hX ⟨c • f, hcf⟩ hres (Df.filter (· ∈ X))
      (fun P hP => by rw [Finsupp.filter_apply_pos _ _ hP, hDf, hord])
      (fun P hP => by rw [Finsupp.filter_apply_neg _ _ hP])
  have e : ∀ X : Set (Place L F), (Df.filter (· ∈ X)).sum (fun _ n => n) = ∑ v ∈ Df.support with v ∈ X, Df v := by
    intro X
    rw [Finsupp.sum, Finsupp.support_filter]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finsupp.filter_apply_pos _ _ hv.2]
  rw [← e D, ← e D', key D hD, key D' hD']

theorem mem_and_not_mem_of_degreeOn [IsAlgClosed L] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (D D' : Set (Place L F)) (hD : R.DegreeOn Q D) (hD' : R.DegreeOn Q D')
    (P₂ : Place L F) (hP₂D : P₂ ∈ D) (hP₂D' : P₂ ∉ D') (P₁ : Place L F) : P₁ ∈ D ∧ P₁ ∉ D' := by
  classical
  by_cases h12 : P₁ = P₂
  · subst h12; exact ⟨hP₂D, hP₂D'⟩
  obtain ⟨h, hnc, hreg⟩ := Place.exists_not_mem_range_and_forall_ne_ord_nonneg L F P₂
  have hrat : P₁.IsRational := isRational_of_isAlgClosed P₁
  have h0 : h ≠ 0 := fun h0 => hnc ⟨0, by rw [h0, map_zero]⟩
  have hmem : ∀ v : Place L F, v ≠ P₂ → h ∈ v.toValuationSubring := fun v hv =>
    Place.mem_of_ord_nonneg v h0 (hreg v hv)
  set a : L := P₁.evalAt h with ha
  set f : F := h - algebraMap L F a with hfdef
  have hf0 : f ≠ 0 := fun hf => hnc ⟨a, (sub_eq_zero.mp hf).symm⟩
  have hfmem : ∀ v : Place L F, v ≠ P₂ → f ∈ v.toValuationSubring := fun v hv =>
    sub_mem (hmem v hv) (v.algebraMap_mem' a)
  have hfP₁ : 1 ≤ P₁.ord f := by
    rw [← Place.evalAt_eq_zero_iff_one_le_ord P₁ hrat hf0 (hfmem P₁ h12), hfdef,
      evalAt_sub P₁ hrat (hmem P₁ h12) (P₁.algebraMap_mem' a), Place.evalAt_algebraMap, ha, sub_self]
  obtain ⟨Df, hDf, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0
  have htot : ∑ v ∈ Df.support, Df v = 0 := by rw [← degree_eq_sum]; exact hdeg
  have hsum := sum_filter_eq_of_degreeOn A R Q D D' hD hD' f hf0 Df hDf

  have e1 : ∀ X : Set (Place L F),
      ∑ v ∈ Df.support, Df v * (if v ∈ X then (1 : ℤ) else 0) = ∑ v ∈ Df.support with v ∈ X, Df v := by
    intro X
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  have hzero : ∑ v ∈ Df.support,
      Df v * ((if v ∈ D' then (1 : ℤ) else 0) - (if v ∈ D then (1 : ℤ) else 0) + 1) = 0 := by
    have : ∀ v ∈ Df.support, Df v * ((if v ∈ D' then (1 : ℤ) else 0) - (if v ∈ D then (1 : ℤ) else 0) + 1) =
        Df v * (if v ∈ D' then (1 : ℤ) else 0) - Df v * (if v ∈ D then (1 : ℤ) else 0) + Df v := by
      intro v _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, e1, hsum, htot, sub_self,
      zero_add]
  have hnonneg : ∀ v ∈ Df.support,
      0 ≤ Df v * ((if v ∈ D' then (1 : ℤ) else 0) - (if v ∈ D then (1 : ℤ) else 0) + 1) := by
    intro v _
    by_cases hv : v = P₂
    · subst hv
      rw [if_neg hP₂D', if_pos hP₂D]
      simp
    · have h1 : 0 ≤ Df v := by rw [hDf]; exact Place.ord_nonneg_of_mem v (hfmem v hv)
      have h2 : (0 : ℤ) ≤ (if v ∈ D' then (1 : ℤ) else 0) - (if v ∈ D then (1 : ℤ) else 0) + 1 := by
        split_ifs <;> norm_num
      exact mul_nonneg h1 h2
  have hP₁supp : P₁ ∈ Df.support := by
    rw [Finsupp.mem_support_iff, hDf]; omega
  have ht := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero P₁ hP₁supp
  have hDf1 : 0 < Df P₁ := by rw [hDf]; omega
  have hfac : (if P₁ ∈ D' then (1 : ℤ) else 0) - (if P₁ ∈ D then (1 : ℤ) else 0) + 1 = 0 := by
    rcases mul_eq_zero.mp ht with h | h
    · omega
    · exact h
  by_cases h1 : P₁ ∈ D'
  · by_cases h2 : P₁ ∈ D
    · rw [if_pos h1, if_pos h2] at hfac; omega
    · rw [if_pos h1, if_neg h2] at hfac; omega
  · by_cases h2 : P₁ ∈ D
    · exact ⟨h2, h1⟩
    · rw [if_neg h1, if_neg h2] at hfac; omega

theorem subset_of_degreeOn [IsAlgClosed L] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (D D' : Set (Place L F)) (hD : R.DegreeOn Q D) (hD' : R.DegreeOn Q D') (hne' : D'.Nonempty) :
    D ⊆ D' := by
  intro P₂ hP₂D
  by_contra hP₂D'
  obtain ⟨P', hP'⟩ := hne'
  exact (mem_and_not_mem_of_degreeOn A R Q D D' hD hD' P₂ hP₂D hP₂D' P').2 hP'

theorem eq_of_degreeOn [IsAlgClosed L] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (D D' : Set (Place L F)) (hD : R.DegreeOn Q D) (hD' : R.DegreeOn Q D')
    (hne : D.Nonempty) (hne' : D'.Nonempty) : D = D' :=
  Set.Subset.antisymm (subset_of_degreeOn A R Q D D' hD hD' hne') (subset_of_degreeOn A R Q D' D hD' hD hne)

theorem nonempty_of_isResidueDisc (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (D : Set (Place L F)) (z : F) (hD : R.IsResidueDisc Q D z) : D.Nonempty := by
  obtain ⟨-, hz, -, huniq, -, -⟩ := hD.1
  obtain ⟨P, ⟨hP, -⟩, -⟩ := huniq 0 (by rw [map_zero]; exact zero_lt_one)
  exact ⟨P, hP⟩

theorem eq_of_isResidueDisc [IsAlgClosed L] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (D : Set (Place L F)) (z : F) (hD : R.IsResidueDisc Q D z)
    (D' : Set (Place L F)) (z' : F) (hD' : R.IsResidueDisc Q D' z') : D = D' :=
  eq_of_degreeOn A R Q D D' hD.2.2 hD'.2.2 (nonempty_of_isResidueDisc A R Q D z hD)
    (nonempty_of_isResidueDisc A R Q D' z' hD')

theorem exists_testDivisor [IsAlgClosed L] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (P₁ P₂ : Place L F) (h12 : P₁ ≠ P₂) :
    ∃ (f : F) (_ : f ≠ 0) (Df : Divisor L F), (∀ v, Df v = v.ord f) ∧
      (∀ v, v ≠ P₂ → 0 ≤ Df v) ∧ 0 < Df P₁ ∧ ∑ v ∈ Df.support, Df v = 0 := by
  obtain ⟨h, hnc, hreg⟩ := Place.exists_not_mem_range_and_forall_ne_ord_nonneg L F P₂
  have hrat : P₁.IsRational := isRational_of_isAlgClosed P₁
  have h0 : h ≠ 0 := fun h0 => hnc ⟨0, by rw [h0, map_zero]⟩
  have hmem : ∀ v : Place L F, v ≠ P₂ → h ∈ v.toValuationSubring := fun v hv =>
    Place.mem_of_ord_nonneg v h0 (hreg v hv)
  set a : L := P₁.evalAt h with ha
  set f : F := h - algebraMap L F a with hfdef
  have hf0 : f ≠ 0 := fun hf => hnc ⟨a, (sub_eq_zero.mp hf).symm⟩
  have hfmem : ∀ v : Place L F, v ≠ P₂ → f ∈ v.toValuationSubring := fun v hv =>
    sub_mem (hmem v hv) (v.algebraMap_mem' a)
  have hfP₁ : 1 ≤ P₁.ord f := by
    rw [← Place.evalAt_eq_zero_iff_one_le_ord P₁ hrat hf0 (hfmem P₁ h12), hfdef,
      evalAt_sub P₁ hrat (hmem P₁ h12) (P₁.algebraMap_mem' a), Place.evalAt_algebraMap, ha, sub_self]
  obtain ⟨Df, hDf, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0
  refine ⟨f, hf0, Df, hDf, fun v hv => ?_, ?_, ?_⟩
  · rw [hDf]; exact Place.ord_nonneg_of_mem v (hfmem v hv)
  · rw [hDf]; omega
  · rw [← degree_eq_sum]; exact hdeg

theorem eq_of_forall_sum_ord_mul_eq_zero [IsAlgClosed L] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (w : Place L F → ℤ) (hbdd : BddBelow (Set.range w))
    (hsum : ∀ f : F, f ≠ 0 → ∀ Df : Divisor L F, (∀ v, Df v = v.ord f) → ∑ v ∈ Df.support, Df v * w v = 0)
    (P P' : Place L F) : w P = w P' := by
  have hne : (Set.range w).Nonempty := ⟨w P, P, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂, w P₂ = sInf (Set.range w) := Int.csInf_mem hne hbdd
  have hmin : ∀ v, w P₂ ≤ w v := fun v => by rw [hP₂]; exact csInf_le hbdd ⟨v, rfl⟩
  have key : ∀ P₁, w P₁ = w P₂ := by
    intro P₁
    by_cases h12 : P₁ = P₂
    · rw [h12]
    obtain ⟨f, hf0, Df, hDf, hnn, hpos, htot⟩ := exists_testDivisor P₁ P₂ h12
    have hzero : ∑ v ∈ Df.support, Df v * (w v - w P₂) = 0 := by
      have : ∀ v ∈ Df.support, Df v * (w v - w P₂) = Df v * w v - w P₂ * Df v := by intro v _; ring
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum f hf0 Df hDf, htot, mul_zero,
        sub_self]
    have hnonneg : ∀ v ∈ Df.support, 0 ≤ Df v * (w v - w P₂) := by
      intro v _
      by_cases hv : v = P₂
      · rw [hv, sub_self, mul_zero]
      · exact mul_nonneg (hnn v hv) (by linarith [hmin v])
    have hP₁supp : P₁ ∈ Df.support := by rw [Finsupp.mem_support_iff]; omega
    have ht := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero P₁ hP₁supp
    rcases mul_eq_zero.mp ht with h | h
    · omega
    · omega
  rw [key P, key P']

end AlgebraicCurve.DiscRigidity

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (h0 : (∃ t : FSS, Transcendental (ResidueField A) t))
    (h1 : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))))
    (h2 : (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers))
    (Q : Place (ResidueField ↥A) FSS)

    (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
    (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (hpk :
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S) ∧
            (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧
            (∀ a : ↥A, ((φ (Polynomial.C a) : ↥(S)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φ Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S)) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S))

    (S' : Subring ↥(fieldBar q M')) (φ' : Polynomial ↥A →+* ↥S') (χ₀' : ↥S' →+* ResidueField ↥A)
    (D' : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (hpk' :
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S') ∧
            (φ').FormallySmooth ∧ (φ').FormallyUnramified ∧
            (∀ a : ↥A, ((φ' (Polynomial.C a) : ↥(S')) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀' (φ' (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀' (φ' Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S') →+* ↥A, (∀ a : ↥A, χ (φ' (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S'), IsLocalRing.residue ↥A (χ f) = χ₀' f) ∧ χ (φ' Polynomial.X) = c) ∧
            (∀ f : ↥(S'), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀' f)) ∧
            (∃ hR : ((φ' Polynomial.X : ↥(S')) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φ' Polynomial.X : ↥(S')) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D' ↔ (P.IsRational ∧ (∀ f : ↥(S'), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S'), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀' f = 0))) ∧
            (∀ χ : ↥(S') →+* ↥A, (∀ a : ↥A, χ (φ' (Polynomial.C a)) = a) →
              (∀ f : ↥(S'), IsLocalRing.residue ↥A (χ f) = χ₀' f) →
              ∃! P, P ∈ D' ∧ ∀ f : ↥(S'), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D', ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S'), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D', P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S'))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S')) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D', f ∈ P.toValuationSubring) → f ∈ S')) :
    ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ D → P ∈ D' := by
  classical

  obtain ⟨hCurve, hEFT⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
    (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(fieldBar q M') := hCurve
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(fieldBar q M') := hEFT

  have hdisc : ∀ (S₁ : Subring ↥(fieldBar q M')) (φ₁ : Polynomial ↥A →+* ↥S₁) (χ₁ : ↥S₁ →+* ResidueField ↥A)
      (D₁ : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
      ((∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S₁) ∧
            (φ₁).FormallySmooth ∧ (φ₁).FormallyUnramified ∧
            (∀ a : ↥A, ((φ₁ (Polynomial.C a) : ↥(S₁)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₁ (φ₁ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₁ (φ₁ Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S₁) →+* ↥A, (∀ a : ↥A, χ (φ₁ (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S₁), IsLocalRing.residue ↥A (χ f) = χ₁ f) ∧ χ (φ₁ Polynomial.X) = c) ∧
            (∀ f : ↥(S₁), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₁ f)) ∧
            (∃ hR : ((φ₁ Polynomial.X : ↥(S₁)) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φ₁ Polynomial.X : ↥(S₁)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D₁ ↔ (P.IsRational ∧ (∀ f : ↥(S₁), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S₁), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₁ f = 0))) ∧
            (∀ χ : ↥(S₁) →+* ↥A, (∀ a : ↥A, χ (φ₁ (Polynomial.C a)) = a) →
              (∀ f : ↥(S₁), IsLocalRing.residue ↥A (χ f) = χ₁ f) →
              ∃! P, P ∈ D₁ ∧ ∀ f : ↥(S₁), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D₁, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S₁), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D₁, P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S₁))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S₁)) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D₁, f ∈ P.toValuationSubring) → f ∈ S₁)) →
      R.IsResidueDisc Q D₁ ((φ₁ Polynomial.X : ↥S₁) : ↥(fieldBar q M')) := by
    intro S₁ φ₁ χ₁ D₁ hpk₁
    obtain ⟨hAS, hφs, hφu, hφC, hχC, hχt, hchart, hres, hordQ, hDdef, hsec, hval, hloc, hloc'⟩ := hpk₁
    have hSR : ∀ f : ↥S₁, (f : ↥(fieldBar q M')) ∈ R.integers := fun f => (hres f).1
    refine AlgebraicCurve.RegularProlongation.isResidueDisc_of_etaleChart_of_sections R Q S₁ hAS φ₁ hφs hφu hφC χ₁
      hχC hχt hchart hSR (fun f => ?_) ?_ D₁ (fun P hP => (hDdef P).mp hP) hsec hval hloc hloc'
    · obtain ⟨hR, hm, e⟩ := hres f
      exact ⟨hm, e⟩
    · obtain ⟨hR, e⟩ := hordQ
      exact e
  have hD₁ := hdisc S φ χ₀ D hpk
  have hD₂ := hdisc S' φ' χ₀' D' hpk'
  have hEq := AlgebraicCurve.DiscRigidity.eq_of_isResidueDisc A R Q D _ hD₁ D' _ hD₂
  intro P hP
  rw [← hEq]
  exact hP

end S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset (solution)
