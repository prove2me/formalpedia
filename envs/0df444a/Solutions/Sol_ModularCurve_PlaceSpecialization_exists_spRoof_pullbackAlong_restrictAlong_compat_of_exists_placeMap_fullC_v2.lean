-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_spRoof_pullbackAlong_restrictAlong_compat_of_exists_placeMap_fullC_v2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ff2307d0-7337-5588-af1b-fa6ae414fede

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_riemannConstant_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_spRoof_pullbackAlong_restrictAlong_compat_of_exists_placeMap_fullC_v2
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace P2mSolSpRoofV2

open Finsupp

section Finsupp

variable {X Y : Type*}

theorem mapDomain_apply_eq_sum [DecidableEq Y] (r : X → Y) (D : X →₀ ℤ) (y : Y) :
    mapDomain r D y = ∑ x ∈ D.support, if r x = y then D x else 0 := by
  simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mapDomain_nonneg (r : X → Y) {D : X →₀ ℤ} (hD : ∀ x, 0 ≤ D x) (y : Y) :
    0 ≤ mapDomain r D y := by
  classical
  rw [mapDomain_apply_eq_sum]
  refine Finset.sum_nonneg fun x _ => ?_
  split_ifs
  · exact hD x
  · exact le_rfl

theorem mapDomain_apply_le_sum (r : X → Y) {D : X →₀ ℤ} (hD : ∀ x, 0 ≤ D x) (y : Y) :
    mapDomain r D y ≤ ∑ x ∈ D.support, D x := by
  classical
  rw [mapDomain_apply_eq_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs
  · exact le_rfl
  · exact hD x

theorem le_mapDomain_apply_self (r : X → Y) {D : X →₀ ℤ} (hD : ∀ x, 0 ≤ D x) (x : X) :
    D x ≤ mapDomain r D (r x) := by
  classical
  by_cases hx : x ∈ D.support
  · rw [mapDomain_apply_eq_sum]
    have := Finset.single_le_sum (f := fun x' => if r x' = r x then D x' else 0)
      (fun x' _ => by
        split_ifs
        · exact hD x'
        · exact le_rfl) hx
    simpa using this
  · rw [Finsupp.notMem_support_iff.mp hx]
    exact mapDomain_nonneg r hD _

theorem mapDomain_apply_of_forall_eq (r : X → Y) (D : X →₀ ℤ) {y : Y} (h : ∀ x, r x = y) :
    mapDomain r D y = ∑ x ∈ D.support, D x := by
  classical
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [if_pos (h x)]

theorem map_single_eq_zsmul {G : Type*} [AddCommGroup G] (Φ : (X →₀ ℤ) →+ G) (x : X)
    (n : ℤ) : Φ (single x n) = n • Φ (single x 1) := by
  rw [← map_zsmul, Finsupp.smul_single_one]

end Finsupp

section Rational

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum (h1 : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [h1 v]

theorem degree_nonneg (h1 : ∀ v : Place K F, v.deg = 1) {D : Divisor K F}
    (hD : ∀ v, 0 ≤ D v) : 0 ≤ Divisor.degree D := by
  rw [degree_eq_sum h1]
  exact Finset.sum_nonneg fun v _ => hD v

theorem eq_zero_of_nonneg_of_degree_eq_zero (h1 : ∀ v : Place K F, v.deg = 1)
    {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) (hdeg : Divisor.degree D = 0) : D = 0 := by
  rw [degree_eq_sum h1] at hdeg
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hD v)).mp hdeg
  ext v
  by_cases hv : v ∈ D.support
  · exact hall v hv
  · exact Finsupp.notMem_support_iff.mp hv

theorem degree_mapDomain_eq {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    (h1 : ∀ v : Place K F, v.deg = 1) (h1' : ∀ w : Place K' F', w.deg = 1)
    (r : Place K F → Place K' F') (D : Divisor K F) :
    Divisor.degree (mapDomain r D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, h1, h1']

end Rational

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

include hφ in
theorem ramificationIndexAlong_pos (w : Place K F') : 0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

theorem pullbackAlong_nonneg {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) (w : Place K F') :
    0 ≤ Divisor.pullbackAlong φ hφ D w := by
  rw [Divisor.pullbackAlong_apply]
  exact mul_nonneg (Int.natCast_nonneg _) (hD _)

theorem single_one_nonneg {X : Type*} (x : X) : ∀ x', 0 ≤ (single x (1 : ℤ)) x' := by
  classical
  intro x'
  rw [Finsupp.single_apply]
  split_ifs <;> norm_num

theorem pullbackAlong_single_nonneg (v : Place K F) (w : Place K F') :
    0 ≤ Divisor.pullbackAlong φ hφ (single v 1) w :=
  pullbackAlong_nonneg φ hφ (single_one_nonneg v) w

theorem pullbackAlong_single_apply_of_ne {v : Place K F} {w : Place K F'}
    (h : w.restrictAlong φ hφ ≠ v) : Divisor.pullbackAlong φ hφ (single v 1) w = 0 := by
  classical
  rw [Divisor.pullbackAlong_apply, Finsupp.single_apply, if_neg (Ne.symm h), mul_zero]

theorem pullbackAlong_single_apply_self (w : Place K F') :
    Divisor.pullbackAlong φ hφ (single (w.restrictAlong φ hφ) 1) w
      = Place.ramificationIndexAlong φ w := by
  rw [Divisor.pullbackAlong_apply, Finsupp.single_eq_same, mul_one]

theorem pullbackAlong_single_apply_le (v : Place K F) (w : Place K F') :
    Divisor.pullbackAlong φ hφ (single v 1) w ≤ Place.ramificationIndexAlong φ w := by
  classical
  rw [Divisor.pullbackAlong_apply, Finsupp.single_apply]
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]; exact Int.natCast_nonneg _

theorem pullbackAlong_apply_le_mul_sum {E : Divisor K F} (hE : ∀ v, 0 ≤ E v) (w : Place K F') :
    Divisor.pullbackAlong φ hφ E w
      ≤ Place.ramificationIndexAlong φ w * ∑ v ∈ E.support, E v := by
  classical
  rw [Divisor.pullbackAlong_apply]
  refine mul_le_mul_of_nonneg_left ?_ (Int.natCast_nonneg _)
  by_cases hx : w.restrictAlong φ hφ ∈ E.support
  · exact Finset.single_le_sum (f := fun v => E v) (fun v _ => hE v) hx
  · rw [Finsupp.notMem_support_iff.mp hx]
    exact Finset.sum_nonneg fun v _ => hE v

end Along

section Engine

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra L F₁] [Algebra L F₂]
variable {C₁ C₂ : Type*} [Field C₁] [Field C₂]
  [Algebra (ResidueField A) C₁] [Algebra (ResidueField A) C₂]
variable [HasPrincipalDivisors L F₂] [HasPrincipalDivisors (ResidueField A) C₂]
variable (φ : F₁ →ₐ[L] F₂) (hφ : φ.toRingHom.IsIntegral)
variable (φb : C₁ →ₐ[ResidueField A] C₂) (hφb : φb.toRingHom.IsIntegral)
variable (r₁ : Place L F₁ → Place (ResidueField A) C₁)
variable (r : Place L F₂ → Place (ResidueField A) C₂)

def defect (v : Place L F₁) : Divisor (ResidueField A) C₂ :=
  mapDomain r (Divisor.pullbackAlong φ hφ (single v 1))
    - Divisor.pullbackAlong φb hφb (single (r₁ v) 1)

def defectHom : Divisor L F₁ →+ Divisor (ResidueField A) C₂ :=
  (Finsupp.mapDomain.addMonoidHom r).comp (Divisor.pullbackAlong φ hφ)
    - (Divisor.pullbackAlong φb hφb).comp (Finsupp.mapDomain.addMonoidHom r₁)

theorem defectHom_apply (D : Divisor L F₁) :
    defectHom φ hφ φb hφb r₁ r D
      = mapDomain r (Divisor.pullbackAlong φ hφ D)
          - Divisor.pullbackAlong φb hφb (mapDomain r₁ D) := by
  simp only [defectHom, AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply]

theorem defectHom_single_one (v : Place L F₁) :
    defectHom φ hφ φb hφb r₁ r (single v 1) = defect φ hφ φb hφb r₁ r v := by
  rw [defectHom_apply, defect, Finsupp.mapDomain_single]

theorem defectHom_single_apply (v : Place L F₁) (n : ℤ) (Y : Place (ResidueField A) C₂) :
    defectHom φ hφ φb hφb r₁ r (single v n) Y = n * defect φ hφ φb hφb r₁ r v Y := by
  rw [map_single_eq_zsmul, defectHom_single_one, Finsupp.smul_apply, smul_eq_mul]

theorem defectHom_principal
    (R₁ : RegularProlongation A F₁ C₁)
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 → ∀ D : Divisor L F₁,
      (∀ P, D P = P.ord (f : F₁)) → ∀ Q, mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (R : RegularProlongation A F₂ C₂)
    (hr : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F₂,
      (∀ P, D P = P.ord (f : F₂)) → ∀ Q, mapDomain r D Q = Q.ord (R.residue f))
    (hRφ : ∀ f : R₁.integers, ∃ h : φ (f : F₁) ∈ R.integers,
      R.residue ⟨_, h⟩ = φb (R₁.residue f))
    {f : F₁} (hf : f ≠ 0) {Df : Divisor L F₁} (hDf : ∀ P, Df P = P.ord f) :
    defectHom φ hφ φb hφb r₁ r Df = 0 := by
  obtain ⟨c, hc, hres⟩ := R₁.exists_smul_mem f hf
  have hc0 : c ≠ 0 := R₁.smul_const_ne_zero hc hres
  set f₀ : R₁.integers := ⟨c • f, hc⟩ with hf₀def
  have hDf' : ∀ P, Df P = P.ord (f₀ : F₁) := fun P => by
    rw [hDf P]
    exact (ConstantReduction.ord_smul P hc0 f).symm
  have E1 := hr₁ f₀ hres Df hDf'
  obtain ⟨hmem, hcomp⟩ := hRφ f₀
  have hres' : R.residue ⟨φ (f₀ : F₁), hmem⟩ ≠ 0 := by
    rw [hcomp]
    exact (map_ne_zero φb).mpr hres
  have hD' : ∀ W, Divisor.pullbackAlong φ hφ Df W
      = W.ord ((⟨φ (f₀ : F₁), hmem⟩ : R.integers) : F₂) := fun W => by
    rw [Divisor.pullbackAlong_apply, hDf' (W.restrictAlong φ hφ), ← Place.ord_restrictAlong φ hφ W]
  have E2 := hr ⟨φ (f₀ : F₁), hmem⟩ hres' (Divisor.pullbackAlong φ hφ Df) hD'
  rw [defectHom_apply, sub_eq_zero]
  ext Y
  rw [E2 Y, hcomp, Place.ord_restrictAlong φb hφb, Divisor.pullbackAlong_apply, E1]

theorem abs_defectHom_apply_le
    (h1F₁ : ∀ v : Place L F₁, v.deg = 1) (h1F₂ : ∀ w : Place L F₂, w.deg = 1)
    (B : ℤ) (hB0 : 0 ≤ B)
    (hB : ∀ D : Divisor L F₁, (∀ P, 0 ≤ D P) →
      Divisor.degree (Divisor.pullbackAlong φ hφ D) ≤ B * Divisor.degree D)
    {D : Divisor L F₁} (hD : ∀ P, 0 ≤ D P) (Y : Place (ResidueField A) C₂) :
    |defectHom φ hφ φb hφb r₁ r D Y|
      ≤ (B + Place.ramificationIndexAlong φb Y) * Divisor.degree D := by
  rw [defectHom_apply, Finsupp.sub_apply]
  have hdegD : 0 ≤ Divisor.degree D := degree_nonneg h1F₁ hD

  have hX : ∀ W, 0 ≤ Divisor.pullbackAlong φ hφ D W := pullbackAlong_nonneg φ hφ hD
  have h1lo : 0 ≤ mapDomain r (Divisor.pullbackAlong φ hφ D) Y := mapDomain_nonneg r hX Y
  have h1hi : mapDomain r (Divisor.pullbackAlong φ hφ D) Y ≤ B * Divisor.degree D := by
    refine (mapDomain_apply_le_sum r hX Y).trans ?_
    rw [← degree_eq_sum h1F₂]
    exact hB D hD

  have hE : ∀ Q, 0 ≤ mapDomain r₁ D Q := mapDomain_nonneg r₁ hD
  have h2lo : 0 ≤ Divisor.pullbackAlong φb hφb (mapDomain r₁ D) Y :=
    pullbackAlong_nonneg φb hφb hE Y
  have h2hi : Divisor.pullbackAlong φb hφb (mapDomain r₁ D) Y
      ≤ Place.ramificationIndexAlong φb Y * Divisor.degree D := by
    rw [Divisor.pullbackAlong_apply]
    refine mul_le_mul_of_nonneg_left ?_ (Int.natCast_nonneg _)
    refine (mapDomain_apply_le_sum r₁ hD _).trans ?_
    rw [← degree_eq_sum h1F₁]
  rw [abs_le]
  constructor <;> nlinarith [h1lo, h1hi, h2lo, h2hi, hdegD, hB0,
    Int.natCast_nonneg (Place.ramificationIndexAlong φb Y)]

theorem exists_fn_zero_pole [HasPrincipalDivisors L F₁]
    (h1F₁ : ∀ v : Place L F₁, v.deg = 1) {g' : ℕ}
    (hRi : ∀ D : Divisor L F₁, (g' : ℤ) ≤ Divisor.degree D →
      ∃ f : F₁, f ≠ 0 ∧ ∀ v, 0 ≤ D v + v.ord f)
    {v P₁ : Place L F₁} (hne : v ≠ P₁) (m : ℕ) :
    ∃ f : F₁, f ≠ 0 ∧ ∃ Df : Divisor L F₁, (∀ P, Df P = P.ord f) ∧ Divisor.degree Df = 0 ∧
      (m : ℤ) ≤ Df v ∧ -((m : ℤ) + g' + 1) ≤ Df P₁ ∧ ∀ P, P ≠ v → P ≠ P₁ → 0 ≤ Df P := by
  classical
  set D : Divisor L F₁ := single P₁ ((m : ℤ) + g' + 1) - single v (m : ℤ) with hD
  have hdegD : Divisor.degree D = g' + 1 := by
    rw [hD, map_sub, Divisor.degree_single, Divisor.degree_single, h1F₁, h1F₁]
    push_cast
    ring
  obtain ⟨f, hf0, hf⟩ := hRi D (by rw [hdegD]; linarith)
  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0
  refine ⟨f, hf0, Df, hDf, hDf0, ?_, ?_, ?_⟩
  · have h := hf v
    have hDv : D v = -(m : ℤ) := by
      rw [hD, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply,
        if_neg (Ne.symm hne), if_pos rfl]
      ring
    rw [hDf v]
    linarith
  · have h := hf P₁
    have hDP : D P₁ = (m : ℤ) + g' + 1 := by
      rw [hD, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
        if_neg hne]
      ring
    rw [hDf P₁]
    linarith
  · intro P hPv hP1
    have h := hf P
    have hDP : D P = 0 := by
      rw [hD, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply,
        if_neg (Ne.symm hP1), if_neg (Ne.symm hPv)]
      ring
    rw [hDf P]
    linarith

theorem defect_eq [HasPrincipalDivisors L F₁]
    (R₁ : RegularProlongation A F₁ C₁)
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 → ∀ D : Divisor L F₁,
      (∀ P, D P = P.ord (f : F₁)) → ∀ Q, mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (R : RegularProlongation A F₂ C₂)
    (hr : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F₂,
      (∀ P, D P = P.ord (f : F₂)) → ∀ Q, mapDomain r D Q = Q.ord (R.residue f))
    (hRφ : ∀ f : R₁.integers, ∃ h : φ (f : F₁) ∈ R.integers,
      R.residue ⟨_, h⟩ = φb (R₁.residue f))
    (h1F₁ : ∀ v : Place L F₁, v.deg = 1) (h1F₂ : ∀ w : Place L F₂, w.deg = 1)
    (B : ℤ) (hB0 : 0 ≤ B)
    (hB : ∀ D : Divisor L F₁, (∀ P, 0 ≤ D P) →
      Divisor.degree (Divisor.pullbackAlong φ hφ D) ≤ B * Divisor.degree D)
    {g' : ℕ}
    (hRi : ∀ D : Divisor L F₁, (g' : ℤ) ≤ Divisor.degree D →
      ∃ f : F₁, f ≠ 0 ∧ ∀ v, 0 ≤ D v + v.ord f)
    (v P₁ : Place L F₁) :
    defect φ hφ φb hφb r₁ r v = defect φ hφ φb hφb r₁ r P₁ := by
  classical
  by_cases hne : v = P₁
  · rw [hne]
  ext Y
  by_contra hY

  set C : ℤ := B + Place.ramificationIndexAlong φb Y with hCdef
  have hC0 : 0 ≤ C := by
    have := Int.natCast_nonneg (Place.ramificationIndexAlong φb Y)
    rw [hCdef]; linarith
  have hCsingle : ∀ P, |defect φ hφ φb hφb r₁ r P Y| ≤ C := fun P => by
    have h := abs_defectHom_apply_le φ hφ φb hφb r₁ r h1F₁ h1F₂ B hB0 hB
      (single_one_nonneg P) Y
    rwa [defectHom_single_one, Divisor.degree_single, h1F₁, Nat.cast_one, mul_one, mul_one]
      at h

  set m : ℕ := (2 * C * (g' + 1)).toNat + 1 with hmdef
  have hm : 2 * C * ((g' : ℤ) + 1) < (m : ℤ) := by
    have := Int.self_le_toNat (2 * C * (g' + 1))
    rw [hmdef]; push_cast; linarith
  obtain ⟨f, hf0, Df, hDf, hDf0, hv, hP1, hpos⟩ :=
    exists_fn_zero_pole h1F₁ hRi hne m
  have hkill := defectHom_principal φ hφ φb hφb r₁ r R₁ hr₁ R hr hRφ hf0 hDf

  set Dp : Divisor L F₁ := Df - single v (Df v) - single P₁ (Df P₁) with hDpdef
  have hDp : ∀ P, 0 ≤ Dp P := by
    intro P
    rw [hDpdef, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
    by_cases hPv : v = P
    · subst hPv
      rw [if_pos rfl, if_neg (Ne.symm hne)]
      simp
    by_cases hP1 : P₁ = P
    · subst hP1
      rw [if_neg hPv, if_pos rfl]
      simp
    rw [if_neg hPv, if_neg hP1, sub_zero, sub_zero]
    exact hpos P (Ne.symm hPv) (Ne.symm hP1)
  have hdegDp : Divisor.degree Dp = -Df v - Df P₁ := by
    rw [hDpdef, map_sub, map_sub, Divisor.degree_single, Divisor.degree_single, h1F₁, h1F₁,
      hDf0]
    push_cast
    ring
  have hdegDp0 : 0 ≤ Divisor.degree Dp := degree_nonneg h1F₁ hDp
  have hdegDple : Divisor.degree Dp ≤ (g' : ℤ) + 1 := by rw [hdegDp]; linarith
  have hdecomp : Df = single v (Df v) + single P₁ (Df P₁) + Dp := by
    rw [hDpdef]; abel

  have h0 : Df v * defect φ hφ φb hφb r₁ r v Y + Df P₁ * defect φ hφ φb hφb r₁ r P₁ Y
      + defectHom φ hφ φb hφb r₁ r Dp Y = 0 := by
    have h := congrArg (fun E : Divisor (ResidueField A) C₂ => E Y) hkill
    rw [hdecomp, map_add, map_add, Finsupp.add_apply, Finsupp.add_apply,
      defectHom_single_apply, defectHom_single_apply] at h
    simpa using h
  have hbd : |defectHom φ hφ φb hφb r₁ r Dp Y| ≤ C * Divisor.degree Dp :=
    abs_defectHom_apply_le φ hφ φb hφb r₁ r h1F₁ h1F₂ B hB0 hB hDp Y

  have hbd' : |defectHom φ hφ φb hφb r₁ r Dp Y| ≤ C * ((g' : ℤ) + 1) :=
    hbd.trans (mul_le_mul_of_nonneg_left hdegDple hC0)
  have hP1bd := hCsingle P₁
  have hvbd := hCsingle v
  rw [abs_le] at hbd' hP1bd hvbd
  have hprod1 : Divisor.degree Dp * defect φ hφ φb hφb r₁ r P₁ Y ≤ ((g' : ℤ) + 1) * C := by
    calc Divisor.degree Dp * defect φ hφ φb hφb r₁ r P₁ Y
        ≤ Divisor.degree Dp * C := mul_le_mul_of_nonneg_left hP1bd.2 hdegDp0
      _ ≤ ((g' : ℤ) + 1) * C := mul_le_mul_of_nonneg_right hdegDple hC0
  have hprod2 : -(((g' : ℤ) + 1) * C) ≤ Divisor.degree Dp * defect φ hφ φb hφb r₁ r P₁ Y := by
    have h1 : Divisor.degree Dp * (-C) ≤ Divisor.degree Dp * defect φ hφ φb hφb r₁ r P₁ Y :=
      mul_le_mul_of_nonneg_left hP1bd.1 hdegDp0
    have h2 : Divisor.degree Dp * C ≤ ((g' : ℤ) + 1) * C :=
      mul_le_mul_of_nonneg_right hdegDple hC0
    nlinarith

  have hkey : Df v * (defect φ hφ φb hφb r₁ r v Y - defect φ hφ φb hφb r₁ r P₁ Y)
      = Divisor.degree Dp * defect φ hφ φb hφb r₁ r P₁ Y
          - defectHom φ hφ φb hφb r₁ r Dp Y := by
    rw [hdegDp]; linear_combination h0
  have hdiff : defect φ hφ φb hφb r₁ r v Y - defect φ hφ φb hφb r₁ r P₁ Y ≠ 0 :=
    sub_ne_zero.mpr hY
  have hmv : (m : ℤ) ≤ Df v := hv
  have hDfv0 : 0 ≤ Df v := le_trans (Int.natCast_nonneg m) hmv
  rcases lt_or_gt_of_ne hdiff with hlt | hgt
  ·
    have hle : defect φ hφ φb hφb r₁ r v Y - defect φ hφ φb hφb r₁ r P₁ Y ≤ -1 := by omega
    have : Df v * (defect φ hφ φb hφb r₁ r v Y - defect φ hφ φb hφb r₁ r P₁ Y)
        ≤ Df v * (-1) := mul_le_mul_of_nonneg_left hle hDfv0
    rw [hkey] at this
    nlinarith
  · have hge : 1 ≤ defect φ hφ φb hφb r₁ r v Y - defect φ hφ φb hφb r₁ r P₁ Y := by omega
    have : Df v * 1
        ≤ Df v * (defect φ hφ φb hφb r₁ r v Y - defect φ hφ φb hφb r₁ r P₁ Y) :=
      mul_le_mul_of_nonneg_left hge hDfv0
    rw [hkey] at this
    nlinarith

theorem exists_apply_ne [HasPrincipalDivisors L F₁]
    (R₁ : RegularProlongation A F₁ C₁)
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 → ∀ D : Divisor L F₁,
      (∀ P, D P = P.ord (f : F₁)) → ∀ Q, mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (h1F₁ : ∀ v : Place L F₁, v.deg = 1)
    (hWA : ∀ Q : Place (ResidueField A) C₁, ∃ g : C₁, g ≠ 0 ∧ Q.ord g ≠ 0)
    (v : Place L F₁) : ∃ v', r₁ v' ≠ r₁ v := by
  by_contra hall
  push Not at hall
  obtain ⟨g, hg0, hgord⟩ := hWA (r₁ v)
  obtain ⟨f₀, hf₀⟩ := R₁.residue_surjective g
  have hres : R₁.residue f₀ ≠ 0 := by rw [hf₀]; exact hg0
  have hf0 : (f₀ : F₁) ≠ 0 := by
    intro h
    apply hres
    have : f₀ = 0 := Subtype.ext h
    rw [this, map_zero]
  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := L) (f₀ : F₁) hf0
  have E1 := hr₁ f₀ hres Df hDf (r₁ v)
  rw [hf₀] at E1
  apply hgord
  rw [← E1, mapDomain_apply_of_forall_eq r₁ Df hall, ← degree_eq_sum h1F₁, hDf0]

theorem defect_eq_zero [HasPrincipalDivisors L F₁]
    (R₁ : RegularProlongation A F₁ C₁)
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 → ∀ D : Divisor L F₁,
      (∀ P, D P = P.ord (f : F₁)) → ∀ Q, mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (R : RegularProlongation A F₂ C₂)
    (hr : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F₂,
      (∀ P, D P = P.ord (f : F₂)) → ∀ Q, mapDomain r D Q = Q.ord (R.residue f))
    (hRφ : ∀ f : R₁.integers, ∃ h : φ (f : F₁) ∈ R.integers,
      R.residue ⟨_, h⟩ = φb (R₁.residue f))
    (h1F₁ : ∀ v : Place L F₁, v.deg = 1) (h1F₂ : ∀ w : Place L F₂, w.deg = 1)
    (h1C₂ : ∀ Y : Place (ResidueField A) C₂, Y.deg = 1)
    (B : ℤ) (hB0 : 0 ≤ B)
    (hB : ∀ D : Divisor L F₁, (∀ P, 0 ≤ D P) →
      Divisor.degree (Divisor.pullbackAlong φ hφ D) ≤ B * Divisor.degree D)
    {g' : ℕ}
    (hRi : ∀ D : Divisor L F₁, (g' : ℤ) ≤ Divisor.degree D →
      ∃ f : F₁, f ≠ 0 ∧ ∀ v, 0 ≤ D v + v.ord f)
    (hWA : ∀ Q : Place (ResidueField A) C₁, ∃ g : C₁, g ≠ 0 ∧ Q.ord g ≠ 0)
    (hdeg : ∀ v, Divisor.degree (Divisor.pullbackAlong φ hφ (single v 1))
      = Divisor.degree (Divisor.pullbackAlong φb hφb (single (r₁ v) 1)))
    (v : Place L F₁) :
    defect φ hφ φb hφb r₁ r v = 0 := by
  obtain ⟨v', hv'⟩ := exists_apply_ne r₁ R₁ hr₁ h1F₁ hWA v
  have hconst := defect_eq φ hφ φb hφb r₁ r R₁ hr₁ R hr hRφ h1F₁ h1F₂ B hB0 hB hRi v v'
  have hnonneg : ∀ Y, 0 ≤ defect φ hφ φb hφb r₁ r v Y := by
    intro Y
    by_cases hY : Y.restrictAlong φb hφb = r₁ v
    · have hY' : Y.restrictAlong φb hφb ≠ r₁ v' := by rw [hY]; exact Ne.symm hv'
      rw [hconst, defect, Finsupp.sub_apply, pullbackAlong_single_apply_of_ne φb hφb hY',
        sub_zero]
      exact mapDomain_nonneg r (pullbackAlong_single_nonneg φ hφ v') Y
    · rw [defect, Finsupp.sub_apply, pullbackAlong_single_apply_of_ne φb hφb hY, sub_zero]
      exact mapDomain_nonneg r (pullbackAlong_single_nonneg φ hφ v) Y
  have hdeg0 : Divisor.degree (defect φ hφ φb hφb r₁ r v) = 0 := by
    rw [defect, map_sub, degree_mapDomain_eq h1F₂ h1C₂, hdeg v, sub_self]
  exact eq_zero_of_nonneg_of_degree_eq_zero h1C₂ hnonneg hdeg0

theorem engine [HasPrincipalDivisors L F₁]
    (R₁ : RegularProlongation A F₁ C₁)
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 → ∀ D : Divisor L F₁,
      (∀ P, D P = P.ord (f : F₁)) → ∀ Q, mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (R : RegularProlongation A F₂ C₂)
    (hr : ∀ f : R.integers, R.residue f ≠ 0 → ∀ D : Divisor L F₂,
      (∀ P, D P = P.ord (f : F₂)) → ∀ Q, mapDomain r D Q = Q.ord (R.residue f))
    (hRφ : ∀ f : R₁.integers, ∃ h : φ (f : F₁) ∈ R.integers,
      R.residue ⟨_, h⟩ = φb (R₁.residue f))
    (h1F₁ : ∀ v : Place L F₁, v.deg = 1) (h1F₂ : ∀ w : Place L F₂, w.deg = 1)
    (h1C₂ : ∀ Y : Place (ResidueField A) C₂, Y.deg = 1)
    (B : ℤ) (hB0 : 0 ≤ B)
    (hB : ∀ D : Divisor L F₁, (∀ P, 0 ≤ D P) →
      Divisor.degree (Divisor.pullbackAlong φ hφ D) ≤ B * Divisor.degree D)
    {g' : ℕ}
    (hRi : ∀ D : Divisor L F₁, (g' : ℤ) ≤ Divisor.degree D →
      ∃ f : F₁, f ≠ 0 ∧ ∀ v, 0 ≤ D v + v.ord f)
    (hWA : ∀ Q : Place (ResidueField A) C₁, ∃ g : C₁, g ≠ 0 ∧ Q.ord g ≠ 0)
    (hdeg : ∀ v, Divisor.degree (Divisor.pullbackAlong φ hφ (single v 1))
      = Divisor.degree (Divisor.pullbackAlong φb hφb (single (r₁ v) 1))) :
    (∀ v, mapDomain r (Divisor.pullbackAlong φ hφ (single v 1))
        = Divisor.pullbackAlong φb hφb (single (r₁ v) 1))
    ∧ ∀ W, (r W).restrictAlong φb hφb = r₁ (W.restrictAlong φ hφ) := by
  have hzero : ∀ v, mapDomain r (Divisor.pullbackAlong φ hφ (single v 1))
      = Divisor.pullbackAlong φb hφb (single (r₁ v) 1) := fun v =>
    sub_eq_zero.mp (defect_eq_zero φ hφ φb hφb r₁ r R₁ hr₁ R hr hRφ h1F₁ h1F₂ h1C₂ B hB0 hB
      hRi hWA hdeg v)
  refine ⟨hzero, fun W => ?_⟩
  by_contra hne
  have heq := congrArg (fun E : Divisor (ResidueField A) C₂ => E (r W))
    (hzero (W.restrictAlong φ hφ))
  rw [pullbackAlong_single_apply_of_ne φb hφb hne] at heq
  have hle := le_mapDomain_apply_self r (pullbackAlong_single_nonneg φ hφ (W.restrictAlong φ hφ)) W
  rw [heq, pullbackAlong_single_apply_self] at hle
  have hpos := ramificationIndexAlong_pos φ hφ W
  omega

end Engine

section Modular

theorem deg_eq_one_bar (N : ℕ) [NeZero N]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.deg = 1 := by
  haveI := isCurveOver_modularFunctionFieldBar N
  exact IsCurveOver.deg_eq_one_of_isAlgClosed (K := AlgebraicClosure ℚ) v

theorem degree_pullbackAlong_le_of_FI {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ) (D : Divisor K F)
    (hD : ∀ P, 0 ≤ D P) :
    Divisor.degree (Divisor.pullbackAlong φ hφ D) ≤ (finrankAlong K φ : ℤ) * Divisor.degree D :=
  le_of_eq (Divisor.degree_pullbackAlong φ hφ hFI D)

theorem weakApprox {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F) :
    ∃ g : F, g ≠ 0 ∧ Q.ord g ≠ 0 := by
  obtain ⟨g, hg0, hg⟩ := Place.exists_forall_ord_eq ({Q} : Finset (Place K F)) (fun _ => 1)
  exact ⟨g, hg0, by rw [hg Q (Finset.mem_singleton_self Q)]; exact one_ne_zero⟩

end Modular

end P2mSolSpRoofV2

end

open P2mSolSpRoofV2 in
theorem solution
    (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (q : ℕ) [hq' : Fact q.Prime] [NeZero (N * q)]
    (hαq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβq : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hαc : HeckeAlphaCIntegral (ResidueField ↥A) N q)
    (hβc : HeckeBetaCIntegral (ResidueField ↥A) N q)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    [HasPrincipalDivisors (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q)]
    (hdeg1 : ∀ Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q),
      Y.deg = 1)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    (r₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      → Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ P, D P = P.ord (f : modularFunctionFieldBar N)) →
      ∀ Q, Finsupp.mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (R : RegularProlongation A (modularFunctionFieldBar (N * q))
      (charLDegeneracyRoof (ResidueField ↥A) N q))
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      → Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q))
    (hr : ∀ f : R.integers, R.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ P, D P = P.ord (f : modularFunctionFieldBar (N * q))) →
      ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f))
    (hRα : ∀ f : R₁.integers,
      ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.integers,
        R.residue ⟨_, h⟩ = heckeAlphaC (ResidueField ↥A) N q (R₁.residue f))
    (hRβ : ∀ f : R₁.integers,
      ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.integers,
        R.residue ⟨_, h⟩ = heckeBetaC (ResidueField ↥A) N q (R₁.residue f))
    (hdegα : ∀ v, Divisor.degree
        (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq (Finsupp.single v 1))
      = Divisor.degree
        (Divisor.pullbackAlong (heckeAlphaC (ResidueField ↥A) N q) hαc (Finsupp.single (r₁ v) 1)))
    (hdegβ : ∀ v, Divisor.degree
        (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))
      = Divisor.degree
        (Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N q) hβc (Finsupp.single (r₁ v) 1))) :
    (∀ v, Finsupp.mapDomain r
          (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq (Finsupp.single v 1))
        = Divisor.pullbackAlong (heckeAlphaC (ResidueField ↥A) N q) hαc
            (Finsupp.single (r₁ v) 1))
    ∧ (∀ v, Finsupp.mapDomain r
          (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))
        = Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N q) hβc
            (Finsupp.single (r₁ v) 1))
    ∧ (∀ W, (r W).restrictAlong (heckeAlphaC (ResidueField ↥A) N q) hαc
        = r₁ (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq))
    ∧ ∀ W, (r W).restrictAlong (heckeBetaC (ResidueField ↥A) N q) hβc
        = r₁ (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq) := by

  have h1F₁ : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.deg = 1 :=
    deg_eq_one_bar N
  have h1F₂ : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), w.deg = 1 :=
    deg_eq_one_bar (N * q)

  obtain ⟨g', hRi⟩ := exists_riemannConstant_modularFunctionFieldBar N

  have hWA : ∀ Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N),
      ∃ g : modularFunctionFieldC (ResidueField ↥A) N, g ≠ 0 ∧ Q.ord g ≠ 0 := fun Q =>
    weakApprox Q

  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective
  have hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq :=
    fundamentalIdentityAlong _ hαq (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q)
      (separableAlong_of_charZero _ hαq)
  have hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq :=
    fundamentalIdentityAlong _ hβq (finiteAlong_heckeBetaBar_of_prime (AlgebraicClosure ℚ) N q)
      (separableAlong_of_charZero _ hβq)

  obtain ⟨hα1, hα2⟩ := engine (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq
    (heckeAlphaC (ResidueField ↥A) N q) hαc r₁ r R₁ hr₁ R hr hRα h1F₁ h1F₂ hdeg1
    (finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)
    (Int.natCast_nonneg _) (degree_pullbackAlong_le_of_FI _ hαq hFIα) hRi hWA hdegα

  obtain ⟨hβ1, hβ2⟩ := engine (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq
    (heckeBetaC (ResidueField ↥A) N q) hβc r₁ r R₁ hr₁ R hr hRβ h1F₁ h1F₂ hdeg1
    (finrankAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ)
    (Int.natCast_nonneg _) (degree_pullbackAlong_le_of_FI _ hβq hFIβ) hRi hWA hdegβ
  exact ⟨hα1, hβ1, hα2, hβ2⟩

end S_ModularCurve_PlaceSpecialization_exists_spRoof_pullbackAlong_restrictAlong_compat_of_exists_placeMap_fullC_v2
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_spRoof_pullbackAlong_restrictAlong_compat_of_exists_placeMap_fullC_v2 (solution)
