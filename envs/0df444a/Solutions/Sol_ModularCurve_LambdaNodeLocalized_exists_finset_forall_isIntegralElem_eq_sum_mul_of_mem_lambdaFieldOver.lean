-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/37d6e34b-10b2-58c7-8a7f-18dc92da45f5

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Theorems.Thm_Subfield_exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finset_forall_mem_jIntegralClosure_eq_sum_mul
import Theorems.Thm_ModularCurve_jIntegralClosure_isNoetherian_and_isLocalization
import Theorems.Thm_ModularCurve_exists_phiIrreducible
import Theorems.Thm_ModularCurve_minpoly_jqNModC_eq
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

namespace L2Fin

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

section Inst

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem isIntegral_map_iff (R₀ : Subring LQ) (x : LQ) :
    IsIntegral ↥(R₀.map (qExpand Qb 2)) x ↔ ((qExpand Qb 2).comp R₀.subtype).IsIntegralElem x := by
  set e : ↥R₀ ≃+* ↥(R₀.map (qExpand Qb 2)) := R₀.equivMapOfInjective (qExpand Qb 2) (qExpand Qb 2).injective with he
  have hcomp : (R₀.map (qExpand Qb 2)).subtype.comp e.toRingHom = (qExpand Qb 2).comp R₀.subtype := by
    ext x; rfl
  constructor
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p.map e.symm.toRingHom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hcomp]
    have : (((R₀.map (qExpand Qb 2)).subtype.comp e.toRingHom).comp e.symm.toRingHom) = (R₀.map (qExpand Qb 2)).subtype := by
      ext y; simp
    rw [this]
    exact hpx
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p.map e.toRingHom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((R₀.map (qExpand Qb 2)).subtype.comp e.toRingHom) x p = 0
    rw [hcomp]
    exact hpx

end Inst
end L2Fin

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq ModularPolynomialData lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap NodeLocalized.exists_finset_forall_mem_jIntegralClosure_eq_sum_mul jIntegralClosure_isNoetherian_and_isLocalization exists_phiIrreducible minpoly_jqNModC_eq qExpand_two_jq_mul_lambdaModC_sq"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval modularLocalizedAtPoint mem_modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver jRing pointEval_eq_zero_of_modularEval_eq_zero exists_finset_forall_mem_jIntegralClosure_eq_sum_mul"
p2m_open "ModularCurve.NodeLocalized"

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem mem_coeffSubring_iff_l2f {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := by
  simp only [coeffSubring, Subring.mem_inf]
  exact Iff.rfl

theorem exists_div_eq_of_mem_l2f (x : AlgebraicClosure ℚ) (hx : x ∈ K) :
    ∃ a b : ↥(coeffSubring A K), (b : AlgebraicClosure ℚ) ≠ 0 ∧ x = a / b := by
  rcases A.mem_or_inv_mem x with h | h
  · refine ⟨⟨x, (mem_coeffSubring_iff_l2f A K).mpr ⟨h, hx⟩⟩, ⟨1, one_mem _⟩, ?_, ?_⟩
    · simp
    · simp
  · by_cases hx0 : x = 0
    · refine ⟨⟨0, zero_mem _⟩, ⟨1, one_mem _⟩, by simp, by simp [hx0]⟩
    refine ⟨⟨1, one_mem _⟩, ⟨x⁻¹, (mem_coeffSubring_iff_l2f A K).mpr ⟨h, IntermediateField.inv_mem K hx⟩⟩, ?_, ?_⟩
    · simpa using hx0
    · simp

theorem constSeries_coeffSubring_apply_l2f (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) := rfl

theorem algebraMap_mem_fieldOver_l2f (N : ℕ) [NeZero N] {x : AlgebraicClosure ℚ} (hx : x ∈ K) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) x ∈ fieldOver N K := by
  refine Subfield.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem jqModC_mem_fieldOver_l2f (N : ℕ) [NeZero N] : jqModC (AlgebraicClosure ℚ) ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem jqNModC_mem_fieldOver_l2f (N : ℕ) [NeZero N] : jqNModC (AlgebraicClosure ℚ) N ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

theorem jqModC_mem_jRing_l2f : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
  Subring.subset_closure (Or.inr rfl)

theorem constSeries_mem_jRing_l2f (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem jRing_le_fieldOver_l2f (N : ℕ) [NeZero N] : jRing A K ≤ (fieldOver N K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact algebraMap_mem_fieldOver_l2f K N ((mem_coeffSubring_iff_l2f A K).mp a.2).2
  · exact jqModC_mem_fieldOver_l2f K N

theorem fieldOver_eq_closure_l2f (N : ℕ) [NeZero N] :
    fieldOver N K = Subfield.closure ((jRing A K : Set (LaurentSeries (AlgebraicClosure ℚ)))
      ∪ {jqNModC (AlgebraicClosure ℚ) N}) := by
  apply le_antisymm
  · rw [fieldOver, Subfield.closure_le]
    rintro x (⟨a, rfl⟩ | rfl | rfl)
    ·
      obtain ⟨b, c, hc, hbc⟩ := exists_div_eq_of_mem_l2f A K (a : AlgebraicClosure ℚ) a.2
      have : CharPReduction.constSeries K.toSubalgebra.toSubring a
          = CharPReduction.constSeries (coeffSubring A K) b / CharPReduction.constSeries (coeffSubring A K) c := by
        show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) = _
        rw [hbc, map_div₀]; rfl
      rw [this]
      exact div_mem (Subfield.subset_closure (Or.inl (constSeries_mem_jRing_l2f A K b)))
        (Subfield.subset_closure (Or.inl (constSeries_mem_jRing_l2f A K c)))
    · exact Subfield.subset_closure (Or.inl (jqModC_mem_jRing_l2f A K))
    · exact Subfield.subset_closure (Or.inr rfl)
  · rw [Subfield.closure_le]
    rintro x (hx | rfl)
    · exact jRing_le_fieldOver_l2f A K N hx
    · exact jqNModC_mem_fieldOver_l2f K N

theorem modularEval_mem_fieldOver_l2f (N : ℕ) [NeZero N] (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    modularEval N (coeffSubring A K) p ∈ fieldOver N K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_C]
      exact algebraMap_mem_fieldOver_l2f K N ((mem_coeffSubring_iff_l2f A K).mp c.2).2
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact jqModC_mem_fieldOver_l2f K N
      · exact jqNModC_mem_fieldOver_l2f K N

end NodeLocalized
end ModularCurve

namespace L2Fin
section Inst2

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem modularLocalizedAtPoint_le_fieldOver :
    modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ≤ (fieldOver (1 * q) K).toSubring := by
  intro f hf
  obtain ⟨r, s, hs, hfs⟩ := (mem_modularLocalizedAtPoint _ _ _ _ _).mp hf
  have hs0 : modularEval (1 * q) (coeffSubring A K) s ≠ 0 := fun h0 =>
    hs (pointEval_eq_zero_of_modularEval_eq_zero red a K s h0)
  have : f = modularEval (1 * q) (coeffSubring A K) r / modularEval (1 * q) (coeffSubring A K) s := by
    rw [eq_div_iff hs0, hfs]
  rw [this]
  show _ ∈ fieldOver (1 * q) K
  exact div_mem (modularEval_mem_fieldOver_l2f A K (1 * q) r) (modularEval_mem_fieldOver_l2f A K (1 * q) s)

theorem closure_le_modularLocalizedAtPoint :
    Subring.closure ((jRing A K : Set LQ) ∪ {jqNModC Qb (1 * q)})
      ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  rw [Subring.closure_le]
  rintro x (hx | rfl)
  · revert hx x
    show jRing A K ≤ _
    rw [jRing, Subring.closure_le]
    rintro x (⟨c, rfl⟩ | rfl)
    · have : CharPReduction.constSeries (coeffSubring A K) c = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) := by
        unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
      rw [this]; exact modularEval_mem_modularLocalizedAtPoint (1 * q) _ _ a (a ^ q) _
    · have : jqModC Qb = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) := by
        unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl
      rw [this]; exact modularEval_mem_modularLocalizedAtPoint (1 * q) _ _ a (a ^ q) _
  · have : jqNModC Qb (1 * q) = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1) := by
      unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl
    rw [this]; exact modularEval_mem_modularLocalizedAtPoint (1 * q) _ _ a (a ^ q) _

theorem exists_div_of_mem_fieldOver {x : LQ} (hx : x ∈ fieldOver (1 * q) K) :
    ∃ y ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q),
      ∃ z ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q), z ≠ 0 ∧ x = y / z := by
  rw [fieldOver_eq_closure_l2f A K (1 * q), Subfield.mem_closure_iff] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  by_cases hz0 : z = 0
  · refine ⟨0, zero_mem _, 1, one_mem _, one_ne_zero, ?_⟩
    rw [hz0, div_zero, zero_div]
  exact ⟨y, closure_le_modularLocalizedAtPoint red a K hy, z, closure_le_modularLocalizedAtPoint red a K hz, hz0, rfl⟩

end Inst2
end L2Fin

namespace FltWs21
namespace HN

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

theorem isIntegral_of_isIntegralElem_qExpand (R₀ : Subring LQ) {y : LQ}
    (h : ((qExpand Qb 2).comp R₀.subtype).IsIntegralElem (qExpand Qb 2 y)) :
    IsIntegral ↥R₀ y := by
  obtain ⟨p, hp, hpy⟩ := h
  refine ⟨p, hp, ?_⟩
  have hφ : Function.Injective (qExpand Qb 2) := (qExpand Qb 2).injective
  apply hφ
  rw [map_zero]
  have := Polynomial.hom_eval₂ p R₀.subtype (qExpand Qb 2) y
  rw [show (algebraMap (↥R₀) LQ) = R₀.subtype from rfl]
  rw [this]
  exact hpy

theorem isIntegralElem_qExpand_of_isIntegral (R₀ : Subring LQ) {y : LQ} (h : IsIntegral ↥R₀ y) :
    ((qExpand Qb 2).comp R₀.subtype).IsIntegralElem (qExpand Qb 2 y) := by
  obtain ⟨p, hp, hpy⟩ := h
  refine ⟨p, hp, ?_⟩
  rw [← Polynomial.hom_eval₂ p R₀.subtype (qExpand Qb 2) y]
  rw [show R₀.subtype = algebraMap (↥R₀) LQ from rfl, hpy, map_zero]

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k]

theorem core (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    ∃ s : Finset (LaurentSeries (AlgebraicClosure ℚ)),
      (∀ c ∈ s, c ∈ (fieldOver (1 * q) K).map (qExpand (AlgebraicClosure ℚ) 2) ∧
        ((qExpand (AlgebraicClosure ℚ) 2).comp
          (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem c) ∧
      ∀ y : LaurentSeries (AlgebraicClosure ℚ),
        y ∈ (fieldOver (1 * q) K).map (qExpand (AlgebraicClosure ℚ) 2) →
        ((qExpand (AlgebraicClosure ℚ) 2).comp
          (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem y →
        ∃ g : LaurentSeries (AlgebraicClosure ℚ) → LaurentSeries (AlgebraicClosure ℚ),
          (∀ c ∈ s, g c ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ∧
          y = ∑ c ∈ s, qExpand (AlgebraicClosure ℚ) 2 (g c) * c := by
  classical
  set R₀ := modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) with hR₀
  set φ := qExpand (AlgebraicClosure ℚ) 2 with hφdef
  have hφ : Function.Injective φ := φ.injective
  obtain ⟨data, -⟩ := ModularCurve.exists_phiIrreducible q
  obtain ⟨s₁, hs₁C, hs₁⟩ := ModularCurve.NodeLocalized.exists_finset_forall_mem_jIntegralClosure_eq_sum_mul (q := q) A K
  obtain ⟨-, -, -, hint⟩ := ModularCurve.jIntegralClosure_isNoetherian_and_isLocalization red a data K

  have hjR : jRing A K ≤ R₀ := by
    rw [jRing, Subring.closure_le]
    rintro x (⟨c, rfl⟩ | rfl)
    · have : CharPReduction.constSeries (coeffSubring A K) c = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) := by
        unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
      rw [this]; exact modularEval_mem_modularLocalizedAtPoint (1 * q) _ _ a (a ^ q) _
    · have : jqModC (AlgebraicClosure ℚ) = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) := by
        unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl
      rw [this]; exact modularEval_mem_modularLocalizedAtPoint (1 * q) _ _ a (a ^ q) _
  refine ⟨s₁.image φ, ?_, ?_⟩
  ·
    intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    have hdC := hs₁C hd
    refine ⟨Subfield.mem_map.mpr ⟨d, hdC.1, rfl⟩, ?_⟩
    refine isIntegralElem_qExpand_of_isIntegral R₀ ?_
    obtain ⟨p, hp, hpd⟩ := hdC.2
    refine ⟨p.map (Subring.inclusion hjR), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpd
  · intro y hy hyint
    obtain ⟨y₀, hy₀F, hy₀⟩ := Subfield.mem_map.mp hy
    have hy₀int : IsIntegral ↥R₀ y₀ :=
      isIntegral_of_isIntegralElem_qExpand R₀ (by rw [hy₀]; exact hyint)
    obtain ⟨c', s, hc'C, hs, hys⟩ := (hint y₀).mp ⟨hy₀F, hy₀int⟩
    obtain ⟨g, hg, hc'⟩ := hs₁ c' hc'C
    have hs0 : modularEval (1 * q) (coeffSubring A K) s ≠ 0 := fun h0 =>
      hs (pointEval_eq_zero_of_modularEval_eq_zero red a K s h0)
    have hsinv : (modularEval (1 * q) (coeffSubring A K) s)⁻¹ ∈ R₀ := by
      rw [hR₀, mem_modularLocalizedAtPoint]
      exact ⟨1, s, hs, by rw [map_one, inv_mul_cancel₀ hs0]⟩

    refine ⟨fun c => g (Function.invFun φ c) * (modularEval (1 * q) (coeffSubring A K) s)⁻¹, ?_, ?_⟩
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      show g (Function.invFun φ (φ d)) * _ ∈ R₀
      rw [Function.leftInverse_invFun hφ d]
      exact R₀.mul_mem (hjR (hg d hd)) hsinv
    · have hy₀eq : y₀ = ∑ d ∈ s₁, (g d * (modularEval (1 * q) (coeffSubring A K) s)⁻¹) * d := by
        have : y₀ = c' * (modularEval (1 * q) (coeffSubring A K) s)⁻¹ := by
          rw [← hys, mul_inv_cancel_right₀ hs0]
        rw [this, hc', Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ => by ring
      rw [Finset.sum_image (fun d _ d' _ h => hφ h), ← hy₀, hy₀eq, map_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      show _ = φ (g (Function.invFun φ (φ d)) * _) * φ d
      rw [Function.leftInverse_invFun hφ d, ← map_mul]

end FltWs21.HN

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

noncomputable section

namespace L2FinPlumbing

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

theorem qExpand_algebraMap (N : ℕ) [NeZero N] (c : Qb) :
    qExpand Qb N (algebraMap Qb LQ c) = algebraMap Qb LQ c := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

theorem jLambda_Qb :
    qExpand Qb 2 (jqModC Qb) * lambdaModC Qb ^ 2 * (16 * lambdaModC Qb - 1) ^ 2
      = (256 * lambdaModC Qb ^ 2 - 16 * lambdaModC Qb + 1) ^ 3 := by
  have h := congrArg (laurentMap (algebraMap ℚ Qb)) ModularCurve.qExpand_two_jq_mul_lambdaModC_sq
  have hj : laurentMap (algebraMap ℚ Qb) jq = jqModC Qb := by
    rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ Qb)
  have hμ : laurentMap (algebraMap ℚ Qb) (lambdaModC ℚ) = lambdaModC Qb := by
    rw [lambdaModC, lambdaModC, laurentMap_laurentMap]
    exact congrArg (fun g => laurentMap g lambdaInt) (RingHom.ext_int _ _)
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, laurentMap_qExpand, hj, hμ, map_ofNat] using h

theorem jLambda_Qb_q (q : ℕ) [NeZero q] :
    qExpand Qb 2 (jqNModC Qb (1 * q)) * lambdaNModC Qb q ^ 2 * (16 * lambdaNModC Qb q - 1) ^ 2
      = (256 * lambdaNModC Qb q ^ 2 - 16 * lambdaNModC Qb q + 1) ^ 3 := by
  have h := congrArg (qExpand Qb q) jLambda_Qb
  have hj : qExpand Qb q (qExpand Qb 2 (jqModC Qb)) = qExpand Qb 2 (jqNModC Qb (1 * q)) := by
    rw [jqNModC, qExpand_qExpand, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hj, lambdaNModC] using h

scoped instance charZero_LQ : CharZero LQ := charZero_of_injective_algebraMap (R := Qb) (algebraMap Qb LQ).injective

variable (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ Qb)

def K₁ : Subfield LQ := (fieldOver (1 * q) K).map (qExpand Qb 2)

scoped instance charZero_K₁ : CharZero ↥(K₁ q K) := RingHom.charZero (K₁ q K).subtype

theorem mem_K₁_iff {x : LQ} : x ∈ K₁ q K ↔ ∃ y ∈ fieldOver (1 * q) K, qExpand Qb 2 y = x := Subfield.mem_map

theorem K₁_le : K₁ q K ≤ lambdaFieldOver q K := by
  rintro x ⟨y, hy, rfl⟩
  exact qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver q K hy

theorem qExpand_jqModC_mem_K₁ : qExpand Qb 2 (jqModC Qb) ∈ K₁ q K :=
  ⟨_, Subfield.subset_closure (Or.inr (Set.mem_insert _ _)), rfl⟩

theorem qExpand_jqNModC_mem_K₁ : qExpand Qb 2 (jqNModC Qb (1 * q)) ∈ K₁ q K :=
  ⟨_, Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _))), rfl⟩

theorem constSeries_mem_K₁ (c : ↥K.toSubalgebra.toSubring) : CharPReduction.constSeries _ c ∈ K₁ q K := by
  refine ⟨CharPReduction.constSeries _ c, Subfield.subset_closure (Or.inl ⟨c, rfl⟩), ?_⟩
  rw [CharPReduction.constSeries, RingHom.comp_apply, qExpand_algebraMap]

section General

variable (F : Subfield LQ)

scoped instance charZero_subfield : CharZero ↥F := RingHom.charZero F.subtype

def jLambdaPoly {R : Type*} [CommRing R] (J : R) : Polynomial R :=
  (Polynomial.C 256 * Polynomial.X ^ 2 - Polynomial.C 16 * Polynomial.X + 1) ^ 3
    - Polynomial.C J * Polynomial.X ^ 2 * (Polynomial.C 16 * Polynomial.X - 1) ^ 2

theorem jLambdaPoly_ne_zero {R : Type*} [CommRing R] [Nontrivial R] (J : R) : jLambdaPoly J ≠ 0 := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  simp [jLambdaPoly] at h0

theorem aeval_jLambdaPoly {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (J : R) (m : S) :
    Polynomial.aeval m (jLambdaPoly J)
      = (256 * m ^ 2 - 16 * m + 1) ^ 3 - algebraMap R S J * m ^ 2 * (16 * m - 1) ^ 2 := by
  simp [jLambdaPoly, map_ofNat]

theorem isAlgebraic_lambdaModC_of_mem (hJ : qExpand Qb 2 (jqModC Qb) ∈ F) : IsAlgebraic (↥F) (lambdaModC Qb) := by
  refine ⟨jLambdaPoly ⟨_, hJ⟩, jLambdaPoly_ne_zero _, ?_⟩
  rw [aeval_jLambdaPoly, sub_eq_zero]
  exact jLambda_Qb.symm

theorem isAlgebraic_lambdaNModC_of_mem (hJq : qExpand Qb 2 (jqNModC Qb (1 * q)) ∈ F) :
    IsAlgebraic (↥F) (lambdaNModC Qb q) := by
  refine ⟨jLambdaPoly ⟨_, hJq⟩, jLambdaPoly_ne_zero _, ?_⟩
  rw [aeval_jLambdaPoly, sub_eq_zero]
  exact (jLambda_Qb_q q).symm

theorem isIntegral_lambdaModC_of_mem (hJ : qExpand Qb 2 (jqModC Qb) ∈ F) : IsIntegral (↥F) (lambdaModC Qb) :=
  (isAlgebraic_lambdaModC_of_mem F hJ).isIntegral

theorem isIntegral_lambdaNModC_of_mem (hJq : qExpand Qb 2 (jqNModC Qb (1 * q)) ∈ F) :
    IsIntegral (↥F) (lambdaNModC Qb q) :=
  (isAlgebraic_lambdaNModC_of_mem q F hJq).isIntegral

def LOver (hFL : F ≤ lambdaFieldOver q K) : IntermediateField (↥F) LQ :=
  (lambdaFieldOver q K).toIntermediateField fun x => hFL x.2

theorem mem_LOver_iff (hFL : F ≤ lambdaFieldOver q K) {x : LQ} : x ∈ LOver q K F hFL ↔ x ∈ lambdaFieldOver q K := Iff.rfl

theorem LOver_eq_adjoin (hFL : F ≤ lambdaFieldOver q K)
    (hconst : ∀ c : ↥K.toSubalgebra.toSubring, CharPReduction.constSeries _ c ∈ F) :
    LOver q K F hFL = IntermediateField.adjoin (↥F) {lambdaModC Qb, lambdaNModC Qb q} := by
  apply le_antisymm
  · intro x hx
    have : lambdaFieldOver q K ≤ (IntermediateField.adjoin (↥F) {lambdaModC Qb, lambdaNModC Qb q}).toSubfield := by
      unfold lambdaFieldOver
      rw [Subfield.closure_le]
      rintro z (⟨c, rfl⟩ | rfl | rfl)
      · exact (IntermediateField.adjoin (↥F) _).algebraMap_mem ⟨_, hconst c⟩
      · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
      · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    exact this hx
  · rw [IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact lambdaModC_mem_lambdaFieldOver q K
    · exact lambdaNModC_mem_lambdaFieldOver q K

theorem finiteDimensional_LOver (hFL : F ≤ lambdaFieldOver q K)
    (hconst : ∀ c : ↥K.toSubalgebra.toSubring, CharPReduction.constSeries _ c ∈ F)
    (hJ : qExpand Qb 2 (jqModC Qb) ∈ F) (hJq : qExpand Qb 2 (jqNModC Qb (1 * q)) ∈ F) :
    FiniteDimensional (↥F) (↥(LOver q K F hFL)) := by
  rw [LOver_eq_adjoin q K F hFL hconst]
  exact IntermediateField.finiteDimensional_adjoin fun x hx => by
    rcases hx with rfl | rfl
    · exact isIntegral_lambdaModC_of_mem F hJ
    · exact isIntegral_lambdaNModC_of_mem q F hJq

theorem finiteDimensional_lambdaFieldOver_of_le (hFL : F ≤ lambdaFieldOver q K)
    (hconst : ∀ c : ↥K.toSubalgebra.toSubring, CharPReduction.constSeries _ c ∈ F)
    (hJ : qExpand Qb 2 (jqModC Qb) ∈ F) (hJq : qExpand Qb 2 (jqNModC Qb (1 * q)) ∈ F) :
    letI := (Subfield.inclusion hFL).toAlgebra
    FiniteDimensional (↥F) (↥(lambdaFieldOver q K)) := by
  letI := (Subfield.inclusion hFL).toAlgebra
  haveI := finiteDimensional_LOver q K F hFL hconst hJ hJq
  let e : (↥(LOver q K F hFL)) ≃ₗ[↥F] (↥(lambdaFieldOver q K)) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact LinearEquiv.finiteDimensional e

end General

def L' : IntermediateField (↥(K₁ q K)) LQ := LOver q K (K₁ q K) (K₁_le q K)

theorem mem_L'_iff {x : LQ} : x ∈ L' q K ↔ x ∈ lambdaFieldOver q K := Iff.rfl

theorem isIntegral_lambdaModC : IsIntegral (↥(K₁ q K)) (lambdaModC Qb) :=
  isIntegral_lambdaModC_of_mem _ (qExpand_jqModC_mem_K₁ q K)

theorem isIntegral_lambdaNModC : IsIntegral (↥(K₁ q K)) (lambdaNModC Qb q) :=
  isIntegral_lambdaNModC_of_mem q _ (qExpand_jqNModC_mem_K₁ q K)

theorem L'_eq_adjoin : L' q K = IntermediateField.adjoin (↥(K₁ q K)) {lambdaModC Qb, lambdaNModC Qb q} :=
  LOver_eq_adjoin q K _ _ (constSeries_mem_K₁ q K)

scoped instance finiteDimensional_L' : FiniteDimensional (↥(K₁ q K)) (↥(L' q K)) :=
  finiteDimensional_LOver q K _ _ (constSeries_mem_K₁ q K) (qExpand_jqModC_mem_K₁ q K) (qExpand_jqNModC_mem_K₁ q K)

scoped instance isSeparable_L' : Algebra.IsSeparable (↥(K₁ q K)) (↥(L' q K)) := Algebra.IsSeparable.of_integral _ _

@[reducible] def algebraK₁L : Algebra (↥(K₁ q K)) (↥(lambdaFieldOver q K)) := (Subfield.inclusion (K₁_le q K)).toAlgebra

theorem finiteDimensional_lambdaFieldOver :
    letI := algebraK₁L q K
    FiniteDimensional (↥(K₁ q K)) (↥(lambdaFieldOver q K)) :=
  finiteDimensional_lambdaFieldOver_of_le q K _ (K₁_le q K) (constSeries_mem_K₁ q K)
    (qExpand_jqModC_mem_K₁ q K) (qExpand_jqNModC_mem_K₁ q K)

theorem isScalarTower_K₁_L : letI := algebraK₁L q K; IsScalarTower (↥(K₁ q K)) (↥(lambdaFieldOver q K)) LQ := by
  letI := algebraK₁L q K
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

section SpanForm

variable (A : ValuationSubring Qb)

def F₀ : Subfield LQ := Subfield.closure (Set.range ((qExpand Qb 2).comp (jRing A K).subtype))

theorem qExpand_mem_F₀ {y : LQ} (hy : y ∈ jRing A K) : qExpand Qb 2 y ∈ F₀ K A :=
  Subfield.subset_closure ⟨⟨y, hy⟩, rfl⟩

theorem jqModC_mem_jRing : jqModC Qb ∈ jRing A K := Subring.subset_closure (Or.inr rfl)

theorem constSeries_mem_jRing (a : ↥(coeffSubring A K)) : CharPReduction.constSeries (coeffSubring A K) a ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem algebraMap_mem_fieldOver' (N : ℕ) [NeZero N] {x : Qb} (hx : x ∈ K) : algebraMap Qb LQ x ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem jRing_le_fieldOver (N : ℕ) [NeZero N] : jRing A K ≤ (fieldOver N K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact algebraMap_mem_fieldOver' K N (Subring.mem_inf.mp a.2).2
  · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem F₀_le : F₀ K A ≤ lambdaFieldOver q K := by
  rw [F₀, Subfield.closure_le]
  rintro x ⟨y, rfl⟩
  exact qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver q K (jRing_le_fieldOver K A (1 * q) y.2)

theorem qExpand_jqModC_mem_F₀ : qExpand Qb 2 (jqModC Qb) ∈ F₀ K A := qExpand_mem_F₀ K A (jqModC_mem_jRing K A)

theorem exists_div_eq_of_mem (x : Qb) (hx : x ∈ K) :
    ∃ a b : ↥(coeffSubring A K), (b : Qb) ≠ 0 ∧ x = a / b := by
  rcases A.mem_or_inv_mem x with h | h
  · exact ⟨⟨x, Subring.mem_inf.mpr ⟨h, hx⟩⟩, ⟨1, one_mem _⟩, by simp, by simp⟩
  · by_cases hx0 : x = 0
    · exact ⟨⟨0, zero_mem _⟩, ⟨1, one_mem _⟩, by simp, by simp [hx0]⟩
    refine ⟨⟨1, one_mem _⟩, ⟨x⁻¹, Subring.mem_inf.mpr ⟨h, IntermediateField.inv_mem K hx⟩⟩, ?_, ?_⟩
    · simpa using hx0
    · simp

theorem constSeries_mem_F₀ (c : ↥K.toSubalgebra.toSubring) : CharPReduction.constSeries _ c ∈ F₀ K A := by
  obtain ⟨a, b, hb, hab⟩ := exists_div_eq_of_mem K A (c : Qb) c.2
  have : CharPReduction.constSeries K.toSubalgebra.toSubring c = algebraMap Qb LQ (a : Qb) / algebraMap Qb LQ (b : Qb) := by
    show algebraMap Qb LQ (c : Qb) = _
    rw [hab, map_div₀]
  rw [this]
  refine div_mem ?_ ?_
  · rw [← qExpand_algebraMap 2]; exact qExpand_mem_F₀ K A (constSeries_mem_jRing K A a)
  · rw [← qExpand_algebraMap 2]; exact qExpand_mem_F₀ K A (constSeries_mem_jRing K A b)

theorem isIntegral_jRing_jqNModC (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral ↥(jRing A K) (jqNModC Qb N) := by
  let jR : ↥(jRing A K) := ⟨jqModC Qb, jqModC_mem_jRing K A⟩
  refine ⟨data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(jRing A K)) jR), data.monic.map _, ?_⟩
  let F := IntermediateField.adjoin Qb ({jqModC Qb} : Set LQ)
  let jF : ↥F := ⟨jqModC Qb, IntermediateField.mem_adjoin_simple_self _ _⟩
  have h0 : Polynomial.aeval (jqNModC Qb N) (minpoly ↥F (jqNModC Qb N)) = 0 := minpoly.aeval ↥F _
  rw [ModularCurve.minpoly_jqNModC_eq Qb N data, Polynomial.aeval_def, Polynomial.eval₂_map] at h0
  rw [Polynomial.eval₂_map]
  convert h0 using 2 <;> try rfl
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp [jR]
    rfl

def toF₀ : ↥(jRing A K) →+* ↥(F₀ K A) :=
  ((qExpand Qb 2).comp (jRing A K).subtype).codRestrict (F₀ K A) fun r => qExpand_mem_F₀ K A r.2

theorem isIntegral_F₀_qExpand_jqNModC : IsIntegral ↥(F₀ K A) (qExpand Qb 2 (jqNModC Qb (1 * q))) := by
  obtain ⟨data, -⟩ := ModularCurve.exists_phiIrreducible (1 * q)
  obtain ⟨p, hp, hpy⟩ := isIntegral_jRing_jqNModC K A (1 * q) data
  refine ⟨p.map (toF₀ K A), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have h1 : (algebraMap (↥(F₀ K A)) LQ).comp (toF₀ K A) = (qExpand Qb 2).comp (algebraMap ↥(jRing A K) LQ) := by
    ext r; rfl
  rw [h1, ← Polynomial.hom_eval₂, hpy, map_zero]

theorem exists_finset_span_lambdaFieldOver [FiniteDimensional ℚ K] :
    ∃ u : Finset (LaurentSeries (AlgebraicClosure ℚ)), ∀ x ∈ lambdaFieldOver q K,
      x ∈ Submodule.span ↥(Subfield.closure (Set.range ((qExpand (AlgebraicClosure ℚ) 2).comp (jRing A K).subtype)))
        (↑u : Set (LaurentSeries (AlgebraicClosure ℚ))) := by
  classical

  show ∃ u : Finset LQ, ∀ x ∈ lambdaFieldOver q K, x ∈ Submodule.span ↥(F₀ K A) (↑u : Set LQ)
  have hF₀L := F₀_le q K A
  let Li : IntermediateField (↥(F₀ K A)) LQ := LOver q K (F₀ K A) hF₀L

  have hμ : IsIntegral (↥(F₀ K A)) (lambdaModC Qb) := isIntegral_lambdaModC_of_mem _ (qExpand_jqModC_mem_F₀ K A)
  have hJq := isIntegral_F₀_qExpand_jqNModC q K A
  let F₁ : IntermediateField (↥(F₀ K A)) LQ := IntermediateField.adjoin (↥(F₀ K A)) {qExpand Qb 2 (jqNModC Qb (1 * q))}
  haveI : FiniteDimensional (↥(F₀ K A)) ↥F₁ := IntermediateField.adjoin.finiteDimensional hJq
  haveI : Algebra.IsIntegral (↥(F₀ K A)) ↥F₁ := Algebra.IsIntegral.of_finite _ _
  have hμq₁ : IsIntegral (↥F₁) (lambdaNModC Qb q) := by
    have hJq₁ : qExpand Qb 2 (jqNModC Qb (1 * q)) ∈ F₁ := IntermediateField.mem_adjoin_simple_self _ _
    refine IsAlgebraic.isIntegral ⟨jLambdaPoly (⟨_, hJq₁⟩ : ↥F₁), jLambdaPoly_ne_zero _, ?_⟩
    rw [aeval_jLambdaPoly, sub_eq_zero]
    exact (jLambda_Qb_q q).symm
  have hμq : IsIntegral (↥(F₀ K A)) (lambdaNModC Qb q) := isIntegral_trans _ hμq₁

  haveI hfin : FiniteDimensional (↥(F₀ K A)) ↥Li := by
    show FiniteDimensional (↥(F₀ K A)) ↥(LOver q K (F₀ K A) hF₀L)
    rw [LOver_eq_adjoin q K (F₀ K A) hF₀L (constSeries_mem_F₀ K A)]
    exact IntermediateField.finiteDimensional_adjoin fun x hx => by
      rcases hx with rfl | rfl
      · exact hμ
      · exact hμq

  obtain ⟨s, hs⟩ := Module.finite_def.mp hfin
  refine ⟨s.image (fun z : ↥Li => (z : LQ)), fun x hx => ?_⟩
  have hx' : (⟨x, hx⟩ : ↥Li) ∈ Submodule.span (↥(F₀ K A)) (↑s : Set ↥Li) := by rw [hs]; exact Submodule.mem_top
  have hmap := Submodule.mem_map_of_mem (f := (Li.val : ↥Li →ₐ[↥(F₀ K A)] LQ).toLinearMap) hx'
  rw [Submodule.map_span] at hmap
  convert hmap using 2 <;> first | rfl | (ext y; simp)

end SpanForm

theorem exists_finset_span_lambdaFieldOver_K₁ (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ∃ u : Finset (LaurentSeries (AlgebraicClosure ℚ)), ∀ x ∈ lambdaFieldOver q K,
      x ∈ Submodule.span ↥(K₁ q K) (↑u : Set (LaurentSeries (AlgebraicClosure ℚ))) := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp (finiteDimensional_L' q K)
  refine ⟨s.image (fun z : ↥(L' q K) => (z : LaurentSeries (AlgebraicClosure ℚ))), fun x hx => ?_⟩
  have hx' : (⟨x, hx⟩ : ↥(L' q K)) ∈ Submodule.span (↥(K₁ q K)) (↑s : Set ↥(L' q K)) := by
    rw [hs]; exact Submodule.mem_top
  have hmap := Submodule.mem_map_of_mem (f := ((L' q K).val : ↥(L' q K) →ₐ[↥(K₁ q K)] _).toLinearMap) hx'
  rw [Submodule.map_span] at hmap
  convert hmap using 2 <;> first | rfl | (ext y; simp)

end L2FinPlumbing
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.L2FinPlumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.L2FinPlumbing"

namespace L2Fin
section Route

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k]

scoped instance charZero_LQ' : CharZero LQ := charZero_of_injective_algebraMap (R := Qb) (algebraMap Qb LQ).injective

set_option maxHeartbeats 12800000 in
theorem main (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    [IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    (u : Finset LQ) (hu : ∀ x ∈ lambdaFieldOver q K,
      x ∈ Submodule.span ↥((fieldOver (1 * q) K).map (qExpand Qb 2)) (↑u : Set LQ))
    (hncore : ∃ s : Finset (LaurentSeries (AlgebraicClosure ℚ)),
      (∀ c ∈ s, c ∈ (fieldOver (1 * q) K).map (qExpand (AlgebraicClosure ℚ) 2) ∧
        ((qExpand (AlgebraicClosure ℚ) 2).comp
          (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem c) ∧
      ∀ y : LaurentSeries (AlgebraicClosure ℚ),
        y ∈ (fieldOver (1 * q) K).map (qExpand (AlgebraicClosure ℚ) 2) →
        ((qExpand (AlgebraicClosure ℚ) 2).comp
          (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem y →
        ∃ g : LaurentSeries (AlgebraicClosure ℚ) → LaurentSeries (AlgebraicClosure ℚ),
          (∀ c ∈ s, g c ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ∧
          y = ∑ c ∈ s, qExpand (AlgebraicClosure ℚ) 2 (g c) * c) :
    ∃ t : Finset (LaurentSeries (AlgebraicClosure ℚ)),
      (∀ c ∈ t, c ∈ lambdaFieldOver q K ∧
        ((qExpand (AlgebraicClosure ℚ) 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem c) ∧
      ∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ lambdaFieldOver q K →
        ((qExpand (AlgebraicClosure ℚ) 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem x →
        ∃ f : LaurentSeries (AlgebraicClosure ℚ) → LaurentSeries (AlgebraicClosure ℚ),
          (∀ c ∈ t, f c ∈ (fieldOver (1 * q) K).map (qExpand (AlgebraicClosure ℚ) 2) ∧
            ((qExpand (AlgebraicClosure ℚ) 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem (f c)) ∧
          x = ∑ c ∈ t, f c * c := by
  classical
  set R₀ := modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) with hR₀
  set φ := qExpand Qb 2 with hφdef
  have hφ : Function.Injective φ := φ.injective

  set R : Subring LQ := R₀.map φ with hRdef
  set F₀ : Subfield LQ := (fieldOver (1 * q) K).map φ with hF₀def
  set L : Subfield LQ := lambdaFieldOver q K with hLdef
  have hR : IsNoetherianRing ↥R := isNoetherianRing_of_ringEquiv _ (R₀.equivMapOfInjective φ hφ)
  have hRF : R ≤ F₀.toSubring := by
    rintro _ ⟨r, hr, rfl⟩
    exact Subfield.mem_map.mpr ⟨r, modularLocalizedAtPoint_le_fieldOver red a K hr, rfl⟩
  have hFL : F₀ ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver q K hy
  have hfrac : ∀ x ∈ F₀, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ x * d = r := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    obtain ⟨y, hy, z, hz, hz0, rfl⟩ := exists_div_of_mem_fieldOver red a K hx₀
    refine ⟨φ y, ⟨y, hy, rfl⟩, φ z, ⟨z, hz, rfl⟩, (map_ne_zero_iff φ hφ).mpr hz0, ?_⟩
    rw [← map_mul, div_mul_cancel₀ _ hz0]

  have hbr : ∀ x : LQ, IsIntegral ↥R x ↔ (φ.comp R₀.subtype).IsIntegralElem x := fun x => isIntegral_map_iff R₀ x

  set N : Set LQ := {x | x ∈ F₀ ∧ IsIntegral ↥R x} with hNdef
  set B : Set LQ := {x | x ∈ L ∧ IsIntegral ↥R x} with hBdef

  obtain ⟨s, hsN, hsgen⟩ := hncore
  have hs : ∀ x ∈ N, x ∈ Submodule.span ↥R (↑s : Set LQ) := by
    rintro x ⟨hxF, hxint⟩
    obtain ⟨g, hg, hxeq⟩ := hsgen x hxF ((hbr x).mp hxint)
    rw [hxeq]
    refine Submodule.sum_mem _ fun c hc => ?_
    have : φ (g c) * c = (⟨φ (g c), ⟨g c, hg c hc, rfl⟩⟩ : ↥R) • c := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr hc))

  obtain ⟨t, htB, hgen⟩ := Subfield.exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span R hR F₀ L hRF hFL hfrac
    N B (fun x => Iff.rfl) (fun x => Iff.rfl) s hs u hu
  refine ⟨t, fun c hc => ?_, ?_⟩
  · obtain ⟨hcL, hcint⟩ := htB (Finset.mem_coe.mpr hc)
    exact ⟨hcL, (hbr c).mp hcint⟩
  · intro x hxL hxint
    obtain ⟨f, hf, hxeq⟩ := hgen x ⟨hxL, (hbr x).mpr hxint⟩
    exact ⟨f, fun c hc => ⟨(hf c hc).1, (hbr _).mp (hf c hc).2⟩, hxeq⟩

end Route
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.L2FinPlumbing"
end L2Fin
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.L2FinPlumbing P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.L2Fin"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.ModularCurve _root_.ModularCurve.NodeLocalized _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver.ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    [IsNoetherianRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))] :
    ∃ t : Finset (LaurentSeries (AlgebraicClosure ℚ)),
      (∀ c ∈ t, c ∈ lambdaFieldOver q K ∧
        ((qExpand (AlgebraicClosure ℚ) 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem c) ∧
      ∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ lambdaFieldOver q K →
        ((qExpand (AlgebraicClosure ℚ) 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem x →
        ∃ f : LaurentSeries (AlgebraicClosure ℚ) → LaurentSeries (AlgebraicClosure ℚ),
          (∀ c ∈ t, f c ∈ (fieldOver (1 * q) K).map (qExpand (AlgebraicClosure ℚ) 2) ∧
            ((qExpand (AlgebraicClosure ℚ) 2).comp (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)).subtype).IsIntegralElem (f c)) ∧
          x = ∑ c ∈ t, f c * c := by
  obtain ⟨u, hu⟩ := L2FinPlumbing.exists_finset_span_lambdaFieldOver_K₁ q K
  exact L2Fin.main red a K u hu (FltWs21.HN.core red a K)

end
end S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_finset_forall_isIntegralElem_eq_sum_mul_of_mem_lambdaFieldOver (solution)
