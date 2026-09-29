-- Prove2me | solution 1 for ModularCurve.MultCovering.cuspZeroBar_not_mem_infChart_dom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7e5d5e36-d253-5c11-8754-abcaa3ddf1e3

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_isZeroSide_cuspZeroBar
import Theorems.Thm_ModularCurve_not_isInftySide_cuspZeroBar
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidalSnd
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_cuspZeroBar_not_mem_infChart_dom
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_cuspZeroBar_not_mem_infChart_dom.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_cuspZeroBar_not_mem_infChart_dom.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull cuspInftyBar qExpand qExpand_one_apply jq jqd_mem_full modularFunctionFieldBar coeffEmb coeffEmb_mem_laurentBaseChange PlaceSpecialization.jFun PlaceSpecialization charLGeomPlaceEquiv cuspZeroBar eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty isZeroSide_cuspZeroBar not_isInftySide_cuspZeroBar ord_cuspZeroBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero not_isStrictType_of_isCuspidalSnd"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "ChartCtx infChart chart"
namespace P2MzCZ
p2m_open "ModularCurve.MultCovering ModularCurve"

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem redFst_eq_placeInfty_of_isCuspidal [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hW : Γ.P.IsCuspidal W) :
    Γ.P.redFst W = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A)
      (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) := by
  rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (IsLocalRing.ResidueField ↥A)
      (Γ.P.redFst W) with ⟨c, hc⟩ | h
  · exact absurd hc (Γ.supply.redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal hW c)
  · exact h

theorem ord_cuspZeroBar_jFun (p : ℕ) [Fact p.Prime] :
    (cuspZeroBar (1 * p)).ord (PlaceSpecialization.jFun (q := p)) = -((1 * p : ℕ) : ℤ) := by
  have hF : IsFrickeAutFull (1 * p) (frickeInvolutionFull (1 * p)) :=
    isFrickeAutFull_frickeInvolutionFull (1 * p) (exists_isFrickeAutFull_of_neZero (1 * p))
  have h := ord_cuspZeroBar_coeffEmb_qExpand (1 * p) hF (1 * p) 1 (mul_one (1 * p))
  have e1 : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (Dvd.intro_left (1 * p) (mul_one (1 * p))))⟩ :
        ↥(modularFunctionFieldBar (1 * p))) = PlaceSpecialization.jFun (q := p) :=
    Subtype.ext (by simp only [qExpand_one_apply]; rfl)
  rw [e1] at h
  exact h

theorem isCuspidal_cuspZeroBar : Γ.P.IsCuspidal (cuspZeroBar (1 * p)) := by
  intro a
  by_contra hpos
  push_neg at hpos
  have hj := ord_cuspZeroBar_jFun p
  have hneg : (cuspZeroBar (1 * p)).ord (PlaceSpecialization.jFun (q := p)) < 0 := by
    rw [hj]; simp [(Fact.out : p.Prime).pos]
  set c := algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ) with hc
  have hj0 : PlaceSpecialization.jFun (q := p) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hneg; exact lt_irrefl _ hneg
  have hd0 : PlaceSpecialization.jFun (q := p) - c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hpos; exact lt_irrefl _ hpos
  by_cases hc0 : c = 0
  · rw [hc0, sub_zero] at hpos; exact lt_irrefl _ (hneg.trans hpos)
  · have hordc : (cuspZeroBar (1 * p)).ord c = 0 := Place.ord_algebraMap _ _
    have hmin := Place.min_ord_le_ord_add (cuspZeroBar (1 * p)) hd0 hc0 (by rw [sub_add_cancel]; exact hj0)
    rw [sub_add_cancel, hordc] at hmin
    have : (0 : ℤ) ≤ (cuspZeroBar (1 * p)).ord (PlaceSpecialization.jFun (q := p)) :=
      le_trans (le_min hpos.le le_rfl) hmin
    exact absurd hneg (not_lt.mpr this)

theorem cuspZeroBar_not_mem_infChart_dom : cuspZeroBar (1 * p) ∉ (infChart Γ).dom := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  haveI : DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A)) := Classical.decEq _
  have hz : Γ.P.IsZeroSide (cuspZeroBar (1 * p)) := isZeroSide_cuspZeroBar Γ.P
  have hcusp : Γ.P.IsCuspidal (cuspZeroBar (1 * p)) := isCuspidal_cuspZeroBar Γ
  have hinf : Γ.P.IsCuspidal (cuspInftyBar (1 * p)) := (Γ.supply.isInftySide_cuspInftyBar).1
  have heq : Γ.P.redFst (cuspZeroBar (1 * p)) = Γ.P.redFst (cuspInftyBar (1 * p)) := by
    rw [redFst_eq_placeInfty_of_isCuspidal Γ _ hcusp, redFst_eq_placeInfty_of_isCuspidal Γ _ hinf]
  rintro (hs | hi | hS)
  · exact (not_isStrictType_of_isCuspidalSnd Γ.P _ hz.1).1 hs
  · exact not_isInftySide_cuspZeroBar Γ.P hi
  · exact (Γ.supply.isAffineGeomPlace_iff _).mp (Γ.supply.sheet.sheet_affine _ hS) heq

end ModularCurve.MultCovering.P2MzCZ

open _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_MultCovering_cuspZeroBar_not_mem_infChart_dom.ModularCurve.MultCovering in
theorem solution {p : ℕ} [Fact p.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    cuspZeroBar (1 * p) ∉ (infChart Γ).dom :=
  ModularCurve.MultCovering.P2MzCZ.cuspZeroBar_not_mem_infChart_dom Γ

end S_ModularCurve_MultCovering_cuspZeroBar_not_mem_infChart_dom
end P2MW
export P2MW.S_ModularCurve_MultCovering_cuspZeroBar_not_mem_infChart_dom (solution)
