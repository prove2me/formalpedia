-- Prove2me | solution 1 for ModularCurve.MultCovering.not_isSSCentred_of_mem_zeroChart_dom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/95a08ac1-f930-54e6-a95e-cbd953effaa6

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_not_isSSCentred_of_mem_zeroChart_dom
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_not_isSSCentred_of_mem_zeroChart_dom.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_not_isSSCentred_of_mem_zeroChart_dom.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull qExpand qExpand_one_apply jq jqd_mem_full modularFunctionFieldBar coeffEmb coeffEmb_mem_laurentBaseChange ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun PlaceSpecialization.jqFun PlaceSpecialization frickeInvolutionBar PlaceSpecialization.LevelOneProlongationPair.not_isSSCentred_of_mem_chartFst_dom frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero frickeInvolutionBar_frickeInvolutionBar pow_mem_ssJSet_iff_of_perfectField"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jF jpF IsSSCentred ChartCtx zeroChart"
namespace P2MzD
p2m_open "ModularCurve.MultCovering ModularCurve"

theorem isFrickeAutFull_frickeInvolutionFull_oneMul (p : ℕ) [Fact p.Prime] :
    IsFrickeAutFull (1 * p) (frickeInvolutionFull (1 * p)) :=
  isFrickeAutFull_frickeInvolutionFull (1 * p) (exists_isFrickeAutFull_of_neZero (1 * p))

theorem frickeInvolutionBar_jF (p : ℕ) [Fact p.Prime] : frickeInvolutionBar (1 * p) (jF p) = jpF p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * p) (isFrickeAutFull_frickeInvolutionFull_oneMul p) 1 p rfl
  have e1 : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (Dvd.intro p rfl))⟩ :
        modularFunctionFieldBar (1 * p)) = jF p := Subtype.ext (by simp only [qExpand_one_apply])
  have e2 : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (Dvd.intro_left 1 rfl))⟩ :
        modularFunctionFieldBar (1 * p)) = jpF p := Subtype.ext rfl
  rw [e1, e2] at h
  exact h

theorem frickeInvolutionBar_symm_apply (p : ℕ) [Fact p.Prime] (y : modularFunctionFieldBar (1 * p)) :
    (frickeInvolutionBar (1 * p)).symm y = frickeInvolutionBar (1 * p) y := by
  apply (frickeInvolutionBar (1 * p)).injective
  rw [AlgEquiv.apply_symm_apply, frickeInvolutionBar_frickeInvolutionBar]

theorem frickeInvolutionBar_jpF (p : ℕ) [Fact p.Prime] : frickeInvolutionBar (1 * p) (jpF p) = jF p := by
  rw [← frickeInvolutionBar_jF p, frickeInvolutionBar_frickeInvolutionBar]

theorem frickeInvolutionBar_jFun (p : ℕ) [Fact p.Prime] :
    frickeInvolutionBar (1 * p) (PlaceSpecialization.jFun (q := p)) = PlaceSpecialization.jqFun (q := p) := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * p) (isFrickeAutFull_frickeInvolutionFull_oneMul p) 1 (1 * p) (one_mul (1 * p))
  have e1 : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (Dvd.intro (1 * p) (one_mul (1 * p))))⟩ :
        ↥(modularFunctionFieldBar (1 * p))) = PlaceSpecialization.jFun (q := p) :=
    Subtype.ext (by simp only [qExpand_one_apply]; rfl)
  have e2 : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (Dvd.intro_left 1 (one_mul (1 * p))))⟩ :
        ↥(modularFunctionFieldBar (1 * p))) = PlaceSpecialization.jqFun (q := p) := Subtype.ext rfl
  rw [e1, e2] at h
  exact h

theorem frickeInvolutionBar_jqFun (p : ℕ) [Fact p.Prime] :
    frickeInvolutionBar (1 * p) (PlaceSpecialization.jqFun (q := p)) = PlaceSpecialization.jFun (q := p) := by
  rw [← frickeInvolutionBar_jFun p, frickeInvolutionBar_frickeInvolutionBar]

end ModularCurve.MultCovering.P2MzD

open ModularCurve.MultCovering.P2MzD

theorem solution {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)))
    (hW : W ∈ (zeroChart Γ).dom) (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ¬ IsSSCentred p A W a := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  rintro ⟨⟨x, hx, hjx⟩, ⟨y, hy, hjy⟩⟩
  have hap : a ^ p ∈ ssJSet p (IsLocalRing.ResidueField ↥A) := (ModularCurve.pow_mem_ssJSet_iff_of_perfectField p a).mpr ha
  refine PlaceSpecialization.LevelOneProlongationPair.not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply
    (frickeInvolutionBar (1 * p) • W) hW (a ^ p) hap ⟨⟨y, hy, ?_⟩, ⟨x, ?_, ?_⟩⟩
  · rw [Place.Transport.ord_smul', frickeInvolutionBar_symm_apply, map_sub, AlgEquiv.commutes,
      frickeInvolutionBar_jFun]
    exact hjy
  · rw [hx, ← pow_mul, ← sq, Γ.supply.pow_sq_eq_self_of_mem a ha]
  · rw [Place.Transport.ord_smul', frickeInvolutionBar_symm_apply, map_sub, AlgEquiv.commutes,
      frickeInvolutionBar_jqFun]
    exact hjx

end S_ModularCurve_MultCovering_not_isSSCentred_of_mem_zeroChart_dom
end P2MW
export P2MW.S_ModularCurve_MultCovering_not_isSSCentred_of_mem_zeroChart_dom (solution)
