-- Prove2me | solution 1 for GlobalTheory.PrinTwo.NoFix.bchar_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:30:58.226408+00:00
-- url     : https://prove2.me/submissions/d046ff10-5daa-4dac-bea8-308cbcab6950

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramifiedPrincipalSeriesNoInvariant
import Theorems.Thm_GlobalTheory_PrinTwo_bchar_one
import Theorems.Thm_GlobalTheory_PrinTwo_coordL_apply
import Theorems.Thm_GlobalTheory_PrinTwo_evL_apply
import Theorems.Thm_GlobalTheory_PrinTwo_val_bor
import Theorems.Thm_GlobalTheory_PrinTwo_val_nL
import Theorems.Thm_GlobalTheory_PrinTwo_val_nU
import Theorems.Thm_GlobalTheory_PrinTwo_val_tD
import Theorems.Thm_GlobalTheory_PrinTwo_val_wE
import Theorems.Thm_GlobalTheory_SmGL_absPow_add
import Theorems.Thm_GlobalTheory_SmGL_absPow_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.PrinTwo.bchar_one
attribute [local simp] GlobalTheory.PrinTwo.coordL_apply
attribute [local simp] GlobalTheory.PrinTwo.evL_apply
attribute [local simp] GlobalTheory.PrinTwo.val_bor
attribute [local simp] GlobalTheory.PrinTwo.val_nL
attribute [local simp] GlobalTheory.PrinTwo.val_nU
attribute [local simp] GlobalTheory.PrinTwo.val_tD
attribute [local simp] GlobalTheory.PrinTwo.val_wE



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PrinTwo
open GlobalTheory GlobalTheory.PrinTwo GlobalTheory.PrinTwo.NoFix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.PrinTwo.NoFix
theorem _root_.solution (μ₁ μ₂ : kˣ →* ℂˣ) (a d t : kˣ) :
    bchar μ₁ μ₂ (a * t) (d * t⁻¹) = bchar μ₁ μ₂ a d * ((μ₁ t * absPow k 1 t / μ₂ t : ℂˣ) : ℂ) := by
  have h1 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by rw [← absPow_add]; norm_num
  have h2 : absPow k (-1 / 2) = (absPow k (1 / 2))⁻¹ := by rw [neg_div, absPow_neg]
  simp only [bchar, h1, h2, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
  have e1 : ((μ₂ t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have e2 : ((absPow k (1 / 2) d : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have e3 : ((absPow k (1 / 2) t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
end GlobalTheory.PrinTwo.NoFix
