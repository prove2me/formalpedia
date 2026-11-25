-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.curv_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:04.034493+00:00
-- url     : https://prove2.me/submissions/6ae36db9-ee78-4272-8969-a5eb0d2fdf66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_blockSS_eq
import Theorems.Thm_GlobalTheory_HermFrame_Model_conn_sub
import Theorems.Thm_GlobalTheory_HermFrame_Model_mContDiffAt_orthCoeff
import Theorems.Thm_GlobalTheory_HermFrame_Model_mdbar_orthCoeff
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
namespace GlobalTheory.HermFrame.Model
theorem _root_.solution (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (ξ η : E) :
    curv (fun x => subGram (H x)) z ξ η =
      blockSS (H z) (curv H z ξ η) - secondFormAdj H z η * secondForm H z ξ := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have he : (fun x => conn (fun x => subGram (H x)) x ξ) =ᶠ[𝓝 z]
      fun x => (conn H x ξ).toBlocks₁₁ + orthCoeff (H x) * (conn H x ξ).toBlocks₂₁ := by
    filter_upwards [h.eventually_isUnit hu, h.subGram.eventually_isUnit hs] with x a b
    rw [conn_sub (H := H) a b, blockSS_eq]
  have c11 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₁₁) z := hc.submatrix Sum.inl Sum.inl
  have c21 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₂₁) z := hc.submatrix Sum.inr Sum.inl
  have ho := mContDiffAt_orthCoeff h1 hs
  rw [curv, mdbar_congr he, mdbar_add c11 (ho.mul c21), mdbar_mul ho c21,
    mdbar_orthCoeff h1 hh hu hs, blockSS_eq, secondForm_eq,
    show (curv H z ξ η).toBlocks₁₁ = -mdbar (fun x => (conn H x ξ).toBlocks₁₁) z η from rfl,
    show (curv H z ξ η).toBlocks₂₁ = -mdbar (fun x => (conn H x ξ).toBlocks₂₁) z η from rfl,
    Matrix.mul_neg]
  abel
end GlobalTheory.HermFrame.Model
