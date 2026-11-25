-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.curv_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:02.911138+00:00
-- url     : https://prove2.me/submissions/69ebdc84-62ba-4d19-a299-5dc17e6e6bab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_blockQQ_eq
import Theorems.Thm_GlobalTheory_HermFrame_Model_mContDiffAt_orthCoeff
import Theorems.Thm_GlobalTheory_HermFrame_Model_mdbar_orthCoeff
import Theorems.Thm_GlobalTheory_HermFrame_Model_conn_quot
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_mul
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_neg


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
    curv (fun x => quotGram (H x)) z ξ η =
      blockQQ (H z) (curv H z ξ η) + secondForm H z ξ * secondFormAdj H z η := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have he : (fun x => conn (fun x => quotGram (H x)) x ξ) =ᶠ[𝓝 z]
      fun x => (conn H x ξ).toBlocks₂₂ + -((conn H x ξ).toBlocks₂₁ * orthCoeff (H x)) := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, h.subGram.eventually_isUnit hs]
      with x c a b
    rw [conn_quot (c.of_le one_le_two) a b, blockQQ_eq, sub_eq_add_neg]
  have c22 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₂₂) z := hc.submatrix Sum.inr Sum.inr
  have c21 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₂₁) z := hc.submatrix Sum.inr Sum.inl
  have ho := mContDiffAt_orthCoeff h1 hs
  rw [curv, mdbar_congr he, mdbar_add c22 (c21.mul ho).neg, mdbar_neg, mdbar_mul c21 ho,
    mdbar_orthCoeff h1 hh hu hs, blockQQ_eq, secondForm_eq,
    show (curv H z ξ η).toBlocks₂₂ = -mdbar (fun x => (conn H x ξ).toBlocks₂₂) z η from rfl,
    show (curv H z ξ η).toBlocks₂₁ = -mdbar (fun x => (conn H x ξ).toBlocks₂₁) z η from rfl,
    Matrix.neg_mul]
  abel
end GlobalTheory.HermFrame.Model
