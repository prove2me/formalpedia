-- Prove2me | solution 1 for GlobalTheory.HermFrame.del_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:48.591705+00:00
-- url     : https://prove2.me/submissions/3e6d6c34-ed47-4211-9471-7d2f765cb743

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_mdel_transpose
import Theorems.Thm_GlobalTheory_HermFrame_mdel_conjTranspose
import Theorems.Thm_GlobalTheory_HermFrame_MContDiffAt_conjTranspose
import Theorems.Thm_GlobalTheory_HermFrame_mdel_mul
import Theorems.Thm_GlobalTheory_HermFrame_form_add_left
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n]
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution (hH : MContDiffAt 1 H z) (hu : IsUnit (H z).det) {s t : E → n → ℂ}
    (hs : ∀ a, ContDiffAt ℝ 1 (fun x => s x a) z) (ht : ∀ a, ContDiffAt ℝ 1 (fun x => t x a) z)
    (ξ : E) : del (fun x => form (H x) (s x) (t x)) z ξ =
      form (H z) (covDel H s z ξ) (t z) + form (H z) (s z) fun a => dbar (fun x => t x a) z ξ := by
  let S : E → Matrix n Unit ℂ := fun x => replicateCol Unit (s x)
  let T : E → Matrix n Unit ℂ := fun x => replicateCol Unit (t x)
  have hS : MContDiffAt 1 S z := fun a _ => hs a
  have hT : MContDiffAt 1 T z := fun a _ => ht a
  have e : ∀ (K : Matrix n n ℂ) (P Q : Matrix n Unit ℂ),
      (Pᵀ * K * Qᴴᵀ) () () = form K (fun a => P a ()) fun a => Q a () := fun K P Q => by
    rw [form_eq_sum, Finset.sum_comm]
    simp [mul_apply, Finset.sum_mul]
  have h := congrFun (congrFun (mdel_mul (hS.transpose.mul hH) hT.conjTranspose.transpose ξ) ()) ()
  rw [mdel_mul hS.transpose hH, mdel_transpose (fun x => (T x)ᴴ), mdel_conjTranspose,
    mdel_transpose, Matrix.add_mul, ← conn_transpose_mul hu, ← Matrix.mul_assoc, ← transpose_mul,
    mdel_apply] at h
  simp only [Matrix.add_apply, e] at h
  refine h.trans ?_
  rw [covDel, form_add_left]
  have : (fun a => (conn H z ξ * S z) a ()) = conn H z ξ *ᵥ s z := rfl
  rw [this]
  change _ + (_ + form (H z) (fun a => del (fun x => s x a) z ξ) (t z)) = _
  change form (H z) (s z) (fun a => dbar (fun x => t x a) z ξ) +
    (form (H z) (conn H z ξ *ᵥ s z) (t z) + _) = _
  ring
end GlobalTheory.HermFrame
