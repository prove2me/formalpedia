-- Prove2me | solution 1 for GlobalTheory.HilbTensorExists.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:30:35.94886+00:00
-- url     : https://prove2.me/submissions/ec10db8a-2348-443d-bf95-22fb4d71b0d3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCompleteDense
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.HilbTensorExists
namespace GlobalTheory.HilbTensorExists
theorem _root_.solution {X L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (s : X → L) (hs : Dense (Submodule.span ℂ (Set.range s) : Set L)) (f : X → X)
    (hf : ∀ x y, ⟪s (f x), s (f y)⟫_ℂ = ⟪s x, s y⟫_ℂ) :
    ∃ T : L →L[ℂ] L, ∀ x, T (s x) = s (f x) := by
  let S := Finsupp.linearCombination ℂ s
  let A := Finsupp.linearCombination ℂ (s ∘ f)
  have key : ∀ c : X →₀ ℂ, ⟪A c, A c⟫_ℂ = ⟪S c, S c⟫_ℂ := by
    intro c
    simp only [A, S, Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
      inner_smul_left, inner_smul_right, Function.comp_apply, hf]
  have hn : ∀ c, ‖A c‖ ≤ 1 * ‖S c‖ := by
    intro c
    rw [one_mul, @norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, key]
  have hd : DenseRange S := by
    rw [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination]
    exact hs
  refine ⟨A.extendOfNorm S, fun x => ?_⟩
  have h := LinearMap.extendOfNorm_eq hd ⟨1, hn⟩ (Finsupp.single x (1 : ℂ))
  simp only [S, A, Finsupp.linearCombination_single, one_smul, Function.comp_apply] at h
  exact h
end GlobalTheory.HilbTensorExists
