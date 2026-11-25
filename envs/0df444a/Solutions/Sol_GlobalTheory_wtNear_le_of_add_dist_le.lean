-- Prove2me | solution 1 for GlobalTheory.wtNear_le_of_add_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:43.105161+00:00
-- url     : https://prove2.me/submissions/5df29653-e67c-4a1a-8c1d-9c508ff3d9ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearLeOfAddDistLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (Λ Λ' : Fin n → ℝ) (t t' : ℝ),
      t + ∑ a, |Λ a - Λ' a| ≤ t' → WtNear E Λ t ≤ WtNear E Λ' t' := by
  intro M _ _ n _ E Λ Λ' t t' h
  unfold WtNear
  apply Submodule.span_mono
  rintro x ⟨ω, hω, hx⟩
  refine ⟨ω, ?_, hx⟩
  have h1 : ∑ a, |ω a - Λ' a| ≤ ∑ a, (|ω a - Λ a| + |Λ a - Λ' a|) :=
    Finset.sum_le_sum fun a _ => abs_sub_le _ _ _
  rw [Finset.sum_add_distrib] at h1
  linarith
end GlobalTheory
