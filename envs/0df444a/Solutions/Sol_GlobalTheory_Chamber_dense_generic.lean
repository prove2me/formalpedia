-- Prove2me | solution 1 for GlobalTheory.Chamber.dense_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:30:04.503716+00:00
-- url     : https://prove2.me/submissions/64b36982-edcf-47b5-8654-74dd608dd0ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_InverseChamberMap
import Theorems.Thm_GlobalTheory_Chamber_IsPar_wt_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical
open GlobalTheory GlobalTheory.Chamber
variable {k : ℕ}
namespace GlobalTheory.Chamber
theorem _root_.solution : Dense (generic k) := by
  have e : generic k = ⋂ x : {x : Finset (SV k) × Finset (SV k) × SV k // IsPar x.1 ∧ x.2.1 ⊆ x.1 ∧ x.2.2 ∈ x.1 \ x.2.1},
      ((Submodule.span ℝ {wt x.1.2.1 x.1.2.2})ᗮ : Set (A0 k))ᶜ := by
    ext l
    simp only [generic, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, SetLike.mem_coe,
      Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact ⟨fun h x => h _ x.2.1 _ x.2.2.1 _ x.2.2.2, fun h P hP Q hQ u hu => h ⟨(P, Q, u), hP, hQ, hu⟩⟩
  rw [e]
  refine dense_iInter_of_isOpen (fun x => (Submodule.isClosed_orthogonal _).isOpen_compl) fun x => ?_
  rw [← interior_eq_empty_iff_dense_compl, ← Set.not_nonempty_iff_eq_empty]
  intro h
  have := (Submodule.orthogonal_eq_top_iff _).1 (Submodule.eq_top_of_nonempty_interior' _ h)
  exact x.2.1.wt_ne_zero x.2.2.1 x.2.2.2 (Submodule.span_singleton_eq_bot.1 this)
end GlobalTheory.Chamber
