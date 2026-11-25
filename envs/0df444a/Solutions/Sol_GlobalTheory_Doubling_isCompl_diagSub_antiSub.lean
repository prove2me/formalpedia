-- Prove2me | solution 1 for GlobalTheory.Doubling.isCompl_diagSub_antiSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:42:05.968219+00:00
-- url     : https://prove2.me/submissions/a06e9a97-4ba6-4466-afb6-190935481151

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_pairVec_mem_antiSub
import Theorems.Thm_GlobalTheory_Doubling_mem_diagSub
import Theorems.Thm_GlobalTheory_Doubling_mem_antiSub
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι)
namespace GlobalTheory.Doubling
theorem _root_.solution [Invertible (2 : A)] : IsCompl (diagSub A e) (antiSub A e) := by
  have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self _
  refine ⟨Submodule.disjoint_def.2 fun w h h' => ?_, codisjoint_iff.2 (eq_top_iff.2 fun w _ => ?_)⟩
  · obtain ⟨x, rfl⟩ := (mem_diagSub e).1 h
    have h3 := (pairVec_mem_antiSub e).1 h'
    have : x = 0 := funext fun i => by
      have := congrFun h3 i
      simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
      linear_combination ⅟(2 : A) * this - x i * h2
    rw [this]; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  · refine Submodule.mem_sup.2 ⟨_, (mem_diagSub e).2 ⟨fun i => ⅟(2 : A) * (w (e (.inl i)) + w (e (.inr i))), rfl⟩,
      _, (mem_antiSub e).2 ⟨fun i => ⅟(2 : A) * (w (e (.inl i)) - w (e (.inr i))), rfl⟩, funext fun j => ?_⟩
    obtain ⟨i | i, rfl⟩ := e.surjective j
    · simp only [Pi.add_apply, pairVec_inl]; linear_combination w (e (.inl i)) * h2
    · simp only [Pi.add_apply, pairVec_inr, Pi.neg_apply]; linear_combination w (e (.inr i)) * h2
end GlobalTheory.Doubling
