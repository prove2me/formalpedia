-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.exists_transv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:42:53.403429+00:00
-- url     : https://prove2.me/submissions/e1dbd7ba-39d7-4fcd-a0f1-a08406692979

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
namespace GlobalTheory.NonGenericLocalCheck
theorem _root_.solution {α : Type*} (rel : α → α → Prop) (hr : Equivalence rel) (S : Set α) :
    ∃ R, IsTransv rel S R := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨∅, Set.empty_subset _, fun x => isEmptyElim x, fun y hy => hy.elim⟩

  obtain ⟨pick, hpk⟩ : ∃ pick : α → α, ∀ x, pick x = Classical.epsilon (fun y => y ∈ S ∧ rel y x) :=
    ⟨_, fun _ => rfl⟩
  have hpick : ∀ x ∈ S, pick x ∈ S ∧ rel (pick x) x := fun x hx => by
    rw [hpk]
    exact Classical.epsilon_spec (p := fun y => y ∈ S ∧ rel y x) ⟨x, hx, hr.refl x⟩
  have hcongr : ∀ x x', rel x x' → pick x = pick x' := by
    intro x x' h
    have hset : (fun y => y ∈ S ∧ rel y x) = (fun y => y ∈ S ∧ rel y x') := by
      funext y
      exact propext ⟨fun ⟨hy, hyx⟩ => ⟨hy, hr.trans hyx h⟩,
        fun ⟨hy, hyx⟩ => ⟨hy, hr.trans hyx (hr.symm h)⟩⟩
    rw [hpk, hpk, hset]
  refine ⟨pick '' S, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hpick x hx).1
  · intro x hx
    exact ⟨pick x, ⟨x, hx, rfl⟩, (hpick x hx).2⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    exact hcongr x x' (hr.trans (hr.symm (hpick x hx).2) (hr.trans h (hpick x' hx').2))
end GlobalTheory.NonGenericLocalCheck
