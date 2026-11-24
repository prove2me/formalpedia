-- Prove2me | solution 1 for GlobalTheory.RelIndexOfMap.index_pi_dep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:43.876646+00:00
-- url     : https://prove2.me/submissions/c7e0c645-8354-419c-a541-362b1ff437c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexEqOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelIndexOfMap
namespace GlobalTheory.RelIndexOfMap
theorem _root_.solution {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, Group (H i)]
    (V : ∀ i, Subgroup (H i)) :
    (Subgroup.pi Set.univ V).index = ∏ i, (V i).index := by
  simp only [Subgroup.index_eq_card]
  rw [← Nat.card_pi]
  let f : ((∀ i, H i) ⧸ Subgroup.pi Set.univ V) → ∀ i, H i ⧸ V i :=
    Quotient.lift (fun g i => (QuotientGroup.mk (g i) : H i ⧸ V i)) (by
      intro a b hab
      have hab' := QuotientGroup.leftRel_apply.1 hab
      funext i
      exact QuotientGroup.eq.2 (hab' i trivial))
  refine Nat.card_eq_of_bijective f ⟨?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂ a b fun a b hab => ?_
    refine QuotientGroup.eq.2 fun i _ => ?_
    exact QuotientGroup.eq.1 (congrFun hab i)
  · intro q
    refine ⟨QuotientGroup.mk fun i => (q i).out, ?_⟩
    funext i
    exact Quotient.out_eq (q i)
end GlobalTheory.RelIndexOfMap
