-- Prove2me | solution 1 for GlobalTheory.periodic_of_mem_span_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:28:24.164646+00:00
-- url     : https://prove2.me/submissions/31b6711c-3e7a-45a4-b427-391f282b13fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Nat
open GlobalTheory
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
omit [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution {F : E → V} {S : Set E}
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) :
    ∀ x, ∀ g ∈ Submodule.span ℤ S, F (x + g) = F x := by
  let P : AddSubgroup E :=
    { carrier := {g | ∀ x, F (x + g) = F x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by rw [← ha (x + -a)]; simp }
  intro x g hg
  have : Submodule.span ℤ S ≤ AddSubgroup.toIntSubmodule P :=
    Submodule.span_le.2 fun s hs y => hper y s hs
  exact this hg x
end GlobalTheory
