-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mul_mem_wordSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:31.279554+00:00
-- url     : https://prove2.me/submissions/6b8e1a47-6a01-48fc-9aba-a20db75fcd48

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_mul_mem_wordSpan
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {P : Fin n × Fin n → Prop} {v : List (Fin n × Fin n)}
    (hv : ∀ a ∈ v, P a) {k : ℕ} {u : U n} (hu : u ∈ wordSpan P k) :
    word v * u ∈ wordSpan P (v.length + k) := by
  induction v with
  | nil => simpa using hu
  | cons a v ih =>
    rw [word_cons, mul_assoc, List.length_cons, show v.length + 1 + k = (v.length + k) + 1 by omega]
    exact e_mul_mem_wordSpan (hv a (List.mem_cons_self ..))
      (ih fun b hb => hv b (List.mem_cons_of_mem _ hb))
end GroundTheory.Automorphic.HarishChandra
