-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_mul_mem_wordSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:18.342784+00:00
-- url     : https://prove2.me/submissions/48697c5c-a379-4d52-baff-503a704a6762

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_mem_wordSpan
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
theorem _root_.solution {P : Fin n × Fin n → Prop} {a : Fin n × Fin n} (ha : P a) {k : ℕ}
    {u : U n} (hu : u ∈ wordSpan P k) : e a * u ∈ wordSpan P (k + 1) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl, rfl⟩ := hx
    rw [← word_cons]
    refine word_mem_wordSpan (w := a :: w) ?_
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ha
    · exact hw b hb
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
end GroundTheory.Automorphic.HarishChandra
