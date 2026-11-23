-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.TopClose.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:44.504867+00:00
-- url     : https://prove2.me/submissions/468858f8-721a-458e-be0e-17295525e591

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
namespace TopClose
theorem _root_.solution {k l : ℕ} {a b a' b' : MvPolynomial (Fin n) ℂ} (h : TopClose k a b)
    (h' : TopClose l a' b') : TopClose (k + l) (a * a') (b * b') := by
  obtain ⟨ha, hb, hab⟩ := h
  obtain ⟨ha', hb', hab'⟩ := h'
  refine ⟨(totalDegree_mul _ _).trans (add_le_add ha ha'),
    (totalDegree_mul _ _).trans (add_le_add hb hb'), ?_⟩
  by_cases e : a = b ∧ a' = b'
  · left; rw [e.1, e.2]
  right
  have key : a * a' - b * b' = (a - b) * a' + b * (a' - b') := by ring
  rw [key]
  refine lt_of_le_of_lt (totalDegree_add _ _) (max_lt ?_ ?_)
  · rcases hab with h1 | h1
    · rw [h1, sub_self, zero_mul, totalDegree_zero]
      rcases hab' with h2 | h2
      · exact absurd ⟨h1, h2⟩ e
      · omega
    · exact lt_of_le_of_lt (totalDegree_mul _ _) (by omega)
  · rcases hab' with h1 | h1
    · rw [h1, sub_self, mul_zero, totalDegree_zero]
      rcases hab with h2 | h2
      · exact absurd ⟨h2, h1⟩ e
      · omega
    · exact lt_of_le_of_lt (totalDegree_mul _ _) (by omega)
end TopClose
end GroundTheory.Automorphic.HarishChandra
