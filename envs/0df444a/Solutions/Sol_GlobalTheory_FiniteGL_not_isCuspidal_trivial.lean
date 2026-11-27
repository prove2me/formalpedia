-- Prove2me | solution 1 for GlobalTheory.FiniteGL.not_isCuspidal_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:53.456784+00:00
-- url     : https://prove2.me/submissions/87f499ca-760c-403f-bb9c-62b7d4716acc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Theorems.Thm_GlobalTheory_FiniteGL_isCuspidal_iff_twoBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.FiniteGL
variable (k : Type) [Field k] {N : ℕ}
variable {k}
variable (k)
variable {k}
namespace GlobalTheory.FiniteGL
theorem _root_.solution (hN : 2 ≤ N) : ¬ IsCuspidal (Representation.trivial ℂ (GL (Fin N) k) ℂ) := by
  intro h
  exact one_ne_zero ((isCuspidal_iff_twoBlocks _).mp h 1 one_pos (by omega) (1 : ℂ) fun u _ => by simp)
end GlobalTheory.FiniteGL
