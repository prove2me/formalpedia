-- Prove2me | solution 1 for GroundTheory.Brauer.centralizer_eq_iff_finrank_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:24:41.02237+00:00
-- url     : https://prove2.me/submissions/2a6ae74b-7a79-433d-8cde-0b742d6ee456

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
import Theorems.Thm_GroundTheory_Brauer_isSimpleRing_of_finiteDimensional
import Theorems.Thm_GroundTheory_Brauer_le_centralizer_of_isMulCommutative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Module
universe u v w
variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]
variable [Algebra.IsCentral K D] [FiniteDimensional K D]
namespace GroundTheory.Brauer
theorem _root_.solution (F : Subalgebra K D) [IsMulCommutative F] :
    Subalgebra.centralizer K (F : Set D) = F ↔ finrank K F ^ 2 = finrank K D := by
  have := isSimpleRing_of_finiteDimensional F
  have h := finrank_mul_finrank_centralizer F
  constructor
  · intro hc
    rw [hc] at h
    rw [sq]
    exact h
  · intro hsq
    have hF : 0 < finrank K F := Module.finrank_pos
    have hdim : finrank K F = finrank K (Subalgebra.centralizer K (F : Set D)) := by
      apply Nat.eq_of_mul_eq_mul_left hF
      rw [h, ← sq, hsq]
    exact (Subalgebra.toSubmodule_injective (Submodule.eq_of_le_of_finrank_eq
      (Subalgebra.toSubmodule.monotone (le_centralizer_of_isMulCommutative F)) hdim)).symm
end GroundTheory.Brauer
