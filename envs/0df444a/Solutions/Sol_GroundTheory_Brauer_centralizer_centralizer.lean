-- Prove2me | solution 1 for GroundTheory.Brauer.centralizer_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:29.484895+00:00
-- url     : https://prove2.me/submissions/033bdf43-cf7d-436b-8655-0558aa6d6b5d

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer

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
open SkolemNoether
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A)
open CentralizerModule
variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] [IsSimpleRing B]
namespace GroundTheory.Brauer
theorem _root_.solution :
    Subalgebra.centralizer K (Subalgebra.centralizer K (B : Set A) : Set A) = B := by
  set C := Subalgebra.centralizer K (B : Set A)
  have : IsSimpleRing C := isSimpleRing_centralizer B
  have h1 := finrank_mul_finrank_centralizer B
  have h2 := finrank_mul_finrank_centralizer C
  have hC : 0 < finrank K C := Module.finrank_pos
  have hle : B ≤ Subalgebra.centralizer K (C : Set A) := Subalgebra.le_centralizer_centralizer K
  have hdim : finrank K B = finrank K (Subalgebra.centralizer K (C : Set A)) := by
    apply Nat.eq_of_mul_eq_mul_left hC
    rw [h2, mul_comm, h1]
  exact (Subalgebra.toSubmodule_injective
    (Submodule.eq_of_le_of_finrank_eq (Subalgebra.toSubmodule.monotone hle) hdim)).symm
end GroundTheory.Brauer
