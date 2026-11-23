-- Prove2me | solution 1 for GroundTheory.Brauer.tensorCentralizerAlgEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:28.089971+00:00
-- url     : https://prove2.me/submissions/68d146da-485b-4ba4-904a-624099942919

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Module
open SkolemNoether
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A)
open CentralizerModule
variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] [IsSimpleRing B]
variable [Algebra.IsCentral K B]
namespace GroundTheory.Brauer
theorem _root_.solution (b : B) (c : Subalgebra.centralizer K (B : Set A)) :
    tensorCentralizerAlgEquiv B (b ⊗ₜ[K] c) = (b : A) * c := by
  simp only [tensorCentralizerAlgEquiv, tensorCentralizerHom, AlgEquiv.ofBijective_apply]
  rfl
end GroundTheory.Brauer
