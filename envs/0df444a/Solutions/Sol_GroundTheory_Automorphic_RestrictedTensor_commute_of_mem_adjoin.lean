-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.commute_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:11.164574+00:00
-- url     : https://prove2.me/submissions/1c4ea1c9-9ca5-4004-9c8c-4d23dfdeb33d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {T : Set (End ℂ M)} {a : End ℂ M} (ha : ∀ t ∈ T, Commute a t) :
    ∀ b ∈ Algebra.adjoin ℂ T, Commute a b := by
  intro b hb
  induction hb using Algebra.adjoin_induction with
  | mem t ht => exact ha t ht
  | algebraMap c => exact (Algebra.commutes' c a).symm
  | add b c _ _ hb hc => exact hb.add_right hc
  | mul b c _ _ hb hc => exact hb.mul_right hc
end GroundTheory.Automorphic.RestrictedTensor
