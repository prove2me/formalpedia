-- Prove2me | solution 1 for GlobalTheory.UniformScalarBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:07.262605+00:00
-- url     : https://prove2.me/submissions/e8d40987-5ee8-441f-9f88-d7e5dfdb4baf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformScalar
import Theorems.Thm_GlobalTheory_UniformScalarBound_uniform_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UniformScalarBound
namespace GlobalTheory.UniformScalarBound
theorem _root_.solution : ∀ {R V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : AddCommGroup V]
    [inst_3 : Module R V] (A B : Submodule R V), Submodule.FG A →
    (∀ x ∈ A, ∃ (s : R), s ≠ (0 : R) ∧ s • x ∈ B) →
    ∃ (s : R), s ≠ (0 : R) ∧ ∀ x ∈ A, s • x ∈ B :=
  fun A B hA h => uniform_scalar A B hA h
end GlobalTheory.UniformScalarBound
