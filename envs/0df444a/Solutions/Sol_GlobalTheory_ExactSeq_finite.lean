-- Prove2me | solution 1 for GlobalTheory.ExactSeq.finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:00.831846+00:00
-- url     : https://prove2.me/submissions/414c5009-7d03-4ebb-9a85-e70f58ba7f2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_GlobalTheory_ExactSeq_finite_of_isNoetherian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
open GlobalTheory.ExactSeq
variable {R : Type*} [Ring R] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
namespace GlobalTheory.ExactSeq
theorem _root_.solution [IsNoetherianRing R] (h : Function.Exact f g) [Module.Finite R A]
    [Module.Finite R C] : Module.Finite R B :=
  finite_of_isNoetherian h
end GlobalTheory.ExactSeq
