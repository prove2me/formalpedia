-- Prove2me | solution 1 for GlobalTheory.ExactSeq.finite_of_isNoetherian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:45:09.508794+00:00
-- url     : https://prove2.me/submissions/95621267-62bb-428b-9e66-13be6b19dda8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero

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
theorem _root_.solution (h : Function.Exact f g) [Module.Finite R A] [IsNoetherian R C] :
    Module.Finite R B :=
  Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
    (fun x ↦ by rw [← h x, Subtype.ext_iff]; rfl) g.surjective_rangeRestrict
end GlobalTheory.ExactSeq
