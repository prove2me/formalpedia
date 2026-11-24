-- Prove2me | solution 1 for GlobalTheory.ExactSeq.finrank_eq_range_add_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:43:41.113185+00:00
-- url     : https://prove2.me/submissions/d6d045f1-edb0-4bd2-b548-5a357ee80166

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
variable {k : Type*} [DivisionRing k]
namespace GlobalTheory.ExactSeq
theorem _root_.solution {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module k A] [Module k B] [Module k C] {f : A →ₗ[k] B} {g : B →ₗ[k] C}
    (h : Function.Exact f g) [Module.Finite k B] :
    finrank k B = finrank k (LinearMap.range f) + finrank k (LinearMap.range g) := by
  rw [← g.finrank_range_add_finrank_ker, h.linearMap_ker_eq, add_comm]
end GlobalTheory.ExactSeq
