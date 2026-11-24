-- Prove2me | solution 1 for GlobalTheory.ExactSeq.finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:09:27.450857+00:00
-- url     : https://prove2.me/submissions/7f74e4c2-16d5-4252-bec4-fa9b9bca4af7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_GlobalTheory_ExactSeq_finite
import Theorems.Thm_GlobalTheory_ExactSeq_finrank_eq_range_add_range

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
    (h : Function.Exact f g) [Module.Finite k A] [Module.Finite k C] :
    finrank k B ≤ finrank k A + finrank k C := by
  have : Module.Finite k B := finite h
  rw [finrank_eq_range_add_range h]
  exact add_le_add f.finrank_range_le (Submodule.finrank_le _)
end GlobalTheory.ExactSeq
