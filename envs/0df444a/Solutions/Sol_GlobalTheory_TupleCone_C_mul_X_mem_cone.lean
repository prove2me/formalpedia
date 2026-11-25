-- Prove2me | solution 1 for GlobalTheory.TupleCone.C_mul_X_mem_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:39.607214+00:00
-- url     : https://prove2.me/submissions/c48a67f2-776c-49dd-b14f-eb352df72e66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}
namespace GlobalTheory.TupleCone
theorem _root_.solution (s : σ) : C (t s) * X ∈ cone o t := Algebra.subset_adjoin ⟨s, rfl⟩
end GlobalTheory.TupleCone
