-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.LatSum.absSum_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:54.746813+00:00
-- url     : https://prove2.me/submissions/f8ac211e-3761-4db6-9a86-5a4eaa07a65b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum
import Theorems.Thm_GlobalTheory_HeckeTwo_LatSum_norm_mixedEmbedding_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.LatSum
variable {F : Type} [Field F] [NumberField F]
variable [IsTotallyReal F]
open scoped Classical
namespace GlobalTheory.HeckeTwo.LatSum
theorem _root_.solution {x : F} (hx : x ≠ 0) : 0 < absSum x := by
  have h : 0 < ‖mixedEmbedding F x‖ := norm_pos_iff.2 fun h =>
    hx ((mixedEmbedding F).injective (h.trans (map_zero _).symm))
  exact h.trans_le (norm_mixedEmbedding_le x)
end GlobalTheory.HeckeTwo.LatSum
