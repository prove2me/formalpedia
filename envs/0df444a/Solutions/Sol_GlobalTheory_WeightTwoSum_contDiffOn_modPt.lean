-- Prove2me | solution 1 for GlobalTheory.WeightTwoSum.contDiffOn_modPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:37.455215+00:00
-- url     : https://prove2.me/submissions/9ac55933-d7f0-4727-8f12-87672b79ae4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Theorems.Thm_GlobalTheory_WeightTwoSum_one_add_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff
open GlobalTheory GlobalTheory.WeightTwoSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.WeightTwoSum
theorem _root_.solution {Φ : Type} [Fintype Φ] (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) :
    ContDiffOn ℂ ∞ (modPt φ e θ) (polydisc I) := by
  refine contDiffOn_pi.2 fun τ => ?_
  unfold modPt defCoord
  refine ContDiffOn.div ?_ ?_ fun z hz => one_add_ne_zero hz _
  · exact (contDiff_const.add ((contDiff_apply ℂ ℂ _).mul contDiff_const)).contDiffOn
  · exact (contDiff_const.add (contDiff_apply ℂ ℂ _)).contDiffOn
end GlobalTheory.WeightTwoSum
