-- Prove2me | solution 1 for GlobalTheory.PartialZetaSum.norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:22:53.684962+00:00
-- url     : https://prove2.me/submissions/6909e9d7-4433-45b7-a61f-c4829aeec9e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumAbsNormCpowUnitClassesPartialZeta

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
open GlobalTheory GlobalTheory.PartialZetaSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.PartialZetaSum
theorem _root_.solution (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    |((Algebra.norm ℚ b.1 : ℚ) : ℝ)| = (Ideal.absNorm (idealOf 𝔟 b) : ℝ) * nrm 𝔟 := by
  have h2 := congrArg FractionalIdeal.absNorm (span_eq 𝔟 b)
  rw [FractionalIdeal.absNorm_span_singleton, map_mul, FractionalIdeal.coeIdeal_absNorm] at h2
  unfold nrm
  rw [← Rat.cast_abs, h2]; push_cast; ring
end GlobalTheory.PartialZetaSum
