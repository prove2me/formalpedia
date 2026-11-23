-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.LatSum.absSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:35.431813+00:00
-- url     : https://prove2.me/submissions/245cd35f-8bfc-4ff9-86c1-f73e90801ae4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum

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
namespace GlobalTheory.HeckeTwo.LatSum
theorem _root_.solution (x : F) : 0 ≤ absSum x := Finset.sum_nonneg fun _ _ => abs_nonneg _
end GlobalTheory.HeckeTwo.LatSum
