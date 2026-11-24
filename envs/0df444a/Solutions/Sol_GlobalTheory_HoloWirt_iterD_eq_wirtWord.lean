-- Prove2me | solution 1 for GlobalTheory.HoloWirt.iterD_eq_wirtWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:28:41.386083+00:00
-- url     : https://prove2.me/submissions/18333d54-07c0-4db8-bb5a-940bfdf7923a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedComplexPartialDerivativeEqWirtingerWord
import Theorems.Thm_GlobalTheory_HoloWirt_iterD_holo_and_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.HoloWirt
namespace GlobalTheory.HoloWirt
theorem _root_.solution : ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ g U → ∀ (l : List I), ∀ z ∈ U,
      iterD l g z = wirtWord (l.map fun i => (i, false)) g z := by
  intro I _ _ U g hU hg l z hz
  exact (iterD_holo_and_eq U g hU hg l).2 hz
end GlobalTheory.HoloWirt
