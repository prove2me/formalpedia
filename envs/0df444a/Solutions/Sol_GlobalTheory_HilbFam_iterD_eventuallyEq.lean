-- Prove2me | solution 1 for GlobalTheory.HilbFam.iterD_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:30:40.697856+00:00
-- url     : https://prove2.me/submissions/5a818bd4-85ca-4a04-ae17-465ac2538c99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IterDEqOfEventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution (I : Type) [Fintype I] [DecidableEq I] (u : List I)
    (f g : (I → ℂ) → ℂ) (z : I → ℂ) (h : f =ᶠ[nhds z] g) :
    iterD u f =ᶠ[nhds z] iterD u g := by
  induction u with
  | nil => exact h
  | cons i u ih =>
    have h2 := ih.eventuallyEq_nhds
    filter_upwards [h2] with w hw
    exact Filter.EventuallyEq.lineDeriv_eq hw
end GlobalTheory.HilbFam
