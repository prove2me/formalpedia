-- Prove2me | solution 1 for GlobalTheory.SiegelAction.posDef_of_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:13.337617+00:00
-- url     : https://prove2.me/submissions/47508c39-e166-4702-b2cf-7acfc08b4f77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace GlobalTheory.SiegelAction
theorem _root_.solution {Y : Matrix ι ι ℝ} (h : (Y.map (fun t => (t : ℂ))).PosDef) :
    Y.PosDef := by
  have hH : Y.IsHermitian := by
    ext i j
    have := congrFun (congrFun h.isHermitian i) j
    simpa using this
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hv : (fun i => (x i : ℂ)) ≠ 0 := fun h0 => hx (by
    ext i
    simpa using congrFun h0 i)
  have := (Complex.pos_iff.1 (h.dotProduct_mulVec_pos hv)).1
  simpa [dotProduct, mulVec, Finset.mul_sum] using this
end GlobalTheory.SiegelAction
