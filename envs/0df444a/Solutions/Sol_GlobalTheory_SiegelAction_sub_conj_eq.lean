-- Prove2me | solution 1 for GlobalTheory.SiegelAction.sub_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:15.480949+00:00
-- url     : https://prove2.me/submissions/393ea685-d051-4a31-8b63-527c8e45ecac

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
omit [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SiegelAction
theorem _root_.solution (τ : Matrix ι ι ℂ) :
    τ - τ.map conj = (2 * I) • τ.map (fun z => (z.im : ℂ)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Complex.sub_conj]
  push_cast
  ring
end GlobalTheory.SiegelAction
