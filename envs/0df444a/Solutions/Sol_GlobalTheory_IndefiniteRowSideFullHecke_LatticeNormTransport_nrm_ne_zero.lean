-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.nrm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:40:22.710685+00:00
-- url     : https://prove2.me/submissions/71bee492-436c-4016-be23-d62672ecb0dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
theorem _root_.solution {K : Type} [Field K] [NumberField K] (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  unfold nrm
  have : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := fun h =>
    𝔞.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast this
end GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
