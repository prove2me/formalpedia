-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_eq_covolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:39:53.1148+00:00
-- url     : https://prove2.me/submissions/38a42238-01a1-4744-8f71-10363fd27009

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
open NumberField nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
open Classical
namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
theorem _root_.solution [IsTotallyReal F]
    (M : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol (M : FractionalIdeal (𝓞 F)⁰ F) =
      ZLattice.covolume (mixedEmbedding.idealLattice F M) := by
  rw [mixedEmbedding.covolume_idealLattice, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
    mul_one, mul_comm]
  rfl
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
