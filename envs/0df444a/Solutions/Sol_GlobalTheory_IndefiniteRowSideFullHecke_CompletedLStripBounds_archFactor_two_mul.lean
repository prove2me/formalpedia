-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:58.191403+00:00
-- url     : https://prove2.me/submissions/0929a03e-2da9-4829-8ea6-9cd765690936

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
theorem _root_.solution (m : I → ℤ) (s : ℂ) : archFactor (fun i => 2 * m i) s = LInf m s := by
  unfold archFactor LInf
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (((|2 * m i| : ℤ) : ℂ)) / 2 = ((|m i| : ℤ) : ℂ) := by
    rw [abs_mul, abs_two]; push_cast; ring
  rw [this]
end GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
