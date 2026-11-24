-- Prove2me | solution 1 for GlobalTheory.ChartRing.algebraMap_injective_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:12:10.054041+00:00
-- url     : https://prove2.me/submissions/6ae57ac8-3341-41e2-a642-1d524396ffe1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
open AlgebraicGeometry
universe u
variable {R : Type*} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0)
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away f S]
include hf
namespace GlobalTheory.ChartRing
theorem _root_.solution : Function.Injective (algebraMap R S) :=
  IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
end GlobalTheory.ChartRing
