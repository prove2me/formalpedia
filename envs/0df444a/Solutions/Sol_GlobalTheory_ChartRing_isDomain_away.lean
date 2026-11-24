-- Prove2me | solution 1 for GlobalTheory.ChartRing.isDomain_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:12:11.014084+00:00
-- url     : https://prove2.me/submissions/214118d4-8ddd-497c-b6f3-1ce1c7767a8d

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
theorem _root_.solution : IsDomain S :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) S
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
end GlobalTheory.ChartRing
