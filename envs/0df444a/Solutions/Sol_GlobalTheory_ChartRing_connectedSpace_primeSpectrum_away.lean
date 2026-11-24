-- Prove2me | solution 1 for GlobalTheory.ChartRing.connectedSpace_primeSpectrum_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:50:29.016397+00:00
-- url     : https://prove2.me/submissions/daeed88b-05d2-411d-a49b-ed8842c60fe7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
import Theorems.Thm_GlobalTheory_ChartRing_irreducibleSpace_primeSpectrum_away

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
theorem _root_.solution : ConnectedSpace (PrimeSpectrum S) :=
  have := irreducibleSpace_primeSpectrum_away hf S
  inferInstance
end GlobalTheory.ChartRing
