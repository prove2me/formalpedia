-- Prove2me | solution 1 for GlobalTheory.ChartRing.denseRange_comap_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:27:58.869804+00:00
-- url     : https://prove2.me/submissions/ac159a3d-f858-49d7-a62f-4429a28b589f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
import Theorems.Thm_GlobalTheory_ChartRing_algebraMap_injective_away

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
theorem _root_.solution : DenseRange (PrimeSpectrum.comap (algebraMap R S)) := by
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap_injective_away hf S)]
  exact bot_le
end GlobalTheory.ChartRing
