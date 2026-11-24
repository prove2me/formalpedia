-- Prove2me | solution 1 for GlobalTheory.ChartRing.continuous_adicTopology_of_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:48.131844+00:00
-- url     : https://prove2.me/submissions/1542028a-66d5-4a22-a238-2e9c302e42d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff

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
variable {A : Type*} [CommRing A] (I : Ideal A)
namespace GlobalTheory.ChartRing
theorem _root_.solution {S : Type*} [CommRing S] (J : Ideal S) (φ : A →+* S)
    (h : I.map φ ≤ J) : @Continuous A S I.adicTopology J.adicTopology φ := by
  letI : WithIdeal A := ⟨I⟩
  letI : WithIdeal S := ⟨J⟩
  exact (WithIdeal.uniformContinuous_of_map_le (f := φ) h).continuous
end GlobalTheory.ChartRing
