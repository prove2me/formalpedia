-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.Tri.of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:26.464082+00:00
-- url     : https://prove2.me/submissions/7abc31e5-dcb7-451f-b5ec-b31e7c8260b2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
namespace Tri
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {S : Type} [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (h : Tri s (g.map f)) : Tri s g :=
  ⟨fun r hr i hi => hf (by rw [map_zero]; exact h.col r hr i hi),
    fun i hi c hc => hf (by rw [map_zero]; exact h.row i hi c hc)⟩
end Tri
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
