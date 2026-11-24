-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.continuous_jQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:26:41.15984+00:00
-- url     : https://prove2.me/submissions/5edd549b-5435-4cc7-bbdb-bb0688b99b9f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_continuous_jG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (A : Ad E R) (ε : ℤˣ) (h : ∀ x, A.σ (A.σ x) = x) (hσ : Continuous A.σ) :
    Continuous (jQ A ε h (ι := ι)) :=
  Continuous.subtype_mk (Continuous.subtype_mk (continuous_jG A.σ hσ) _) _
end GlobalTheory.CompanionTheory.RgEisLevi
