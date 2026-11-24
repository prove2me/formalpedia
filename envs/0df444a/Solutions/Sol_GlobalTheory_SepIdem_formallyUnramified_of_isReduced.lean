-- Prove2me | solution 1 for GlobalTheory.SepIdem.formallyUnramified_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:34.852964+00:00
-- url     : https://prove2.me/submissions/cbd44d33-881c-4a1b-af55-d82c1679a43b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormallyUnramifiedOfIsReduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.SepIdem
namespace GlobalTheory.SepIdem
theorem _root_.solution (K A : Type) [Field K] [PerfectField K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [IsReduced A] : Algebra.FormallyUnramified K A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : Finite (MaximalSpectrum A) := inferInstance
  have h : Algebra.FormallyUnramified K (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) := by
    rw [Algebra.FormallyUnramified.pi_iff]
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyUnramified.of_isSeparable K _
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi A).restrictScalars K).symm
end GlobalTheory.SepIdem
