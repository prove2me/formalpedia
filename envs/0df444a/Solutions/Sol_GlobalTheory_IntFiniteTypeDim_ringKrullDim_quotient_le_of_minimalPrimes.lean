-- Prove2me | solution 1 for GlobalTheory.IntFiniteTypeDim.ringKrullDim_quotient_le_of_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:17:42.429153+00:00
-- url     : https://prove2.me/submissions/c7877aba-c141-4fc7-9226-c419770df967

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimQuotientMinimalPrimeOverL
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimQuotientLeOfMinimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntFiniteTypeDim
namespace GlobalTheory.IntFiniteTypeDim
theorem _root_.solution {A : Type} [CommRing A] (I : Ideal A)
    (c : WithBot ℕ∞) (h : ∀ P ∈ I.minimalPrimes, ringKrullDim (A ⧸ P) ≤ c) :
    ringKrullDim (A ⧸ I) ≤ c := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun s => ?_
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := s.head.1.asIdeal) s.head.2
  refine le_trans ?_ (h P hP)
  rw [ringKrullDim_quotient]
  let t : LTSeries (PrimeSpectrum.zeroLocus (R := A) P) :=
    ⟨s.length, fun i => ⟨(s i).1, hle.trans (show s.head.1 ≤ (s i).1 from s.head_le i)⟩,
      fun i => s.step i⟩
  exact Order.LTSeries.length_le_krullDim t
end GlobalTheory.IntFiniteTypeDim
