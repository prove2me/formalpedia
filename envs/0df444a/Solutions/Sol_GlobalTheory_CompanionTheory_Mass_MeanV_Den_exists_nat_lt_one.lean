-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.Den.exists_nat_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:43.136242+00:00
-- url     : https://prove2.me/submissions/f0ad4520-ffe1-4db2-96f6-abd8b85b348f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV GlobalTheory.CompanionTheory.Mass.MeanV.Den
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Mass.MeanV.Den
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ v.valuation F (p : F) < 1 := by
  refine ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h), ?_⟩
  have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  have h : (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F) = ((Ideal.absNorm v.asIdeal : ℕ) : F) := by simp
  rw [← h]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hm
end GlobalTheory.CompanionTheory.Mass.MeanV.Den
