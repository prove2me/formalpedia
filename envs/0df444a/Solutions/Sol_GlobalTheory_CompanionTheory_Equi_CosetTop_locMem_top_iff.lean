-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetTop.locMem_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:49.022285+00:00
-- url     : https://prove2.me/submissions/d1b4bd77-c4ee-45a6-b5b3-9c449be10d45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetUnitIdealIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetTop
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Equi.CosetTop
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    LocMem (⊤ : Ideal (𝓞 F)) v z ↔ v.valuation F z ≤ 1 := by
  constructor
  · rintro ⟨s, hs, y, -, h⟩
    have h1 : v.valuation F (s : F) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 : v.valuation F (s : F) * v.valuation F z = v.valuation F (y : F) := by
      rw [← map_mul, h]
    rw [h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one v y
  · intro hz
    have hmem : z ∈ HeightOneSpectrum.valuationSubringAtPrime F v := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hz
    obtain ⟨a, s, hs, h⟩ := hmem
    refine ⟨s, hs, a, Submodule.mem_top, ?_⟩
    have hs0 : (s : F) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := RingOfIntegers.coe_injective (by simpa using h0)
      rw [this]
      exact v.asIdeal.zero_mem
    rw [h]
    change (s : F) * ((a : F) * (s : F)⁻¹) = a
    field_simp
end GlobalTheory.CompanionTheory.Equi.CosetTop
