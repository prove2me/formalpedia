-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.NullV.card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:23:14.350248+00:00
-- url     : https://prove2.me/submissions/edc9af92-b8a7-4b46-842a-fa182c05ca32

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.NullV
namespace GlobalTheory.CompanionTheory.SW.NullV
theorem _root_.solution {K : Type} [Field K] (a b q : K) (hq : q ≠ 0) (r : ℕ → K)
    (hr : Function.Injective r) (s : Finset ℕ)
    (h : ∀ i ∈ s, a + r i * b + r i ^ 2 * q = 0) : s.card ≤ 2 := by
  by_contra hc
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.1 (not_le.1 hc)
  have h1 := h i hi
  have h2 := h j hj
  have h3 := h k hk
  have e12 : (r i - r j) * (b + (r i + r j) * q) = 0 := by linear_combination h1 - h2
  have e13 : (r i - r k) * (b + (r i + r k) * q) = 0 := by linear_combination h1 - h3
  have f12 := (mul_eq_zero.1 e12).resolve_left (sub_ne_zero.2 fun e => hij (hr e))
  have f13 := (mul_eq_zero.1 e13).resolve_left (sub_ne_zero.2 fun e => hik (hr e))
  have g : (r j - r k) * q = 0 := by linear_combination f12 - f13
  exact (mul_ne_zero (sub_ne_zero.2 fun e => hjk (hr e)) hq) g
end GlobalTheory.CompanionTheory.SW.NullV
