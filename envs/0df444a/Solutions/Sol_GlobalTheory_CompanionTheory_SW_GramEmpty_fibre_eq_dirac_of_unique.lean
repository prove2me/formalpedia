-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_eq_dirac_of_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:21:20.826956+00:00
-- url     : https://prove2.me/submissions/4844bce4-f0c6-4efd-a3ee-1134386b15c1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankZeroGramFiberMeasure

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramEmpty
namespace GlobalTheory.CompanionTheory.SW.GramEmpty
theorem _root_.solution {V X : Type} [MeasurableSpace V] [MeasurableSpace X] [Subsingleton V]
    [Subsingleton X] (μ : Measure V) (ν : Measure X) (m : X → Measure V) (x₀ : V)
    (hμ : μ Set.univ = 1) (hν : ν Set.univ = 1)
    (h : ∀ φ : V → ℝ≥0∞, Measurable φ → ∫⁻ v, φ v ∂μ = ∫⁻ b, ∫⁻ v, φ v ∂(m b) ∂ν) (S : X) :
    m S = Measure.dirac x₀ := by
  have h1 := h (fun _ => 1) measurable_const
  have hc : (fun b => ∫⁻ _, (1 : ℝ≥0∞) ∂(m b)) = fun _ => m S Set.univ := by
    funext b
    rw [Subsingleton.elim b S]
    simp
  rw [hc] at h1
  simp only [lintegral_const, one_mul, hμ, hν, mul_one] at h1
  ext s _
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · rw [Subsingleton.eq_univ_of_nonempty hs, ← h1]
    simp
end GlobalTheory.CompanionTheory.SW.GramEmpty
