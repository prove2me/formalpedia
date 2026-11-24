-- Prove2me | solution 1 for GlobalTheory.setIntegral_comp_add_of_lattice_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:42.209052+00:00
-- url     : https://prove2.me/submissions/fd717638-155b-4e46-b527-d97ab5876d24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open MeasureTheory Module
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution [SecondCountableTopology E]
    (L : Submodule ℤ E) [Countable L] {D : Set E}
    (hD : IsAddFundamentalDomain L D μ) {F : E → ℂ} (hF : ∀ (l : L) z, F (z + l) = F z) (c : E) :
    ∫ z in D, F (z + c) ∂μ = ∫ z in D, F z ∂μ := by
  have : VAddInvariantMeasure L E μ := ⟨fun g s _ => measure_preimage_add μ (g : E) s⟩
  have hpres := measurePreserving_add_right μ c
  have hD' : IsAddFundamentalDomain L ((fun x => x + c) '' D) μ :=
    hD.image_of_equiv (Equiv.addRight c)
      (measurePreserving_add_right μ (-c)).quasiMeasurePreserving (Equiv.refl _)
      (fun g x => add_assoc _ _ _)
  rw [← hpres.setIntegral_image_emb (MeasurableEquiv.addRight c).measurableEmbedding]
  refine (hD'.setIntegral_eq hD fun g x => ?_)
  show F ((g : E) + x) = F x
  rw [add_comm]
  exact hF g x
end GlobalTheory
