-- Prove2me | solution 1 for GlobalTheory.integrable_of_lattice_translate_dominated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:27.219137+00:00
-- url     : https://prove2.me/submissions/4960e266-8595-4188-85a2-5946f7c48728

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_isAddFundamentalDomain_latticeCell
import Theorems.Thm_GlobalTheory_isBounded_latticeCell
import Theorems.Thm_GlobalTheory_measurableSet_latticeCell
import Theorems.Thm_GlobalTheory_volume_latticeCell_lt_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real FourierTransform
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
omit [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x) :
    Integrable f := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  obtain ⟨R, hR⟩ := (isBounded_latticeCell L).exists_norm_le
  obtain ⟨g, hg, h⟩ := hdom R
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm,
    (isAddFundamentalDomain_latticeCell L volume).lintegral_eq_tsum'']
  calc ∑' x : L, ∫⁻ u in latticeCell L, ‖f (x +ᵥ u)‖ₑ
      ≤ ∑' x : L, ENNReal.ofReal (g x) * volume (latticeCell L) := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        rw [← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_latticeCell L) fun u hu ↦ ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (h x u (hR u hu))
    _ < ⊤ := by
        rw [ENNReal.tsum_mul_right]
        exact ENNReal.mul_lt_top hg.tsum_ofReal_lt_top (volume_latticeCell_lt_top L)
end GlobalTheory
