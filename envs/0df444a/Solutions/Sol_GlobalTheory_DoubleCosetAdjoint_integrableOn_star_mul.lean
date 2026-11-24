-- Prove2me | solution 1 for GlobalTheory.DoubleCosetAdjoint.integrableOn_star_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:25:01.824036+00:00
-- url     : https://prove2.me/submissions/dd1e7148-f4eb-4fdd-84ac-e4926ee181f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSumFundamentalDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.DoubleCosetAdjoint
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)
omit [Group H] [IsTopologicalGroup H] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
namespace GlobalTheory.DoubleCosetAdjoint
theorem _root_.solution (F F' : H → ℂ) (hF : Continuous F) (hF' : Continuous F')
    (h1 : IntegrableOn (fun h => star (F h) * F h) 𝓕 μ)
    (h2 : IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ) :
    IntegrableOn (fun h => star (F h) * F' h) 𝓕 μ := by
  refine Integrable.mono' (h1.norm.add h2.norm)
    (hF.star.mul hF').aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)
  simp only [Pi.add_apply, norm_mul, norm_star]
  nlinarith [sq_nonneg (‖F h‖ - ‖F' h‖), mul_nonneg (norm_nonneg (F h)) (norm_nonneg (F' h))]
end GlobalTheory.DoubleCosetAdjoint
