-- Prove2me | solution 1 for GlobalTheory.CoordScale.pi_smul_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:02:47.415957+00:00
-- url     : https://prove2.me/submissions/6a69dc27-0bd9-4426-8a48-e478c93f72e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreimageReindexScaleComplexLe
import Theorems.Thm_GlobalTheory_CoordScale_sigmaFinite_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoordScale
open MeasureTheory
namespace GlobalTheory.CoordScale
theorem _root_.solution {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ι → ENNReal) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  have : ∀ i, SigmaFinite (c i • μ i) := fun i => sigmaFinite_smul (μ i) (hc i)
  refine Measure.pi_eq (fun s hs => ?_)
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]
end GlobalTheory.CoordScale
