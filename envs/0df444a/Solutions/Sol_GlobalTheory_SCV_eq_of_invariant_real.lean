-- Prove2me | solution 1 for GlobalTheory.SCV.eq_of_invariant_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:21:19.314002+00:00
-- url     : https://prove2.me/submissions/279d06f1-6b4b-4842-8a58-7a016c05ffed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Theorems.Thm_GlobalTheory_SCV_eq_of_invariant_realSubspace
import Theorems.Thm_GlobalTheory_SCV_span_scaledRealPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology
open GlobalTheory GlobalTheory.SCV
variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.SCV
theorem _root_.solution {f : (ι → ℂ) → V} {U : Set (ι → ℂ)}
    (hU : IsOpen U) (hU' : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ x : ι → ℝ, (z + fun i => (x i : ℂ)) ∈ U → f (z + fun i => (x i : ℂ)) = f z)
    {z w : ι → ℂ} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_invariant_realSubspace (span_scaledRealPoints one_ne_zero) hU hU' hf ?_ hz hw
  rintro y hy _ ⟨x, rfl⟩
  simpa only [one_mul] using h y hy x
end GlobalTheory.SCV
