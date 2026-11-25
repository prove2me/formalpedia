-- Prove2me | solution 1 for GlobalTheory.SharpGradient.normSq_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:07:16.32777+00:00
-- url     : https://prove2.me/submissions/5b320f7a-24e2-4f91-8242-3f1c6650d648

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {n : ℕ}
namespace GlobalTheory.SharpGradient
theorem _root_.solution {ι : Type} [Fintype ι] (a : ι → ℂ) (s L : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hL : ∀ i, 0 ≤ L i) (h : ∀ i, Complex.normSq (a i) ≤ s i * L i) :
    Complex.normSq (∑ i, a i) ≤ (∑ i, s i) * ∑ i, L i := by
  rw [Complex.normSq_eq_norm_sq]
  have h1 : ‖∑ i, a i‖ ≤ ∑ i, ‖a i‖ := norm_sum_le _ _
  have h2 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
    (r := fun i => ‖a i‖) (f := s) (g := L) (fun i _ => hs i) (fun i _ => hL i)
    (fun i _ => by rw [← Complex.normSq_eq_norm_sq]; exact h i)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
end GlobalTheory.SharpGradient
