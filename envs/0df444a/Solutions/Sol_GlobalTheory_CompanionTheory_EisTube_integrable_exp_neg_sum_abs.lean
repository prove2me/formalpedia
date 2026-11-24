-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.integrable_exp_neg_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:28.593678+00:00
-- url     : https://prove2.me/submissions/8d8f8897-724f-494d-88d4-4232d4dee218

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {ι : Type} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ι → ℝ => Real.exp (-(c * ∑ i, |t i|))) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-c * |x|)) := by
    have h1 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
    have h2 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Iic 0) :=
      (integrableOn_exp_mul_Iic hc 0).congr_fun (fun x hx => by rw [abs_of_nonpos hx, neg_mul_neg])
        measurableSet_Iic
    have h3 := h2.union h1
    rw [Set.Iic_union_Ioi, integrableOn_univ] at h3
    exact h3
  have hI : Integrable (fun t : ι → ℝ => ∏ i, Real.exp (-c * |t i|)) (Measure.pi fun _ => volume) :=
    Integrable.fintype_prod (f := fun _ x => Real.exp (-c * |x|)) fun _ => h1
  rw [volume_pi]
  refine hI.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [← Real.exp_sum, neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]
end GlobalTheory.CompanionTheory.EisTube
