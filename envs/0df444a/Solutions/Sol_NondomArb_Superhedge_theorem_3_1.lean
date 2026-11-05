-- Prove2me | solution 1 for NondomArb.Superhedge.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:03:51.841255+00:00
-- url     : https://prove2.me/submissions/85e8f364-28a4-4ca6-8412-fbd28e4940b7

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_OnePeriod
import Theorems.Thm_NondomArb_Superhedge_lemma_3_3
open MeasureTheory Filter Topology NondomArb.Superhedge.OnePeriod
open NondomArb.Superhedge

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS) :
    NA Pset ΔS ↔ ∀ P ∈ Pset, ∃ Q ∈ MartMeasures Pset ΔS, P ≪ Q := by
  constructor
  · intro hNA P hP0
    have h := (lemma_3_3 Pset hP ΔS hΔS hNA (fun _ => (0:ℝ)) measurable_const).2 P hP0
    obtain ⟨R, hR, hPR, hzero⟩ := intrinsicInterior_subset h
    obtain ⟨hprob, hac, hfin⟩ := hR
    have hint : Integrable ΔS R := by
      refine ⟨hΔS.aestronglyMeasurable, lt_of_le_of_lt (lintegral_mono fun ω => ?_) hfin⟩
      rw [← ofReal_norm]
      simp
    exact ⟨R, ⟨hprob, hac, hint, hzero.symm⟩, hPR⟩
  · intro h H hge
    set A := {ω | H ⬝ᵥ ΔS ω ≠ 0} with hA
    have hdot : Measurable fun ω => H ⬝ᵥ ΔS ω := by
      show Measurable fun ω => ∑ i, H i * ΔS ω i
      exact Finset.measurable_sum _ fun i _ =>
        measurable_const.mul ((measurable_pi_apply i).comp hΔS)
    have hAm : MeasurableSet A := (measurableSet_eq_fun hdot measurable_const).compl
    refine ⟨A, hAm, fun ω hω => hω, fun P hP0 => ?_⟩
    obtain ⟨Q, ⟨hprob, ⟨P', hP', hQP'⟩, hint, hzero⟩, hPQ⟩ := h P hP0
    obtain ⟨B, _, hsub, h0⟩ := hge
    have hQge : 0 ≤ᵐ[Q] fun ω => H ⬝ᵥ ΔS ω :=
      measure_mono_null (fun ω hω => hsub hω) (hQP' (h0 P' hP'))
    have hcomp : ∀ i, Integrable (fun ω => ΔS ω i) Q := fun i => hint.eval i
    have hdi : Integrable (fun ω => H ⬝ᵥ ΔS ω) Q := by
      show Integrable (fun ω => ∑ i, H i * ΔS ω i) Q
      exact integrable_finsetSum _ fun i _ => (hcomp i).const_mul (H i)
    have hE : ∫ ω, H ⬝ᵥ ΔS ω ∂Q = 0 := by
      show ∫ ω, ∑ i, H i * ΔS ω i ∂Q = 0
      rw [integral_finsetSum _ fun i _ => (hcomp i).const_mul (H i)]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_const_mul, ← eval_integral hcomp i, hzero]
      simp
    have hae := (integral_eq_zero_iff_of_nonneg_ae hQge hdi).mp hE
    exact hPQ (ae_iff.mp hae)
