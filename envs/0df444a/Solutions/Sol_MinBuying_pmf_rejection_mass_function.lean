-- Prove2me | solution 1 for MinBuying.pmf_rejection_mass_function
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:06:56.818515+00:00
-- url     : https://prove2.me/submissions/7f3db947-024c-44c7-a1fc-e61bdc96d0e4

import Theorems.Thm_MinBuying_pmf_affiliated_marginal

open MeasureTheory Set MinBuying
open scoped BigOperators ENNReal
noncomputable section

namespace MinBuyingPMFMassConditioningProof

private lemma filter_toMeasure {α : Type*} [MeasurableSpace α] (w : PMF α)
    (B : Set α) (hB : MeasurableSet B) (h : ∃ v ∈ B, v ∈ w.support) :
    (w.filter B h).toMeasure = ProbabilityTheory.cond w.toMeasure B := by
  classical
  ext T hT
  rw [PMF.toMeasure_apply _ hT,ProbabilityTheory.cond_apply' hT,
    PMF.toMeasure_apply _ hB,PMF.toMeasure_apply _ (hB.inter hT)]
  have hi : T.indicator (w.filter B h) = fun v =>
      (B ∩ T).indicator w v * (∑' u,B.indicator w u)⁻¹ := by
    funext v
    by_cases hvB : v ∈ B <;> by_cases hvT : v ∈ T <;> simp [PMF.filter_apply,hvB,hvT]
  rw [hi,ENNReal.tsum_mul_right,mul_comm]

private lemma mtp2_restrict (n : ℕ) (f : Valuations (n+1) → ℝ)
    (hf : ∀ v,0 ≤ f v) (hmtp : MTP2 f) (a : ℝ) :
    MTP2 (fun v => if v 0 < a then f v else 0) := by
  intro v w
  by_cases hv : v 0 < a
  · by_cases hw : w 0 < a
    · have hmax : max (v 0) (w 0) < a := max_lt hv hw
      have hmin : min (v 0) (w 0) < a := (min_le_left _ _).trans_lt hv
      simpa only [hv,hw,hmax,hmin,if_true] using hmtp v w
    · simp only [hw,if_false,mul_zero]
      apply mul_nonneg <;> split_ifs <;> first | exact hf _ | exact le_rfl
  · simp only [hv,if_false,zero_mul]
    apply mul_nonneg <;> split_ifs <;> first | exact hf _ | exact le_rfl

private lemma mtp2_scale {n : ℕ} (f : Valuations n → ℝ) (hmtp : MTP2 f) (c : ℝ) :
    MTP2 (fun v => c*f v) := by
  intro v w
  have h := mul_le_mul_of_nonneg_left (hmtp v w) (sq_nonneg c)
  calc
    (c*f v)*(c*f w) = c^2*(f v*f w) := by ring
    _ ≤ c^2*(f (fun i => max (v i) (w i))*f (fun i => min (v i) (w i))) := h
    _ = (c*f (fun i => max (v i) (w i)))*(c*f (fun i => min (v i) (w i))) := by ring

private lemma filter_mtp2 (n : ℕ) (w : PMF (Valuations (n+1)))
    (hmtp : MTP2 (fun v => (w v).toReal)) (a : ℝ)
    (h : ∃ v ∈ {v : Valuations (n+1) | v 0 < a}, v ∈ w.support) :
    MTP2 (fun v => ((w.filter {v : Valuations (n+1) | v 0 < a} h) v).toReal) := by
  classical
  let B : Set (Valuations (n+1)) := {v | v 0 < a}
  have hid : (fun v => ((w.filter B h) v).toReal) =
      fun v => ((∑' u, B.indicator w u)⁻¹).toReal *
        (if v 0 < a then (w v).toReal else 0) := by
    funext v
    rw [PMF.filter_apply,ENNReal.toReal_mul]
    by_cases hv : v 0 < a <;> simp [B,hv,mul_comm]
  rw [hid]
  exact mtp2_scale _ (mtp2_restrict n _ (fun _ => ENNReal.toReal_nonneg) hmtp a) _

end MinBuyingPMFMassConditioningProof

theorem solution (n : ℕ) (w : PMF (Valuations (n+1)))
    (hmtp : MTP2 (fun v => (w v).toReal)) (a : ℝ)
    (hB : 0 < w.toMeasure {v : Valuations (n+1) | v 0 < a}) :
    ∃ z : PMF (Valuations n),
      Measure.map (fun v : Valuations (n+1) => fun i : Fin n => v i.succ)
        (ProbabilityTheory.cond w.toMeasure {v : Valuations (n+1) | v 0 < a}) = z.toMeasure ∧
      MTP2 (fun v => (z v).toReal) := by
  classical
  let B : Set (Valuations (n+1)) := {v | v 0 < a}
  have hmB : MeasurableSet B := measurableSet_lt (measurable_pi_apply 0) measurable_const
  have hex : ∃ v ∈ B, v ∈ w.support := by
    by_contra h
    have hz : w.toMeasure B = 0 := (w.toMeasure_apply_eq_zero_iff hmB).mpr
      (Set.disjoint_left.mpr (fun v hv hB => h ⟨v,hB,hv⟩))
    exact ne_of_gt hB hz
  let wf := w.filter B hex
  have hmeasure : wf.toMeasure = ProbabilityTheory.cond w.toMeasure B :=
    MinBuyingPMFMassConditioningProof.filter_toMeasure w B hmB hex
  have hfil : MTP2 (fun v => (wf v).toReal) :=
    MinBuyingPMFMassConditioningProof.filter_mtp2 n w hmtp a hex
  have htail : Measurable (fun v : Valuations (n+1) => fun i : Fin n => v i.succ) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)
  refine ⟨wf.map (fun v : Valuations (n+1) => fun i : Fin n => v i.succ),?_,
    pmf_affiliated_marginal n wf hfil⟩
  rw [← PMF.toMeasure_map _ wf htail,hmeasure]
