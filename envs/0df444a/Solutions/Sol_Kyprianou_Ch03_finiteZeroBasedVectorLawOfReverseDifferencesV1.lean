-- Prove2me | solution 1 for Kyprianou.Ch03.finiteZeroBasedVectorLawOfReverseDifferencesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T09:44:49.056243+00:00
-- url     : https://prove2.me/submissions/60bca0d8-0a84-4532-8dc2-2a1b754c2218

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (n : Nat)
    (F G : Omega → Fin (n + 1) → Real)
    (hF : AEMeasurable F P) (hG : AEMeasurable G P)
    (hF0 : ∀ ω, F ω 0 = 0) (hG0 : ∀ ω, G ω 0 = 0)
    (hLaw : P.map (fun ω : Omega => fun i : Fin n =>
      F ω i.castSucc - F ω i.succ) =
      P.map (fun ω : Omega => fun i : Fin n =>
        G ω i.castSucc - G ω i.succ)) :
    P.map F = P.map G := by
  classical
  let D (v : Fin (n + 1) → ℝ) (i : Fin n) := v i.castSucc - v i.succ
  let R (v : Fin n → ℝ) (j : Fin (n + 1)) :=
    - ∑ k ∈ Finset.range j.val, (if h : k < n then v ⟨k, h⟩ else 0)
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro j
    apply Measurable.neg
    refine Finset.measurable_sum _ fun k _ => ?_
    by_cases hk : k < n
    · simpa only [dif_pos hk] using (measurable_pi_apply (⟨k, hk⟩ : Fin n))
    · simp only [dif_neg hk]
      exact measurable_const
  have hD : Measurable D :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i.castSucc).sub
      (measurable_pi_apply i.succ)
  have key (v : Fin (n + 1) → ℝ) (hv : v 0 = 0) : R (D v) = v := by
    funext j
    let a (k : ℕ) := if h : k < n + 1 then v ⟨k, h⟩ else 0
    have h0 : a 0 = 0 := by simp [a, hv]
    have hj : a j.val = v j := by simp only [a, dif_pos j.isLt]
    have ht (m : ℕ) : ∑ k ∈ Finset.range m, (a k - a (k + 1)) = a 0 - a m := by
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    unfold R
    rw [show (∑ k ∈ Finset.range j.val,
        (if h : k < n then D v ⟨k, h⟩ else 0)) =
        ∑ k ∈ Finset.range j.val, (a k - a (k + 1)) from by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k < n := by have := Finset.mem_range.mp hk; omega
      have hks : k + 1 < n + 1 := by omega
      have hkc : k < n + 1 := by omega
      simp only [D, a, dif_pos hkn, dif_pos hks, dif_pos hkc]
      rfl]
    rw [ht, h0, hj]
    ring
  have eF : R ∘ (D ∘ F) = F := funext fun ω => key (F ω) (hF0 ω)
  have eG : R ∘ (D ∘ G) = G := funext fun ω => key (G ω) (hG0 ω)
  change P.map (D ∘ F) = P.map (D ∘ G) at hLaw
  have hmF := hD.comp_aemeasurable hF
  have hmG := hD.comp_aemeasurable hG
  have h := congrArg (Measure.map R) hLaw
  rw [AEMeasurable.map_map_of_aemeasurable hR.aemeasurable hmF,
      AEMeasurable.map_map_of_aemeasurable hR.aemeasurable hmG, eF, eG] at h
  exact h
