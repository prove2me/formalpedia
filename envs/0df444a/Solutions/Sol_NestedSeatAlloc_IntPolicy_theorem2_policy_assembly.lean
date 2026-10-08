-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem2_policy_assembly
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:40:11.829615+00:00
-- url     : https://prove2.me/submissions/1baa6600-e1d3-40cf-bf35-eb8609638908

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

set_option autoImplicit false

namespace NSA91910933

open NestedSeatAlloc.IntPolicy MeasureTheory ProbabilityTheory

/-- Deterministic demands: every class has demand `1/2`. -/
noncomputable def X0 : ℕ → Unit → ℝ := fun _ _ => 1 / 2

/-- Fares `f k = 2 - k`: `f 1 = 1`, `f 2 = 0`, `f 3 = -1`. -/
noncomputable def f0 : ℕ → ℝ := fun k => 2 - (k : ℝ)

/-- The expected revenue `min(s, 1/2)` of the first class. -/
noncomputable def G : ℝ → ℝ := fun s => if s < 1 / 2 then s else 1 / 2

lemma f0_two : f0 2 = 0 := by norm_num [f0]

lemma f0_three : f0 3 = -1 := by norm_num [f0]

lemma ER1 (q : ℕ → ℝ) : expRevenue (Measure.dirac ()) X0 f0 q 1 = G := by
  funext s
  unfold expRevenue
  rw [integral_dirac]
  simp only [revenue, X0, f0, G]
  norm_num

lemma ER2 (q : ℕ → ℝ) (hq : 1 ≤ q 1) : expRevenue (Measure.dirac ()) X0 f0 q 2 = G := by
  funext s
  unfold expRevenue
  rw [integral_dirac]
  have e1 : f0 1 = 1 := by norm_num [f0]
  have e2 : f0 2 = 0 := by norm_num [f0]
  simp only [revenue, X0, e1, e2, G, one_mul, mul_zero, zero_add]
  by_cases hs : s < q 1
  · rw [if_pos hs]
  · rw [if_neg hs]
    have hs2 : ¬ s < 1 / 2 := by linarith
    have hq2 : ¬ q 1 < 1 / 2 := by linarith
    rw [if_neg hs2, if_neg hq2]
    by_cases h3 : s < q 1 + 1 / 2
    · rw [if_pos h3]
    · rw [if_neg h3, if_neg (by linarith : ¬ s - 1 / 2 < 1 / 2)]

lemma G_deriv0 : HasDerivAt G 1 0 := by
  have h : G =ᶠ[nhds (0 : ℝ)] id := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    simp only [G, id]
    rw [if_pos (show s < 1 / 2 from hs)]
  exact (hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq h

lemma G_derivn (t : ℝ) (ht : 1 ≤ t) : HasDerivAt G 0 t := by
  have h : G =ᶠ[nhds t] fun _ => (1 / 2 : ℝ) := by
    filter_upwards [Ioi_mem_nhds (by linarith : (1 / 2 : ℝ) < t)] with s hs
    simp only [G]
    rw [if_neg (by simp only [Set.mem_Ioi] at hs; linarith)]
  exact (hasDerivAt_const t (1 / 2 : ℝ)).congr_of_eventuallyEq h

lemma G_right_nonneg (t : ℕ) (r : ℝ) (h : HasDerivWithinAt G r (Set.Ici (t : ℝ)) t) : 0 ≤ r := by
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0
    have h' : HasDerivWithinAt G 1 (Set.Ici ((0 : ℕ) : ℝ)) ((0 : ℕ) : ℝ) := by
      simpa using G_deriv0.hasDerivWithinAt (s := Set.Ici (0 : ℝ))
    have := (uniqueDiffWithinAt_Ici _).eq_deriv _ h h'
    linarith
  · have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast hpos
    have := (uniqueDiffWithinAt_Ici _).eq_deriv _ h (G_derivn _ ht).hasDerivWithinAt
    linarith

lemma no_policy (p : ℕ → ℕ)
    (h1 : InSubdiff (expRevenue (Measure.dirac ()) X0 f0 (fun i => (p i : ℝ)) 1) (p 1) (f0 2))
    (h2 : InSubdiff (expRevenue (Measure.dirac ()) X0 f0 (fun i => (p i : ℝ)) 2) (p 2) (f0 3)) :
    False := by
  rw [ER1] at h1
  obtain ⟨⟨r1, hr1, hr1c⟩, _⟩ := h1
  rw [f0_two] at hr1c
  rcases Nat.eq_zero_or_pos (p 1) with h0 | hpos
  · rw [h0, Nat.cast_zero] at hr1
    have := (uniqueDiffWithinAt_Ici _).eq_deriv _ hr1 G_deriv0.hasDerivWithinAt
    linarith
  · have hq : (1 : ℝ) ≤ (p 1 : ℝ) := by exact_mod_cast hpos
    rw [ER2 (fun i => (p i : ℝ)) hq] at h2
    obtain ⟨⟨r2, hr2, hr2c⟩, _⟩ := h2
    have := G_right_nonneg (p 2) r2 hr2
    rw [f0_three] at hr2c
    linarith

lemma indep0 : iIndepFun X0 (Measure.dirac ()) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  simp only [Measure.dirac_apply]
  by_cases h : ∀ i ∈ S, () ∈ X0 i ⁻¹' sets i
  · rw [Set.indicator_of_mem (Set.mem_iInter₂.2 h), Finset.prod_eq_one]
    · rfl
    · intro i hi
      rw [Set.indicator_of_mem (h i hi)]
      rfl
  · push Not at h
    obtain ⟨i, hi, hni⟩ := h
    rw [Set.indicator_of_notMem (fun hm => hni (Set.mem_iInter₂.1 hm i hi)),
      Finset.prod_eq_zero hi (Set.indicator_of_notMem hni _)]

lemma model0 : IsSeatModel (Measure.dirac ()) X0 f0 where
  isProb := inferInstance
  meas := fun _ => measurable_const
  indep := indep0
  nonneg := fun _ _ => by norm_num [X0]
  fare_strictAnti := fun k _ => by
    simp only [f0]
    push_cast
    linarith

lemma G_not_clbi : ¬ IsCLBI G := by
  rintro ⟨_, h⟩
  obtain ⟨a, b, hab⟩ := h 0
  have e0 := hab 0 (by norm_num)
  have e1 := hab (1 / 2) (by norm_num)
  have e2 := hab 1 (by norm_num)
  simp only [G] at e0 e1 e2
  norm_num at e0 e1 e2
  linarith

lemma hprefix0 : ∀ k (p : ℕ → ℕ), 1 ≤ k →
      (∀ j, 1 ≤ j → j ≤ k →
        InSubdiff (expRevenue (Measure.dirac ()) X0 f0 (fun i => (p i : ℝ)) j) (p j) (f0 (j + 1))) →
      IsCLBI (expRevenue (Measure.dirac ()) X0 f0 (fun i => (p i : ℝ)) k) →
      ∃ n : ℕ, ∀ j, 1 ≤ j → j ≤ k + 1 →
        InSubdiff (expRevenue (Measure.dirac ()) X0 f0 (fun i =>
          if i = k + 1 then (n : ℝ) else (p i : ℝ)) j)
          (if j = k + 1 then n else p j) (f0 (j + 1)) := by
  intro k p hk hpre hclbi
  exfalso
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    rw [ER1] at hclbi
    exact G_not_clbi hclbi
  · exact no_policy p (hpre 1 le_rfl (by omega)) (hpre 2 (by norm_num) hk2)

lemma hbase0 : ∃ n : ℕ,
    InSubdiff (expRevenue (Measure.dirac ()) X0 f0 (fun i => (n : ℝ)) 1) n (f0 2) := by
  refine ⟨1, ?_⟩
  rw [ER1, f0_two, Nat.cast_one]
  exact ⟨⟨0, (G_derivn 1 le_rfl).hasDerivWithinAt, le_rfl⟩,
    Or.inr ⟨0, (G_derivn 1 le_rfl).hasDerivWithinAt, le_rfl⟩⟩

end NSA91910933

open NestedSeatAlloc.IntPolicy MeasureTheory ProbabilityTheory in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hprefix : ∀ k (p : ℕ → ℕ), 1 ≤ k →
      (∀ j, 1 ≤ j → j ≤ k →
        InSubdiff (expRevenue P X f (fun i => (p i : ℝ)) j) (p j) (f (j + 1))) →
      IsCLBI (expRevenue P X f (fun i => (p i : ℝ)) k) →
      ∃ n : ℕ, ∀ j, 1 ≤ j → j ≤ k + 1 →
        InSubdiff (expRevenue P X f (fun i =>
          if i = k + 1 then (n : ℝ) else (p i : ℝ)) j)
          (if j = k + 1 then n else p j) (f (j + 1)))
    (hbase : ∃ n : ℕ,
      InSubdiff (expRevenue P X f (fun i => (n : ℝ)) 1) n (f 2)),
    ∃ p : ℕ → ℕ, SubdiffCondition P X f (fun k => (p k : ℝ))) := by
  intro H
  obtain ⟨p, hp⟩ := @H Unit _ (Measure.dirac ()) NSA91910933.X0 NSA91910933.f0
    NSA91910933.model0 NSA91910933.hprefix0 NSA91910933.hbase0
  exact NSA91910933.no_policy p (hp 1 le_rfl) (hp 2 (by norm_num))
