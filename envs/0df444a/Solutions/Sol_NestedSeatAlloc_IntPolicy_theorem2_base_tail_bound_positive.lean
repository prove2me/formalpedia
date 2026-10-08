-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem2_base_tail_bound_positive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:54:35.977934+00:00
-- url     : https://prove2.me/submissions/f8c5b4b3-066e-4a14-bae8-17fa20cddbf2

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

set_option autoImplicit false

namespace NestedSeatAlloc.IntPolicy.TailPos93

open MeasureTheory ProbabilityTheory Filter Topology

/-- Pointwise affine decomposition of the one-class revenue on `[N, N+1]` for integer demand. -/
lemma rev1_affine (f p x : ℕ → ℝ) (N : ℕ) (hx : ∃ n : ℕ, x 1 = n) (t : ℝ)
    (ht : t ∈ Set.Icc (N : ℝ) (N + 1)) :
    revenue f p x 1 t = revenue f p x 1 N +
      ({y : ℝ | (N : ℝ) + 1 ≤ y}.indicator (fun _ => (t - N) * f 1) (x 1)) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨h1, h2⟩ := ht
  simp only [revenue, Set.indicator, Set.mem_setOf_eq]
  rw [hn]
  rcases Nat.lt_or_ge N n with h | h
  · have hN1 : (N : ℝ) + 1 ≤ n := by exact_mod_cast h
    have hNn : (N : ℝ) < n := by linarith
    rw [if_pos hNn, if_pos hN1]
    by_cases htn : t < n
    · rw [if_pos htn]; ring
    · rw [if_neg htn]
      rw [show (n : ℝ) = N + 1 by linarith, show t = N + 1 by linarith]; ring
  · have hnN : (n : ℝ) ≤ N := by exact_mod_cast h
    have h3 : ¬ t < n := by linarith
    have h4 : ¬ (N : ℝ) < n := by linarith
    have h5 : ¬ (N : ℝ) + 1 ≤ n := by linarith
    rw [if_neg h3, if_neg h4, if_neg h5]; ring

end NestedSeatAlloc.IntPolicy.TailPos93

open NestedSeatAlloc.IntPolicy.TailPos93 in
open MeasureTheory ProbabilityTheory Filter Topology in
theorem NestedSeatAlloc.IntPolicy.TailPos93.main {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : NestedSeatAlloc.IntPolicy.IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ s, 0 < s ∧ ∃ r,
      HasDerivWithinAt (NestedSeatAlloc.IntPolicy.expRevenue P X f p 1) r (Set.Ici s) s ∧
        r < f 2 := by
  have := hM.isProb
  have hX : Measurable (X 1) := hM.meas 1
  have hf1 : 0 < f 1 := hpos 1 le_rfl
  have hf2 : 0 < f 2 := hpos 2 (by norm_num)
  -- tail sets
  set A : ℕ → Set Ω := fun n => {ω | (n : ℝ) ≤ X 1 ω} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le measurable_const hX
  have hAanti : Antitone A := by
    intro m n hmn ω hω
    simp only [hA, Set.mem_setOf_eq] at hω ⊢
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hAinter : (⋂ n, A n) = ∅ := by
    ext ω
    simp only [hA, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt (X 1 ω)
    exact ⟨n, hn⟩
  have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P) (fun n => (hAm n).nullMeasurableSet) hAanti
      ⟨0, measure_ne_top P _⟩
    rwa [hAinter, measure_empty] at this
  have hlimR : Tendsto (fun n => f 1 * P.real (A n)) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    have h2 : Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
      simpa [Function.comp_def, Measure.real] using h
    simpa using h2.const_mul (f 1)
  have hev : ∀ᶠ n in atTop, f 1 * P.real (A n) < f 2 := hlimR.eventually (gt_mem_nhds hf2)
  obtain ⟨M, hMlt⟩ := (hev.and (eventually_ge_atTop 2)).exists
  obtain ⟨hMf, hM2⟩ := hMlt
  -- N = M - 1 ≥ 1
  set N : ℕ := M - 1 with hNdef
  have hNM : N + 1 = M := by omega
  have hN1 : 1 ≤ N := by omega
  -- the tail set in the form used by the indicator
  set B : Set Ω := {ω | (N : ℝ) + 1 ≤ X 1 ω} with hB
  have hBA : B = A M := by
    ext ω; simp only [hB, hA, Set.mem_setOf_eq]; rw [← hNM]; push_cast; rfl
  have hBm : MeasurableSet B := hBA ▸ hAm M
  -- integrability of the base revenue
  have hmeasN : Measurable (fun ω => NestedSeatAlloc.IntPolicy.revenue f p (fun i => X i ω) 1 N) := by
    simp only [NestedSeatAlloc.IntPolicy.revenue]
    exact Measurable.ite (measurableSet_lt measurable_const hX) measurable_const
      (hX.const_mul _)
  have hintN : Integrable (fun ω => NestedSeatAlloc.IntPolicy.revenue f p (fun i => X i ω) 1 N) P := by
    refine Integrable.mono' (integrable_const (|f 1| * N)) hmeasN.aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    simp only [NestedSeatAlloc.IntPolicy.revenue, Real.norm_eq_abs]
    have h0 : 0 ≤ X 1 ω := hM.nonneg 1 ω
    split_ifs with h
    · rw [abs_mul, Nat.abs_cast]
    · rw [abs_mul, abs_of_nonneg h0]
      exact mul_le_mul_of_nonneg_left (not_lt.mp h) (abs_nonneg _)
  -- affine formula for expRevenue on [N, N+1]
  set c : ℝ := f 1 * P.real B with hc
  have haff : ∀ t ∈ Set.Icc (N : ℝ) (N + 1),
      NestedSeatAlloc.IntPolicy.expRevenue P X f p 1 t =
        NestedSeatAlloc.IntPolicy.expRevenue P X f p 1 N + (t - N) * c := by
    intro t ht
    unfold NestedSeatAlloc.IntPolicy.expRevenue
    have hpt : ∀ ω, NestedSeatAlloc.IntPolicy.revenue f p (fun i => X i ω) 1 t =
        NestedSeatAlloc.IntPolicy.revenue f p (fun i => X i ω) 1 N +
          B.indicator (fun _ => (t - N) * f 1) ω := by
      intro ω
      rw [rev1_affine f p (fun i => X i ω) N (hint 1 ω) t ht]
      congr 1
    simp_rw [hpt]
    rw [integral_add hintN ((integrable_const _).indicator hBm), integral_indicator_const _ hBm]
    rw [hc, smul_eq_mul]; ring
  refine ⟨N, by exact_mod_cast hN1, c, ?_, ?_⟩
  · have hlin : HasDerivWithinAt
        (fun t => NestedSeatAlloc.IntPolicy.expRevenue P X f p 1 N + (t - N) * c) c
        (Set.Ici (N : ℝ)) N := by
      have := ((hasDerivAt_id (N : ℝ)).sub_const (N : ℝ)).mul_const c
      simpa using (this.const_add (NestedSeatAlloc.IntPolicy.expRevenue P X f p 1 N)).hasDerivWithinAt
    refine hlin.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Icc_mem_nhdsGE (show (N : ℝ) < N + 1 by linarith)] with t ht
      exact haff t ht
    · simp
  · rw [hc, hBA]; exact hMf

open MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : NestedSeatAlloc.IntPolicy.IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ s, 0 < s ∧ ∃ r,
      HasDerivWithinAt (NestedSeatAlloc.IntPolicy.expRevenue P X f p 1) r (Set.Ici s) s ∧ r < f 2 := by
  exact NestedSeatAlloc.IntPolicy.TailPos93.main P X f p hM hint hpos
