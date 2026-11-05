-- Prove2me | solution 1 for JSQHalfinWhitt.Tightness.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:12:16.707207+00:00
-- url     : https://prove2.me/submissions/07fda5a9-04a2-4d74-bcbc-ad5bd9ccb359

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_1

namespace JSQHalfinWhitt.Tightness

open scoped Classical

section Cut
variable {n : ℕ}
/-- an index beyond which all coordinates vanish -/
noncomputable def cut (q : State n) : ℕ := Classical.choose q.2.2.2 + 1

lemma cut_spec (q : State n) : ∀ i, cut q ≤ i + 1 → q.1 i = 0 := by
  intro i hi
  exact Classical.choose_spec q.2.2.2 i (by unfold cut at hi; omega)

lemma not_arrives_of_ge (hn : 1 ≤ n) (q : State n) (i : ℕ) (hi : cut q ≤ i) :
    ¬ ArrivesAt q i := by
  rintro ⟨h1, _⟩
  have := h1 (cut q - 1) (by unfold cut at hi ⊢; omega)
  rw [cut_spec q (cut q - 1) (by unfold cut; omega)] at this
  omega

lemma dep_rate_zero (q : State n) (i : ℕ) (hi : cut q ≤ i) :
    ((q.1 i : ℝ) - (q.1 (i + 1) : ℝ)) = 0 := by
  rw [cut_spec q i (by omega), cut_spec q (i + 1) (by omega)]; simp

end Cut

section Coord

variable {n : ℕ}

lemma up_coord (q : State n) (i j : ℕ) :
    (up q i).1 j = if ArrivesAt q i ∧ j = i then q.1 j + 1 else q.1 j := by
  by_cases h : ArrivesAt q i
  · have : up q i = ⟨Function.update q.1 i (q.1 i + 1), up_mem q i h⟩ := dif_pos h
    rw [this]
    show Function.update q.1 i (q.1 i + 1) j = _
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj, Function.update_of_ne hj]
  · have : up q i = q := dif_neg h
    rw [this]; simp [h]

lemma down_coord (q : State n) (i j : ℕ) :
    (down q i).1 j = if q.1 (i + 1) < q.1 i ∧ j = i then q.1 j - 1 else q.1 j := by
  by_cases h : q.1 (i + 1) < q.1 i
  · have : down q i = ⟨Function.update q.1 i (q.1 i - 1), down_mem q i h⟩ := dif_pos h
    rw [this]
    show Function.update q.1 i (q.1 i - 1) j = _
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj, Function.update_of_ne hj]
  · have : down q i = q := dif_neg h
    rw [this]; simp [h]

lemma genQ_local (lam : ℝ) (f : State n → ℝ) (q : State n) (s : Finset ℕ)
    (hf : ∀ i ∉ s, f (up q i) = f q ∧ f (down q i) = f q) :
    genQ n lam f q = ∑ i ∈ s, (if ArrivesAt q i then (n : ℝ) * lam else 0) * (f (up q i) - f q) +
      ∑ i ∈ s, ((q.1 i : ℝ) - (q.1 (i + 1) : ℝ)) * (f (down q i) - f q) := by
  unfold genQ
  rw [tsum_eq_sum (s := s), tsum_eq_sum (s := s)]
  · intro i hi; rw [(hf i hi).2]; simp
  · intro i hi; rw [(hf i hi).1]; simp

/-- generator on a single coordinate -/
lemma genQ_coord (lam : ℝ) (q : State n) (i : ℕ) :
    genQ n lam (fun q => (q.1 i : ℝ)) q =
      (if ArrivesAt q i then (n : ℝ) * lam else 0) - ((q.1 i : ℝ) - (q.1 (i + 1) : ℝ)) := by
  rw [genQ_local lam _ q {i}]
  · simp only [Finset.sum_singleton]
    rw [up_coord, down_coord]
    by_cases h1 : ArrivesAt q i
    · by_cases h2 : q.1 (i + 1) < q.1 i
      · simp [h1, h2]; push_cast [Nat.cast_sub (by omega : 1 ≤ q.1 i)]; ring
      · have : q.1 (i+1) = q.1 i := le_antisymm (q.2.2.1 (Nat.le_succ i)) (by omega)
        simp [h1, h2, this]
    · by_cases h2 : q.1 (i + 1) < q.1 i
      · simp [h1, h2]; push_cast [Nat.cast_sub (by omega : 1 ≤ q.1 i)]; ring
      · have : q.1 (i+1) = q.1 i := le_antisymm (q.2.2.1 (Nat.le_succ i)) (by omega)
        simp [h1, h2, this]
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    rw [up_coord, down_coord]; simp [Ne.symm hj, hj]

end Coord

section Expect

variable {S : Type*}

lemma summable_bdd (π : S → ℝ) (hπ0 : ∀ q, 0 ≤ π q) (hπs : Summable π) (h : S → ℝ) (M : ℝ)
    (hb : ∀ q, |h q| ≤ M) : Summable (fun q => π q * h q) := by
  refine Summable.of_norm_bounded (g := fun q => M * π q) (hπs.mul_left M) (fun q => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ0 q)]
  nlinarith [hb q, hπ0 q, abs_nonneg (h q)]

lemma expect_sub' (π : S → ℝ) (h1 h2 : S → ℝ) (s1 : Summable (fun q => π q * h1 q))
    (s2 : Summable (fun q => π q * h2 q)) :
    expect π (fun q => h1 q - h2 q) = expect π h1 - expect π h2 := by
  unfold expect
  rw [← s1.tsum_sub s2]; congr 1; funext q; ring

lemma expect_add' (π : S → ℝ) (h1 h2 : S → ℝ) (s1 : Summable (fun q => π q * h1 q))
    (s2 : Summable (fun q => π q * h2 q)) :
    expect π (fun q => h1 q + h2 q) = expect π h1 + expect π h2 := by
  unfold expect
  rw [← s1.tsum_add s2]; congr 1; funext q; ring

lemma expect_cmul (π : S → ℝ) (c : ℝ) (h : S → ℝ) :
    expect π (fun q => c * h q) = c * expect π h := by
  unfold expect
  rw [← tsum_mul_left]; congr 1; funext q; ring

lemma expect_const (π : S → ℝ) (c : ℝ) (h1 : ∑' q, π q = 1) :
    expect π (fun _ => c) = c := by
  unfold expect
  rw [tsum_mul_right, h1, one_mul]

lemma expect_mono (π : S → ℝ) (hπ0 : ∀ q, 0 ≤ π q) (h1 h2 : S → ℝ)
    (s1 : Summable (fun q => π q * h1 q)) (s2 : Summable (fun q => π q * h2 q))
    (hle : ∀ q, h1 q ≤ h2 q) : expect π h1 ≤ expect π h2 := by
  unfold expect
  exact s1.tsum_le_tsum (fun q => mul_le_mul_of_nonneg_left (hle q) (hπ0 q)) s2

lemma prob_eq_expect (π : S → ℝ) (A : S → Prop) :
    prob π A = expect π (fun q => if A q then 1 else 0) := by
  unfold prob expect; congr 1; funext q; by_cases h : A q <;> simp [h]

end Expect

section Lemma2

variable {n : ℕ}

theorem lemma_2_proof (n : ℕ) (lam : ℝ) (hn : 1 ≤ n) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : State n → ℝ) (hπ : IsStationaryDist (genQ n lam) π) :
    ∀ i : ℕ, expect π (fun q => (q.1 i : ℝ)) =
      n * lam * prob π (fun q => ∀ j, j < i → q.1 j = n) := by
  have hπ0 := hπ.1
  have hπs := hπ.2.1
  have hcoord_b : ∀ (i : ℕ) (q : State n), |(q.1 i : ℝ)| ≤ n := by
    intro i q
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast q.2.1 i
  -- u k := E[q_k - nλ 1(full_k)]
  set u : ℕ → ℝ := fun k => ∑' q, π q * ((q.1 k : ℝ) -
    (n : ℝ) * lam * (if ∀ j, j < k → q.1 j = n then 1 else 0)) with hu
  have hub : ∀ k (q : State n), |(q.1 k : ℝ) -
      (n : ℝ) * lam * (if ∀ j, j < k → q.1 j = n then 1 else 0)| ≤ n + n * lam := by
    intro k q
    refine (abs_sub _ _).trans ?_
    have := hcoord_b k q
    have : |(n : ℝ) * lam * (if ∀ j, j < k → q.1 j = n then 1 else 0)| ≤ n * lam := by
      split_ifs
      · rw [mul_one, abs_of_nonneg (by positivity)]
      · simp; positivity
    linarith
  have hsum_full : ∀ k, Summable (fun q : State n => π q *
      (if ∀ j, j < k → q.1 j = n then (1 : ℝ) else 0)) := by
    intro k
    refine summable_bdd π hπ0 hπs _ 1 (fun q => ?_)
    split_ifs <;> simp
  have hsum_coord : ∀ k, Summable (fun q : State n => π q * (q.1 k : ℝ)) :=
    fun k => summable_bdd π hπ0 hπs _ n (hcoord_b k)
  have hu_eq : ∀ k, u k = expect π (fun q => (q.1 k : ℝ)) -
      n * lam * prob π (fun q => ∀ j, j < k → q.1 j = n) := by
    intro k
    rw [prob_eq_expect]
    unfold expect
    beta_reduce
    rw [← tsum_mul_left]
    have e := (hsum_coord k).tsum_sub ((hsum_full k).mul_left ((n : ℝ) * lam))
    refine (Eq.trans (tsum_congr (fun q => ?_)) e).trans ?_
    · ring
    · congr 1
      refine tsum_congr (fun x => ?_)
      by_cases h : ∀ j < k, x.1 j = n <;> simp [h]
  -- step: u k = u (k+1)
  have hstep : ∀ k, u k = u (k + 1) := by
    intro k
    have hb := lemma_1 n lam hn hlam0 hlam1 π hπ (fun q => (q.1 k : ℝ))
      (by
        refine summable_bdd π hπ0 hπs _ n (fun q => ?_)
        rw [abs_abs]; exact hcoord_b k q)
    have hG := hb.2
    unfold expect at hG
    simp_rw [genQ_coord] at hG
    have hpt : ∀ q : State n, (if ArrivesAt q k then (n : ℝ) * lam else 0) =
        (n : ℝ) * lam * (if ∀ j, j < k → q.1 j = n then 1 else 0) -
        (n : ℝ) * lam * (if ∀ j, j < k + 1 → q.1 j = n then 1 else 0) := by
      intro q
      have hle := q.2.1 k
      by_cases hA : ArrivesAt q k
      · have h1 : ∀ j, j < k → q.1 j = n := hA.1
        have h2 : ¬ ∀ j, j < k + 1 → q.1 j = n := fun h => by
          have := h k (by omega); have := hA.2; omega
        rw [if_pos hA, if_pos h1, if_neg h2]; ring
      · by_cases h1 : ∀ j, j < k → q.1 j = n
        · have hk : q.1 k = n := by
            by_contra hne
            exact hA ⟨h1, by omega⟩
          have h2 : ∀ j, j < k + 1 → q.1 j = n := by
            intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
            · exact h1 j hj
            · rw [hj]; exact hk
          rw [if_neg hA, if_pos h1, if_pos h2]; ring
        · have h2 : ¬ ∀ j, j < k + 1 → q.1 j = n := fun h => h1 (fun j hj => h j (by omega))
          rw [if_neg hA, if_neg h1, if_neg h2]; ring
    have : u (k + 1) - u k = ∑' q, π q * ((if ArrivesAt q k then (n : ℝ) * lam else 0) -
        ((q.1 k : ℝ) - (q.1 (k + 1) : ℝ))) := by
      rw [hu]
      simp only
      have s1 : Summable (fun q : State n => π q * ((q.1 k : ℝ) -
          (n : ℝ) * lam * (if ∀ j, j < k → q.1 j = n then 1 else 0))) :=
        summable_bdd π hπ0 hπs _ _ (hub k)
      have s2 : Summable (fun q : State n => π q * ((q.1 (k+1) : ℝ) -
          (n : ℝ) * lam * (if ∀ j, j < k + 1 → q.1 j = n then 1 else 0))) :=
        summable_bdd π hπ0 hπs _ _ (hub (k+1))
      rw [← s2.tsum_sub s1]
      refine tsum_congr (fun q => ?_)
      rw [hpt q]; ring
    rw [hG] at this
    linarith
  have hconst : ∀ i m, u i = u (i + m) := by
    intro i m
    induction m with
    | zero => rfl
    | succ m ih => rw [ih, hstep (i + m)]; rfl
  -- limit
  have hlim : ∀ i, Filter.Tendsto (fun m => u (i + m)) Filter.atTop (nhds 0) := by
    intro i
    have := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
      (f := fun m (q : State n) => π q * ((q.1 (i + m) : ℝ) -
        (n : ℝ) * lam * (if ∀ j, j < i + m → q.1 j = n then 1 else 0)))
      (g := fun _ => 0) (bound := fun q => π q * (n + n * lam))
      (hπs.mul_right _) ?_ ?_
    · rw [tsum_zero] at this; exact this
    · intro q
      apply tendsto_const_nhds.congr'
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      refine ⟨cut q, fun m hm => ?_⟩
      have h0 : q.1 (i + m) = 0 := cut_spec q _ (by omega)
      have hnf : ¬ ∀ j, j < i + m → q.1 j = n := by
        intro h
        have hc1 : 1 ≤ cut q := by unfold cut; omega
        have := h (i + m - 1) (by omega)
        rw [cut_spec q (i + m - 1) (by omega)] at this
        omega
      simp [h0, hnf]
    · refine Filter.Eventually.of_forall (fun m q => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ0 q)]
      exact mul_le_mul_of_nonneg_left (hub _ q) (hπ0 q)
  intro i
  have h0 : u i = 0 := by
    have := hlim i
    simp_rw [← hconst i] at this
    exact tendsto_nhds_unique tendsto_const_nhds this
  rw [hu_eq] at h0
  linarith

end Lemma2

end JSQHalfinWhitt.Tightness

open JSQHalfinWhitt.Tightness in
theorem solution (n : ℕ) (lam : ℝ) (hn : 1 ≤ n) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : State n → ℝ) (hπ : IsStationaryDist (genQ n lam) π) :
    expect π (fun q => (q.1 0 : ℝ)) = n * lam ∧
      ∀ i : ℕ, 1 ≤ i →
        expect π (fun q => (q.1 i : ℝ)) = n * lam * prob π (fun q => ∀ j, j < i → q.1 j = n) := by
  refine ⟨?_, fun i _ => lemma_2_proof n lam hn hlam0 hlam1 π hπ i⟩
  rw [lemma_2_proof n lam hn hlam0 hlam1 π hπ 0]
  have : prob π (fun q => ∀ j, j < 0 → q.1 j = n) = 1 := by
    unfold prob
    simp only [Nat.not_lt_zero, false_imp_iff, implies_true, if_true]
    exact hπ.2.2.1
  rw [this, mul_one]
