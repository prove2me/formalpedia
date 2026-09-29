-- Prove2me | solution 1 for MarkovMixing.optional_stopping
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T20:08:19.517916+00:00
-- url     : https://prove2.me/submissions/e0714d23-4b29-45e7-8da7-647a0b2f7ef6

import Definitions.Def_mm_martingale
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Optional stopping theorem, version 2 (LPW Corollary 17.7)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reindex a sum over trajectories of length `n+2` by (prefix, last state). -/
private lemma snoc_sum {n : ℕ} (f : (Fin (n + 2) → V) → ℝ) :
    ∑ ω : Fin (n + 2) → V, f ω
      = ∑ ω : Fin (n + 1) → V, ∑ y : V, f (Fin.snoc ω y) := by
  let e : ((Fin (n + 1) → V) × V) ≃ (Fin (n + 2) → V) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun ω => (Fin.init ω, ω (Fin.last _))
      left_inv := by intro p; ext <;> simp
      right_inv := by intro ω; simp }
  have := Equiv.sum_comp e f
  rw [← this, Fintype.sum_prod_type]
  rfl

private lemma snoc_lt {n : ℕ} (ω : Fin (n + 1) → V) (y : V) (j : ℕ)
    (h : j < n + 1) (h2 : j < n + 2) :
    (Fin.snoc ω y : Fin (n + 2) → V) ⟨j, h2⟩ = ω ⟨j, h⟩ := by
  have he : (⟨j, h2⟩ : Fin (n + 2)) = Fin.castSucc ⟨j, h⟩ := rfl
  rw [he, Fin.snoc_castSucc]

/-- The prefix of a snoc is the prefix of the original, at a small index. -/
private lemma pathPrefix_snoc_castSucc {n : ℕ} (ω : Fin (n + 1) → V) (y : V)
    (i : Fin n) :
    pathPrefix (Fin.snoc ω y : Fin (n + 2) → V) i.castSucc = pathPrefix ω i := by
  funext j
  simp only [pathPrefix]
  exact snoc_lt ω y j.val (by have := j.isLt; have := i.isLt; simp at *; omega) _

/-- The full-length prefix of a snoc is the original trajectory. -/
private lemma pathPrefix_snoc_last {n : ℕ} (ω : Fin (n + 1) → V) (y : V) :
    pathPrefix (Fin.snoc ω y : Fin (n + 2) → V) (Fin.last n) = ω := by
  funext j
  simp only [pathPrefix]
  have h : (j : ℕ) < n + 1 := by have := j.isLt; simpa using this
  rw [snoc_lt ω y j.val h]
  congr 1

private lemma pathWeight_snoc (P : Matrix V V ℝ) {n : ℕ}
    (ω : Fin (n + 1) → V) (y : V) :
    pathWeight P (Fin.snoc ω y : Fin (n + 2) → V)
      = pathWeight P ω * P (ω (Fin.last n)) y := by
  simp only [pathWeight]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [show (i.castSucc : Fin (n + 1)).castSucc = (i.castSucc : Fin (n+1)).castSucc from rfl,
      Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc]
    congr 1
    rw [show (Fin.last n).succ = Fin.last (n + 1) from rfl, Fin.snoc_last]

/-- The unnormalized weight of a trajectory that has *not* stopped strictly
before time `n`, starting from `x`. -/
private def wt (P : Matrix V V ℝ) (x : V)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (n : ℕ) (ω : Fin (n + 1) → V) : ℝ :=
  (if ω 0 = x then (1 : ℝ) else 0) * pathWeight P ω *
    ∏ u : Fin n, (1 - s u.val (pathPrefix ω u))

private lemma wt_snoc (P : Matrix V V ℝ) (x : V)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) {n : ℕ} (ω : Fin (n + 1) → V) (y : V) :
    wt P x s (n + 1) (Fin.snoc ω y)
      = wt P x s n ω * (1 - s n ω) * P (ω (Fin.last n)) y := by
  simp only [wt]
  have h0 : (Fin.snoc ω y : Fin (n + 2) → V) 0 = ω 0 := by
    have : (0 : Fin (n + 2)) = Fin.castSucc (0 : Fin (n + 1)) := rfl
    rw [this, Fin.snoc_castSucc]
  have hprod : (∏ u : Fin (n + 1),
      (1 - s u.val (pathPrefix (Fin.snoc ω y : Fin (n + 2) → V) u)))
      = (∏ u : Fin n, (1 - s u.val (pathPrefix ω u))) * (1 - s n ω) := by
    rw [Fin.prod_univ_castSucc]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by
        rw [pathPrefix_snoc_castSucc]; rfl
    · rw [pathPrefix_snoc_last]; rfl
  rw [h0, hprod, pathWeight_snoc]
  ring

private lemma wt_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) (x : V)
    {s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ}
    (hs01 : ∀ (t : ℕ) (ω : Fin (t + 1) → V), s t ω = 0 ∨ s t ω = 1)
    (n : ℕ) (ω : Fin (n + 1) → V) : 0 ≤ wt P x s n ω := by
  have hpw : 0 ≤ pathWeight P ω :=
    Finset.prod_nonneg fun i _ => hP.1 _ _
  refine mul_nonneg (mul_nonneg ?_ hpw) (Finset.prod_nonneg fun u _ => ?_)
  · positivity
  · rcases hs01 u.val (pathPrefix ω u) with h | h <;> rw [h] <;> norm_num

/-- One-step decomposition of a weighted sum over trajectories. -/
private lemma sum_snoc_wt (P : Matrix V V ℝ) (x : V)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) {n : ℕ}
    (g : (Fin (n + 2) → V) → ℝ) :
    ∑ ω' : Fin (n + 2) → V, wt P x s (n + 1) ω' * g ω'
      = ∑ ω : Fin (n + 1) → V, wt P x s n ω * (1 - s n ω) *
          ∑ y, P (ω (Fin.last n)) y * g (Fin.snoc ω y) := by
  rw [snoc_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [wt_snoc]; ring

/-- The martingale recursion: the "not yet stopped" expectation drops by
exactly the mass stopped at time `n`. -/
private lemma A_succ (P : Matrix V V ℝ) (x : V)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ)
    (M : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (hM : IsChainMartingale P M) (n : ℕ) :
    ∑ ω : Fin (n + 2) → V, wt P x s (n + 1) ω * M (n + 1) ω
      = (∑ ω : Fin (n + 1) → V, wt P x s n ω * M n ω)
        - ∑ ω : Fin (n + 1) → V, wt P x s n ω * s n ω * M n ω := by
  rw [sum_snoc_wt P x s (fun ω' => M (n + 1) ω'), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [hM n ω]; ring

private lemma r_succ (P : Matrix V V ℝ) (hP : IsStochastic P) (x : V)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (n : ℕ) :
    (∑ ω : Fin (n + 2) → V, wt P x s (n + 1) ω)
      = (∑ ω : Fin (n + 1) → V, wt P x s n ω)
        - ∑ ω : Fin (n + 1) → V, wt P x s n ω * s n ω := by
  have h := sum_snoc_wt P x s (n := n) (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [hP.2 (ω (Fin.last n))]; ring

private lemma stopAt_sum (P : Matrix V V ℝ) (x : V)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (n : ℕ) :
    (∑ y, stopAtProb P x s n y)
      = ∑ ω : Fin (n + 1) → V, wt P x s n ω * s n ω := by
  simp only [stopAtProb, wt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω 0 = x
  · simp [h]
  · simp [h]

end

end MarkovMixing

open MarkovMixing

/-- **Corollary 17.7, the Optional Stopping Theorem** (LPW). -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (M : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) (hM : IsChainMartingale P M)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ)
    (hs01 : ∀ (t : ℕ) (ω : Fin (t + 1) → V), s t ω = 0 ∨ s t ω = 1)
    (x : V) (hfin : (∑' t : ℕ, ∑ y, stopAtProb P x s t y) = 1)
    (K : ℝ) (hK : ∀ (t : ℕ) (ω : Fin (t + 1) → V), |M t ω| ≤ K) :
    stoppedExp P x s M = M 0 (fun _ => x) := by
  classical
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ,
      A = fun n => ∑ ω : Fin (n + 1) → V, wt P x s n ω * M n ω := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ,
      a = fun n => ∑ ω : Fin (n + 1) → V, wt P x s n ω * s n ω * M n ω := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ,
      r = fun n => ∑ ω : Fin (n + 1) → V, wt P x s n ω := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ → ℝ,
      p = fun n => ∑ y, stopAtProb P x s n y := ⟨_, rfl⟩
  -- the recursions
  have hAsucc : ∀ n, A (n + 1) = A n - a n := by
    intro n; simp only [hA, ha]; exact A_succ P x s M hM n
  have hrsucc : ∀ n, r (n + 1) = r n - p n := by
    intro n; simp only [hr, hp, stopAt_sum]; exact r_succ P hP x s n
  have hpeq : ∀ n, p n = ∑ ω : Fin (n + 1) → V, wt P x s n ω * s n ω := by
    intro n; simp only [hp]; exact stopAt_sum P x s n
  -- the unique length-one trajectory starting at `x`
  have huniq : ∀ ω : Fin 1 → V, ω ≠ (fun _ => x) → ω 0 ≠ x := by
    intro ω hne h
    exact hne (funext fun i => by
      rw [Subsingleton.elim i (0 : Fin 1)]; exact h)
  have hA0 : A 0 = M 0 (fun _ => x) := by
    simp only [hA, wt]
    rw [Finset.sum_eq_single (fun _ => x)]
    · simp [pathWeight]
    · intro b _ hb; simp [huniq b hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hr0 : r 0 = 1 := by
    simp only [hr, wt]
    rw [Finset.sum_eq_single (fun _ => x)]
    · simp [pathWeight]
    · intro b _ hb; simp [huniq b hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- nonnegativity and the bounds
  have hwtnn : ∀ (n : ℕ) (ω : Fin (n + 1) → V), 0 ≤ wt P x s n ω :=
    fun n ω => wt_nonneg hP x hs01 n ω
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 (fun _ => x))
  have hpnn : ∀ n, 0 ≤ p n := by
    intro n; rw [hpeq]
    refine Finset.sum_nonneg fun ω _ => mul_nonneg (hwtnn n ω) ?_
    rcases hs01 n ω with h | h <;> rw [h] <;> norm_num
  have hAbd : ∀ n, |A n| ≤ K * r n := by
    intro n
    calc |A n| ≤ ∑ ω : Fin (n + 1) → V, |wt P x s n ω * M n ω| := by
          rw [hA]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω : Fin (n + 1) → V, wt P x s n ω * K := by
          refine Finset.sum_le_sum fun ω _ => ?_
          rw [abs_mul, abs_of_nonneg (hwtnn n ω)]
          exact mul_le_mul_of_nonneg_left (hK n ω) (hwtnn n ω)
      _ = K * r n := by rw [hr, ← Finset.sum_mul]; ring
  have habd : ∀ n, |a n| ≤ K * p n := by
    intro n
    have hnn : ∀ ω : Fin (n + 1) → V, 0 ≤ wt P x s n ω * s n ω := by
      intro ω
      refine mul_nonneg (hwtnn n ω) ?_
      rcases hs01 n ω with h | h <;> rw [h] <;> norm_num
    calc |a n| ≤ ∑ ω : Fin (n + 1) → V, |wt P x s n ω * s n ω * M n ω| := by
          rw [ha]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω : Fin (n + 1) → V, (wt P x s n ω * s n ω) * K := by
          refine Finset.sum_le_sum fun ω _ => ?_
          rw [abs_mul, abs_of_nonneg (hnn ω)]
          exact mul_le_mul_of_nonneg_left (hK n ω) (hnn ω)
      _ = K * p n := by rw [hpeq, ← Finset.sum_mul]; ring
  -- the tail of the stopping time vanishes
  have hfin' : (∑' t : ℕ, p t) = 1 := by simp only [hp]; exact hfin
  have hsp : Summable p := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hfin'
    norm_num at hfin'
  have htp : Filter.Tendsto (fun n => ∑ t ∈ Finset.range n, p t) Filter.atTop
      (nhds 1) := by
    rw [← hfin']; exact hsp.hasSum.tendsto_sum_nat
  have hreq : ∀ n, r n = 1 - ∑ t ∈ Finset.range n, p t := by
    intro n
    induction n with
    | zero => simp [hr0]
    | succ k ih => rw [hrsucc, ih, Finset.sum_range_succ]; ring
  have htr : Filter.Tendsto r Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n => 1 - ∑ t ∈ Finset.range n, p t)
        Filter.atTop (nhds (1 - 1)) := Filter.Tendsto.sub tendsto_const_nhds htp
    rw [show (0 : ℝ) = 1 - 1 by norm_num]
    exact h1.congr fun n => (hreq n).symm
  have hhi : Filter.Tendsto (fun n => K * r n) Filter.atTop (nhds 0) := by
    simpa using htr.const_mul K
  have htA : Filter.Tendsto A Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => -(K * r n))
      (h := fun n => K * r n) ?_ hhi (fun n => neg_le_of_abs_le (hAbd n))
      (fun n => le_of_abs_le (hAbd n))
    simpa using hhi.neg
  -- summability of the stopped contributions
  have hsa : Summable a := by
    refine Summable.of_norm_bounded (hsp.mul_left K) fun n => ?_
    rw [Real.norm_eq_abs]; exact habd n
  have hpartial : ∀ n, ∑ t ∈ Finset.range n, a t = A 0 - A n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, hAsucc]; ring
  have hlim : (∑' n, a n) = A 0 := by
    refine tendsto_nhds_unique hsa.hasSum.tendsto_sum_nat ?_
    have h2 : Filter.Tendsto (fun n => A 0 - A n) Filter.atTop (nhds (A 0 - 0)) :=
      Filter.Tendsto.sub tendsto_const_nhds htA
    rw [sub_zero] at h2
    exact h2.congr fun n => (hpartial n).symm
  -- identify `stoppedExp` with `∑' a`
  have hse : stoppedExp P x s M = ∑' n, a n := by
    simp only [stoppedExp, ha]
    refine tsum_congr fun t => Finset.sum_congr rfl fun ω _ => ?_
    simp only [wt]
    by_cases h : ω 0 = x
    · simp [h]
    · simp [h]
  rw [hse, hlim, hA0]
