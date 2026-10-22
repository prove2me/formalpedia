-- Prove2me | solution 1 for MDPComplexity.AverageCost.follow_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T17:30:38.651988+00:00
-- url     : https://prove2.me/submissions/d2991b6a-d893-4792-8d04-ed5d36a31d71

import Mathlib
import Definitions.Def_MDPComplexity_AverageCost_Model

open MDPComplexity.AverageCost Filter Finset

theorem fc_per0 (f : ℕ → ℝ) (n : ℕ) (q : ℕ) :
    ∑ i ∈ range (n * q), f (i % n) = q * ∑ i ∈ range n, f i := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show n * (q + 1) = n * q + n by ring, Finset.sum_range_add, ih]
    have : ∑ x ∈ range n, f ((n * q + x) % n) = ∑ i ∈ range n, f i := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    rw [this]; push_cast; ring

theorem fc_per (f : ℕ → ℝ) (n : ℕ) (q r : ℕ) (hr : r ≤ n) :
    ∑ i ∈ range (n * q + r), f (i % n) = q * ∑ i ∈ range n, f i + ∑ i ∈ range r, f i := by
  rw [Finset.sum_range_add, fc_per0]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_range] at hx
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem fc_bound (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (m : ℕ) :
    |∑ i ∈ range m, f (i % n) - m * ((∑ i ∈ range n, f i) / n)| ≤
      2 * ∑ i ∈ range n, |f i| := by
  set B := ∑ i ∈ range n, |f i|
  set Ct := ∑ i ∈ range n, f i
  have hm := Nat.div_add_mod m n
  have hr := Nat.mod_lt m hn
  have e1 : ∑ i ∈ range m, f (i % n) = ((m / n : ℕ) : ℝ) * Ct + ∑ i ∈ range (m % n), f i := by
    conv_lhs => rw [← hm]
    exact fc_per f n _ _ hr.le
  have e2 : (m : ℝ) = n * ((m / n : ℕ) : ℝ) + ((m % n : ℕ) : ℝ) := by exact_mod_cast hm.symm
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have e3 : (m:ℝ) * (Ct / n) = ((m / n : ℕ) : ℝ) * Ct + ((m % n : ℕ) : ℝ) * Ct / n := by
    rw [e2]; field_simp
  rw [e1, e3]
  have hR : |∑ i ∈ range (m % n), f i| ≤ B :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hr.le)
        (fun _ _ _ => abs_nonneg _))
  have hC : |Ct| ≤ B := Finset.abs_sum_le_sum_abs _ _
  have hq : |((m % n : ℕ) : ℝ) * Ct / n| ≤ B := by
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((m % n : ℕ) : ℝ)),
      abs_of_pos hnr, div_le_iff₀ hnr]
    have : ((m % n : ℕ) : ℝ) ≤ n := by exact_mod_cast hr.le
    nlinarith [abs_nonneg Ct]
  have := abs_sub (∑ i ∈ range (m % n), f i) (((m % n : ℕ) : ℝ) * Ct / n)
  calc _ = |∑ i ∈ range (m % n), f i - ((m % n : ℕ) : ℝ) * Ct / n| := by congr 1; ring
    _ ≤ _ := by linarith

theorem fc_avg (f : ℕ → ℝ) (μ K : ℝ) (L : ℕ)
    (h : ∀ T ≥ L, |∑ t ∈ range (T+1), f t - T * μ| ≤ K) :
    Tendsto (fun T : ℕ => (∑ t ∈ range (T+1), f t) / T) atTop (nhds μ) := by
  have h1 : Tendsto (fun T : ℕ => μ - K / T) atTop (nhds μ) := by
    simpa using (tendsto_const_nhds (x := μ)).sub (tendsto_const_div_atTop_nhds_zero_nat K)
  have h2 : Tendsto (fun T : ℕ => μ + K / T) atTop (nhds μ) := by
    simpa using (tendsto_const_nhds (x := μ)).add (tendsto_const_div_atTop_nhds_zero_nat K)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2
  · filter_upwards [eventually_ge_atTop (max L 1)] with T hT
    have hT1 : (0:ℝ) < T := by exact_mod_cast (lt_of_lt_of_le one_pos (le_of_max_le_right hT))
    have hb := abs_le.1 (h T (le_of_max_le_left hT))
    rw [show μ - K / T = (T * μ - K) / T by field_simp]
    exact div_le_div_of_nonneg_right (by linarith [hb.1]) hT1.le
  · filter_upwards [eventually_ge_atTop (max L 1)] with T hT
    have hT1 : (0:ℝ) < T := by exact_mod_cast (lt_of_lt_of_le one_pos (le_of_max_le_right hT))
    have hb := abs_le.1 (h T (le_of_max_le_left hT))
    rw [show μ + K / T = (T * μ + K) / T by field_simp]
    exact div_le_div_of_nonneg_right (by linarith [hb.2]) hT1.le

section
variable {S : Type*} [Fintype S] [DecidableEq S]

def fcTr (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) : M.D s' := e ▸ x

theorem fcTr_next (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.next s' (fcTr M e x) = M.next s x := by subst e; rfl

theorem fcTr_c (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.c s' (fcTr M e x) = M.c s x := by subst e; rfl

noncomputable def fcPol (M : DetMDP S) {L : ℕ} (W : M.Walk L) (C : M.Cycle) : M.Policy :=
  fun s t =>
    if h1 : t < L then
      (if h : W.v ⟨t, by omega⟩ = s then fcTr M h (W.d ⟨t, h1⟩) else Classical.arbitrary _)
    else
      (if h : C.v ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩ = s then
        fcTr M h (C.d ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩) else Classical.arbitrary _)

def fcQ (M : DetMDP S) {L : ℕ} (W : M.Walk L) (C : M.Cycle) (t : ℕ) : S :=
  if h : t < L then W.v ⟨t, by omega⟩ else C.v ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩

theorem fc_stepW (M : DetMDP S) {L : ℕ} (W : M.Walk L) (C : M.Cycle) (t : ℕ) (h : t < L) :
    M.next (W.v ⟨t, by omega⟩) (fcPol M W C (W.v ⟨t, by omega⟩) t) = W.v ⟨t + 1, by omega⟩ ∧
    M.c (W.v ⟨t, by omega⟩) (fcPol M W C (W.v ⟨t, by omega⟩) t) =
      M.c (W.v ⟨t, by omega⟩) (W.d ⟨t, h⟩) := by
  simp only [fcPol]
  rw [dif_pos h, dif_pos trivial, fcTr_next, fcTr_c]
  exact ⟨W.step ⟨t, h⟩, rfl⟩

theorem fc_stepC (M : DetMDP S) {L : ℕ} (W : M.Walk L) (C : M.Cycle) (t : ℕ) (h : ¬ t < L) :
    M.next (C.v ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩)
      (fcPol M W C (C.v ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩) t) =
      C.v ⟨((t - L) % C.len + 1) % C.len, Nat.mod_lt _ C.positive⟩ ∧
    M.c (C.v ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩)
      (fcPol M W C (C.v ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩) t) =
      M.c (C.v ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩)
        (C.d ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩) := by
  simp only [fcPol]
  rw [dif_neg h, dif_pos trivial, fcTr_next, fcTr_c]
  exact ⟨C.step _, rfl⟩

theorem fc_path (M : DetMDP S) (s₀ : S) {L : ℕ} (W : M.Walk L) (C : M.Cycle)
    (hs : W.start = s₀) (hf : W.finish = C.base) :
    ∀ t, M.path s₀ (fcPol M W C) t = fcQ M W C t := by
  intro t
  induction t with
  | zero =>
    show s₀ = fcQ M W C 0
    unfold fcQ
    by_cases hL : 0 < L
    · rw [dif_pos hL]; exact hs.symm
    · rw [dif_neg hL]
      obtain rfl : L = 0 := by omega
      rw [← hs]
      show W.v ⟨0, _⟩ = _
      have e1 : W.v ⟨0, Nat.zero_lt_succ 0⟩ = W.finish := rfl
      rw [e1, hf]
      exact congrArg C.v (Fin.ext (by simp))
  | succ t ih =>
    show M.next (M.path s₀ (fcPol M W C) t) (fcPol M W C (M.path s₀ (fcPol M W C) t) t) = _
    rw [ih]
    by_cases h : t < L
    · have hq : fcQ M W C t = W.v ⟨t, by omega⟩ := dif_pos h
      rw [hq, (fc_stepW M W C t h).1]
      unfold fcQ
      by_cases h' : t + 1 < L
      · rw [dif_pos h']
      · rw [dif_neg h']
        have e : t + 1 = L := by omega
        calc W.v ⟨t + 1, by omega⟩ = W.finish := congrArg W.v (Fin.ext e)
          _ = C.base := hf
          _ = _ := congrArg C.v (Fin.ext (by
              show 0 = (t + 1 - L) % C.len
              rw [show t + 1 - L = 0 by omega, Nat.zero_mod]))
    · have hq : fcQ M W C t = C.v ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩ := dif_neg h
      rw [hq, (fc_stepC M W C t h).1]
      unfold fcQ
      rw [dif_neg (by omega)]
      exact congrArg C.v (Fin.ext (by
        show ((t - L) % C.len + 1) % C.len = (t + 1 - L) % C.len
        rw [Nat.mod_add_mod, show t + 1 - L = t - L + 1 by omega]))

noncomputable def fcCyc (M : DetMDP S) (C : M.Cycle) (k : ℕ) : ℝ :=
  if h : k < C.len then M.c (C.v ⟨k, h⟩) (C.d ⟨k, h⟩) else 0

theorem fc_stage (M : DetMDP S) (s₀ : S) {L : ℕ} (W : M.Walk L) (C : M.Cycle)
    (hs : W.start = s₀) (hf : W.finish = C.base) (t : ℕ) (ht : ¬ t < L) :
    M.stageCost s₀ (fcPol M W C) t = fcCyc M C ((t - L) % C.len) := by
  unfold DetMDP.stageCost
  rw [fc_path M s₀ W C hs hf t]
  have hq : fcQ M W C t = C.v ⟨(t - L) % C.len, Nat.mod_lt _ C.positive⟩ := dif_neg ht
  rw [hq, (fc_stepC M W C t ht).2]
  unfold fcCyc
  rw [dif_pos (Nat.mod_lt _ C.positive)]

theorem fc_mean (M : DetMDP S) (C : M.Cycle) :
    C.mean = (∑ i ∈ range C.len, fcCyc M C i) / C.len := by
  unfold DetMDP.Cycle.mean
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  unfold fcCyc
  rw [dif_pos j.isLt]
end

theorem solution {S : Type*} [Fintype S] [DecidableEq S] (M : DetMDP S) (s₀ : S) :
    ∀ C : M.Cycle, M.Reachable s₀ C.base →
      ∃ δ : M.Policy, Tendsto (M.average s₀ δ) atTop (nhds C.mean) := by
  intro C hC
  obtain ⟨L, W, hs, hf⟩ := hC
  refine ⟨fcPol M W C, ?_⟩
  set f := M.stageCost s₀ (fcPol M W C) with hfdef
  set A := ∑ t ∈ range L, f t
  set B := ∑ i ∈ range C.len, |fcCyc M C i|
  have hn := C.positive
  apply fc_avg f C.mean (|A| + 2 * B + |(L:ℝ) - 1| * |C.mean|) L
  intro T hT
  have hm : T + 1 = L + (T + 1 - L) := by omega
  rw [hm, Finset.sum_range_add]
  have hper : ∑ x ∈ range (T + 1 - L), f (L + x) =
      ∑ x ∈ range (T + 1 - L), fcCyc M C (x % C.len) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hfdef, fc_stage M s₀ W C hs hf (L + x) (by omega), Nat.add_sub_cancel_left]
  rw [hper]
  have hb := fc_bound (fcCyc M C) C.len hn (T + 1 - L)
  rw [← fc_mean] at hb
  have hcast : (((T + 1 - L : ℕ)) : ℝ) = (T : ℝ) + 1 - L := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hb
  have hb' := abs_le.1 hb
  have hP : |((L:ℝ) - 1) * C.mean| = |(L:ℝ) - 1| * |C.mean| := abs_mul _ _
  have hP1 := neg_abs_le (((L:ℝ) - 1) * C.mean)
  have hP2 := le_abs_self (((L:ℝ) - 1) * C.mean)
  have hA1 := neg_abs_le A
  have hA2 := le_abs_self A
  rw [abs_le]
  constructor <;> nlinarith
