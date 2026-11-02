-- Prove2me | solution 1 for MLRPCake.EnvyFree.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:54:45.391864+00:00
-- url     : https://prove2.me/submissions/17aa5450-7b88-4d5c-92e4-2de60dc1996e

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Theorems.Thm_MLRPCake_EnvyFree_proposition_1

open MLRPCake.EnvyFree MeasureTheory

namespace MLRPLemma2Aux

lemma cut_le_one {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (ℓ τ : ℝ) : cut f k ℓ τ ≤ 1 := by
  unfold cut
  split_ifs with h
  · obtain ⟨y, hy, hy2⟩ := h
    exact le_trans (csInf_le ⟨ℓ, fun z hz => hz.1.1⟩ ⟨hy, hy2⟩) hy.2
  · exact le_rfl

lemma cut_ge {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (ℓ τ : ℝ) (hℓ : ℓ ≤ 1) : ℓ ≤ cut f k ℓ τ := by
  unfold cut
  split_ifs with h
  · obtain ⟨y, hy, hy2⟩ := h
    exact le_csInf ⟨y, hy, hy2⟩ (fun z hz => hz.1.1)
  · exact hℓ

lemma cut_one {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (τ : ℝ) : cut f k 1 τ = 1 :=
  le_antisymm (cut_le_one f k 1 τ) (cut_ge f k 1 τ le_rfl)

lemma cut_zero {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (ℓ : ℝ) (hℓ : ℓ ≤ 1) : cut f k ℓ 0 = ℓ := by
  apply le_antisymm _ (cut_ge f k ℓ 0 hℓ)
  have hmem : ℓ ∈ {y | y ∈ Set.Icc ℓ 1 ∧ val f k ℓ y = 0} := ⟨⟨le_rfl, hℓ⟩, by simp [val]⟩
  unfold cut
  rw [if_pos ⟨ℓ, hmem.1, hmem.2⟩]
  exact csInf_le ⟨ℓ, fun z hz => hz.1.1⟩ hmem

lemma rd_mem {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ∀ k, rd f k x ∈ Set.Icc (0:ℝ) 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [rd]
    | 1, _ => simpa [rd] using hx
    | k + 2, ih =>
      simp only [rd]
      have h1 := ih (k + 1) (by omega)
      exact ⟨le_trans h1.1 (cut_ge f k _ _ h1.2), cut_le_one f k _ _⟩

lemma eval_eq_val {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (a b : ℝ) (hab : a ≤ b) :
    eval f k a b = val f k a b := by
  unfold eval val
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

lemma rd_zero {n : ℕ} (f : Fin n → ℝ → ℝ) : ∀ k, rd f k 0 = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [rd]
    | 1, _ => simp [rd]
    | k + 2, ih =>
      simp only [rd]
      rw [ih k (by omega), ih (k + 1) (by omega), eval_eq_val f k 0 0 le_rfl]
      simp only [val, intervalIntegral.integral_same]
      exact cut_zero f k 0 zero_le_one

lemma rd_one {n : ℕ} (f : Fin n → ℝ → ℝ) : ∀ k, 1 ≤ k → rd f k 1 = 1 := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp [rd]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      show cut f m (rd f (m + 1) 1) _ = 1
      rw [ih (by omega)]
      exact cut_one f m _

lemma rd_sticky {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) :
    ∀ m k, 1 ≤ k → rd f k x = 1 → rd f (k + m) x = 1 := by
  intro m
  induction m with
  | zero => intro k _ h; simpa using h
  | succ m ih =>
    intro k hk h
    have := ih k hk h
    obtain ⟨j, hj⟩ : ∃ j, k + m = j + 1 := ⟨k + m - 1, by omega⟩
    rw [hj] at this
    have e : k + (m + 1) = j + 2 := by omega
    rw [e]
    show cut f j (rd f (j + 1) x) _ = 1
    rw [this]
    exact cut_one f j _

lemma integrable_sub {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (k : ℕ) (hk : k < n)
    (a b : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    IntervalIntegrable (dens f k) volume a b := by
  have hd : dens f k = f ⟨k, hk⟩ := by simp [dens, hk]
  rw [hd]
  apply (hf ⟨k, hk⟩).2.2.1.mono_set
  rw [Set.uIcc_of_le zero_le_one]
  intro u hu
  rcases le_total a b with h | h
  · rw [Set.uIcc_of_le h] at hu; exact ⟨le_trans ha.1 hu.1, le_trans hu.2 hb.2⟩
  · rw [Set.uIcc_of_ge h] at hu; exact ⟨le_trans hb.1 hu.1, le_trans hu.2 ha.2⟩

lemma val_nonneg {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (k : ℕ) (hk : k < n)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : 0 ≤ val f k a b := by
  unfold val
  have hd : dens f k = f ⟨k, hk⟩ := by simp [dens, hk]
  rw [hd]
  apply intervalIntegral.integral_nonneg hab
  intro u hu
  exact (hf ⟨k, hk⟩).1 u ⟨le_trans ha hu.1, le_trans hu.2 hb⟩

lemma val_add {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (k : ℕ) (hk : k < n)
    (a b c : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hc : c ∈ Set.Icc (0:ℝ) 1) : val f k a b + val f k b c = val f k a c := by
  unfold val
  exact intervalIntegral.integral_add_adjacent_intervals (integrable_sub f hf k hk a b ha hb)
    (integrable_sub f hf k hk b c hb hc)

/-- If the cut lands strictly below `1`, it realizes the requested value. -/
lemma val_cut {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (k : ℕ) (hk : k < n)
    (ℓ τ : ℝ) (hℓ : ℓ ∈ Set.Icc (0:ℝ) 1) (hlt : cut f k ℓ τ < 1) :
    val f k ℓ (cut f k ℓ τ) = τ := by
  unfold cut at hlt ⊢
  split_ifs at hlt ⊢ with h
  · set S := {y | y ∈ Set.Icc ℓ 1 ∧ val f k ℓ y = τ} with hS
    have hcont : ContinuousOn (fun y => val f k ℓ y) (Set.Icc ℓ 1) := by
      have := intervalIntegral.continuousOn_primitive_interval'
        (integrable_sub f hf k hk ℓ 1 hℓ ⟨zero_le_one, le_rfl⟩) (a := ℓ)
        (by rw [Set.uIcc_of_le hℓ.2]; exact ⟨le_rfl, hℓ.2⟩)
      rw [Set.uIcc_of_le hℓ.2] at this
      exact this
    have hclosed : IsClosed S := by
      have := hcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := τ))
      rw [hS]; exact this
    have hne : S.Nonempty := by obtain ⟨y, hy, hy2⟩ := h; exact ⟨y, hy, hy2⟩
    exact (hclosed.csInf_mem hne ⟨ℓ, fun z hz => hz.1.1⟩).2
  · exact absurd hlt (lt_irrefl _)

/-- Lipschitz cut queries force every nondegenerate interval to have positive value. -/
lemma val_pos {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (lam : ℝ) (hlam : 1 ≤ lam)
    (hL : QueriesLipschitz f lam) (k : ℕ) (hk : k < n) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) : 0 < val f k a b := by
  have h0 := val_nonneg f hf k hk a b ha hab.le hb
  rcases h0.lt_or_eq with h | h
  · exact h
  exfalso
  have hlam0 : 0 < lam := by linarith
  set τ := (b - a) / (2 * lam) with hτ
  have hτpos : 0 < τ := by rw [hτ]; apply div_pos <;> linarith
  have hain : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha, by linarith⟩
  have hbin : b ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, hb⟩
  -- values inside [a,b] vanish
  have hzero : ∀ y, a ≤ y → y ≤ b → val f k a y = 0 := by
    intro y hay hyb
    have hyin : y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have e := val_add f hf k hk a y b hain hyin hbin
    have p1 := val_nonneg f hf k hk a y ha hay (by linarith)
    have p2 := val_nonneg f hf k hk y b (by linarith) hyb hb
    linarith
  have hcutb : b ≤ cut f k a τ := by
    unfold cut
    split_ifs with hex
    · obtain ⟨y, hy, hy2⟩ := hex
      apply le_csInf (show Set.Nonempty {y | y ∈ Set.Icc a 1 ∧ val f k a y = τ} from ⟨y, hy, hy2⟩)
      intro z hz
      by_contra hzb
      push Not at hzb
      have := hzero z hz.1.1 hzb.le
      rw [hz.2] at this
      linarith
    · exact hb
  have hcuta : cut f k a 0 = a := cut_zero f k a (by linarith)
  have hlip := (hL ⟨k, hk⟩).2 a 0 a τ hain hain le_rfl hτpos.le
  simp only at hlip
  rw [hcuta, sub_self, abs_zero, sub_zero, abs_of_pos hτpos, max_eq_right hτpos.le] at hlip
  have : lam * τ = (b - a) / 2 := by rw [hτ]; field_simp
  have h3 := le_abs_self (cut f k a τ - a)
  linarith

end MLRPLemma2Aux

open MLRPLemma2Aux

theorem solution (n : ℕ) (f : Fin n → ℝ → ℝ) (lam δ : ℝ) (hn : 2 ≤ n) (hf : IsInstance f)
    (hlam : 1 ≤ lam) (hL : QueriesLipschitz f lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∃ xh ∈ Set.Ioo (0:ℝ) 1, rd f n xh = 1 - δ) ∧
    ∀ xh ∈ Set.Ioo (0:ℝ) 1, rd f n xh = 1 - δ → IsRipple f δ (fun k => rd f k xh) := by
  constructor
  · -- intermediate value theorem
    have hP := MLRPCake.EnvyFree.proposition_1 n f lam hn hf hlam hL
    have hcont : ContinuousOn (rd f n) (Set.Icc (0:ℝ) 1) := by
      have hLip : LipschitzOnWith (Real.toNNReal (lam ^ (2 * (n - 1)))) (rd f n)
          (Set.Icc (0:ℝ) 1) := by
        apply LipschitzOnWith.of_dist_le_mul
        intro x hx y hy
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
        exact hP y x hy hx
      exact hLip.continuousOn
    have hivt := intermediate_value_Icc zero_le_one hcont
    rw [rd_zero f n, rd_one f n (by omega)] at hivt
    obtain ⟨xh, hxh, hval⟩ := hivt (⟨by linarith, by linarith⟩ : 1 - δ ∈ Set.Icc (0:ℝ) 1)
    refine ⟨xh, ⟨?_, ?_⟩, hval⟩
    · rcases hxh.1.lt_or_eq with h | h
      · exact h
      · rw [← h, rd_zero] at hval; linarith
    · rcases hxh.2.lt_or_eq with h | h
      · exact h
      · rw [h, rd_one f n (by omega)] at hval; linarith
  · intro xh hxh hval
    have hxi : xh ∈ Set.Icc (0:ℝ) 1 := ⟨hxh.1.le, hxh.2.le⟩
    have hmem := rd_mem f xh hxi
    -- no cut point before the last one is truncated to 1
    have hlt1 : ∀ k, 1 ≤ k → k ≤ n → rd f k xh < 1 := by
      intro k hk hkn
      by_contra hc
      push Not at hc
      have h1 : rd f k xh = 1 := le_antisymm (hmem k).2 hc
      have := rd_sticky f xh (n - k) k hk h1
      rw [show k + (n - k) = n by omega, hval] at this
      linarith
    have hmono : ∀ k, rd f k xh ≤ rd f (k + 1) xh := by
      intro k
      rcases k with _ | k
      · simp only [rd]; exact hxh.1.le
      · show rd f (k + 1) xh ≤ cut f k (rd f (k + 1) xh) _
        exact cut_ge f k _ _ (hmem (k + 1)).2
    -- the ripple equalities
    have heq : ∀ i, i + 1 < n →
        val f i (rd f i xh) (rd f (i + 1) xh) = val f i (rd f (i + 1) xh) (rd f (i + 2) xh) := by
      intro i hi
      have hlt := hlt1 (i + 2) (by omega) (by omega)
      have hrd : rd f (i + 2) xh = cut f i (rd f (i + 1) xh)
          (eval f i (rd f i xh) (rd f (i + 1) xh)) := rfl
      rw [hrd] at hlt ⊢
      rw [val_cut f hf i (by omega) _ _ (hmem (i + 1)) hlt]
      exact (eval_eq_val f i _ _ (hmono i)).symm
    -- strict increase and positivity
    have hstr : ∀ i, i + 1 < n → rd f i xh < rd f (i + 1) xh := by
      intro i
      induction i with
      | zero => intro _; simp only [rd]; exact hxh.1
      | succ i ih =>
        intro hi
        have hprev := ih (by omega)
        have hp := val_pos f hf lam hlam hL i (by omega) _ _ (hmem i).1 hprev (hmem (i + 1)).2
        rw [heq i (by omega)] at hp
        by_contra hc
        push Not at hc
        have : val f i (rd f (i + 1) xh) (rd f (i + 2) xh) ≤ 0 := by
          unfold val
          rw [intervalIntegral.integral_symm]
          have := val_nonneg f hf i (by omega) (rd f (i + 2) xh) (rd f (i + 1) xh)
            (hmem (i + 2)).1 hc (hmem (i + 1)).2
          unfold val at this
          linarith
        linarith
    refine ⟨by simp [rd], fun k _ => hmono k, (hmem n).2, le_of_eq hval.symm, ?_⟩
    intro i hi
    exact ⟨heq i hi, val_pos f hf lam hlam hL i (by omega) _ _ (hmem i).1 (hstr i hi)
      (hmem (i + 1)).2⟩
