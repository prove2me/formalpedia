-- Prove2me | solution 1 for LimitedPriceChanges.LowerBound.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:37:02.475479+00:00
-- url     : https://prove2.me/submissions/db94cc48-623e-42bd-8658-5fed7b6dbb1d

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_Policy

namespace LPC2Aux
open Finset

/-- restriction of a path to its first `t` coordinates -/
def pre {N : ℕ} (d : Fin N → Bool) (t : ℕ) (ht : t ≤ N) : Fin t → Bool :=
  fun i => d (Fin.castLE ht i)

/-- path weight of an adaptive Bernoulli kernel -/
noncomputable def W (k : (t : ℕ) → (Fin t → Bool) → ℝ) (N : ℕ) (d : Fin N → Bool) : ℝ :=
  ∏ t : Fin N, (if d t then k t.val (pre d t.val t.isLt.le) else 1 - k t.val (pre d t.val t.isLt.le))

lemma pre_snoc {N : ℕ} (d : Fin N → Bool) (b : Bool) (t : ℕ) (ht : t ≤ N) :
    pre (Fin.snoc (α := fun _ => Bool) d b) t (ht.trans (Nat.le_succ N)) = pre d t ht := by
  funext i
  simp only [pre]
  have : (Fin.castLE (ht.trans (Nat.le_succ N)) i : Fin (N+1)) = Fin.castSucc (Fin.castLE ht i) := by
    ext; simp
  rw [this, Fin.snoc_castSucc]

lemma pre_snoc_last {N : ℕ} (d : Fin N → Bool) (b : Bool) :
    pre (Fin.snoc (α := fun _ => Bool) d b) N (Nat.le_succ N) = d := by
  have := pre_snoc d b N le_rfl
  rw [this]; funext i; simp [pre]

lemma pre_pre {N : ℕ} (d : Fin N → Bool) (t u : ℕ) (htu : t ≤ u) (hu : u ≤ N) :
    pre (pre d u hu) t htu = pre d t (htu.trans hu) := by
  funext i; simp [pre]

lemma pre_self {N : ℕ} (d : Fin N → Bool) : pre d N le_rfl = d := by
  funext i; simp [pre]

lemma W_snoc (k : (t : ℕ) → (Fin t → Bool) → ℝ) (N : ℕ) (d : Fin N → Bool) (b : Bool) :
    W k (N+1) (Fin.snoc (α := fun _ => Bool) d b) =
      W k N d * (if b then k N d else 1 - k N d) := by
  unfold W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro t _
    have h1 : (Fin.snoc (α := fun _ => Bool) d b) (Fin.castSucc t) = d t := Fin.snoc_castSucc _ _ _
    have h2 := pre_snoc d b t.val t.isLt.le
    simp only [Fin.val_castSucc]
    rw [h1, h2]
  · simp only [Fin.snoc_last, Fin.val_last]
    rw [pre_snoc_last]

lemma sum_snoc {N : ℕ} (f : (Fin (N+1) → Bool) → ℝ) :
    ∑ d : Fin (N+1) → Bool, f d = ∑ d : Fin N → Bool, ∑ b : Bool, f (Fin.snoc (α := fun _ => Bool) d b) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (N+1) => Bool)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma marg (k : (t : ℕ) → (Fin t → Bool) → ℝ) (K : ℕ) (φ : (Fin K → Bool) → ℝ) :
    ∀ N (hK : K ≤ N), ∑ d : Fin N → Bool, W k N d * φ (pre d K hK) = ∑ e : Fin K → Bool, W k K e * φ e := by
  intro N hK
  induction N, hK using Nat.le_induction with
  | base => simp [pre_self]
  | succ N hKN ih =>
    rw [sum_snoc]
    rw [← ih]
    apply Finset.sum_congr rfl
    intro d _
    simp only [W_snoc, Fintype.sum_bool, if_true]
    have h1 := pre_snoc d true K hKN
    have h2 := pre_snoc d false K hKN
    rw [h1, h2]
    simp only [Bool.false_eq_true, if_false]
    ring

lemma W_nonneg (k : (t : ℕ) → (Fin t → Bool) → ℝ) (hk : ∀ t h, 0 ≤ k t h ∧ k t h ≤ 1) (N : ℕ)
    (d : Fin N → Bool) : 0 ≤ W k N d := by
  unfold W
  apply Finset.prod_nonneg
  intro t _
  split_ifs
  · exact (hk _ _).1
  · linarith [(hk t.val (pre d t.val t.isLt.le)).2]

lemma W_sum (k : (t : ℕ) → (Fin t → Bool) → ℝ) (N : ℕ) : ∑ d : Fin N → Bool, W k N d = 1 := by
  have := marg k 0 (fun _ => 1) N (Nat.zero_le N)
  simp only [mul_one] at this
  rw [this]
  simp [W]

lemma bc (k k' : (t : ℕ) → (Fin t → Bool) → ℝ) (hk : ∀ t h, 0 ≤ k t h ∧ k t h ≤ 1)
    (hk' : ∀ t h, 0 ≤ k' t h ∧ k' t h ≤ 1) (H : ℕ → ℝ) (hH0 : ∀ t, 0 ≤ H t)
    (hH : ∀ t h, 1 - (Real.sqrt (k t h) * Real.sqrt (k' t h) +
        Real.sqrt (1 - k t h) * Real.sqrt (1 - k' t h)) ≤ H t) :
    ∀ N, 1 - ∑ t ∈ Finset.range N, H t ≤
      ∑ d : Fin N → Bool, Real.sqrt (W k N d) * Real.sqrt (W k' N d) := by
  intro N
  induction N with
  | zero => simp [W]
  | succ N ih =>
    rw [sum_snoc]
    have hle : ∑ d : Fin N → Bool, Real.sqrt (W k N d) * Real.sqrt (W k' N d) ≤ 1 := by
      calc _ ≤ ∑ d : Fin N → Bool, (W k N d + W k' N d) / 2 := by
            apply Finset.sum_le_sum; intro d _
            have a1 := W_nonneg k hk N d
            have a2 := W_nonneg k' hk' N d
            nlinarith [Real.sq_sqrt a1, Real.sq_sqrt a2, sq_nonneg (Real.sqrt (W k N d) - Real.sqrt (W k' N d))]
        _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, W_sum, W_sum]; norm_num
    have hstep : ∀ d : Fin N → Bool,
        Real.sqrt (W k N d) * Real.sqrt (W k' N d) * (1 - H N) ≤
        ∑ b : Bool, Real.sqrt (W k (N+1) (Fin.snoc (α := fun _ => Bool) d b)) *
          Real.sqrt (W k' (N+1) (Fin.snoc (α := fun _ => Bool) d b)) := by
      intro d
      simp only [W_snoc, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      have a1 := W_nonneg k hk N d
      have a2 := W_nonneg k' hk' N d
      have b1 := hk N d
      have b2 := hk' N d
      rw [Real.sqrt_mul a1, Real.sqrt_mul a2, Real.sqrt_mul a1, Real.sqrt_mul a2]
      have := hH N d
      have s0 : 0 ≤ Real.sqrt (W k N d) * Real.sqrt (W k' N d) := by positivity
      nlinarith
    calc 1 - ∑ t ∈ Finset.range (N+1), H t
        = (1 - ∑ t ∈ Finset.range N, H t) - H N := by rw [Finset.sum_range_succ]; ring
      _ ≤ (∑ d : Fin N → Bool, Real.sqrt (W k N d) * Real.sqrt (W k' N d)) -
            (∑ d : Fin N → Bool, Real.sqrt (W k N d) * Real.sqrt (W k' N d)) * H N := by
          have := hH0 N
          nlinarith
      _ = ∑ d : Fin N → Bool, Real.sqrt (W k N d) * Real.sqrt (W k' N d) * (1 - H N) := by
          rw [← Finset.sum_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun d _ => hstep d)

/-- total variation from the Bhattacharyya coefficient -/
lemma tv_bc {ι : Type} [Fintype ι] (P Q φ : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) (hφ : ∀ i, 0 ≤ φ i ∧ φ i ≤ 1) :
    ∑ i, Q i * φ i - 2 * Real.sqrt (2 * (1 - ∑ i, Real.sqrt (P i) * Real.sqrt (Q i))) ≤
      ∑ i, P i * φ i := by
  set BC := ∑ i, Real.sqrt (P i) * Real.sqrt (Q i)
  have habs : ∑ i, |P i - Q i| ≤ 2 * Real.sqrt (2 * (1 - BC)) := by
    have e : ∀ i, |P i - Q i| = |Real.sqrt (P i) - Real.sqrt (Q i)| * (Real.sqrt (P i) + Real.sqrt (Q i)) := by
      intro i
      have : P i - Q i = (Real.sqrt (P i) - Real.sqrt (Q i)) * (Real.sqrt (P i) + Real.sqrt (Q i)) := by
        nlinarith [Real.sq_sqrt (hP i), Real.sq_sqrt (hQ i)]
      rw [this, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt (P i) + Real.sqrt (Q i))]
    simp_rw [e]
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => |Real.sqrt (P i) - Real.sqrt (Q i)|) (fun i => Real.sqrt (P i) + Real.sqrt (Q i))
    have s1 : ∑ i, |Real.sqrt (P i) - Real.sqrt (Q i)| ^ 2 = 2 - 2 * BC := by
      have : ∀ i, |Real.sqrt (P i) - Real.sqrt (Q i)| ^ 2 = P i + Q i - 2 * (Real.sqrt (P i) * Real.sqrt (Q i)) := by
        intro i; rw [sq_abs]; nlinarith [Real.sq_sqrt (hP i), Real.sq_sqrt (hQ i)]
      simp_rw [this]; rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hP1, hQ1, ← Finset.mul_sum]; ring
    have s2 : ∑ i, (Real.sqrt (P i) + Real.sqrt (Q i)) ^ 2 = 2 + 2 * BC := by
      have : ∀ i, (Real.sqrt (P i) + Real.sqrt (Q i)) ^ 2 = P i + Q i + 2 * (Real.sqrt (P i) * Real.sqrt (Q i)) := by
        intro i; nlinarith [Real.sq_sqrt (hP i), Real.sq_sqrt (hQ i)]
      simp_rw [this]; rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hP1, hQ1, ← Finset.mul_sum]; ring
    rw [s1, s2] at cs
    have hBC0 : 0 ≤ BC := Finset.sum_nonneg (fun i _ => by positivity)
    have hBC1 : BC ≤ 1 := by
      have : 0 ≤ 2 - 2 * BC := by rw [← s1]; positivity
      linarith
    have hS0 : 0 ≤ ∑ i, |Real.sqrt (P i) - Real.sqrt (Q i)| * (Real.sqrt (P i) + Real.sqrt (Q i)) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    rw [show (2:ℝ) * Real.sqrt (2 * (1 - BC)) = Real.sqrt (4 * (2 * (1 - BC))) by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), show (4:ℝ) = 2^2 by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have : ∑ i, Q i * φ i - ∑ i, P i * φ i ≤ ∑ i, |P i - Q i| := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro i _
    have := hφ i
    have h2 : Q i * φ i - P i * φ i = (Q i - P i) * φ i := by ring
    rw [h2]
    calc (Q i - P i) * φ i ≤ |Q i - P i| * φ i := by
          apply mul_le_mul_of_nonneg_right (le_abs_self _) this.1
      _ ≤ |Q i - P i| * 1 := by apply mul_le_mul_of_nonneg_left this.2 (abs_nonneg _)
      _ = |P i - Q i| := by rw [mul_one, abs_sub_comm]
  linarith

open LimitedPriceChanges.LowerBound

lemma sq_sqrt_diff_le (a b : ℝ) (ha : 1/12 ≤ a) (hb : 1/12 ≤ b) :
    (Real.sqrt a - Real.sqrt b)^2 ≤ 6 * (a - b)^2 := by
  have hu := Real.sq_sqrt (show (0:ℝ) ≤ a by linarith)
  have hv := Real.sq_sqrt (show (0:ℝ) ≤ b by linarith)
  have u0 := Real.sqrt_nonneg a
  have v0 := Real.sqrt_nonneg b
  have h : (Real.sqrt a - Real.sqrt b)^2 * (Real.sqrt a + Real.sqrt b)^2 = (a-b)^2 := by
    nth_rewrite 3 [← hu]; nth_rewrite 3 [← hv]; ring
  have h2 : 1/6 ≤ (Real.sqrt a + Real.sqrt b)^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg (Real.sqrt a - Real.sqrt b))]

lemma nu_eq (p z : ℝ) (hp : p ∈ Set.Icc (1:ℝ) 6) (hz : z ∈ Set.Icc (1/6 : ℝ) (1/4)) :
    nu p z = 1 - p * z / 2 := by
  unfold nu
  obtain ⟨hp1, hp2⟩ := hp; obtain ⟨hz1, hz2⟩ := hz
  apply max_eq_right
  nlinarith

lemma nu_bounds (p z : ℝ) (hp : p ∈ Set.Icc (1:ℝ) 6) (hz : z ∈ Set.Icc (1/6 : ℝ) (1/4)) :
    1/4 ≤ nu p z ∧ nu p z ≤ 11/12 := by
  rw [nu_eq p z hp hz]
  obtain ⟨hp1, hp2⟩ := hp; obtain ⟨hz1, hz2⟩ := hz
  constructor <;> nlinarith

lemma hell (p z z' : ℝ) (hp : p ∈ Set.Icc (1:ℝ) 6) (hz : z ∈ Set.Icc (1/6 : ℝ) (1/4))
    (hz' : z' ∈ Set.Icc (1/6 : ℝ) (1/4)) :
    1 - (Real.sqrt (nu p z) * Real.sqrt (nu p z') +
        Real.sqrt (1 - nu p z) * Real.sqrt (1 - nu p z')) ≤ 54 * (z - z')^2 := by
  have e1 := nu_eq p z hp hz
  have e2 := nu_eq p z' hp hz'
  obtain ⟨a1, a2⟩ := nu_bounds p z hp hz
  obtain ⟨b1, b2⟩ := nu_bounds p z' hp hz'
  have k1 := sq_sqrt_diff_le (nu p z) (nu p z') (by linarith) (by linarith)
  have k2 := sq_sqrt_diff_le (1 - nu p z) (1 - nu p z') (by linarith) (by linarith)
  have q1 := Real.sq_sqrt (show (0:ℝ) ≤ nu p z by linarith)
  have q2 := Real.sq_sqrt (show (0:ℝ) ≤ nu p z' by linarith)
  have q3 := Real.sq_sqrt (show (0:ℝ) ≤ 1 - nu p z by linarith)
  have q4 := Real.sq_sqrt (show (0:ℝ) ≤ 1 - nu p z' by linarith)
  have hab : (nu p z - nu p z')^2 ≤ 9 * (z - z')^2 := by
    rw [e1, e2]
    have : (1 - p * z / 2 - (1 - p * z' / 2))^2 = (p/2)^2 * (z - z')^2 := by ring
    rw [this]
    obtain ⟨hp1, hp2⟩ := hp
    have : (p/2)^2 ≤ 9 := by nlinarith
    nlinarith [sq_nonneg (z - z')]
  have hab2 : (1 - nu p z - (1 - nu p z'))^2 = (nu p z - nu p z')^2 := by ring
  nlinarith

lemma regret_eq (p z : ℝ) (hp : p ∈ Set.Icc (1:ℝ) 6) (hz : z ∈ Set.Icc (1/6 : ℝ) (1/4)) :
    Gstar z - rev p z = z / 2 * (p - 1/z)^2 := by
  unfold Gstar rev
  rw [nu_eq p z hp hz]
  have : z ≠ 0 := by have := hz.1; intro h; rw [h] at this; norm_num at this
  field_simp
  ring

/-! ### The instance family -/

noncomputable def aa (m : ℕ) : ℝ := 1 / (100 * 2^(m+1) * ((m:ℝ)+1)^2)
noncomputable def ee (r : ℝ) (i : ℕ) : ℝ := 1 / (Real.sqrt r)^i
def sg (b : Bool) : ℝ := if b then 1 else -1
noncomputable def zt (m : ℕ) (r : ℝ) (k : ℕ) (ζ : Fin (m+1) → Bool) : ℝ :=
  1/5 + aa m * ∑ i : Fin (m+1), (if i.val ≤ k then sg (ζ i) * ee r i else 0)
def flp {m : ℕ} (j : Fin (m+1)) (ζ : Fin (m+1) → Bool) : Fin (m+1) → Bool :=
  Function.update ζ j (!ζ j)

lemma aa_pos (m : ℕ) : 0 < aa m := by unfold aa; positivity

lemma aa_mul (m : ℕ) : aa m * ((m:ℝ)+1) ≤ 1/100 := by
  unfold aa
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : (1:ℝ) ≤ 2^(m+1) := one_le_pow₀ (by norm_num)
  have h2 : (1:ℝ) ≤ (m:ℝ) + 1 := by have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith
  nlinarith [mul_le_mul h1 (le_refl (((m:ℝ)+1))) (by positivity) (by positivity)]

lemma ee_pos (r : ℝ) (hr : 1 ≤ r) (i : ℕ) : 0 < ee r i := by
  unfold ee; have : 0 < Real.sqrt r := Real.sqrt_pos.2 (by linarith); positivity

lemma ee_le_one (r : ℝ) (hr : 1 ≤ r) (i : ℕ) : ee r i ≤ 1 := by
  unfold ee
  have : 1 ≤ Real.sqrt r := by rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hr
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ this

lemma ee_anti (r : ℝ) (hr : 1 ≤ r) (i j : ℕ) (hij : i ≤ j) : ee r j ≤ ee r i := by
  unfold ee
  have : 1 ≤ Real.sqrt r := by rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hr
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ this hij

lemma ee_succ (r : ℝ) (hr : 1 ≤ r) (i : ℕ) : ee r (i+1) = ee r i / Real.sqrt r := by
  unfold ee; rw [pow_succ]; field_simp

lemma ee_sq (r : ℝ) (hr : 1 ≤ r) (i : ℕ) : ee r i ^ 2 = 1 / r^i := by
  unfold ee; rw [div_pow, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by linarith)]; simp

lemma zt_mem (m : ℕ) (r : ℝ) (hr : 1 ≤ r) (k : ℕ) (ζ : Fin (m+1) → Bool) :
    zt m r k ζ ∈ Set.Icc (1/6 : ℝ) (1/4) := by
  unfold zt
  have hs : |∑ i : Fin (m+1), (if i.val ≤ k then sg (ζ i) * ee r i else 0)| ≤ (m:ℝ) + 1 := by
    calc _ ≤ ∑ i : Fin (m+1), |(if i.val ≤ k then sg (ζ i) * ee r i else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (m+1), (1:ℝ) := by
          apply Finset.sum_le_sum; intro i _
          split_ifs
          · rw [abs_mul]
            have : |sg (ζ i)| = 1 := by unfold sg; split_ifs <;> simp
            rw [this, one_mul, abs_of_pos (ee_pos r hr i)]; exact ee_le_one r hr i
          · simp
      _ = (m:ℝ) + 1 := by simp
  have ha := aa_mul m
  have ha0 := aa_pos m
  have h3 := abs_le.1 hs
  constructor <;> nlinarith

lemma zt_diff (m : ℕ) (r : ℝ) (hr : 1 ≤ r) (k : ℕ) (ζ : Fin (m+1) → Bool) :
    |zt m r m ζ - zt m r k ζ| ≤ aa m * ((m:ℝ)+1) * ee r (k+1) := by
  unfold zt
  have : (1/5 + aa m * ∑ i : Fin (m+1), (if i.val ≤ m then sg (ζ i) * ee r i else 0)) -
      (1/5 + aa m * ∑ i : Fin (m+1), (if i.val ≤ k then sg (ζ i) * ee r i else 0)) =
      aa m * ∑ i : Fin (m+1), (if k < i.val then sg (ζ i) * ee r i else 0) := by
    rw [add_sub_add_left_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1; apply Finset.sum_congr rfl; intro i _
    have him : i.val ≤ m := Nat.lt_succ_iff.1 i.isLt
    by_cases hk : i.val ≤ k
    · simp [hk, him, show ¬ k < i.val by omega]
    · simp [hk, him, show k < i.val by omega]
  rw [this, abs_mul, abs_of_pos (aa_pos m), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (aa_pos m).le
  calc _ ≤ ∑ i : Fin (m+1), |(if k < i.val then sg (ζ i) * ee r i else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (m+1), ee r (k+1) := by
        apply Finset.sum_le_sum; intro i _
        split_ifs with h
        · rw [abs_mul]
          have : |sg (ζ i)| = 1 := by unfold sg; split_ifs <;> simp
          rw [this, one_mul, abs_of_pos (ee_pos r hr i)]; exact ee_anti r hr _ _ h
        · simp; exact (ee_pos r hr _).le
    _ = ((m:ℝ)+1) * ee r (k+1) := by simp

lemma zt_flp_inv (m : ℕ) (r : ℝ) (k : ℕ) (j : Fin (m+1)) (hkj : k < j.val) (ζ : Fin (m+1) → Bool) :
    zt m r k (flp j ζ) = zt m r k ζ := by
  unfold zt; congr 2; apply Finset.sum_congr rfl; intro i _
  split_ifs with h
  · have : i ≠ j := by intro e; subst e; omega
    simp [flp, Function.update_of_ne this]
  · rfl

lemma zt_flp_diff (m : ℕ) (r : ℝ) (hr : 1 ≤ r) (j : Fin (m+1)) (ζ : Fin (m+1) → Bool) :
    |zt m r j.val ζ - zt m r j.val (flp j ζ)| = 2 * aa m * ee r j.val := by
  unfold zt
  rw [add_sub_add_left_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · simp only [le_refl, if_true, flp, Function.update_self]
    have : sg (ζ j) * ee r j.val - sg (!ζ j) * ee r j.val = 2 * sg (ζ j) * ee r j.val := by
      cases ζ j <;> simp [sg] <;> ring
    rw [this, abs_mul, abs_mul, abs_mul, abs_of_pos (aa_pos m), abs_of_pos (ee_pos r hr _), abs_two]
    · have : |sg (ζ j)| = 1 := by unfold sg; split_ifs <;> simp
      rw [this]; ring
  · intro i _ hij
    simp [flp, Function.update_of_ne hij]
  · simp

lemma flp_flp {m : ℕ} (j : Fin (m+1)) (ζ : Fin (m+1) → Bool) : flp j (flp j ζ) = ζ := by
  funext i; by_cases h : i = j
  · subst h; simp [flp]
  · simp [flp, Function.update_of_ne h]

lemma flp_self {m : ℕ} (j : Fin (m+1)) (ζ : Fin (m+1) → Bool) : flp j ζ j = !ζ j := by
  simp [flp]

lemma flp_ne {m : ℕ} (j l : Fin (m+1)) (h : l ≠ j) (ζ : Fin (m+1) → Bool) : flp j ζ l = ζ l := by
  simp [flp, Function.update_of_ne h]

lemma flp_comm {m : ℕ} (j l : Fin (m+1)) (h : l ≠ j) (ζ : Fin (m+1) → Bool) :
    flp j (flp l ζ) = flp l (flp j ζ) := by
  funext i
  by_cases hij : i = j
  · subst hij; simp [flp, Function.update_of_ne (Ne.symm h)]
  · by_cases hil : i = l
    · subst hil; simp [flp, Function.update_of_ne hij]
    · simp [flp, Function.update_of_ne hij, Function.update_of_ne hil]

/-- the "wrong side at level ℓ" indicator -/
noncomputable def J (m : ℕ) (r : ℝ) (l : Fin (m+1)) (ζ : Fin (m+1) → Bool) (p : ℝ) : ℝ :=
  if |p - 1 / zt m r l.val ζ| > |p - 1 / zt m r l.val (flp l ζ)| ∨
      (|p - 1 / zt m r l.val ζ| = |p - 1 / zt m r l.val (flp l ζ)| ∧ ζ l = true) then 1 else 0

lemma J_sum (m : ℕ) (r : ℝ) (l : Fin (m+1)) (ζ : Fin (m+1) → Bool) (p : ℝ) :
    J m r l ζ p + J m r l (flp l ζ) p = 1 := by
  unfold J
  rw [flp_flp, flp_self]
  set A := |p - 1 / zt m r l.val ζ|
  set B := |p - 1 / zt m r l.val (flp l ζ)|
  rcases lt_trichotomy A B with h | h | h
  · have : ¬ (A > B ∨ (A = B ∧ ζ l = true)) := by
      rintro (h' | ⟨h', _⟩) <;> linarith
    rw [if_neg this, if_pos (Or.inl h)]; norm_num
  · cases hz : ζ l <;> simp [h]
  · have : ¬ (B > A ∨ (B = A ∧ (!ζ l) = true)) := by
      rintro (h' | ⟨h', _⟩) <;> linarith
    rw [if_pos (Or.inl h), if_neg this]; norm_num

lemma J_inv (m : ℕ) (r : ℝ) (l j : Fin (m+1)) (hlj : l.val < j.val) (ζ : Fin (m+1) → Bool) (p : ℝ) :
    J m r l (flp j ζ) p = J m r l ζ p := by
  have hne : l ≠ j := by intro e; subst e; omega
  unfold J
  rw [zt_flp_inv m r l.val j hlj]
  rw [show flp l (flp j ζ) = flp j (flp l ζ) from (flp_comm j l hne ζ).symm,
    zt_flp_inv m r l.val j hlj, flp_ne j l hne]

lemma J_nonneg (m : ℕ) (r : ℝ) (l : Fin (m+1)) (ζ : Fin (m+1) → Bool) (p : ℝ) :
    0 ≤ J m r l ζ p ∧ J m r l ζ p ≤ 1 := by
  unfold J; split_ifs <;> norm_num

lemma J_regret (m : ℕ) (r : ℝ) (hr : (40 * ((m:ℝ)+1))^2 ≤ r) (l : Fin (m+1))
    (ζ : Fin (m+1) → Bool) (p : ℝ) (hp : p ∈ Set.Icc (1:ℝ) 6) (hJ : J m r l ζ p ≠ 0) :
    aa m ^ 2 * ee r l.val ^ 2 ≤ Gstar (zt m r m ζ) - rev p (zt m r m ζ) := by
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hr1 : 1 ≤ r := by nlinarith
  have hsr : 40 * ((m:ℝ)+1) ≤ Real.sqrt r := by
    rw [show 40 * ((m:ℝ)+1) = Real.sqrt ((40 * ((m:ℝ)+1))^2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hr
  set x := zt m r l.val ζ with hx
  set y := zt m r l.val (flp l ζ) with hy
  set z := zt m r m ζ with hz
  have mx := zt_mem m r hr1 l.val ζ
  have my := zt_mem m r hr1 l.val (flp l ζ)
  have mz := zt_mem m r hr1 m ζ
  rw [← hx] at mx; rw [← hy] at my; rw [← hz] at mz
  obtain ⟨x1, x2⟩ := mx; obtain ⟨y1, y2⟩ := my; obtain ⟨z1, z2⟩ := mz
  have hxy : |x - y| = 2 * aa m * ee r l.val := zt_flp_diff m r hr1 l ζ
  have hzx : |z - x| ≤ aa m * ((m:ℝ)+1) * ee r (l.val+1) := zt_diff m r hr1 l.val ζ
  rw [ee_succ r hr1] at hzx
  have he := ee_pos r hr1 l.val
  have ha := aa_pos m
  have hsr0 : 0 < Real.sqrt r := by linarith
  -- |z - x| ≤ aa ε / 40
  have hzx' : |z - x| ≤ aa m * ee r l.val / 40 := by
    calc |z - x| ≤ aa m * ((m:ℝ)+1) * (ee r l.val / Real.sqrt r) := hzx
      _ ≤ aa m * ((m:ℝ)+1) * (ee r l.val / (40 * ((m:ℝ)+1))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_left he.le (by positivity) hsr
      _ = aa m * ee r l.val / 40 := by field_simp
  -- J = 1 gives |p - 1/x| ≥ |p - 1/y|
  have hJ' : |p - 1/y| ≤ |p - 1/x| := by
    unfold J at hJ
    split_ifs at hJ with h
    · rcases h with h | ⟨h, _⟩
      · exact h.le
      · exact h.ge
    · exact absurd rfl hJ
  have inv_xy : 16 * |x - y| ≤ |1/x - 1/y| := by
    have e : 1/x - 1/y = (y - x) * (1 / (x*y)) := by field_simp
    rw [e, abs_mul, abs_sub_comm y x, abs_of_pos (by positivity : (0:ℝ) < 1/(x*y))]
    have : 16 ≤ 1/(x*y) := by
      rw [le_one_div (by norm_num) (by positivity)]; nlinarith
    nlinarith [abs_nonneg (x - y)]
  have inv_zx : |1/z - 1/x| ≤ 36 * |z - x| := by
    have e : 1/z - 1/x = (x - z) * (1 / (z*x)) := by field_simp
    rw [e, abs_mul, abs_sub_comm x z, abs_of_pos (by positivity : (0:ℝ) < 1/(z*x))]
    have : 1/(z*x) ≤ 36 := by
      rw [one_div_le (by positivity) (by norm_num)]; nlinarith
    nlinarith [abs_nonneg (z - x)]
  have t1 : |1/x - 1/y| ≤ |p - 1/x| + |p - 1/y| := by
    calc |1/x - 1/y| = |(p - 1/y) - (p - 1/x)| := by ring_nf
      _ ≤ |p - 1/y| + |p - 1/x| := abs_sub _ _
      _ = _ := by ring
  have t2 : |p - 1/x| ≤ |p - 1/z| + |1/z - 1/x| := by
    calc |p - 1/x| = |(p - 1/z) + (1/z - 1/x)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have key : 15 * (aa m * ee r l.val) ≤ |p - 1/z| := by
    rw [hxy] at inv_xy
    nlinarith
  rw [regret_eq p z hp ⟨z1, z2⟩]
  have hsq : (15 * (aa m * ee r l.val))^2 ≤ (p - 1/z)^2 := by
    rw [← sq_abs (p - 1/z)]
    exact pow_le_pow_left₀ (by positivity) key 2
  nlinarith

/-! ### Epoch boundaries -/

noncomputable def nn (r : ℝ) (l : ℕ) : ℕ := ⌊r ^ l⌋₊ - 1

lemma floor_pow_ge_one (r : ℝ) (hr : 1 ≤ r) (l : ℕ) : 1 ≤ ⌊r ^ l⌋₊ := by
  rw [Nat.one_le_floor_iff]; exact one_le_pow₀ hr

lemma nn_cast (r : ℝ) (hr : 1 ≤ r) (l : ℕ) : (nn r l : ℝ) = ⌊r ^ l⌋₊ - 1 := by
  unfold nn; rw [Nat.cast_sub (floor_pow_ge_one r hr l)]; simp

lemma nn_zero (r : ℝ) : nn r 0 = 0 := by simp [nn]

lemma nn_le (r : ℝ) (hr : 1 ≤ r) (l : ℕ) : (nn r l : ℝ) ≤ r ^ l := by
  rw [nn_cast r hr]
  have := Nat.floor_le (pow_nonneg (by linarith : (0:ℝ) ≤ r) l)
  linarith

lemma nn_gap (r : ℝ) (hr : 4 ≤ r) (l : ℕ) : r ^ (l+1) / 2 ≤ (nn r (l+1) : ℝ) - nn r l := by
  rw [nn_cast r (by linarith), nn_cast r (by linarith)]
  have h1 := Nat.lt_floor_add_one (r ^ (l+1))
  have h2 := Nat.floor_le (pow_nonneg (by linarith : (0:ℝ) ≤ r) l)
  have h3 : 1 ≤ r ^ l := one_le_pow₀ (by linarith)
  rw [pow_succ] at h1 ⊢
  nlinarith

lemma nn_strictMono (r : ℝ) (hr : 4 ≤ r) : StrictMono (nn r) := by
  apply strictMono_nat_of_lt_succ
  intro l
  have := nn_gap r hr l
  have : 0 < r ^ (l+1) / 2 := by positivity
  exact_mod_cast (show (nn r l : ℝ) < nn r (l+1) by linarith)

lemma nn_exists (r : ℝ) (hr : 4 ≤ r) (t : ℕ) : ∃ k, t < nn r (k+1) :=
  ⟨t, Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ((nn_strictMono r hr).id_le (t+1))⟩

open Classical in
noncomputable def Lf (r : ℝ) (t : ℕ) : ℕ :=
  if h : ∃ k, t < nn r (k+1) then Nat.find h else 0

lemma Lf_spec (r : ℝ) (hr : 4 ≤ r) (t : ℕ) : t < nn r (Lf r t + 1) := by
  classical
  have h := nn_exists r hr t
  unfold Lf; rw [dif_pos h]; convert Nat.find_spec h

lemma Lf_lt (r : ℝ) (hr : 4 ≤ r) (t j : ℕ) (ht : t < nn r j) : Lf r t < j := by
  classical
  have h := nn_exists r hr t
  rcases j with _ | j
  · rw [nn_zero] at ht; omega
  · unfold Lf; rw [dif_pos h]
    have := Nat.find_min' h ht
    convert Nat.lt_succ_of_le this

/-! ### The reference law and the exact probability of the bad event -/

def rs {N : ℕ} (e : Fin N → Bool) (t : ℕ) : Fin t → Bool :=
  fun i => if h : i.val < N then e ⟨i.val, h⟩ else false

lemma rs_pre {N : ℕ} (e : Fin N → Bool) (u t : ℕ) (hu : u ≤ N) (htu : t ≤ u) :
    rs (pre e u hu) t = rs e t := by
  funext i
  have h1 : i.val < u := lt_of_lt_of_le i.isLt htu
  simp [rs, pre, h1, lt_of_lt_of_le h1 hu]

lemma W_congr (k k' : (t : ℕ) → (Fin t → Bool) → ℝ) (N : ℕ)
    (h : ∀ t, t < N → ∀ x, k t x = k' t x) (d : Fin N → Bool) : W k N d = W k' N d := by
  unfold W; apply Finset.prod_congr rfl; intro t _
  rw [h t.val t.isLt]

noncomputable def Gj (m : ℕ) (r : ℝ) (pr : (t : ℕ) → (Fin t → Bool) → ℝ) (j : ℕ)
    (ζ : Fin (m+1) → Bool) {N : ℕ} (e : Fin N → Bool) : ℝ :=
  ∏ l : Fin (m+1), (if l.val < j then J m r l ζ (pr (nn r l) (rs e (nn r l))) else 1)

noncomputable def kQ (m : ℕ) (r : ℝ) (pr : (t : ℕ) → (Fin t → Bool) → ℝ)
    (ζ : Fin (m+1) → Bool) : (t : ℕ) → (Fin t → Bool) → ℝ :=
  fun t h => nu (pr t h) (zt m r (Lf r t) ζ)

noncomputable def kP (m : ℕ) (r : ℝ) (pr : (t : ℕ) → (Fin t → Bool) → ℝ)
    (ζ : Fin (m+1) → Bool) : (t : ℕ) → (Fin t → Bool) → ℝ :=
  fun t h => nu (pr t h) (zt m r m ζ)

lemma Gj_nonneg (m : ℕ) (r : ℝ) (pr : (t : ℕ) → (Fin t → Bool) → ℝ) (j : ℕ)
    (ζ : Fin (m+1) → Bool) {N : ℕ} (e : Fin N → Bool) :
    0 ≤ Gj m r pr j ζ e ∧ Gj m r pr j ζ e ≤ 1 := by
  unfold Gj
  constructor
  · apply Finset.prod_nonneg; intro l _; split_ifs
    · exact (J_nonneg _ _ _ _ _).1
    · norm_num
  · apply Finset.prod_le_one
    · intro l _; split_ifs
      · exact (J_nonneg _ _ _ _ _).1
      · norm_num
    · intro l _; split_ifs
      · exact (J_nonneg _ _ _ _ _).2
      · norm_num

lemma Gj_pre (m : ℕ) (r : ℝ) (hr : 4 ≤ r) (pr : (t : ℕ) → (Fin t → Bool) → ℝ) (j : ℕ)
    (ζ : Fin (m+1) → Bool) {N : ℕ} (e : Fin N → Bool) (u : ℕ) (hu : u ≤ N)
    (hju : ∀ l, l < j → nn r l ≤ u) :
    Gj m r pr j ζ (pre e u hu) = Gj m r pr j ζ e := by
  unfold Gj; apply Finset.prod_congr rfl; intro l _
  split_ifs with h
  · rw [rs_pre e u (nn r l) hu (hju l h)]
  · rfl

lemma sum_flip {m : ℕ} (j : Fin (m+1)) (f g : (Fin (m+1) → Bool) → ℝ)
    (hf : ∀ ζ, f (flp j ζ) = f ζ) (hg : ∀ ζ, g ζ + g (flp j ζ) = 1) :
    ∑ ζ, f ζ * g ζ = (∑ ζ, f ζ) / 2 := by
  have hinv : Function.Involutive (flp j) := fun ζ => flp_flp j ζ
  have h1 : ∑ ζ, f ζ * g ζ = ∑ ζ, f (flp j ζ) * g (flp j ζ) :=
    (Equiv.sum_comp hinv.toPerm (fun ζ => f ζ * g ζ)).symm
  have h2 : ∑ ζ, f (flp j ζ) * g (flp j ζ) = ∑ ζ, (f ζ - f ζ * g ζ) := by
    apply Finset.sum_congr rfl; intro ζ _
    rw [hf]; have := hg ζ; rw [show g (flp j ζ) = 1 - g ζ by linarith]; ring
  rw [Finset.sum_sub_distrib] at h2
  linarith

noncomputable def VV (m : ℕ) (r : ℝ) (pr : (t : ℕ) → (Fin t → Bool) → ℝ) (j : ℕ) : ℝ :=
  ∑ ζ : Fin (m+1) → Bool, ∑ e : Fin (nn r j) → Bool, W (kQ m r pr ζ) (nn r j) e * Gj m r pr j ζ e

lemma VV_zero (m : ℕ) (r : ℝ) (pr : (t : ℕ) → (Fin t → Bool) → ℝ) :
    VV m r pr 0 = 2 ^ (m+1) := by
  unfold VV
  have : ∀ ζ : Fin (m+1) → Bool, ∑ e : Fin (nn r 0) → Bool,
      W (kQ m r pr ζ) (nn r 0) e * Gj m r pr 0 ζ e = 1 := by
    intro ζ
    have hG : ∀ e : Fin (nn r 0) → Bool, Gj m r pr 0 ζ e = 1 := by
      intro e; unfold Gj; simp
    simp_rw [hG, mul_one]; exact W_sum _ _
  simp_rw [this]; simp

lemma VV_succ (m : ℕ) (r : ℝ) (hr : 4 ≤ r) (pr : (t : ℕ) → (Fin t → Bool) → ℝ)
    (j : Fin (m+1)) : VV m r pr (j.val+1) = VV m r pr j.val / 2 := by
  have hmono := nn_strictMono r hr
  have hle : nn r j.val ≤ nn r (j.val+1) := (hmono (Nat.lt_succ_self _)).le
  unfold VV
  -- marginalize
  have step1 : ∀ ζ : Fin (m+1) → Bool,
      ∑ e : Fin (nn r (j.val+1)) → Bool, W (kQ m r pr ζ) (nn r (j.val+1)) e * Gj m r pr (j.val+1) ζ e
      = ∑ e : Fin (nn r j.val) → Bool, W (kQ m r pr ζ) (nn r j.val) e * Gj m r pr (j.val+1) ζ e := by
    intro ζ
    rw [← marg (kQ m r pr ζ) (nn r j.val) (fun e => Gj m r pr (j.val+1) ζ e) (nn r (j.val+1)) hle]
    apply Finset.sum_congr rfl; intro e _
    rw [Gj_pre m r hr pr (j.val+1) ζ e (nn r j.val) hle]
    intro l hl; exact hmono.monotone (Nat.lt_succ_iff.1 hl)
  simp_rw [step1]
  -- split the product
  have split : ∀ (ζ : Fin (m+1) → Bool) (e : Fin (nn r j.val) → Bool),
      Gj m r pr (j.val+1) ζ e = Gj m r pr j.val ζ e * J m r j ζ (pr (nn r j.val) (rs e (nn r j.val))) := by
    intro ζ e
    unfold Gj
    have hJ : J m r j ζ (pr (nn r j.val) (rs e (nn r j.val))) =
        ∏ l : Fin (m+1), (if l = j then J m r l ζ (pr (nn r l) (rs e (nn r l))) else 1) := by
      rw [Finset.prod_ite_eq']; simp
    rw [hJ, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro l _
    by_cases h1 : l.val < j.val
    · have : l ≠ j := by intro e; subst e; omega
      simp [h1, Nat.lt_succ_of_lt h1, this]
    · by_cases h2 : l = j
      · subst h2; simp
      · have : ¬ l.val < j.val + 1 := by
          intro h; apply h2; apply Fin.ext; omega
        simp [h1, this, h2]
  simp_rw [split]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl; intro e _
  simp_rw [← mul_assoc]
  apply sum_flip j
  · intro ζ
    congr 1
    · apply W_congr
      intro t ht x
      unfold kQ
      rw [zt_flp_inv m r (Lf r t) j (Lf_lt r hr t j.val ht)]
    · unfold Gj; apply Finset.prod_congr rfl; intro l _
      split_ifs with h
      · exact J_inv m r l j h ζ _
      · rfl
  · intro ζ; exact J_sum m r j ζ _

lemma VV_top (m : ℕ) (r : ℝ) (hr : 4 ≤ r) (pr : (t : ℕ) → (Fin t → Bool) → ℝ) :
    VV m r pr (m+1) = 1 := by
  have : ∀ j, j ≤ m + 1 → VV m r pr j = 2 ^ (m+1) / 2 ^ j := by
    intro j
    induction j with
    | zero => intro _; rw [VV_zero]; simp
    | succ j ih =>
      intro hj
      have := VV_succ m r hr pr ⟨j, by omega⟩
      simp only at this
      rw [this, ih (by omega), pow_succ]; field_simp; ring
  rw [this (m+1) le_rfl]; field_simp

lemma zt_ge (m : ℕ) (r : ℝ) (k : ℕ) (hk : m ≤ k) (ζ : Fin (m+1) → Bool) :
    zt m r k ζ = zt m r m ζ := by
  unfold zt; congr 2; apply Finset.sum_congr rfl; intro i _
  have : i.val ≤ m := Nat.lt_succ_iff.1 i.isLt
  simp [this, show i.val ≤ k by omega]

lemma H_le (m : ℕ) (r : ℝ) (hr : 4 ≤ r) (ζ : Fin (m+1) → Bool) (t : ℕ) :
    54 * (zt m r m ζ - zt m r (Lf r t) ζ)^2 ≤
      ∑ k ∈ Finset.range (m+1), (if t < nn r (k+1) then 54 * aa m ^ 2 * ((m:ℝ)+1)^2 / r^(k+1) else 0) := by
  have hr1 : 1 ≤ r := by linarith
  have hnn : ∀ k ∈ Finset.range (m+1), 0 ≤ (if t < nn r (k+1) then 54 * aa m ^ 2 * ((m:ℝ)+1)^2 / r^(k+1) else 0) := by
    intro k _; split_ifs
    · have : 0 < r := by linarith
      positivity
    · rfl
  by_cases hk : m ≤ Lf r t
  · rw [zt_ge m r _ hk]; simp only [sub_self]; norm_num
    exact Finset.sum_nonneg hnn
  · push Not at hk
    have hmem : Lf r t ∈ Finset.range (m+1) := Finset.mem_range.2 (by omega)
    refine le_trans ?_ (Finset.single_le_sum hnn hmem)
    rw [if_pos (Lf_spec r hr t)]
    have hd := zt_diff m r hr1 (Lf r t) ζ
    have hsq : (zt m r m ζ - zt m r (Lf r t) ζ)^2 ≤ (aa m * ((m:ℝ)+1) * ee r (Lf r t + 1))^2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    rw [mul_pow, ee_sq r hr1, mul_pow] at hsq
    have : 54 * aa m ^ 2 * ((m:ℝ)+1)^2 / r^(Lf r t + 1) = 54 * (aa m ^ 2 * ((m:ℝ)+1)^2 * (1 / r^(Lf r t + 1))) := by
      ring
    rw [this]; linarith

lemma Hsum_le (m : ℕ) (r : ℝ) (hr : 4 ≤ r) (ζ : Fin (m+1) → Bool) (N : ℕ) :
    ∑ t ∈ Finset.range N, 54 * (zt m r m ζ - zt m r (Lf r t) ζ)^2 ≤ 54 * aa m ^ 2 * ((m:ℝ)+1)^3 := by
  have hr0 : 0 < r := by linarith
  calc _ ≤ ∑ t ∈ Finset.range N, ∑ k ∈ Finset.range (m+1),
        (if t < nn r (k+1) then 54 * aa m ^ 2 * ((m:ℝ)+1)^2 / r^(k+1) else 0) :=
        Finset.sum_le_sum (fun t _ => H_le m r hr ζ t)
    _ = ∑ k ∈ Finset.range (m+1), ∑ t ∈ Finset.range N,
        (if t < nn r (k+1) then 54 * aa m ^ 2 * ((m:ℝ)+1)^2 / r^(k+1) else 0) := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range (m+1), 54 * aa m ^ 2 * ((m:ℝ)+1)^2 := by
        apply Finset.sum_le_sum; intro k _
        set c := 54 * aa m ^ 2 * ((m:ℝ)+1)^2 / r^(k+1)
        have hc : 0 ≤ c := by positivity
        rw [← Finset.sum_filter]
        calc ∑ t ∈ Finset.filter (fun t => t < nn r (k+1)) (Finset.range N), c
            ≤ ∑ t ∈ Finset.range (nn r (k+1)), c := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro t ht; simp only [Finset.mem_filter] at ht; exact Finset.mem_range.2 ht.2
              · intros; exact hc
          _ = (nn r (k+1) : ℝ) * c := by simp
          _ ≤ r^(k+1) * c := mul_le_mul_of_nonneg_right (nn_le r (by linarith) _) hc
          _ = 54 * aa m ^ 2 * ((m:ℝ)+1)^2 := by
              simp only [c]; field_simp
    _ = 54 * aa m ^ 2 * ((m:ℝ)+1)^3 := by simp; ring

lemma const_ok (m : ℕ) :
    2 * Real.sqrt (2 * (54 * aa m ^ 2 * ((m:ℝ)+1)^3)) ≤ 1 / (2 * 2^(m+1)) := by
  have hY : (1:ℝ) ≤ (m:ℝ)+1 := by have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith
  have hX : (0:ℝ) < 2^(m+1) := by positivity
  have e : 2 * (54 * aa m ^ 2 * ((m:ℝ)+1)^3) = 108 / (10000 * (2^(m+1))^2 * ((m:ℝ)+1)) := by
    unfold aa; field_simp; ring
  rw [e]
  have h2 : Real.sqrt (108 / (10000 * (2^(m+1))^2 * ((m:ℝ)+1))) ≤ Real.sqrt ((1 / (4 * 2^(m+1)))^2) := by
    apply Real.sqrt_le_sqrt
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0:ℝ) < (2^(m+1))^2 := by positivity
    nlinarith
  rw [Real.sqrt_sq (by positivity)] at h2
  calc 2 * Real.sqrt _ ≤ 2 * (1 / (4 * 2^(m+1))) := by linarith
    _ = 1 / (2 * 2^(m+1)) := by field_simp; ring

lemma kernels_ok (m : ℕ) (r : ℝ) (hr : 4 ≤ r) (pr : (t : ℕ) → (Fin t → Bool) → ℝ)
    (hpr : ∀ t h, pr t h ∈ Set.Icc (1:ℝ) 6) (z : ℝ) (hz : z ∈ Set.Icc (1/6 : ℝ) (1/4)) :
    ∀ t h, 0 ≤ nu (pr t h) z ∧ nu (pr t h) z ≤ 1 := by
  intro t h
  have := nu_bounds _ _ (hpr t h) hz
  constructor <;> linarith

lemma PG_sum (m : ℕ) (r : ℝ) (hr : 4 ≤ r) (pr : (t : ℕ) → (Fin t → Bool) → ℝ)
    (hpr : ∀ t h, pr t h ∈ Set.Icc (1:ℝ) 6) :
    1/2 ≤ ∑ ζ : Fin (m+1) → Bool, ∑ e : Fin (nn r (m+1)) → Bool,
      W (kP m r pr ζ) (nn r (m+1)) e * Gj m r pr (m+1) ζ e := by
  have hr1 : 1 ≤ r := by linarith
  set N := nn r (m+1)
  have hQ : ∑ ζ : Fin (m+1) → Bool, ∑ e : Fin N → Bool,
      W (kQ m r pr ζ) N e * Gj m r pr (m+1) ζ e = 1 := VV_top m r hr pr
  have each : ∀ ζ : Fin (m+1) → Bool,
      ∑ e : Fin N → Bool, W (kQ m r pr ζ) N e * Gj m r pr (m+1) ζ e - 1 / (2 * 2^(m+1)) ≤
      ∑ e : Fin N → Bool, W (kP m r pr ζ) N e * Gj m r pr (m+1) ζ e := by
    intro ζ
    have hkP := kernels_ok m r hr pr hpr _ (zt_mem m r hr1 m ζ)
    have hkQ : ∀ t h, 0 ≤ kQ m r pr ζ t h ∧ kQ m r pr ζ t h ≤ 1 := by
      intro t h; exact kernels_ok m r hr pr hpr _ (zt_mem m r hr1 (Lf r t) ζ) t h
    have hbc := bc (kP m r pr ζ) (kQ m r pr ζ) hkP hkQ
      (fun t => 54 * (zt m r m ζ - zt m r (Lf r t) ζ)^2) (fun t => by positivity)
      (fun t h => hell (pr t h) _ _ (hpr t h) (zt_mem m r hr1 m ζ) (zt_mem m r hr1 (Lf r t) ζ)) N
    have htv := tv_bc (fun e => W (kP m r pr ζ) N e) (fun e => W (kQ m r pr ζ) N e)
      (fun e => Gj m r pr (m+1) ζ e) (fun e => W_nonneg _ hkP N e) (fun e => W_nonneg _ hkQ N e)
      (W_sum _ N) (W_sum _ N) (fun e => Gj_nonneg m r pr (m+1) ζ e)
    have hH := Hsum_le m r hr ζ N
    have hs : 2 * Real.sqrt (2 * (1 - ∑ e : Fin N → Bool,
        Real.sqrt (W (kP m r pr ζ) N e) * Real.sqrt (W (kQ m r pr ζ) N e))) ≤ 1 / (2 * 2^(m+1)) := by
      refine le_trans ?_ (const_ok m)
      have := Real.sqrt_le_sqrt (show 2 * (1 - ∑ e : Fin N → Bool,
        Real.sqrt (W (kP m r pr ζ) N e) * Real.sqrt (W (kQ m r pr ζ) N e)) ≤
        2 * (54 * aa m ^ 2 * ((m:ℝ)+1)^3) by linarith)
      linarith
    linarith
  have := Finset.sum_le_sum (fun ζ (_ : ζ ∈ Finset.univ) => each ζ)
  rw [Finset.sum_sub_distrib, hQ] at this
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at this
  have e : (((2:ℕ)^(m+1) : ℕ) : ℝ) * (1 / (2 * 2^(m+1))) = 1/2 := by push_cast; field_simp
  rw [e] at this
  linarith

/-! ### Pigeonhole over the epochs -/

lemma pigeon {T m : ℕ} (q : Fin T → ℝ) (C : Finset (Fin T))
    (hC : ∀ t : Fin T, (∃ ht : t.val + 1 < T, q t ≠ q ⟨t.val+1, ht⟩) → t ∈ C)
    (hc : C.card ≤ m) (n : ℕ → ℕ) (hn : StrictMono n) (hT : n (m+1) ≤ T) :
    ∃ l, l ≤ m ∧ ∀ (t t' : Fin T), n l ≤ t.val → t.val < n (l+1) → t'.val = n l → q t = q t' := by
  classical
  by_contra H
  push Not at H
  have hchg : ∀ l : Fin (m+1), ∃ u : Fin T, n l.val ≤ u.val ∧ u.val + 1 < n (l.val+1) ∧ u ∈ C := by
    intro l
    obtain ⟨t, t', h1, h2, h3, h4⟩ := H l.val (Nat.lt_succ_iff.1 l.isLt)
    by_contra hno
    push Not at hno
    let qq : ℕ → ℝ := fun x => if h : x < T then q ⟨x, h⟩ else 0
    have hstep : ∀ k, n l.val + k < n (l.val+1) → qq (n l.val + k) = qq (n l.val) := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hlt : n l.val + k + 1 < T := lt_of_lt_of_le hk
          (le_trans (hn.monotone (by omega : l.val + 1 ≤ m + 1)) hT)
        rw [← ih (by omega)]
        have hnot : ¬ (⟨n l.val + k, by omega⟩ : Fin T) ∈ C :=
          hno ⟨n l.val + k, by omega⟩ (by simp) (by simp only; omega)
        have heq : q ⟨n l.val + k, by omega⟩ = q ⟨n l.val + k + 1, hlt⟩ := by
          by_contra hne
          exact hnot (hC _ ⟨hlt, hne⟩)
        simp only [qq, dif_pos (show n l.val + k < T by omega)]
        rw [heq, dif_pos (show n l.val + (k+1) < T by omega)]
        congr 1
    have := hstep (t.val - n l.val) (by omega)
    rw [show n l.val + (t.val - n l.val) = t.val by omega] at this
    simp only [qq, dif_pos t.isLt, dif_pos (show n l.val < T by omega)] at this
    apply h4
    rw [this]; congr 1; ext; simp [h3]
  choose u hu1 hu2 hu3 using hchg
  have hinj : Function.Injective u := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (fun e => hne (Fin.ext e)) with h | h
    · have := hn.monotone (show a.val + 1 ≤ b.val by omega)
      have := hu2 a; have := hu1 b; rw [hab] at *; omega
    · have := hn.monotone (show b.val + 1 ≤ a.val by omega)
      have := hu2 b; have := hu1 a; rw [hab] at *; omega
  have hsub : Finset.univ.image u ⊆ C := by
    intro x hx; obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hx; exact hu3 a
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at this
  omega

lemma regret_nonneg (p z : ℝ) (hp : p ∈ Set.Icc (1:ℝ) 6) (hz : z ∈ Set.Icc (1/6 : ℝ) (1/4)) :
    0 ≤ Gstar z - rev p z := by
  rw [regret_eq p z hp hz]; have := hz.1; positivity

lemma path_regret {S : Type} (m : ℕ) (r : ℝ) (hr : (40 * ((m:ℝ)+1))^2 ≤ r) (T : ℕ)
    (hT : nn r (m+1) + 1 = T)
    (price : (t : ℕ) → S → (Fin t → Bool) → ℝ) (hpr : ∀ t s h, price t s h ∈ Set.Icc (1:ℝ) 6)
    (s : S) (d : Fin T → Bool) (hc : changeCount price s d ≤ m) (ζ : Fin (m+1) → Bool) :
    aa m ^ 2 * r / 2 * Gj m r (fun t h => price t s h) (m+1) ζ (pre d (nn r (m+1)) (by omega)) ≤
      ∑ t : Fin T, (Gstar (zt m r m ζ) - rev (priceAlong price s d t) (zt m r m ζ)) := by
  classical
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hr4 : 4 ≤ r := by nlinarith
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  set z := zt m r m ζ
  have hz := zt_mem m r hr1 m ζ
  have hnn : ∀ t : Fin T, 0 ≤ Gstar z - rev (priceAlong price s d t) z :=
    fun t => regret_nonneg _ _ (hpr _ _ _) hz
  set G := Gj m r (fun t h => price t s h) (m+1) ζ (pre d (nn r (m+1)) (by omega))
  have hG := Gj_nonneg m r (fun t h => price t s h) (m+1) ζ (pre d (nn r (m+1)) (by omega))
  by_cases hG0 : G = 0
  · rw [hG0, mul_zero]; exact Finset.sum_nonneg (fun t _ => hnn t)
  have hJ : ∀ l : Fin (m+1), J m r l ζ (price (nn r l) s (rs (pre d (nn r (m+1)) (by omega)) (nn r l))) ≠ 0 := by
    intro l
    have := Finset.prod_ne_zero_iff.1 hG0 l (Finset.mem_univ _)
    simpa [l.isLt] using this
  have hmono := nn_strictMono r hr4
  -- pigeonhole
  obtain ⟨l, hlm, hblk⟩ := pigeon (T := T) (m := m) (fun t => priceAlong price s d t)
    (Finset.univ.filter (fun t : Fin T =>
      if ht : t.val + 1 < T then priceAlong price s d t ≠ priceAlong price s d ⟨t.val + 1, ht⟩ else False))
    (by
      intro t ⟨ht, hne⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, dif_pos ht]; exact hne)
    (by unfold changeCount at hc; convert hc)
    (nn r) hmono (by omega)
  have hlT : nn r l < T := by
    have : nn r l < nn r (m+1) := hmono (by omega)
    omega
  have hl1T : nn r (l+1) ≤ nn r (m+1) := hmono.monotone (by omega)
  -- price in the block
  set p := price (nn r l) s (rs (pre d (nn r (m+1)) (by omega)) (nn r l))
  have hpl : priceAlong price s d ⟨nn r l, hlT⟩ = p := by
    simp only [priceAlong, p]
    congr 1
    funext i
    have hi : i.val < nn r (m+1) := lt_of_lt_of_le i.isLt (hmono.monotone (by omega))
    simp [rs, pre, hi]
  have hreg : aa m ^ 2 * ee r l ^ 2 ≤ Gstar z - rev p z :=
    J_regret m r hr ⟨l, Nat.lt_succ_of_le hlm⟩ ζ p (hpr _ _ _) (hJ ⟨l, Nat.lt_succ_of_le hlm⟩)
  rw [ee_sq r hr1] at hreg
  -- sum over the block
  let f : ℕ → ℝ := fun t => if h : t < T then Gstar z - rev (priceAlong price s d ⟨t, h⟩) z else 0
  have hsum : ∑ t : Fin T, (Gstar z - rev (priceAlong price s d t) z) = ∑ t ∈ Finset.range T, f t := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl; intro t _; simp [f, t.isLt]
  rw [hsum]
  have hf0 : ∀ t, 0 ≤ f t := by
    intro t; simp only [f]; split_ifs with h
    · exact hnn ⟨t, h⟩
    · rfl
  have hsub : Finset.Ico (nn r l) (nn r (l+1)) ⊆ Finset.range T := by
    intro t ht; rw [Finset.mem_Ico] at ht; rw [Finset.mem_range]; omega
  have hblock : ∀ t ∈ Finset.Ico (nn r l) (nn r (l+1)), aa m ^ 2 * (1 / r^l) ≤ f t := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have htT : t < T := by omega
    simp only [f, dif_pos htT]
    rw [hblk ⟨t, htT⟩ ⟨nn r l, hlT⟩ ht.1 ht.2 rfl, hpl]
    exact hreg
  calc aa m ^ 2 * r / 2 * G ≤ aa m ^ 2 * r / 2 := by
        have : 0 ≤ aa m ^ 2 * r / 2 := by positivity
        nlinarith [hG.2]
    _ = (r^(l+1) / 2) * (aa m ^ 2 * (1 / r^l)) := by
        rw [pow_succ]; field_simp; ring
    _ ≤ ((nn r (l+1) : ℝ) - nn r l) * (aa m ^ 2 * (1 / r^l)) :=
        mul_le_mul_of_nonneg_right (nn_gap r hr4 l) (by positivity)
    _ = ∑ t ∈ Finset.Ico (nn r l) (nn r (l+1)), aa m ^ 2 * (1 / r^l) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
          Nat.cast_sub (hmono.monotone (Nat.le_succ l))]
    _ ≤ ∑ t ∈ Finset.Ico (nn r l) (nn r (l+1)), f t := Finset.sum_le_sum hblock
    _ ≤ ∑ t ∈ Finset.range T, f t :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hf0 t)

lemma seed_sum {S : Type} (m : ℕ) (r : ℝ) (hr : (40 * ((m:ℝ)+1))^2 ≤ r) (T : ℕ)
    (hT : nn r (m+1) + 1 = T)
    (price : (t : ℕ) → S → (Fin t → Bool) → ℝ) (hpr : ∀ t s h, price t s h ∈ Set.Icc (1:ℝ) 6)
    (s : S) (hc : ∀ d : Fin T → Bool, changeCount price s d ≤ m) :
    aa m ^ 2 * r / 4 ≤ ∑ ζ : Fin (m+1) → Bool, ∑ d : Fin T → Bool,
      W (kP m r (fun t h => price t s h) ζ) T d *
        ∑ t : Fin T, (Gstar (zt m r m ζ) - rev (priceAlong price s d t) (zt m r m ζ)) := by
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hr4 : 4 ≤ r := by nlinarith
  have hr1 : 1 ≤ r := by linarith
  set pr : (t : ℕ) → (Fin t → Bool) → ℝ := fun t h => price t s h
  have hpr' : ∀ t h, pr t h ∈ Set.Icc (1:ℝ) 6 := fun t h => hpr t s h
  have hN : nn r (m+1) ≤ T := by omega
  have each : ∀ ζ : Fin (m+1) → Bool,
      aa m ^ 2 * r / 2 * ∑ e : Fin (nn r (m+1)) → Bool,
        W (kP m r pr ζ) (nn r (m+1)) e * Gj m r pr (m+1) ζ e ≤
      ∑ d : Fin T → Bool, W (kP m r pr ζ) T d *
        ∑ t : Fin T, (Gstar (zt m r m ζ) - rev (priceAlong price s d t) (zt m r m ζ)) := by
    intro ζ
    have hk := kernels_ok m r hr4 pr hpr' _ (zt_mem m r hr1 m ζ)
    rw [← marg (kP m r pr ζ) (nn r (m+1)) (fun e => Gj m r pr (m+1) ζ e) T hN, Finset.mul_sum]
    apply Finset.sum_le_sum; intro d _
    have h1 := path_regret m r hr T hT price hpr s d (hc d) ζ
    have h2 := W_nonneg (kP m r pr ζ) hk T d
    calc aa m ^ 2 * r / 2 * (W (kP m r pr ζ) T d * Gj m r pr (m+1) ζ (pre d (nn r (m+1)) hN))
        = W (kP m r pr ζ) T d * (aa m ^ 2 * r / 2 * Gj m r pr (m+1) ζ (pre d (nn r (m+1)) hN)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  have hP := PG_sum m r hr4 pr hpr'
  calc aa m ^ 2 * r / 4 = aa m ^ 2 * r / 2 * (1/2) := by ring
    _ ≤ aa m ^ 2 * r / 2 * ∑ ζ : Fin (m+1) → Bool, ∑ e : Fin (nn r (m+1)) → Bool,
          W (kP m r pr ζ) (nn r (m+1)) e * Gj m r pr (m+1) ζ e :=
        mul_le_mul_of_nonneg_left hP (by have := aa_pos m; positivity)
    _ = ∑ ζ : Fin (m+1) → Bool, aa m ^ 2 * r / 2 * ∑ e : Fin (nn r (m+1)) → Bool,
          W (kP m r pr ζ) (nn r (m+1)) e * Gj m r pr (m+1) ζ e := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun ζ _ => each ζ)

lemma integrand_eq {S : Type} [MeasurableSpace S] {T m : ℕ} (π : Policy S T m) (z : ℝ)
    (hz : z ∈ Set.Icc (1/6 : ℝ) (1/4)) (s : S) :
    ∑ d : Fin T → Bool, pathWeight π z s d *
      ∑ t : Fin T, ENNReal.ofReal (Gstar z - rev (priceAlong π.price s d t) z) =
    ENNReal.ofReal (∑ d : Fin T → Bool, W (fun t h => nu (π.price t s h) z) T d *
      ∑ t : Fin T, (Gstar z - rev (priceAlong π.price s d t) z)) := by
  have hk : ∀ t h, 0 ≤ nu (π.price t s h) z ∧ nu (π.price t s h) z ≤ 1 := by
    intro t h; have := nu_bounds _ _ (π.feasible t s h) hz; constructor <;> linarith
  have hg : ∀ d (t : Fin T), 0 ≤ Gstar z - rev (priceAlong π.price s d t) z :=
    fun d t => regret_nonneg _ _ (π.feasible _ _ _) hz
  rw [ENNReal.ofReal_sum_of_nonneg (fun d _ => mul_nonneg (W_nonneg _ hk T d)
    (Finset.sum_nonneg (fun t _ => hg d t)))]
  apply Finset.sum_congr rfl; intro d _
  rw [ENNReal.ofReal_mul (W_nonneg _ hk T d), ENNReal.ofReal_sum_of_nonneg (fun t _ => hg d t)]
  congr 1
  unfold pathWeight W
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl; intro t _
    split_ifs <;> rfl
  · intro t _
    have := hk t.val (pre d t.val t.isLt.le)
    split_ifs
    · exact this.1
    · linarith [this.2]

lemma integrand_meas {S : Type} [MeasurableSpace S] {T m : ℕ} (π : Policy S T m) (z : ℝ) :
    Measurable (fun s => ∑ d : Fin T → Bool, pathWeight π z s d *
      ∑ t : Fin T, ENNReal.ofReal (Gstar z - rev (priceAlong π.price s d t) z)) := by
  have hc1 : Continuous (fun p : ℝ => nu p z) := by unfold nu; fun_prop
  have hc2 : Continuous (fun p : ℝ => Gstar z - rev p z) := by unfold rev nu; fun_prop
  have hp : ∀ d (t : Fin T), Measurable (fun s => priceAlong π.price s d t) := by
    intro d t; unfold priceAlong; exact π.measurable _ _
  apply Finset.measurable_sum; intro d _
  apply Measurable.mul
  · unfold pathWeight
    apply Finset.measurable_prod; intro t _
    by_cases h : d t
    · simp only [h, if_true]
      exact ENNReal.measurable_ofReal.comp (hc1.measurable.comp (hp d t))
    · simp only [h, Bool.false_eq_true, if_false]
      exact ENNReal.measurable_ofReal.comp ((measurable_const.sub hc1.measurable).comp (hp d t))
  · apply Finset.measurable_sum; intro t _
    exact ENNReal.measurable_ofReal.comp (hc2.measurable.comp (hp d t))

end LPC2Aux

open LimitedPriceChanges.LowerBound in
theorem solution (m : ℕ) (hm : 1 ≤ m) :
    ∃ K7 : ℝ, 0 < K7 ∧ ∃ T0 : ℕ, ∀ T ≥ T0,
      ∀ (S : Type) [MeasurableSpace S] (μ : MeasureTheory.Measure S)
        [MeasureTheory.IsProbabilityMeasure μ] (π : Policy S T m),
        ∃ z ∈ Set.Icc (1 / 6 : ℝ) (5 / 6 : ℝ),
          ENNReal.ofReal (K7 * (T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1))) ≤
            regret μ π z := by
  classical
  open LPC2Aux in
  refine ⟨aa m ^ 2 / (4 * 2^(m+1)), by have := aa_pos m; positivity,
    (1600 * (m+1)^2)^(m+1), ?_⟩
  intro T hT S _ μ _ π
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  set r : ℝ := (T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1)) with hrdef
  have hinv : (1 : ℝ) / ((m : ℝ) + 1) = (((m+1 : ℕ) : ℝ))⁻¹ := by push_cast; ring
  have hT0 : (0:ℝ) ≤ T := Nat.cast_nonneg T
  have hrpow : r ^ (m+1) = T := by
    rw [hrdef, hinv]; exact Real.rpow_inv_natCast_pow hT0 (by omega)
  have hrbig : (40 * ((m:ℝ)+1))^2 ≤ r := by
    have h1 : (((1600 * (m+1)^2)^(m+1) : ℕ) : ℝ) ≤ T := by exact_mod_cast hT
    push_cast at h1
    have h2 := Real.rpow_le_rpow (by positivity) h1 (show (0:ℝ) ≤ (((m+1 : ℕ) : ℝ))⁻¹ by positivity)
    rw [Real.pow_rpow_inv_natCast (by positivity) (by omega)] at h2
    rw [hrdef, hinv]
    calc (40 * ((m:ℝ)+1))^2 = 1600 * ((m:ℝ)+1)^2 := by ring
      _ ≤ _ := h2
  have hr4 : 4 ≤ r := by nlinarith
  have hr1 : 1 ≤ r := by linarith
  have hTpos : 1 ≤ T := by
    have : (1:ℝ) ≤ T := by rw [← hrpow]; exact one_le_pow₀ hr1
    exact_mod_cast this
  have hTn : LPC2Aux.nn r (m+1) + 1 = T := by
    unfold LPC2Aux.nn; rw [hrpow, Nat.floor_natCast]; omega
  -- the family
  let F : (Fin (m+1) → Bool) → S → ENNReal := fun ζ s =>
    ∑ d : Fin T → Bool, pathWeight π (LPC2Aux.zt m r m ζ) s d *
      ∑ t : Fin T, ENNReal.ofReal (Gstar (LPC2Aux.zt m r m ζ) - rev (priceAlong π.price s d t) (LPC2Aux.zt m r m ζ))
  have hF : ∀ ζ, regret μ π (LPC2Aux.zt m r m ζ) = ∫⁻ s, F ζ s ∂μ := fun ζ => rfl
  have hsum : ENNReal.ofReal (LPC2Aux.aa m ^ 2 * r / 4) ≤ ∑ ζ : Fin (m+1) → Bool, ∫⁻ s, F ζ s ∂μ := by
    rw [← MeasureTheory.lintegral_finsetSum _ (fun ζ _ => LPC2Aux.integrand_meas π _)]
    calc ENNReal.ofReal (LPC2Aux.aa m ^ 2 * r / 4)
        = ∫⁻ _s, ENNReal.ofReal (LPC2Aux.aa m ^ 2 * r / 4) ∂μ := by
          rw [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
      _ ≤ ∫⁻ s, ∑ ζ : Fin (m+1) → Bool, F ζ s ∂μ := by
          apply MeasureTheory.lintegral_mono; intro s
          simp only [F]
          simp_rw [LPC2Aux.integrand_eq π _ (LPC2Aux.zt_mem m r hr1 m _) s]
          have hR := LPC2Aux.seed_sum m r hrbig T hTn π.price π.feasible s (fun d => π.changes s d)
          rw [← ENNReal.ofReal_sum_of_nonneg]
          · apply ENNReal.ofReal_le_ofReal
            exact hR
          · intro ζ _
            apply Finset.sum_nonneg; intro d _
            apply mul_nonneg
            · exact LPC2Aux.W_nonneg _ (LPC2Aux.kernels_ok m r hr4 _ (fun t h => π.feasible t s h) _
                (LPC2Aux.zt_mem m r hr1 m ζ)) T d
            · exact Finset.sum_nonneg (fun t _ => LPC2Aux.regret_nonneg _ _ (π.feasible _ _ _)
                (LPC2Aux.zt_mem m r hr1 m ζ))
  by_contra hcon
  push Not at hcon
  have hlt : ∀ ζ : Fin (m+1) → Bool, ∫⁻ s, F ζ s ∂μ <
      ENNReal.ofReal (LPC2Aux.aa m ^ 2 / (4 * 2^(m+1)) * r) := by
    intro ζ
    have hz := LPC2Aux.zt_mem m r hr1 m ζ
    exact hcon _ ⟨hz.1, by linarith [hz.2]⟩
  have := ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun ζ (_ : ζ ∈ Finset.univ) => hlt ζ)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul] at this
  have e : ((2 ^ (m+1) : ℕ) : ENNReal) * ENNReal.ofReal (LPC2Aux.aa m ^ 2 / (4 * 2^(m+1)) * r) =
      ENNReal.ofReal (LPC2Aux.aa m ^ 2 * r / 4) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; push_cast; field_simp
  rw [e] at this
  exact absurd (lt_of_le_of_lt hsum this) (lt_irrefl _)
