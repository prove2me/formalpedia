-- Prove2me | solution 1 for MatrixAnalytic.PHRenewal.uniformization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T04:00:48.381998+00:00
-- url     : https://prove2.me/submissions/8f900f56-944a-4fe4-a2f3-d274645c09bb

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep
import Definitions.Def_MatrixAnalytic_PHRenewal_Counting
import Definitions.Def_MatrixAnalytic_PHRenewal_Uniformization

open Matrix MeasureTheory Filter Topology
open MatrixAnalytic.PHRenewal

/-- coefficient of `z^d` in `(A + z B)^n` -/
def g77coef {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) : ℕ → ℕ → Matrix ι ι ℝ
  | n, 0 => A ^ n
  | 0, _ + 1 => 0
  | n + 1, d + 1 => A * g77coef A B n (d + 1) + B * g77coef A B n d

/-- level-structured matrix, `A` on the diagonal blocks, `B` on the superdiagonal blocks -/
def g77lev {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (K : ℕ) :
    Matrix (Fin (K + 1) × ι) (Fin (K + 1) × ι) ℝ :=
  fun a b => if (b.1 : ℕ) = (a.1 : ℕ) then A a.2 b.2
    else if (b.1 : ℕ) = (a.1 : ℕ) + 1 then B a.2 b.2 else 0

theorem g77_countGen {ι : Type*} [Fintype ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ) (K : ℕ) :
    countGen τ T K = g77lev T (vecMulVec (exitVec T) τ) K := by
  ext a b; simp [countGen, g77lev, vecMulVec_apply]

theorem g77coef_zero_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (d : ℕ) :
    g77coef A B 0 (d + 1) = 0 := rfl

theorem g77lev_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (K : ℕ)
    (N : Matrix (Fin (K + 1) × ι) (Fin (K + 1) × ι) ℝ) (a b : Fin (K + 1) × ι) :
    (g77lev A B K * N) a b = (∑ i', A a.2 i' * N (a.1, i') b) +
      (if h : (a.1 : ℕ) + 1 < K + 1 then ∑ i', B a.2 i' * N (⟨(a.1 : ℕ) + 1, h⟩, i') b else 0) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hsplit : ∀ (l : Fin (K + 1)) (i' : ι), g77lev A B K a (l, i') * N (l, i') b =
      (if l = a.1 then A a.2 i' * N (l, i') b else 0) +
      (if (l : ℕ) = (a.1 : ℕ) + 1 then B a.2 i' * N (l, i') b else 0) := by
    intro l i'
    simp only [g77lev]
    by_cases h1 : l = a.1
    · subst h1; simp
    · have h1' : (l : ℕ) ≠ (a.1 : ℕ) := fun h => h1 (Fin.ext h)
      simp [h1, h1']
  simp only [hsplit, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    simp
  · split_ifs with h
    · rw [Finset.sum_comm]
      have : ∀ l : Fin (K + 1), ((l : ℕ) = (a.1 : ℕ) + 1) ↔ l = ⟨(a.1 : ℕ) + 1, h⟩ := by
        intro l; rw [Fin.ext_iff]
      simp only [this]
      simp
    · refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun i' _ => ?_
      rw [if_neg]
      intro hl; have := l.2; omega

theorem g77coef_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (n d : ℕ) :
    g77coef A B (n + 1) d = A * g77coef A B n d + (if d = 0 then 0 else B * g77coef A B n (d - 1)) := by
  cases d with
  | zero => simp [g77coef, pow_succ']
  | succ d => simp [g77coef]

theorem g77lev_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (K n : ℕ) :
    ∀ a b : Fin (K + 1) × ι, (g77lev A B K ^ n) a b =
      if (a.1 : ℕ) ≤ (b.1 : ℕ) then g77coef A B n ((b.1 : ℕ) - (a.1 : ℕ)) a.2 b.2 else 0 := by
  induction n with
  | zero =>
    intro a b
    rw [pow_zero, Matrix.one_apply]
    obtain ⟨⟨l, hl⟩, i⟩ := a
    obtain ⟨⟨m, hm⟩, j⟩ := b
    simp only [Prod.mk.injEq, Fin.mk.injEq]
    by_cases hlm : l = m
    · subst hlm; simp [g77coef, Matrix.one_apply]
    · rw [if_neg (by tauto)]
      split_ifs with h
      · have : m - l = (m - l - 1) + 1 := by omega
        rw [this, g77coef_zero_succ]; rfl
      · rfl
  | succ n ih =>
    intro a b
    rw [pow_succ', g77lev_mul]
    simp only [ih]
    obtain ⟨⟨l, hl⟩, i⟩ := a
    obtain ⟨⟨m, hm⟩, j⟩ := b
    simp only
    have h1 : (∑ i', A i i' * (if l ≤ m then g77coef A B n (m - l) i' j else 0)) =
        if l ≤ m then (A * g77coef A B n (m - l)) i j else 0 := by
      split_ifs <;> simp [Matrix.mul_apply]
    have h2 : (if h : l + 1 < K + 1 then ∑ i', B i i' *
          (if l + 1 ≤ m then g77coef A B n (m - (l + 1)) i' j else 0) else 0) =
        if l + 1 ≤ m then (B * g77coef A B n (m - l - 1)) i j else 0 := by
      by_cases h : l + 1 ≤ m
      · rw [dif_pos (by omega), if_pos h]
        simp only [if_pos h, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [show m - (l + 1) = m - l - 1 by omega]
      · rw [if_neg h]
        split_ifs
        · simp
        · rfl
    rw [h1, h2, g77coef_succ]
    by_cases hlm : l ≤ m
    · rw [if_pos hlm, if_pos hlm, Matrix.add_apply]
      congr 1
      by_cases hd : m - l = 0
      · rw [if_pos hd, if_neg (by omega)]; rfl
      · rw [if_neg hd, if_pos (by omega)]
    · rw [if_neg hlm, if_neg hlm, if_neg (by omega), add_zero]

section g77sec0
open scoped Norms.Operator
theorem g77_expser {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (a b : m) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • M ^ n) a b) (NormedSpace.exp M a b) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M
  exact Pi.hasSum.1 (Pi.hasSum.1 h a) b
end g77sec0

theorem g77_expser_smul {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (x : ℝ) (a b : m) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * x ^ n) * (M ^ n) a b) (NormedSpace.exp (x • M) a b) := by
  have h := g77_expser (x • M) a b
  simp only [smul_pow, Matrix.smul_apply, smul_eq_mul] at h
  convert h using 2; ring

noncomputable def g77P {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (x : ℝ) (d : ℕ) :
    Matrix ι ι ℝ :=
  fun i j => ∑' n : ℕ, ((n.factorial : ℝ)⁻¹ * x ^ n) * g77coef A B n d i j

theorem g77_exp_lev_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (K : ℕ)
    (x : ℝ) (a b : Fin (K + 1) × ι) (hab : (a.1 : ℕ) ≤ b.1) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * x ^ n) * g77coef A B n ((b.1 : ℕ) - a.1) a.2 b.2)
      (NormedSpace.exp (x • g77lev A B K) a b) := by
  have h := g77_expser_smul (g77lev A B K) x a b
  simp only [g77lev_pow, if_pos hab] at h
  exact h

theorem g77_hasSumP {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (x : ℝ) (d : ℕ)
    (i j : ι) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * x ^ n) * g77coef A B n d i j) (g77P A B x d i j) := by
  have h := g77_exp_lev_hasSum A B d x (0, i) (Fin.last d, j) (by simp)
  simp only [Fin.val_last, Fin.val_zero, Nat.sub_zero] at h
  exact h.summable.hasSum

theorem g77_exp_lev {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (K : ℕ)
    (x : ℝ) (a b : Fin (K + 1) × ι) :
    NormedSpace.exp (x • g77lev A B K) a b =
      if (a.1 : ℕ) ≤ b.1 then g77P A B x ((b.1 : ℕ) - a.1) a.2 b.2 else 0 := by
  split_ifs with hab
  · exact (g77_exp_lev_hasSum A B K x a b hab).unique (g77_hasSumP A B x _ a.2 b.2)
  · have h := g77_expser_smul (g77lev A B K) x a b
    simp only [g77lev_pow, if_neg hab, mul_zero] at h
    exact h.unique hasSum_zero

theorem g77_countProb {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (k : ℕ) (x : ℝ) : countProb τ T k x = g77P T (vecMulVec (exitVec T) τ) x k := by
  ext i j
  simp only [countProb, g77_countGen, g77_exp_lev]
  simp

section g77sec
open scoped Norms.Operator

theorem g77_deriv_entry {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (a b : m) (x : ℝ) :
    HasDerivAt (fun y : ℝ => NormedSpace.exp (y • M) a b) ((M * NormedSpace.exp (x • M)) a b) x := by
  let L : Matrix m m ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun N => N a b
      map_add' := by intro N N'; rfl
      map_smul' := by intro c N; rfl }
  have hd := hasDerivAt_exp_smul_const' (𝕂 := ℝ) M x
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt x hd

end g77sec

theorem g77_deriv_P {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (k : ℕ) (x : ℝ)
    (i j : ι) :
    HasDerivAt (fun y => g77P A B y k i j)
      ((A * g77P A B x k) i j + (if k = 0 then 0 else (B * g77P A B x (k - 1)) i j)) x := by
  have hfun : (fun y => g77P A B y k i j) =
      fun y : ℝ => NormedSpace.exp (y • g77lev A B k) (0, i) (Fin.last k, j) := by
    funext y; rw [g77_exp_lev]; simp
  rw [hfun]
  refine (g77_deriv_entry (g77lev A B k) (0, i) (Fin.last k, j) x).congr_deriv ?_
  rw [g77lev_mul]
  simp only [g77_exp_lev, Fin.val_zero, Fin.val_last, zero_le, if_true, Nat.sub_zero, zero_add]
  congr 1 <;> rcases k with _ | k <;> simp [Matrix.mul_apply]

theorem g77coef_vanish {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) :
    ∀ n k, n < k → g77coef A B n k = 0 := by
  intro n
  induction n with
  | zero => intro k hk; obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; rfl
  | succ n ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [g77coef, ih (k + 1) (by omega), ih k (by omega), mul_zero, add_zero]

theorem g77_binom {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (z : ℝ) (n : ℕ) :
    (A + z • B) ^ n = ∑ k ∈ Finset.range (n + 1), z ^ k • g77coef A B n k := by
  induction n with
  | zero => simp [g77coef]
  | succ n ih =>
    rw [pow_succ', ih, Finset.mul_sum]
    have hA : ∀ k ∈ Finset.range (n + 1), (A + z • B) * (z ^ k • g77coef A B n k) =
        z ^ k • (A * g77coef A B n k) + z ^ (k + 1) • (B * g77coef A B n k) := by
      intro k _
      rw [add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ, mul_comm z]
    rw [Finset.sum_congr rfl hA, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun k => z ^ k • g77coef A B (n + 1) k)]
    simp only [g77coef_succ, smul_add, Finset.sum_add_distrib, Nat.add_sub_cancel,
      Nat.succ_ne_zero, if_false, pow_zero, one_smul, if_true]
    rw [Finset.sum_range_succ (fun k => z ^ (k + 1) • (A * g77coef A B n (k + 1)))]
    rw [g77coef_vanish A B n (n + 1) (by omega), mul_zero, smul_zero, add_zero]
    rw [Finset.sum_range_succ' (fun k => z ^ k • (A * g77coef A B n k))]
    simp only [pow_zero, one_smul, mul_zero, add_zero]
    abel

/-- entrywise ℓ¹ norm -/
def g77s {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, |M i j|

theorem g77s_nonneg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : 0 ≤ g77s M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem g77s_entry {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (i j : ι) : |M i j| ≤ g77s M := by
  unfold g77s
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
    (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => |M i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

theorem g77s_add {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℝ) : g77s (M + N) ≤ g77s M + g77s N := by
  unfold g77s
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => abs_add_le _ _

theorem g77s_mul {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℝ) : g77s (M * N) ≤ g77s M * g77s N := by
  unfold g77s
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, |(M * N) i j| ≤ ∑ j, ∑ l, |M i l| * |N l j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp [abs_mul]
    _ = ∑ l, |M i l| * ∑ j, |N l j| := by
        rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ l, |M i l| * ∑ l', ∑ j, |N l' j| := by
        refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact Finset.single_le_sum (f := fun l => ∑ j, |N l j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)
    _ = (∑ j, |M i j|) * ∑ i, ∑ j, |N i j| := by rw [Finset.sum_mul]

theorem g77s_zero {ι : Type*} [Fintype ι] : g77s (0 : Matrix ι ι ℝ) = 0 := by simp [g77s]

theorem g77coef_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), g77s (g77coef A B n k) ≤
      g77s (1 : Matrix ι ι ℝ) * (g77s A + g77s B) ^ n := by
  induction n with
  | zero => simp [g77coef]
  | succ n ih =>
    have hb : ∀ k, g77s (g77coef A B (n + 1) k) ≤
        g77s A * g77s (g77coef A B n k) +
          (if k = 0 then 0 else g77s B * g77s (g77coef A B n (k - 1))) := by
      intro k
      rw [g77coef_succ]
      refine (g77s_add _ _).trans (add_le_add (g77s_mul _ _) ?_)
      split_ifs
      · rw [g77s_zero]
      · exact g77s_mul _ _
    refine (Finset.sum_le_sum fun k _ => hb k).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_succ (fun k => g77s (g77coef A B n k)),
      g77coef_vanish A B n (n + 1) (by omega), g77s_zero, add_zero]
    have e2 : ∑ k ∈ Finset.range (n + 1 + 1),
        (if k = 0 then 0 else g77s B * g77s (g77coef A B n (k - 1))) =
        g77s B * ∑ k ∈ Finset.range (n + 1), g77s (g77coef A B n k) := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp
    rw [e2, pow_succ]
    have h0 : 0 ≤ ∑ k ∈ Finset.range (n + 1), g77s (g77coef A B n k) :=
      Finset.sum_nonneg fun _ _ => g77s_nonneg _
    have hA := g77s_nonneg A
    have hB := g77s_nonneg B
    calc g77s A * ∑ k ∈ Finset.range (n + 1), g77s (g77coef A B n k) +
          g77s B * ∑ k ∈ Finset.range (n + 1), g77s (g77coef A B n k)
        = (g77s A + g77s B) * ∑ k ∈ Finset.range (n + 1), g77s (g77coef A B n k) := by ring
      _ ≤ (g77s A + g77s B) * (g77s (1 : Matrix ι ι ℝ) * (g77s A + g77s B) ^ n) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = _ := by ring

theorem g77_gen {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (x z : ℝ)
    (hz : |z| ≤ 1) (i j : ι) :
    HasSum (fun k : ℕ => z ^ k * g77P A B x k i j) (NormedSpace.exp (x • (A + z • B)) i j) := by
  set c : ℕ → ℝ := fun n => (n.factorial : ℝ)⁻¹ * x ^ n with hc
  set f : ℕ × ℕ → ℝ := fun p => c p.1 * (z ^ p.2 * g77coef A B p.1 p.2 i j) with hf
  set C := g77s A + g77s B
  set g : ℕ × ℕ → ℝ := fun p => |x| ^ p.1 / (p.1.factorial : ℝ) * g77s (g77coef A B p.1 p.2)
  have hg0 : 0 ≤ g := fun p => mul_nonneg (by positivity) (g77s_nonneg _)
  have hgs : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    have hfin : ∀ n, ∀ k ∉ Finset.range (n + 1), g (n, k) = 0 := by
      intro n k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [g, g77coef_vanish A B n k (by omega), g77s_zero]
    refine ⟨fun n => summable_of_ne_finset_zero (hfin n), ?_⟩
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k => hg0 _) (fun n => ?_)
      ((Real.summable_pow_div_factorial (|x| * C)).mul_left (g77s (1 : Matrix ι ι ℝ)))
    rw [tsum_eq_sum (hfin n)]
    simp only [g]
    rw [← Finset.mul_sum, mul_pow]
    calc |x| ^ n / (n.factorial : ℝ) * ∑ k ∈ Finset.range (n + 1), g77s (g77coef A B n k)
        ≤ |x| ^ n / (n.factorial : ℝ) * (g77s (1 : Matrix ι ι ℝ) * C ^ n) :=
          mul_le_mul_of_nonneg_left (g77coef_bound A B n) (by positivity)
      _ = _ := by ring
  have hfs : Summable f := by
    refine Summable.of_norm_bounded hgs fun p => ?_
    simp only [f, c, Real.norm_eq_abs, g, abs_mul, abs_inv, abs_pow, Nat.abs_cast]
    rw [div_eq_inv_mul]
    have h1 : |z| ^ p.2 ≤ 1 := pow_le_one₀ (abs_nonneg z) hz
    have h2 := g77s_entry (g77coef A B p.1 p.2) i j
    have h3 : |z| ^ p.2 * |g77coef A B p.1 p.2 i j| ≤ g77s (g77coef A B p.1 p.2) := by
      calc |z| ^ p.2 * |g77coef A B p.1 p.2 i j| ≤ 1 * g77s (g77coef A B p.1 p.2) :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc (p.1.factorial : ℝ)⁻¹ * |x| ^ p.1 * (|z| ^ p.2 * |g77coef A B p.1 p.2 i j|)
        ≤ (p.1.factorial : ℝ)⁻¹ * |x| ^ p.1 * g77s (g77coef A B p.1 p.2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  -- order 1
  have hrow : ∀ n, HasSum (fun k => f (n, k)) (c n * ((A + z • B) ^ n) i j) := by
    intro n
    have hfin : ∀ k ∉ Finset.range (n + 1), f (n, k) = 0 := by
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [f, g77coef_vanish A B n k (by omega)]
    have hv : c n * ((A + z • B) ^ n) i j = ∑ k ∈ Finset.range (n + 1), f (n, k) := by
      rw [g77_binom, Matrix.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [f, Matrix.smul_apply, smul_eq_mul]
    rw [hv]; exact hasSum_sum_of_ne_finset_zero hfin
  have h1 := hfs.hasSum.prod_fiberwise hrow
  have hval : ∑' p, f p = NormedSpace.exp (x • (A + z • B)) i j :=
    h1.unique (g77_expser_smul (A + z • B) x i j)
  -- order 2
  have hcol : ∀ k, HasSum (fun n => f (n, k)) (z ^ k * g77P A B x k i j) := by
    intro k
    have := (g77_hasSumP A B x k i j).mul_left (z ^ k)
    have e : (fun n => f (n, k)) = fun n => z ^ k * (((n.factorial : ℝ)⁻¹ * x ^ n) * g77coef A B n k i j) := by
      funext n; simp only [f, c]; ring
    rw [e]; exact this
  have h2 := hfs.prod_symm.hasSum.prod_fiberwise (fun k => hcol k)
  have e3 : ∑' p : ℕ × ℕ, f p.swap = ∑' p, f p := (Equiv.prodComm ℕ ℕ).tsum_eq f
  rw [e3, hval] at h2
  exact h2

theorem g77_unifK {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ) (c : ℝ) :
    ∀ m ν, unifK τ T c m ν = g77coef (unifP T c) (vecMulVec (unifExit T c) τ) m ν := by
  intro m
  induction m with
  | zero => intro ν; cases ν <;> rfl
  | succ m ih =>
    intro ν
    cases ν with
    | zero => rfl
    | succ ν => simp only [unifK, g77coef, ih]

section g77sec2
open scoped Norms.Operator

theorem g77_exp_lev_unif {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (K : ℕ)
    (c x : ℝ) (hc : c ≠ 0) :
    NormedSpace.exp (x • g77lev A B K) =
      Real.exp (-(c * x)) • NormedSpace.exp ((c * x) • g77lev (c⁻¹ • A + 1) (c⁻¹ • B) K) := by
  have hsplit : x • g77lev A B K = (c * x) • g77lev (c⁻¹ • A + 1) (c⁻¹ • B) K +
      algebraMap ℝ (Matrix (Fin (K + 1) × ι) (Fin (K + 1) × ι) ℝ) (-(c * x)) := by
    ext a b
    obtain ⟨⟨l, hl⟩, i⟩ := a
    obtain ⟨⟨m, hm⟩, j⟩ := b
    simp only [g77lev, Matrix.smul_apply, Matrix.add_apply, Matrix.algebraMap_matrix_apply,
      Matrix.one_apply, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply, Prod.mk.injEq,
      Fin.mk.injEq]
    by_cases hml : m = l
    · subst hml
      by_cases hij : i = j
      · subst hij; simp; field_simp; ring
      · simp [hij]; field_simp
    · have hlm : ¬ l = m := fun h => hml h.symm
      simp only [hml, hlm, false_and, if_false, add_zero, mul_zero, neg_mul]
      split_ifs
      · field_simp
      · simp
  have hcomm : Commute ((c * x) • g77lev (c⁻¹ • A + 1) (c⁻¹ • B) K)
      (algebraMap ℝ (Matrix (Fin (K + 1) × ι) (Fin (K + 1) × ι) ℝ) (-(c * x))) :=
    (Algebra.commutes _ _).symm
  have hal := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ)
    (𝔸 := Matrix (Fin (K + 1) × ι) (Fin (K + 1) × ι) ℝ) (-(c * x))
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm]
  erw [← hal]
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  rw [← Real.exp_eq_exp_ℝ]

end g77sec2

theorem g77_uniformization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T)
    (c : ℝ) (hc_ge : ∀ i, |T i i| ≤ c) (hc_attained : ∃ i, |T i i| = c) :
    unifExit T c = (fun _ => 1) - unifP T c *ᵥ (fun _ => 1) ∧
    ∀ ν : ℕ, ∀ x : ℝ, 0 ≤ x →
      HasSum
        (fun j : ℕ => (Real.exp (-c * x) * (c * x) ^ (j + ν) / ((j + ν).factorial : ℝ)) •
          unifK τ T c (j + ν) ν)
        (countProb τ T ν x) := by
  obtain ⟨i0, hi0⟩ := hc_attained
  have hc : 0 < c := by rw [← hi0]; exact abs_pos.2 (hrep.diag_neg i0).ne
  refine ⟨?_, fun ν x _ => ?_⟩
  · funext i
    simp only [unifExit, unifP, exitVec, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, add_mulVec,
      one_mulVec, smul_mulVec, Pi.add_apply, smul_eq_mul]
    ring
  · set B := vecMulVec (exitVec T) τ
    have hB : vecMulVec (unifExit T c) τ = c⁻¹ • B := by
      ext i j; simp [B, unifExit, vecMulVec_apply, mul_assoc]
    have hK : ∀ m, unifK τ T c m ν = g77coef (c⁻¹ • T + 1) (c⁻¹ • B) m ν := by
      intro m; rw [g77_unifK, hB]; rfl
    simp only [hK]
    rw [g77_countProb]
    refine Pi.hasSum.2 fun i => Pi.hasSum.2 fun j => ?_
    have h1 := congrFun (congrFun (g77_exp_lev_unif T B ν c x hc.ne') (0, i)) (Fin.last ν, j)
    simp only [g77_exp_lev, Matrix.smul_apply, Fin.val_zero, Fin.val_last, zero_le, if_true,
      Nat.sub_zero, smul_eq_mul] at h1
    rw [h1]
    have h2 := (g77_hasSumP (c⁻¹ • T + 1) (c⁻¹ • B) (c * x) ν i j).mul_left (Real.exp (-(c * x)))
    rw [← hasSum_nat_add_iff' ν] at h2
    have h0 : ∑ n ∈ Finset.range ν, Real.exp (-(c * x)) * (((n.factorial : ℝ)⁻¹ * (c * x) ^ n) *
        g77coef (c⁻¹ • T + 1) (c⁻¹ • B) n ν i j) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_range] at hn
      rw [g77coef_vanish _ _ n ν hn]; simp
    rw [h0, sub_zero] at h2
    have e : (fun n : ℕ => Real.exp (-(c * x)) * (((n + ν).factorial : ℝ)⁻¹ * (c * x) ^ (n + ν) *
        g77coef (c⁻¹ • T + 1) (c⁻¹ • B) (n + ν) ν i j)) =
        fun n : ℕ => ((Real.exp (-c * x) * (c * x) ^ (n + ν) / ((n + ν).factorial : ℝ)) •
          g77coef (c⁻¹ • T + 1) (c⁻¹ • B) (n + ν) ν) i j := by
      funext n
      rw [Matrix.smul_apply, smul_eq_mul, neg_mul]
      ring
    rw [e] at h2
    exact h2

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T)
    (c : ℝ) (hc_ge : ∀ i, |T i i| ≤ c) (hc_attained : ∃ i, |T i i| = c) :
    unifExit T c = (fun _ => 1) - unifP T c *ᵥ (fun _ => 1) ∧
    ∀ ν : ℕ, ∀ x : ℝ, 0 ≤ x →
      HasSum
        (fun j : ℕ => (Real.exp (-c * x) * (c * x) ^ (j + ν) / ((j + ν).factorial : ℝ)) •
          unifK τ T c (j + ν) ν)
        (countProb τ T ν x) :=
  g77_uniformization τ T hrep c hc_ge hc_attained
