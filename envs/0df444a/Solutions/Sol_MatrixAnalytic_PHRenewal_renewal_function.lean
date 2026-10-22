-- Prove2me | solution 1 for MatrixAnalytic.PHRenewal.renewal_function
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T04:13:01.862511+00:00
-- url     : https://prove2.me/submissions/a18bcb36-9bcb-488a-80f5-4e57a68962a8

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep
import Definitions.Def_MatrixAnalytic_PHRenewal_Counting

open Matrix MeasureTheory Filter Topology

section g69d1sec
open scoped Norms.Operator

theorem g69d1_expser {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (a b : m) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • M ^ n) a b) (NormedSpace.exp M a b) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M
  exact Pi.hasSum.1 (Pi.hasSum.1 h a) b

theorem g69d1_pow_nonneg {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (n : ℕ) : ∀ i j, 0 ≤ (M ^ n) i j := by
  induction n with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j; rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hM k j)

theorem g69d1_exp_nonneg_of_nonneg {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (i j : m) : 0 ≤ NormedSpace.exp M i j := by
  refine (g69d1_expser M i j).nonneg fun n => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (g69d1_pow_nonneg M hM n i j)

theorem g69d1_exp_metzler_nonneg {m : Type*} [Fintype m] [DecidableEq m] (T : Matrix m m ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ T i j) (x : ℝ) (hx : 0 ≤ x) (i j : m) :
    0 ≤ NormedSpace.exp (x • T) i j := by
  set c : ℝ := ∑ k, |T k k|
  set M : Matrix m m ℝ := T + algebraMap ℝ (Matrix m m ℝ) c
  have hM : ∀ i j, 0 ≤ M i j := by
    intro i j
    simp only [M, Matrix.add_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j
    · subst h; simp only [if_true]
      have : |T i i| ≤ c := Finset.single_le_sum (f := fun k => |T k k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ i)
      have := neg_abs_le (T i i)
      simp only [Algebra.algebraMap_self, RingHom.id_apply]; linarith
    · rw [if_neg h, add_zero]; exact hoff i j h
  have hsplit : x • T = x • M + algebraMap ℝ (Matrix m m ℝ) (-(x * c)) := by
    ext a b
    simp only [M, Matrix.smul_apply, Matrix.add_apply, Matrix.algebraMap_matrix_apply,
      smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
    split_ifs <;> ring
  have hcomm : Commute (x • M) (algebraMap ℝ (Matrix m m ℝ) (-(x * c))) :=
    (Algebra.commutes _ _).symm
  have hal := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix m m ℝ) (-(x * c))
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm]
  erw [← hal]
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, Matrix.smul_apply, smul_eq_mul]
  refine mul_nonneg ?_ (g69d1_exp_nonneg_of_nonneg _ (fun a b => mul_nonneg hx (hM a b)) i j)
  rw [← Real.exp_eq_exp_ℝ]; exact (Real.exp_pos _).le

/-- derivative of a linear functional of exp(yT) -/
theorem g69d1_deriv_lin {m : Type*} [Fintype m] [DecidableEq m] (T : Matrix m m ℝ)
    (L : Matrix m m ℝ →ₗ[ℝ] ℝ) (x : ℝ) :
    HasDerivAt (fun y => L (NormedSpace.exp (y • T))) (L (NormedSpace.exp (x • T) * T)) x := by
  have hd := (hasDerivAt_exp_smul_const (𝕂 := ℝ) T x)
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt x hd

theorem g69d1_exp_add {m : Type*} [Fintype m] [DecidableEq m] (T : Matrix m m ℝ) (x s : ℝ) :
    NormedSpace.exp ((x + s) • T) = NormedSpace.exp (s • T) * NormedSpace.exp (x • T) := by
  rw [add_comm, add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl T).smul_left s).smul_right x

end g69d1sec

theorem g69d1_integral_gen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hoff : ∀ i j, i ≠ j → 0 ≤ T i j)
    (hex : ∀ i, 0 ≤ (-(T *ᵥ fun _ => (1:ℝ))) i) (hdet : IsUnit T.det) :
    ∀ i j : ι,
      IntegrableOn (fun x : ℝ => NormedSpace.exp (x • T) i j) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), NormedSpace.exp (x • T) i j = (-T⁻¹) i j := by
  set E : ℝ → Matrix ι ι ℝ := fun x => NormedSpace.exp (x • T) with hE
  have hnn : ∀ x, 0 ≤ x → ∀ i j, 0 ≤ E x i j := fun x hx i j =>
    g69d1_exp_metzler_nonneg T hoff x hx i j
  set one : ι → ℝ := fun _ => 1
  -- row sums
  set v : ℝ → ι → ℝ := fun x => E x *ᵥ one with hv
  have hvd : ∀ i x, HasDerivAt (fun y => v y i) (-(E x *ᵥ (-(T *ᵥ fun _ => (1:ℝ)))) i) x := by
    intro i x
    let L : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
      { toFun := fun M => (M *ᵥ one) i
        map_add' := by intro M N; simp [add_mulVec]
        map_smul' := by intro c M; simp [smul_mulVec] }
    have := g69d1_deriv_lin T L x
    refine this.congr_deriv ?_
    show ((E x * T) *ᵥ one) i = _
    rw [← mulVec_mulVec, mulVec_neg, Pi.neg_apply, neg_neg]
  have hvnn : ∀ i x, 0 ≤ x → 0 ≤ v x i := fun i x hx =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hnn x hx i j) (by norm_num)
  have hanti : ∀ i, AntitoneOn (fun y => v y i) (Set.Ici 0) := by
    intro i
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · exact fun x _ => (hvd i x).continuousAt.continuousWithinAt
    · exact fun x _ => (hvd i x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hvd i x).deriv, neg_nonpos]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hnn x (le_of_lt hx) i j) (hex j)
  -- limits
  have hlim : ∀ i, ∃ l, Tendsto (fun y => v y i) atTop (𝓝 l) := by
    intro i
    let g : ℝ → ℝ := fun y => v (max y 0) i
    have hg : Antitone g := fun a b hab =>
      hanti i (le_max_right a 0) (le_max_right b 0) (max_le_max hab le_rfl)
    have hb : BddBelow (Set.range g) := ⟨0, by rintro _ ⟨y, rfl⟩; exact hvnn i _ (le_max_right _ _)⟩
    refine ⟨_, (tendsto_atTop_ciInf hg hb).congr' ?_⟩
    filter_upwards [eventually_ge_atTop 0] with y hy
    simp [g, max_eq_left hy]
  choose l hl using hlim
  have hinv : ∀ s, 0 ≤ s → E s *ᵥ l = l := by
    intro s hs
    funext i
    have h1 : Tendsto (fun y => (E s *ᵥ v y) i) atTop (𝓝 ((E s *ᵥ l) i)) := by
      simp only [mulVec, dotProduct]
      exact tendsto_finsetSum _ fun j _ => (hl j).const_mul _
    have h2 : (fun y => (E s *ᵥ v y) i) = fun y => v (y + s) i := by
      funext y
      simp only [hv, hE, mulVec_mulVec, g69d1_exp_add]
    rw [h2] at h1
    exact tendsto_nhds_unique h1 ((hl i).comp (tendsto_atTop_add_const_right _ s tendsto_id))
  have hinv' : ∀ s, E s *ᵥ l = l := by
    intro s
    rcases le_total 0 s with hs | hs
    · exact hinv s hs
    · have h0 : E s * E (-s) = 1 := by
        simp only [hE]; rw [← g69d1_exp_add]; simp
      conv_lhs => rw [← hinv (-s) (by linarith), mulVec_mulVec, h0, one_mulVec]
  have hTl : T *ᵥ l = 0 := by
    funext i
    let L : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
      { toFun := fun M => (M *ᵥ l) i
        map_add' := by intro M N; simp [add_mulVec]
        map_smul' := by intro c M; simp [smul_mulVec] }
    have h1 := g69d1_deriv_lin T L 0
    have h2 : (fun y : ℝ => L (NormedSpace.exp (y • T))) = fun _ => l i := by
      funext y; exact congrFun (hinv' y) i
    rw [h2] at h1
    have := h1.unique (hasDerivAt_const (0:ℝ) (l i))
    simpa [L] using this
  have hl0 : l = 0 := by
    have : T⁻¹ *ᵥ (T *ᵥ l) = l := by
      rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
    rw [← this, hTl, mulVec_zero]
  -- entries tend to zero
  have hE0 : ∀ i j, Tendsto (fun y => E y i j) atTop (𝓝 0) := by
    intro i j
    have := hl i
    rw [hl0] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with y hy using hnn y hy i j
    · filter_upwards [eventually_ge_atTop 0] with y hy
      show E y i j ≤ ∑ k, E y i k * 1
      simp only [mul_one]
      exact Finset.single_le_sum (f := fun k => E y i k) (fun k _ => hnn y hy i k)
        (Finset.mem_univ j)
  intro i j
  set F : ℝ → ℝ := fun y => (E y * T⁻¹) i j
  have hFd : ∀ x, HasDerivAt F (E x i j) x := by
    intro x
    let L : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
      { toFun := fun M => (M * T⁻¹) i j
        map_add' := by intro M N; simp [add_mul]
        map_smul' := by intro c M; simp }
    have := g69d1_deriv_lin T L x
    refine this.congr_deriv ?_
    show (E x * T * T⁻¹) i j = _
    rw [mul_assoc, mul_nonsing_inv _ hdet, mul_one]
  have hF0 : Tendsto F atTop (𝓝 0) := by
    have : Tendsto (fun y => ∑ k, E y i k * T⁻¹ k j) atTop (𝓝 (∑ k : ι, (0:ℝ) * T⁻¹ k j)) :=
      tendsto_finsetSum _ fun k _ => (hE0 i k).mul_const _
    simpa [F, Matrix.mul_apply] using this
  have hderiv : ∀ x ∈ Set.Ici (0:ℝ), HasDerivAt F (E x i j) x := fun x _ => hFd x
  have hpos : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ E x i j := fun x hx => hnn x (le_of_lt hx) i j
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hF0, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hF0]
  simp [F, hE]

theorem g69d1_neg_inv_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hoff : ∀ i j, i ≠ j → 0 ≤ T i j)
    (hex : ∀ i, 0 ≤ (-(T *ᵥ fun _ => (1:ℝ))) i) (hdet : IsUnit T.det) (i j : ι) :
    0 ≤ (-T⁻¹) i j := by
  rw [← (g69d1_integral_gen T hoff hex hdet i j).2]
  refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
  exact g69d1_exp_metzler_nonneg T hoff x (le_of_lt hx) i j



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


open Matrix MeasureTheory Filter Topology
open MatrixAnalytic.PHRenewal

theorem g77coef_succ_right {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) :
    ∀ n k, g77coef A B (n + 1) k =
      g77coef A B n k * A + (if k = 0 then 0 else g77coef A B n (k - 1) * B) := by
  intro n
  induction n with
  | zero =>
    intro k
    rcases k with _ | _ | k
    · simp [g77coef]
    · simp [g77coef]
    · simp [g77coef]
  | succ n ih =>
    intro k
    rw [g77coef_succ A B (n + 1) k]
    rcases k with _ | k
    · simp only [g77coef, if_true, add_zero]
      exact (Commute.self_pow A (n + 1)).eq
    · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rcases k with _ | k
      · calc A * g77coef A B (n + 1) 1 + B * g77coef A B (n + 1) 0
            = A * (g77coef A B n 1 * A + g77coef A B n 0 * B) + B * (g77coef A B n 0 * A) := by
              rw [ih 1, ih 0]; simp
          _ = (A * g77coef A B n 1 + B * g77coef A B n 0) * A + (A * g77coef A B n 0) * B := by
              have hc : A * g77coef A B n 0 = g77coef A B n 0 * A := by
                simp only [g77coef]; exact (Commute.self_pow A n).eq
              simp only [mul_add, add_mul, ← mul_assoc, hc]; abel
          _ = _ := by rw [g77coef_succ A B n 1, g77coef_succ A B n 0]; simp
      · calc A * g77coef A B (n + 1) (k + 2) + B * g77coef A B (n + 1) (k + 1)
            = A * (g77coef A B n (k + 2) * A + g77coef A B n (k + 1) * B) +
                B * (g77coef A B n (k + 1) * A + g77coef A B n k * B) := by
              rw [ih (k + 2), ih (k + 1)]; simp
          _ = (A * g77coef A B n (k + 2) + B * g77coef A B n (k + 1)) * A +
                (A * g77coef A B n (k + 1) + B * g77coef A B n k) * B := by
              simp only [mul_add, add_mul, mul_assoc]; abel
          _ = _ := by rw [g77coef_succ A B n (k + 2), g77coef_succ A B n (k + 1)]; simp

/-- `∑ k k c(n,k) u` -/
noncomputable def g77m {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (u : ι → ℝ)
    (n : ℕ) : ι → ℝ :=
  ∑ k ∈ Finset.range (n + 1), (k : ℝ) • (g77coef A B n k *ᵥ u)

theorem g77m_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (u : ι → ℝ)
    (hD : (A + B) *ᵥ u = 0) (n : ℕ) :
    g77m A B u (n + 1) = (A + B) ^ n *ᵥ (B *ᵥ u) := by
  have hbin := g77_binom A B 1 n
  simp only [one_smul, one_pow] at hbin
  rw [hbin, Matrix.sum_mulVec]
  unfold g77m
  have h1 : ∀ k : ℕ, (k : ℝ) • (g77coef A B (n + 1) k *ᵥ u) =
      (k : ℝ) • (g77coef A B n k *ᵥ (A *ᵥ u)) +
        (if k = 0 then 0 else (k : ℝ) • (g77coef A B n (k - 1) *ᵥ (B *ᵥ u))) := by
    intro k
    rw [g77coef_succ_right, add_mulVec, smul_add, mulVec_mulVec]
    split_ifs
    · simp
    · rw [mulVec_mulVec]
  simp only [h1, Finset.sum_add_distrib]
  have e1 : ∑ k ∈ Finset.range (n + 1 + 1), (k : ℝ) • (g77coef A B n k *ᵥ (A *ᵥ u)) =
      ∑ k ∈ Finset.range (n + 1), (k : ℝ) • (g77coef A B n k *ᵥ (A *ᵥ u)) := by
    rw [Finset.sum_range_succ, g77coef_vanish A B n (n + 1) (by omega), zero_mulVec, smul_zero,
      add_zero]
  have e2 : ∑ k ∈ Finset.range (n + 1 + 1),
      (if k = 0 then 0 else (k : ℝ) • (g77coef A B n (k - 1) *ᵥ (B *ᵥ u))) =
      ∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1) • (g77coef A B n k *ᵥ (B *ᵥ u)) := by
    rw [Finset.sum_range_succ']
    simp
  have hAu : A *ᵥ u = -(B *ᵥ u) := by
    rw [add_mulVec] at hD; exact eq_neg_of_add_eq_zero_left hD
  rw [e1, e2, hAu]
  simp only [mulVec_neg, smul_neg, add_smul, one_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

/-- generic Fubini for triangular coefficient arrays weighted by `xⁿ/n!` -/
theorem g77_fubini (x : ℝ) (a : ℕ → ℕ → ℝ) (hfin : ∀ n k, n < k → a n k = 0) (C D : ℝ)
    (hb : ∀ n, ∑ k ∈ Finset.range (n + 1), |a n k| ≤ D * C ^ n)
    (Pk : ℕ → ℝ) (hPk : ∀ k, HasSum (fun n => ((n.factorial : ℝ)⁻¹ * x ^ n) * a n k) (Pk k))
    (S : ℝ) (hS : HasSum (fun n => ((n.factorial : ℝ)⁻¹ * x ^ n) *
      ∑ k ∈ Finset.range (n + 1), a n k) S) : HasSum Pk S := by
  set c : ℕ → ℝ := fun n => (n.factorial : ℝ)⁻¹ * x ^ n with hc
  set f : ℕ × ℕ → ℝ := fun p => c p.1 * a p.1 p.2 with hf
  set g : ℕ × ℕ → ℝ := fun p => |x| ^ p.1 / (p.1.factorial : ℝ) * |a p.1 p.2|
  have hg0 : 0 ≤ g := fun p => mul_nonneg (by positivity) (abs_nonneg _)
  have hgs : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    have hfin' : ∀ n, ∀ k ∉ Finset.range (n + 1), g (n, k) = 0 := by
      intro n k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [g, hfin n k (by omega)]
    refine ⟨fun n => summable_of_ne_finset_zero (hfin' n), ?_⟩
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k => hg0 _) (fun n => ?_)
      ((Real.summable_pow_div_factorial (|x| * C)).mul_left D)
    rw [tsum_eq_sum (hfin' n)]
    simp only [g]
    rw [← Finset.mul_sum, mul_pow]
    calc |x| ^ n / (n.factorial : ℝ) * ∑ k ∈ Finset.range (n + 1), |a n k|
        ≤ |x| ^ n / (n.factorial : ℝ) * (D * C ^ n) :=
          mul_le_mul_of_nonneg_left (hb n) (by positivity)
      _ = _ := by ring
  have hfs : Summable f := by
    refine Summable.of_norm_bounded hgs fun p => ?_
    simp only [f, c, g, Real.norm_eq_abs, abs_mul, abs_inv, abs_pow, Nat.abs_cast]
    rw [div_eq_inv_mul]
  have hrow : ∀ n, HasSum (fun k => f (n, k)) (c n * ∑ k ∈ Finset.range (n + 1), a n k) := by
    intro n
    have hfin' : ∀ k ∉ Finset.range (n + 1), f (n, k) = 0 := by
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [f, hfin n k (by omega)]
    have hv : c n * ∑ k ∈ Finset.range (n + 1), a n k = ∑ k ∈ Finset.range (n + 1), f (n, k) := by
      rw [Finset.mul_sum]
    rw [hv]; exact hasSum_sum_of_ne_finset_zero hfin'
  have h1 := hfs.hasSum.prod_fiberwise hrow
  have hval : ∑' p, f p = S := h1.unique hS
  have h2 := hfs.prod_symm.hasSum.prod_fiberwise (fun k => hPk k)
  have e3 : ∑' p : ℕ × ℕ, f p.swap = ∑' p, f p := (Equiv.prodComm ℕ ℕ).tsum_eq f
  rw [e3, hval] at h2
  exact h2

theorem g77N_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι ℝ) (n : ℕ) :
    (Matrix.fromBlocks D 1 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) ^ (n + 1) =
      Matrix.fromBlocks (D ^ (n + 1)) (D ^ n) 0 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Matrix.fromBlocks_multiply]
    simp [pow_succ]

theorem g77N_ll {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι ℝ) (y : ℝ) (i j : ι) :
    NormedSpace.exp (y • (Matrix.fromBlocks D 1 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) (Sum.inl i) (Sum.inl j)
      = NormedSpace.exp (y • D) i j := by
  have h1 := g77_expser_smul (Matrix.fromBlocks D 1 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) y (Sum.inl i) (Sum.inl j)
  have h2 := g77_expser_smul D y i j
  have e : ∀ n, ((Matrix.fromBlocks D 1 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) ^ n) (Sum.inl i) (Sum.inl j)
      = (D ^ n) i j := by
    intro n
    rcases n with _ | n
    · simp [Matrix.one_apply]
    · rw [g77N_pow]; simp
  simp only [e] at h1
  exact h1.unique h2

theorem g77N_lr {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι ℝ) (y : ℝ) (i j : ι) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * y ^ n) * (if n = 0 then 0 else (D ^ (n - 1)) i j))
      (NormedSpace.exp (y • (Matrix.fromBlocks D 1 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ))
        (Sum.inl i) (Sum.inr j)) := by
  have h1 := g77_expser_smul (Matrix.fromBlocks D 1 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) y (Sum.inl i) (Sum.inr j)
  have e : ∀ n, ((Matrix.fromBlocks D 1 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) ^ n) (Sum.inl i) (Sum.inr j)
      = if n = 0 then 0 else (D ^ (n - 1)) i j := by
    intro n
    rcases n with _ | n
    · simp [Matrix.one_apply]
    · rw [g77N_pow]; simp
  simp only [e] at h1
  exact h1

section g77sec3
open scoped Norms.Operator

theorem g77_deriv_entry' {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (a b : m) (x : ℝ) :
    HasDerivAt (fun y : ℝ => NormedSpace.exp (y • M) a b) ((NormedSpace.exp (x • M) * M) a b) x := by
  let L : Matrix m m ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun N => N a b
      map_add' := by intro N N'; rfl
      map_smul' := by intro c N; rfl }
  have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) M x
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt x hd

end g77sec3

theorem g77N_deriv {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι ℝ) (x : ℝ) (i j : ι) :
    HasDerivAt (fun y : ℝ => NormedSpace.exp (y • (Matrix.fromBlocks D 1 0 0 :
      Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) (Sum.inl i) (Sum.inr j)) (NormedSpace.exp (x • D) i j) x := by
  refine (g77_deriv_entry' _ _ _ x).congr_deriv ?_
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [Matrix.one_apply, g77N_ll]

theorem g77_absdot {ι : Type*} [Fintype ι] (β : ι → ℝ) (M : Matrix ι ι ℝ) :
    |β ⬝ᵥ (M *ᵥ fun _ => (1:ℝ))| ≤ (∑ i, |β i|) * g77s M := by
  simp only [dotProduct, mulVec, mul_one, g77s]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem g77_meanCount {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hτ : ∑ i, τ i = 1) (β : ι → ℝ) (y : ℝ) :
    HasSum (fun k : ℕ => (k : ℝ) * (β ⬝ᵥ (countProb τ T k y *ᵥ fun _ => 1)))
      (∑ i, ∑ j, β i * NormedSpace.exp (y • (Matrix.fromBlocks (phaseGen τ T) 1 0 0 :
        Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) (Sum.inl i) (Sum.inr j) * exitVec T j) := by
  set B := vecMulVec (exitVec T) τ with hBdef
  set D := phaseGen τ T with hDdef
  have hD : D = T + B := rfl
  simp only [g77_countProb]
  set one : ι → ℝ := fun _ => 1
  have hB1 : B *ᵥ one = exitVec T := by
    funext i; simp [B, one, mulVec, dotProduct, vecMulVec_apply, ← Finset.mul_sum, hτ]
  have hD1 : (T + B) *ᵥ one = 0 := by
    rw [add_mulVec, hB1]; simp [exitVec, one]
  set a : ℕ → ℕ → ℝ := fun n k => (k : ℝ) * (β ⬝ᵥ (g77coef T B n k *ᵥ one)) with ha
  refine g77_fubini y a ?_ ((2:ℝ) * (g77s T + g77s B)) ((∑ i, |β i|) * g77s (1 : Matrix ι ι ℝ))
    ?_ _ ?_ _ ?_
  · intro n k hk; simp [a, g77coef_vanish T B n k hk]
  · intro n
    have hk : ∀ k ∈ Finset.range (n + 1), |a n k| ≤ 2 ^ n * ((∑ i, |β i|) * g77s (g77coef T B n k)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [a, abs_mul, Nat.abs_cast]
      have h1 : (k : ℝ) ≤ 2 ^ n := by
        have : k < 2 ^ n := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self)
        exact_mod_cast this.le
      exact mul_le_mul h1 (g77_absdot β _) (abs_nonneg _) (by positivity)
    refine (Finset.sum_le_sum hk).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hb := g77coef_bound T B n
    have hβ : 0 ≤ ∑ i, |β i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc 2 ^ n * ((∑ i, |β i|) * ∑ k ∈ Finset.range (n + 1), g77s (g77coef T B n k))
        ≤ 2 ^ n * ((∑ i, |β i|) * (g77s (1 : Matrix ι ι ℝ) * (g77s T + g77s B) ^ n)) := by
          gcongr
      _ = _ := by rw [mul_pow]; ring
  · intro k
    have hs : HasSum (fun n => (k : ℝ) * ∑ i, ∑ j, β i *
        (((n.factorial : ℝ)⁻¹ * y ^ n) * g77coef T B n k i j))
        ((k : ℝ) * ∑ i, ∑ j, β i * g77P T B y k i j) :=
      (hasSum_sum fun i _ => hasSum_sum fun j _ => (g77_hasSumP T B y k i j).mul_left (β i)).mul_left _
    have e1 : (fun n => ((n.factorial : ℝ)⁻¹ * y ^ n) * a n k) =
        fun n => (k : ℝ) * ∑ i, ∑ j, β i * (((n.factorial : ℝ)⁻¹ * y ^ n) * g77coef T B n k i j) := by
      funext n
      simp only [a, one, dotProduct, mulVec, mul_one, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have e2 : (k : ℝ) * (β ⬝ᵥ (g77P T B y k *ᵥ one)) = (k : ℝ) * ∑ i, ∑ j, β i * g77P T B y k i j := by
      simp only [one, dotProduct, mulVec, mul_one, Finset.mul_sum]
    rw [e1, e2]; exact hs
  · have hs : HasSum (fun n => ∑ i, ∑ j, β i * ((((n.factorial : ℝ)⁻¹ * y ^ n) *
        (if n = 0 then 0 else (D ^ (n - 1)) i j)) * exitVec T j))
        (∑ i, ∑ j, β i * NormedSpace.exp (y • (Matrix.fromBlocks D 1 0 0 :
          Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) (Sum.inl i) (Sum.inr j) * exitVec T j) := by
      refine hasSum_sum fun i _ => hasSum_sum fun j _ => ?_
      have := ((g77N_lr D y i j).mul_right (exitVec T j)).mul_left (β i)
      rw [← mul_assoc] at this
      exact this
    have e : ∀ n, ((n.factorial : ℝ)⁻¹ * y ^ n) * ∑ k ∈ Finset.range (n + 1), a n k =
        ∑ i, ∑ j, β i * ((((n.factorial : ℝ)⁻¹ * y ^ n) *
          (if n = 0 then 0 else (D ^ (n - 1)) i j)) * exitVec T j) := by
      intro n
      have hm : ∑ k ∈ Finset.range (n + 1), a n k = β ⬝ᵥ g77m T B one n := by
        simp only [a, g77m, dotProduct_sum, dotProduct_smul, smul_eq_mul]
      rw [hm]
      rcases n with _ | n
      · simp [g77m]
      · rw [g77m_succ T B one hD1, hB1, ← hD]
        simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, dotProduct, mulVec,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    simp only [e]
    exact hs

theorem g77_meanCount_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hτ : ∑ i, τ i = 1) (β : ι → ℝ) :
    (fun y => meanCount β τ T y) = fun y => ∑ i, ∑ j, β i * NormedSpace.exp (y •
      (Matrix.fromBlocks (phaseGen τ T) 1 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)) (Sum.inl i) (Sum.inr j) *
        exitVec T j := by
  funext y
  exact (g77_meanCount τ T hτ β y).tsum_eq

theorem g77_renewal_density {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hτ : ∑ i, τ i = 1) (β : ι → ℝ) (x : ℝ) :
    HasDerivAt (fun y => meanCount β τ T y)
      (β ⬝ᵥ (NormedSpace.exp (x • phaseGen τ T) *ᵥ exitVec T)) x := by
  rw [g77_meanCount_eq τ T hτ β]
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (((g77N_deriv (phaseGen τ T) x i j).const_mul (β i)).mul_const (exitVec T j))
  have e : β ⬝ᵥ (NormedSpace.exp (x • phaseGen τ T) *ᵥ exitVec T) =
      ∑ i, ∑ j, β i * NormedSpace.exp (x • phaseGen τ T) i j * exitVec T j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]; exact h


open Matrix MeasureTheory Filter Topology
open MatrixAnalytic.PHRenewal

theorem g77_D_apply {ι : Type*} [Fintype ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ) (a b : ι) :
    phaseGen τ T a b = T a b + exitVec T a * τ b := by
  simp [phaseGen, vecMulVec_apply]

theorem g77_D_one {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hτ : ∑ i, τ i = 1) : phaseGen τ T *ᵥ (fun _ => (1:ℝ)) = 0 := by
  funext a
  simp only [mulVec, dotProduct, mul_one, g77_D_apply, Finset.sum_add_distrib, ← Finset.mul_sum, hτ]
  simp [exitVec, mulVec, dotProduct]

theorem g77_D_irred {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T) :
    ∀ a b, Relation.ReflTransGen (PosRate (phaseGen τ T)) a b := by
  have hTD : ∀ a b, PosRate T a b → PosRate (phaseGen τ T) a b := by
    rintro a b ⟨hab, h⟩
    refine ⟨hab, ?_⟩
    rw [g77_D_apply]
    have := mul_nonneg (hrep.exit_nonneg a) (hrep.tau_nonneg b)
    linarith
  intro a b
  obtain ⟨k, hak, htk⟩ := hirr.1 a
  obtain ⟨i, hτi, hib⟩ := hirr.2 b
  refine (Relation.ReflTransGen.mono hTD _ _ hak).trans
    (Relation.ReflTransGen.trans ?_ (Relation.ReflTransGen.mono hTD _ _ hib))
  by_cases hki : k = i
  · subst hki; exact Relation.ReflTransGen.refl
  · refine Relation.ReflTransGen.single ⟨hki, ?_⟩
    rw [g77_D_apply]
    have := hrep.offDiag_nonneg k i hki
    have := mul_pos htk hτi
    linarith

theorem g77_ker {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T) (v : ι → ℝ)
    (hv : phaseGen τ T *ᵥ v = 0) (i : ι) : ∀ j, v j = v i := by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max v
  have hoffD : ∀ a b, a ≠ b → 0 ≤ phaseGen τ T a b := by
    intro a b hab
    rw [g77_D_apply]
    have := mul_nonneg (hrep.exit_nonneg a) (hrep.tau_nonneg b)
    have := hrep.offDiag_nonneg a b hab
    linarith
  have hstep : ∀ b c, v b = v i0 → PosRate (phaseGen τ T) b c → v c = v i0 := by
    intro b c hb ⟨hbc, hpos⟩
    have h1 : ∑ j, phaseGen τ T b j * (v j - v b) = 0 := by
      have e1 := congrFun hv b
      have e2 := congrFun (g77_D_one τ T hrep.tau_sum_one) b
      simp only [mulVec, dotProduct, mul_one, Pi.zero_apply] at e1 e2
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, e1, e2, zero_mul, sub_zero]
    have hnp : ∀ j ∈ Finset.univ, phaseGen τ T b j * (v j - v b) ≤ 0 := by
      intro j _
      by_cases hj : j = b
      · subst hj; simp
      · exact mul_nonpos_of_nonneg_of_nonpos (hoffD b j (Ne.symm hj)) (by rw [hb]; linarith [hi0 j])
    have := (Finset.sum_eq_zero_iff_of_nonpos hnp).1 h1 c (Finset.mem_univ c)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hpos.ne'
    · linarith
  have hall : ∀ j, v j = v i0 := by
    intro j
    have hp := g77_D_irred τ T hrep hirr i0 j
    induction hp with
    | refl => rfl
    | tail _ hbc ih => exact hstep _ _ ih hbc
  intro j; rw [hall j, hall i]

theorem g77_vmv_mulVec {ι : Type*} [Fintype ι] (u v w : ι → ℝ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem g77_vecMul_vmv {ι : Type*} [Fintype ι] (u v w : ι → ℝ) :
    w ᵥ* vecMulVec u v = (w ⬝ᵥ u) • v := by
  ext i
  simp only [vecMul, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem g77_smul_vecMul {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) (M : Matrix ι ι ℝ) :
    (a • v) ᵥ* M = a • (v ᵥ* M) := by
  funext j; simp [vecMul, dotProduct, Finset.mul_sum, mul_assoc]

/-- facts about `π` -/
theorem g77_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) :
    statVec τ T ⬝ᵥ (fun _ => (1:ℝ)) = 1 ∧ statVec τ T ᵥ* phaseGen τ T = 0 ∧
    statVec τ T ⬝ᵥ exitVec T = (meanInterrenewal τ T)⁻¹ := by
  have hdet := hrep.nonsingular
  set one : ι → ℝ := fun _ => 1
  set u := τ ᵥ* T⁻¹ with hu
  set s := u ⬝ᵥ one with hs
  have hTt : T⁻¹ *ᵥ exitVec T = -one := by
    simp only [exitVec, mulVec_neg, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
    rfl
  have hut : u ⬝ᵥ exitVec T = -1 := by
    rw [hu, ← dotProduct_mulVec, hTt, dotProduct_neg]
    simp [one, dotProduct, hrep.tau_sum_one]
  have hnegT : (-T)⁻¹ = -T⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [neg_mul_neg, nonsing_inv_mul _ hdet]
  have hM : meanInterrenewal τ T = -s := by
    simp only [meanInterrenewal, hnegT, neg_mulVec, dotProduct_neg, hs, hu, dotProduct_mulVec]
    rfl
  -- s ≠ 0
  have hs0 : s ≠ 0 := by
    intro h0
    set w := (-T⁻¹) *ᵥ one with hw
    have hwnn : ∀ i, 0 ≤ w i := fun i => Finset.sum_nonneg fun j _ =>
      mul_nonneg (g69d1_neg_inv_nonneg T hrep.offDiag_nonneg hrep.exit_nonneg hdet i j) (by simp [one])
    have hTw : (-T) *ᵥ w = one := by
      rw [hw, mulVec_mulVec, neg_mul_neg, mul_nonsing_inv _ hdet, one_mulVec]
    have hτw : τ ⬝ᵥ w = 0 := by
      have : s = -(τ ⬝ᵥ w) := by
        rw [hs, hu, ← dotProduct_mulVec, hw, neg_mulVec, dotProduct_neg, neg_neg]
      linarith
    obtain ⟨i, hi⟩ : ∃ i, 0 < τ i := by
      by_contra hcon
      push Not at hcon
      have : ∑ i, τ i ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
      linarith [hrep.tau_sum_one]
    have hwi : w i = 0 := by
      simp only [dotProduct] at hτw
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hrep.tau_nonneg j) (hwnn j)).1
        hτw i (Finset.mem_univ i)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hi.ne'
      · exact h
    have h1 := congrFun hTw i
    simp only [mulVec, dotProduct, one, Matrix.neg_apply] at h1
    have h2 : ∑ j, -T i j * w j ≤ 0 := by
      refine Finset.sum_nonpos fun j _ => ?_
      by_cases hj : j = i
      · subst hj; rw [hwi, mul_zero]
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hrep.offDiag_nonneg i j (Ne.symm hj)]) (hwnn j)
    linarith
  have hpi : statVec τ T = s⁻¹ • u := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hpi, smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hs0]
  · rw [hpi, g77_smul_vecMul]
    have : u ᵥ* phaseGen τ T = 0 := by
      rw [phaseGen, vecMul_add, g77_vecMul_vmv, hut, hu, vecMul_vecMul,
        nonsing_inv_mul _ hdet, vecMul_one]
      simp
    rw [this, smul_zero]
  · rw [hpi, smul_dotProduct, hut, hM, smul_eq_mul, inv_neg]; ring

theorem g77_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T) :
    IsUnit (phaseGen τ T - statMatrix τ T) := by
  obtain ⟨hπ1, hπD, -⟩ := g77_pi τ T hrep
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set π := statVec τ T
  have hPv : statMatrix τ T *ᵥ v = (π ⬝ᵥ v) • (fun _ => (1:ℝ)) := g77_vmv_mulVec _ _ _
  have hπv : π ⬝ᵥ v = 0 := by
    have h1 := congrArg (fun w => π ⬝ᵥ w) hv
    simp only [sub_mulVec, dotProduct_sub, dotProduct_zero, dotProduct_mulVec, hπD, zero_dotProduct,
      hPv, dotProduct_smul, smul_eq_mul, hπ1, mul_one, zero_sub, neg_eq_zero] at h1
    exact h1
  have hDv : phaseGen τ T *ᵥ v = 0 := by
    rw [sub_mulVec, hPv, hπv, zero_smul, sub_zero] at hv; exact hv
  apply hv0
  obtain ⟨i⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hrep.tau_sum_one
    simp at this
  have hc := g77_ker τ T hrep hirr v hDv i
  have hvc : v = v i • (fun _ => (1:ℝ)) := by funext j; simp [hc j]
  rw [hvc, dotProduct_smul, hπ1, smul_eq_mul, mul_one] at hπv
  rw [hvc, hπv, zero_smul]

/-- the upper-right block `W(x) = ∑ xⁿ⁺¹/(n+1)! Dⁿ` -/
noncomputable def g77W {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι ℝ) (x : ℝ) :
    Matrix ι ι ℝ :=
  fun i j => NormedSpace.exp (x • (Matrix.fromBlocks D 1 0 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ))
    (Sum.inl i) (Sum.inr j)

theorem g77W_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι ℝ) (x : ℝ) :
    g77W D x * D = NormedSpace.exp (x • D) - 1 := by
  ext i j
  have h1 : HasSum (fun n : ℕ => ∑ l, (((n.factorial : ℝ)⁻¹ * x ^ n) *
      (if n = 0 then 0 else (D ^ (n - 1)) i l)) * D l j) ((g77W D x * D) i j) := by
    rw [Matrix.mul_apply]
    exact hasSum_sum fun l _ => (g77N_lr D x i l).mul_right (D l j)
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * x ^ n) * (D ^ n) i j -
      (if n = 0 then (1 : Matrix ι ι ℝ) i j else 0)) (NormedSpace.exp (x • D) i j - (1 : Matrix ι ι ℝ) i j) :=
    (g77_expser_smul D x i j).sub (hasSum_ite_eq 0 _)
  rw [Matrix.sub_apply]
  refine h1.unique (h2.congr_fun ?_)
  intro n
  rcases n with _ | n
  · simp
  · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, sub_zero]
    rw [show (D ^ (n + 1)) i j = ∑ l, (D ^ n) i l * D l j by rw [pow_succ, Matrix.mul_apply],
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem g77W_one {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι ℝ)
    (hD1 : D *ᵥ (fun _ => (1:ℝ)) = 0) (x : ℝ) :
    g77W D x *ᵥ (fun _ => (1:ℝ)) = x • (fun _ => (1:ℝ)) := by
  funext i
  have h1 : HasSum (fun n : ℕ => ∑ j, (((n.factorial : ℝ)⁻¹ * x ^ n) *
      (if n = 0 then 0 else (D ^ (n - 1)) i j)) * 1) ((g77W D x *ᵥ (fun _ => (1:ℝ))) i) := by
    simp only [mulVec, dotProduct]
    exact hasSum_sum fun j _ => (g77N_lr D x i j).mul_right 1
  have hpow : ∀ m, (D ^ (m + 1)) *ᵥ (fun _ => (1:ℝ)) = 0 := by
    intro m; rw [pow_succ, ← mulVec_mulVec, hD1, mulVec_zero]
  have h2 : HasSum (fun n : ℕ => if n = 1 then x else 0) x := hasSum_ite_eq 1 x
  simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  refine h1.unique (h2.congr_fun ?_)
  intro n
  rcases n with _ | _ | n
  · simp
  · simp [Matrix.one_apply]
  · simp only [mul_one, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, ← Finset.mul_sum]
    have := congrFun (hpow n) i
    simp only [mulVec, dotProduct, mul_one, Pi.zero_apply] at this
    rw [this, mul_zero]; simp

theorem g77_renewal_function {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T) (x : ℝ) :
    IsUnit (phaseGen τ T - statMatrix τ T) ∧
    Summable (fun k : ℕ => (k : ℝ) * (τ ⬝ᵥ (countProb τ T k x *ᵥ fun _ => 1))) ∧
    renewalFunction τ T x =
      1 + x * (meanInterrenewal τ T)⁻¹ +
        τ ⬝ᵥ (((NormedSpace.exp (x • phaseGen τ T) - 1) *
          (phaseGen τ T - statMatrix τ T)⁻¹) *ᵥ exitVec T) := by
  have hU := g77_isUnit τ T hrep hirr
  have hmc := g77_meanCount τ T hrep.tau_sum_one τ x
  refine ⟨hU, hmc.summable, ?_⟩
  obtain ⟨hπ1, hπD, hπt⟩ := g77_pi τ T hrep
  set D := phaseGen τ T
  set Pm := statMatrix τ T with hPdef
  set G := D - Pm
  set W := g77W D x
  set one : ι → ℝ := fun _ => 1
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hU
  have hD1 : D *ᵥ one = 0 := g77_D_one τ T hrep.tau_sum_one
  -- meanCount = τ W t
  have hmean : meanCount τ τ T x = τ ⬝ᵥ (W *ᵥ exitVec T) := by
    rw [show meanCount τ τ T x = _ from hmc.tsum_eq]
    simp only [dotProduct, mulVec, Finset.mul_sum, W, g77W]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  -- Π identities
  have hP' : Pm = vecMulVec one (statVec τ T) := rfl
  have hWP : W * Pm = x • Pm := by
    rw [hP']
    ext i j
    simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    have := congrFun (g77W_one D hD1 x) i
    simp only [mulVec, dotProduct, mul_one, Pi.smul_apply, smul_eq_mul, one] at this
    simp only [one, one_mul]
    rw [← Finset.sum_mul, this]
  have hPG : Pm * G = -Pm := by
    simp only [G, mul_sub]
    have h1 : Pm * D = 0 := by
      rw [hP']; ext i j
      have := congrFun hπD j
      simp only [vecMul, dotProduct, Pi.zero_apply] at this
      simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply, mul_assoc, ← Finset.mul_sum,
        this, mul_zero]
    have h2 : Pm * Pm = Pm := by
      rw [hP']; ext i j
      simp only [Matrix.mul_apply, vecMulVec_apply]
      have : ∑ l, one i * statVec τ T l * (one l * statVec τ T j) =
          one i * statVec τ T j * (statVec τ T ⬝ᵥ one) := by
        simp only [dotProduct, Finset.mul_sum, one]; refine Finset.sum_congr rfl fun l _ => ?_; ring
      rw [this, hπ1, mul_one]
    rw [h1, h2, zero_sub]
  have hPGinv : Pm * G⁻¹ = -Pm := by
    have : Pm = -(Pm * G) := by rw [hPG, neg_neg]
    calc Pm * G⁻¹ = -(Pm * G) * G⁻¹ := by rw [← this]
      _ = -Pm := by rw [neg_mul, mul_assoc, mul_nonsing_inv _ hGdet, mul_one]
  have hWG : W * G = (NormedSpace.exp (x • D) - 1) - x • Pm := by
    simp only [G, mul_sub, W, g77W_mul, ← hWP]
  have hW : W = (NormedSpace.exp (x • D) - 1) * G⁻¹ + x • Pm := by
    calc W = W * G * G⁻¹ := by rw [mul_assoc, mul_nonsing_inv _ hGdet, mul_one]
      _ = _ := by rw [hWG, sub_mul, smul_mul_assoc, hPGinv, smul_neg, sub_neg_eq_add]
  have hPt : τ ⬝ᵥ (Pm *ᵥ exitVec T) = (meanInterrenewal τ T)⁻¹ := by
    rw [hP', g77_vmv_mulVec, hπt, dotProduct_smul, smul_eq_mul]
    simp [one, dotProduct, hrep.tau_sum_one]
  rw [renewalFunction, hmean, hW, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, hPt,
    smul_eq_mul]
  ring

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T)
    (x : ℝ) (hx : 0 ≤ x) :
    IsUnit (phaseGen τ T - statMatrix τ T) ∧
    Summable (fun k : ℕ => (k : ℝ) * (τ ⬝ᵥ (countProb τ T k x *ᵥ fun _ => 1))) ∧
    renewalFunction τ T x =
      1 + x * (meanInterrenewal τ T)⁻¹ +
        τ ⬝ᵥ (((NormedSpace.exp (x • phaseGen τ T) - 1) *
          (phaseGen τ T - statMatrix τ T)⁻¹) *ᵥ exitVec T) :=
  g77_renewal_function τ T hrep hirr x
