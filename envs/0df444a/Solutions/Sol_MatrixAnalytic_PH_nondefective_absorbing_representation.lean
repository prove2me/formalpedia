-- Prove2me | solution 1 for MatrixAnalytic.PH.nondefective_absorbing_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T03:50:57.369533+00:00
-- url     : https://prove2.me/submissions/53ea458b-649a-4ffc-be59-e251fe55cbde

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open Matrix
open MatrixAnalytic.PH
open scoped Norms.Operator

@[simp] theorem g69d1_G_n {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (b) :
    generator T none b = 0 := rfl
@[simp] theorem g69d1_G_sn {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (j : ι) :
    generator T (some j) none = exitRates T j := rfl
@[simp] theorem g69d1_G_ss {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (i j : ι) :
    generator T (some i) (some j) = T i j := rfl

theorem g69d1_Gpow_none {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (k : ℕ)
    (b : Option ι) : (generator T ^ (k + 1)) none b = 0 := by
  rw [pow_succ', Matrix.mul_apply]; simp

theorem g69d1_Gpow_some {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (k : ℕ) :
    ∀ i j, (generator T ^ k) (some i) (some j) = (T ^ k) i j := by
  induction k with
  | zero => intro i j; simp [Matrix.one_apply]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply, Fintype.sum_option, pow_succ, Matrix.mul_apply]
    simp [ih]

theorem g69d1_G_rowsum {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (k : ℕ) :
    (generator T ^ (k + 1)) *ᵥ (fun _ => (1:ℝ)) = 0 := by
  have h1 : generator T *ᵥ (fun _ => (1:ℝ)) = 0 := by
    funext a
    cases a with
    | none => simp [mulVec, dotProduct, Fintype.sum_option]
    | some i => simp [mulVec, dotProduct, Fintype.sum_option, exitRates]
  rw [pow_succ, ← mulVec_mulVec, h1, mulVec_zero]

theorem g69d1_expser {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (a b : m) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • M ^ n) a b) (NormedSpace.exp M a b) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M
  exact Pi.hasSum.1 (Pi.hasSum.1 h a) b

theorem g69d1_exp_ss {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (x : ℝ)
    (i j : ι) : transFun T x (some i) (some j) = NormedSpace.exp (x • T) i j := by
  have h1 := g69d1_expser (x • generator T) (some i) (some j)
  have h2 := g69d1_expser (x • T) i j
  simp only [smul_pow, Matrix.smul_apply, g69d1_Gpow_some] at h1 h2
  exact h1.unique h2

theorem g69d1_exp_nn {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (x : ℝ) :
    transFun T x none none = 1 := by
  have h1 := g69d1_expser (x • generator T) none none
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • (x • generator T) ^ n) none none)
      1 := by
    convert hasSum_ite_eq 0 (1:ℝ) using 1
    funext n
    cases n with
    | zero => simp
    | succ n => simp [smul_pow, g69d1_Gpow_none]
  exact h1.unique h2

theorem g69d1_exp_rowsum {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (x : ℝ)
    (a : Option ι) : ∑ b, transFun T x a b = 1 := by
  have h1 : HasSum (fun n : ℕ => ∑ b, ((n.factorial : ℝ)⁻¹ • (x • generator T) ^ n) a b)
      (∑ b, transFun T x a b) := hasSum_sum fun b _ => g69d1_expser _ a b
  have h2 : HasSum (fun n : ℕ => ∑ b, ((n.factorial : ℝ)⁻¹ • (x • generator T) ^ n) a b) 1 := by
    convert hasSum_ite_eq 0 (1:ℝ) using 1
    funext n
    cases n with
    | zero => simp [Matrix.one_apply]
    | succ n =>
      have := congrFun (g69d1_G_rowsum T n) a
      simp only [mulVec, dotProduct, mul_one, Pi.zero_apply] at this
      simp [smul_pow, ← Finset.mul_sum, this]
  exact h1.unique h2


open MeasureTheory Filter Topology

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


theorem g69d1_integral_gen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hoff : ∀ i j, i ≠ j → 0 ≤ T i j)
    (hex : ∀ i, 0 ≤ (-(T *ᵥ fun _ => (1:ℝ))) i) (hdet : IsUnit T.det) :
    ∀ i j : ι,
      IntegrableOn (fun x : ℝ => NormedSpace.exp (x • T) i j) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), NormedSpace.exp (x • T) i j = (-T⁻¹) i j ∧
      Tendsto (fun x : ℝ => NormedSpace.exp (x • T) i j) atTop (𝓝 0) := by
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
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hF0, ?_, hE0 i j⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hF0]
  simp [F, hE]


theorem g77_sn {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (x : ℝ) (i : ι) :
    transFun T x (some i) none = 1 - ∑ j, NormedSpace.exp (x • T) i j := by
  have := g69d1_exp_rowsum T x (some i)
  rw [Fintype.sum_option] at this
  simp only [g69d1_exp_ss] at this
  linarith

theorem g77_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hoff : ∀ i j, i ≠ j → 0 ≤ T i j)
    (hex : ∀ i, 0 ≤ (-(T *ᵥ fun _ => (1:ℝ))) i) :
    ∃ l : ι → ℝ, (∀ i, Tendsto (fun y : ℝ => (NormedSpace.exp (y • T) *ᵥ fun _ => (1:ℝ)) i)
      atTop (𝓝 (l i))) ∧ (∀ i, 0 ≤ l i) ∧ T *ᵥ l = 0 := by
  set E : ℝ → Matrix ι ι ℝ := fun x => NormedSpace.exp (x • T) with hE
  have hnn : ∀ x, 0 ≤ x → ∀ i j, 0 ≤ E x i j := fun x hx i j =>
    g69d1_exp_metzler_nonneg T hoff x hx i j
  set one : ι → ℝ := fun _ => 1
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
  refine ⟨l, hl, fun i => ?_, hTl⟩
  exact ge_of_tendsto (hl i) (by filter_upwards [eventually_ge_atTop 0] with y hy using hvnn i y hy)

/-- powers of a restriction to a closed set of indices -/
theorem g77_pow_restrict {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : Matrix ι ι ℝ) (g : κ → ι) (hg : Function.Injective g)
    (hcl : ∀ a k, k ∉ Set.range g → T (g a) k = 0) (n : ℕ) :
    (∀ a b, (T.submatrix g g ^ n) a b = (T ^ n) (g a) (g b)) ∧
    (∀ a k, k ∉ Set.range g → (T ^ n) (g a) k = 0) := by
  induction n with
  | zero =>
    refine ⟨fun a b => ?_, fun a k hk => ?_⟩
    · simp [Matrix.one_apply, hg.eq_iff]
    · rw [pow_zero, Matrix.one_apply, if_neg]
      rintro rfl; exact hk ⟨a, rfl⟩
  | succ n ih =>
    refine ⟨fun a b => ?_, fun a k hk => ?_⟩
    · rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
      refine Fintype.sum_of_injective g hg (fun c => T.submatrix g g a c * (T.submatrix g g ^ n) c b)
        (fun k => T (g a) k * (T ^ n) k (g b)) ?_ ?_
      · intro k hk; rw [hcl a k hk, zero_mul]
      · intro c; rw [ih.1]; rfl
    · rw [pow_succ', Matrix.mul_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j ∈ Set.range g
      · obtain ⟨c, rfl⟩ := hj; rw [ih.2 c k hk, mul_zero]
      · rw [hcl a j hj, zero_mul]

theorem g77_exp_restrict {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : Matrix ι ι ℝ) (g : κ → ι) (hg : Function.Injective g)
    (hcl : ∀ a k, k ∉ Set.range g → T (g a) k = 0) (x : ℝ) :
    (∀ a b, NormedSpace.exp (x • T.submatrix g g) a b = NormedSpace.exp (x • T) (g a) (g b)) ∧
    (∀ a k, k ∉ Set.range g → NormedSpace.exp (x • T) (g a) k = 0) := by
  constructor
  · intro a b
    have h1 := g69d1_expser (x • T.submatrix g g) a b
    have h2 := g69d1_expser (x • T) (g a) (g b)
    simp only [smul_pow, Matrix.smul_apply, (g77_pow_restrict T g hg hcl _).1] at h1 h2
    exact h1.unique h2
  · intro a k hk
    have h2 := g69d1_expser (x • T) (g a) k
    simp only [smul_pow, Matrix.smul_apply, (g77_pow_restrict T g hg hcl _).2 a k hk,
      smul_zero] at h2
    exact h2.unique (hasSum_zero (α := ℝ))

theorem g77_cdf_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (x : ℝ) :
    cdf τ T x = 1 - τ ⬝ᵥ (NormedSpace.exp (x • T) *ᵥ fun _ => (1 : ℝ)) := by
  have hsn : ∀ i, transFun T x (some i) none = 1 - (NormedSpace.exp (x • T) *ᵥ fun _ => (1 : ℝ)) i := by
    intro i
    have := g69d1_exp_rowsum T x (some i)
    rw [Fintype.sum_option] at this
    simp only [g69d1_exp_ss, mulVec, dotProduct, mul_one] at this ⊢
    linarith
  unfold cdf
  rw [Fintype.sum_option]
  simp only [initDist, g69d1_exp_nn, hsn, mul_sub, mul_one, Finset.sum_sub_distrib, initAtom,
    dotProduct]
  ring

theorem g77_nondef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (hrep : IsPHRep τ T) (hnd : Nondefective τ T) :
    ∃ (m : ℕ) (τ' : Fin m → ℝ) (T' : Matrix (Fin m) (Fin m) ℝ),
      IsPHRep τ' T' ∧ (∀ i, AbsorbedAS T' i) ∧ ∀ x : ℝ, 0 ≤ x → cdf τ' T' x = cdf τ T x := by
  have hoff : ∀ i j, i ≠ j → 0 ≤ T i j := hrep.generator.offDiag_nonneg
  have hex : ∀ i, 0 ≤ (-(T *ᵥ fun _ => (1:ℝ))) i := hrep.generator.exitRates_nonneg
  obtain ⟨l, hl, hl0, hTl⟩ := g77_limit T hoff hex
  set e := Fintype.equivFin {i // l i = 0}
  set g : Fin (Fintype.card {i // l i = 0}) → ι := fun a => (e.symm a).1 with hgdef
  have hg : Function.Injective g := fun a b h => e.symm.injective (Subtype.ext h)
  have hrange : ∀ k, k ∈ Set.range g ↔ l k = 0 := by
    intro k; constructor
    · rintro ⟨a, rfl⟩; exact (e.symm a).2
    · intro hk; exact ⟨e ⟨k, hk⟩, by simp [g]⟩
  have hlg : ∀ a, l (g a) = 0 := fun a => (hrange _).1 ⟨a, rfl⟩
  have hcl : ∀ a k, k ∉ Set.range g → T (g a) k = 0 := by
    intro a k hk
    have hlk : 0 < l k := lt_of_le_of_ne (hl0 k) (fun h => hk ((hrange k).2 h.symm))
    have h1 := congrFun hTl (g a)
    simp only [mulVec, dotProduct, Pi.zero_apply] at h1
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ T (g a) j * l j := by
      intro j _
      by_cases hj : j = g a
      · subst hj; rw [hlg a, mul_zero]
      · exact mul_nonneg (hoff _ _ (Ne.symm hj)) (hl0 j)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1 k (Finset.mem_univ k)
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h hlk.ne'
  -- τ vanishes off the range
  have hτl : ∀ i, τ i * l i = 0 := by
    have h1 : Tendsto (fun y : ℝ => τ ⬝ᵥ (NormedSpace.exp (y • T) *ᵥ fun _ => (1 : ℝ))) atTop
        (𝓝 (τ ⬝ᵥ l)) := by
      simp only [dotProduct]
      exact tendsto_finsetSum _ fun i _ => (hl i).const_mul _
    have h2 : Tendsto (fun y : ℝ => τ ⬝ᵥ (NormedSpace.exp (y • T) *ᵥ fun _ => (1 : ℝ))) atTop
        (𝓝 0) := by
      have := hnd.const_sub (1:ℝ)
      simp only [g77_cdf_eq, sub_sub_cancel, sub_self] at this
      exact this
    have h3 : τ ⬝ᵥ l = 0 := tendsto_nhds_unique h1 h2
    simp only [dotProduct] at h3
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hrep.init_nonneg i) (hl0 i)).1 h3 i (Finset.mem_univ i)
  have hτ0 : ∀ k, k ∉ Set.range g → τ k = 0 := by
    intro k hk
    have hlk : l k ≠ 0 := fun h => hk ((hrange k).2 h)
    rcases mul_eq_zero.1 (hτl k) with h | h
    · exact h
    · exact absurd h hlk
  have hrow : ∀ (x : ℝ) a, ∑ b, NormedSpace.exp (x • T.submatrix g g) a b =
      (NormedSpace.exp (x • T) *ᵥ fun _ => (1 : ℝ)) (g a) := by
    intro x a
    have hr := g77_exp_restrict T g hg hcl x
    simp only [mulVec, dotProduct, mul_one]
    refine Fintype.sum_of_injective g hg (fun b => NormedSpace.exp (x • T.submatrix g g) a b)
      (fun k => NormedSpace.exp (x • T) (g a) k) ?_ ?_
    · intro k hk; exact hr.2 a k hk
    · intro b; exact hr.1 a b
  refine ⟨_, τ ∘ g, T.submatrix g g, ?_, ?_, ?_⟩
  · refine ⟨⟨fun a => hrep.generator.diag_neg (g a), fun a b hab => hoff _ _ (hg.ne hab), ?_⟩,
      fun a => hrep.init_nonneg (g a), ?_⟩
    · intro a
      have : exitRates (T.submatrix g g) a = exitRates T (g a) := by
        simp only [exitRates, mulVec, dotProduct, mul_one, Pi.neg_apply]
        congr 1
        refine Fintype.sum_of_injective g hg (fun b => T.submatrix g g a b)
          (fun k => T (g a) k) ?_ ?_
        · intro k hk; exact hcl a k hk
        · intro b; rfl
      rw [this]; exact hrep.generator.exitRates_nonneg (g a)
    · have : initAtom (τ ∘ g) = initAtom τ := by
        simp only [initAtom]
        congr 1
        exact Fintype.sum_of_injective g hg (fun b => (τ ∘ g) b) τ hτ0 (fun b => rfl)
      rw [this]; exact hrep.initAtom_nonneg
  · intro a
    unfold AbsorbedAS
    simp only [g77_sn, hrow]
    have := (hl (g a)).const_sub (1:ℝ)
    rwa [hlg a, sub_zero] at this
  · intro x _
    rw [g77_cdf_eq, g77_cdf_eq]
    congr 1
    simp only [dotProduct]
    refine Fintype.sum_of_injective g hg _ _ ?_ ?_
    · intro k hk; rw [hτ0 k hk, zero_mul]
    · intro b
      simp only [Function.comp, mulVec, dotProduct, mul_one]
      congr 1
      have := hrow x b
      simp only [mulVec, dotProduct, mul_one] at this
      exact this

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (hrep : IsPHRep τ T) (hnd : Nondefective τ T) :
    ∃ (m : ℕ) (τ' : Fin m → ℝ) (T' : Matrix (Fin m) (Fin m) ℝ),
      IsPHRep τ' T' ∧ (∀ i, AbsorbedAS T' i) ∧ ∀ x : ℝ, 0 ≤ x → cdf τ' T' x = cdf τ T x :=
  g77_nondef τ T hrep hnd
