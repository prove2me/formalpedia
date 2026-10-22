-- Prove2me | solution 1 for MatrixAnalytic.PH.absorption_iff_nonsingular
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T03:45:32.242584+00:00
-- url     : https://prove2.me/submissions/3d7133e2-398e-44c5-aa00-e9cbf2e0f69d

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

theorem g77_main {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (hrep : IsPHRep τ T) :
    ((∀ i, AbsorbedAS T i) ↔ IsUnit T.det) ∧
    (IsUnit T.det → ∀ i j : ι,
      expectedTime T i j ≠ ⊤ ∧ (expectedTime T i j).toReal = (-T⁻¹) i j) := by
  have hoff : ∀ i j, i ≠ j → 0 ≤ T i j := hrep.generator.offDiag_nonneg
  have hex : ∀ i, 0 ≤ (-(T *ᵥ fun _ => (1:ℝ))) i := hrep.generator.exitRates_nonneg
  refine ⟨⟨fun habs => ?_, fun hdet i => ?_⟩, fun hdet i j => ?_⟩
  · by_contra hdet
    have hd0 : T.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    obtain ⟨v, hv0, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd0
    -- exp(yT) v = v
    have hconst : ∀ y : ℝ, ∀ i, (NormedSpace.exp (y • T) *ᵥ v) i = v i := by
      intro y i
      let L : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
        { toFun := fun M => (M *ᵥ v) i
          map_add' := by intro M N; simp [add_mulVec]
          map_smul' := by intro c M; simp [smul_mulVec] }
      have hd : ∀ x, HasDerivAt (fun y : ℝ => L (NormedSpace.exp (y • T))) 0 x := by
        intro x
        refine (g69d1_deriv_lin T L x).congr_deriv ?_
        show ((NormedSpace.exp (x • T) * T) *ᵥ v) i = 0
        rw [← mulVec_mulVec, hTv, mulVec_zero]; rfl
      have := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
        (fun x => (hd x).deriv) y 0
      simpa [L] using this
    have hE0 : ∀ i j, Tendsto (fun y : ℝ => NormedSpace.exp (y • T) i j) atTop (𝓝 0) := by
      intro i j
      have h1 : Tendsto (fun y : ℝ => ∑ k, NormedSpace.exp (y • T) i k) atTop (𝓝 0) := by
        have := (habs i).const_sub (1:ℝ)
        simp only [g77_sn, sub_sub_cancel, sub_self] at this
        exact this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
      · filter_upwards [eventually_ge_atTop 0] with y hy
          using g69d1_exp_metzler_nonneg T hoff y hy i j
      · filter_upwards [eventually_ge_atTop 0] with y hy
        exact Finset.single_le_sum (f := fun k => NormedSpace.exp (y • T) i k)
          (fun k _ => g69d1_exp_metzler_nonneg T hoff y hy i k) (Finset.mem_univ j)
    apply hv0
    funext i
    have h1 : Tendsto (fun y : ℝ => (NormedSpace.exp (y • T) *ᵥ v) i) atTop (𝓝 0) := by
      have : Tendsto (fun y : ℝ => ∑ k, NormedSpace.exp (y • T) i k * v k) atTop
          (𝓝 (∑ k : ι, (0:ℝ) * v k)) := tendsto_finsetSum _ fun k _ => (hE0 i k).mul_const _
      simpa [mulVec, dotProduct] using this
    simp only [hconst] at h1
    exact tendsto_nhds_unique tendsto_const_nhds h1
  · have h := g69d1_integral_gen T hoff hex hdet
    unfold AbsorbedAS
    simp only [g77_sn]
    have : Tendsto (fun y : ℝ => ∑ k, NormedSpace.exp (y • T) i k) atTop (𝓝 (∑ k : ι, (0:ℝ))) :=
      tendsto_finsetSum _ fun k _ => (h i k).2.2
    simpa using this.const_sub (1:ℝ)
  · obtain ⟨hint, hval, -⟩ := g69d1_integral_gen T hoff hex hdet i j
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] fun x : ℝ => NormedSpace.exp (x • T) i j := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact g69d1_exp_metzler_nonneg T hoff x (le_of_lt hx) i j
    have heq : expectedTime T i j = ENNReal.ofReal (∫ x in Set.Ioi (0 : ℝ), NormedSpace.exp (x • T) i j) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
      unfold expectedTime
      simp only [g69d1_exp_ss]
    have hI : 0 ≤ ∫ x in Set.Ioi (0 : ℝ), NormedSpace.exp (x • T) i j := integral_nonneg_of_ae hnn
    refine ⟨by rw [heq]; exact ENNReal.ofReal_ne_top, ?_⟩
    rw [heq, ENNReal.toReal_ofReal hI, hval]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (hrep : IsPHRep τ T) :
    ((∀ i, AbsorbedAS T i) ↔ IsUnit T.det) ∧
    (IsUnit T.det → ∀ i j : ι,
      expectedTime T i j ≠ ⊤ ∧ (expectedTime T i j).toReal = (-T⁻¹) i j) :=
  g77_main τ T hrep
