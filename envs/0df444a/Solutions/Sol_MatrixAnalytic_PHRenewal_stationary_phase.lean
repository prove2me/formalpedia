-- Prove2me | solution 1 for MatrixAnalytic.PHRenewal.stationary_phase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:09:18.448977+00:00
-- url     : https://prove2.me/submissions/34a41684-0acd-41f6-a1a1-e7dcd125a1c6

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep

open Matrix
open MatrixAnalytic.PHRenewal
open Filter Topology
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

theorem g69d1_vmv_mulVec {ι : Type*} [Fintype ι] (u v w : ι → ℝ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem g69d1_smul_vecMul {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) (M : Matrix ι ι ℝ) :
    (a • v) ᵥ* M = a • (v ᵥ* M) := by
  funext j; simp [vecMul, dotProduct, Finset.mul_sum, mul_assoc]

open MatrixAnalytic.PHRenewal in
theorem g69d1_stationary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) :
    IsUnit (phaseGen τ T - statMatrix τ T) ∧
    (∀ i, 0 ≤ statVec τ T i) ∧
    statVec τ T ᵥ* phaseGen τ T = 0 ∧
    ∑ i, statVec τ T i = 1 ∧
    (∀ v : ι → ℝ, v ᵥ* phaseGen τ T = 0 → ∑ i, v i = 1 → v = statVec τ T) ∧
    statVec τ T ᵥ* (phaseGen τ T - statMatrix τ T)⁻¹ = -statVec τ T := by
  have hdet := hrep.nonsingular
  set one : ι → ℝ := fun _ => 1 with hone
  set t := exitVec T with ht
  set w := τ ᵥ* T⁻¹ with hw
  set c := w ⬝ᵥ one with hc
  have hneg := g69d1_neg_inv_nonneg T hrep.offDiag_nonneg hrep.exit_nonneg hdet
  have hwT : w ᵥ* T = τ := by rw [hw, vecMul_vecMul, nonsing_inv_mul _ hdet, vecMul_one]
  have hτ1 : τ ⬝ᵥ one = 1 := by simpa [dotProduct, hone] using hrep.tau_sum_one
  have hwt : w ⬝ᵥ t = -1 := by
    rw [ht, exitVec, dotProduct_neg, dotProduct_mulVec, hwT, hτ1]
  have hT1 : T⁻¹ *ᵥ t = -one := by
    rw [ht, exitVec, mulVec_neg, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  have hwnp : ∀ j, w j ≤ 0 := by
    intro j
    have : 0 ≤ ∑ i, τ i * (-T⁻¹) i j :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hrep.tau_nonneg i) (hneg i j)
    simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib] at this
    simp only [hw, vecMul, dotProduct]; linarith
  have hcneg : c < 0 := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < τ i := by
      by_contra h
      push Not at h
      have : ∑ i, τ i ≤ 0 := Finset.sum_nonpos fun i _ => h i
      linarith [hrep.tau_sum_one]
    have hrow : 0 < ∑ j, (-T⁻¹) i j := by
      rcases (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hneg i j).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : ∀ j, (-T⁻¹) i j = 0 := fun j =>
          (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hneg i j).1 h.symm j (Finset.mem_univ j)
        have := congrFun (congrFun (nonsing_inv_mul T hdet) i) i
        rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
        have h0 : ∑ k, T⁻¹ i k * T k i = 0 := Finset.sum_eq_zero fun k _ => by
          have := hz k; simp only [Matrix.neg_apply, neg_eq_zero] at this; simp [this]
        linarith
    have hc' : -c = ∑ i, τ i * ∑ j, (-T⁻¹) i j := by
      simp only [hc, hw, vecMul, dotProduct, hone, mul_one, Matrix.neg_apply, Finset.mul_sum]
      rw [Finset.sum_comm]; simp
    have : τ i * ∑ j, (-T⁻¹) i j ≤ ∑ i, τ i * ∑ j, (-T⁻¹) i j :=
      Finset.single_le_sum (f := fun i => τ i * ∑ j, (-T⁻¹) i j)
        (fun k _ => mul_nonneg (hrep.tau_nonneg k) (Finset.sum_nonneg fun j _ => hneg k j))
        (Finset.mem_univ i)
    nlinarith [mul_pos hi hrow]
  have hcne : c ≠ 0 := hcneg.ne
  have hπ : statVec τ T = c⁻¹ • w := rfl
  have hπ1 : statVec τ T ⬝ᵥ one = 1 := by
    rw [hπ, smul_dotProduct, smul_eq_mul, ← hc, inv_mul_cancel₀ hcne]
  have hπD : statVec τ T ᵥ* phaseGen τ T = 0 := by
    rw [hπ, phaseGen, vecMul_add, vecMul_vecMulVec, g69d1_smul_vecMul, smul_dotProduct, hwT,
      ← ht, hwt]
    funext j; simp
  have hPi : statMatrix τ T = vecMulVec one (statVec τ T) := rfl
  have hπPi : statVec τ T ᵥ* statMatrix τ T = statVec τ T := by
    rw [hPi, vecMul_vecMulVec, hπ1, one_smul]
  have hπM : statVec τ T ᵥ* (phaseGen τ T - statMatrix τ T) = -statVec τ T := by
    rw [vecMul_sub, hπD, hπPi, zero_sub]
  have hunit : IsUnit (phaseGen τ T - statMatrix τ T) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hd
    obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hd
    apply hx0
    have hDx : phaseGen τ T *ᵥ x = (statVec τ T ⬝ᵥ x) • one := by
      rw [sub_mulVec, sub_eq_zero] at hx
      rw [hx, hPi, g69d1_vmv_mulVec]
    have hπx : statVec τ T ⬝ᵥ x = 0 := by
      have h1 := congrArg (fun y => statVec τ T ⬝ᵥ y) hDx
      simp only [dotProduct_mulVec, hπD, zero_dotProduct, dotProduct_smul, hπ1, smul_eq_mul,
        mul_one] at h1
      exact h1.symm
    rw [hπx, zero_smul, phaseGen, add_mulVec, g69d1_vmv_mulVec] at hDx
    have hx1 : x = (τ ⬝ᵥ x) • one := by
      have h2 := congrArg (fun y => T⁻¹ *ᵥ y) hDx
      simp only [mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec, mulVec_smul,
        ← ht, hT1, mulVec_zero] at h2
      rw [smul_neg, add_neg_eq_zero] at h2
      exact h2
    have : τ ⬝ᵥ x = 0 := by
      have h3 := hπx
      rw [hx1, dotProduct_smul, hπ1, smul_eq_mul, mul_one] at h3
      exact h3
    rw [hx1, this, zero_smul]
  refine ⟨hunit, ?_, hπD, ?_, ?_, ?_⟩
  · intro i
    rw [hπ, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg_of_nonpos_of_nonpos (inv_lt_zero.2 hcneg).le (hwnp i)
  · simpa [dotProduct, hone] using hπ1
  · intro v hv hv1
    rw [phaseGen, vecMul_add, vecMul_vecMulVec, add_eq_zero_iff_eq_neg] at hv
    have hv' : v = -(v ⬝ᵥ t) • w := by
      have := congrArg (fun y => y ᵥ* T⁻¹) hv
      simp only [vecMul_vecMul, mul_nonsing_inv _ hdet, vecMul_one, neg_vecMul] at this
      rw [neg_smul, hw, ← g69d1_smul_vecMul]; exact this
    have hs : -(v ⬝ᵥ t) * c = 1 := by
      have : v ⬝ᵥ one = 1 := by simpa [dotProduct, hone] using hv1
      rw [hv', smul_dotProduct, smul_eq_mul] at this
      exact this
    rw [hv', hπ]
    congr 1
    field_simp
    linarith
  · have := congrArg (fun y => y ᵥ* (phaseGen τ T - statMatrix τ T)⁻¹) hπM
    simp only [vecMul_vecMul] at this
    rw [mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit), vecMul_one, neg_vecMul] at this
    exact (neg_eq_iff_eq_neg.mpr this).symm

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ)
    (hrep : IsPHRenewalRep τ T) (hirr : IsIrreducibleRep τ T) :
    IsUnit (phaseGen τ T - statMatrix τ T) ∧
    (∀ i, 0 ≤ statVec τ T i) ∧
    statVec τ T ᵥ* phaseGen τ T = 0 ∧
    ∑ i, statVec τ T i = 1 ∧
    (∀ v : ι → ℝ, v ᵥ* phaseGen τ T = 0 → ∑ i, v i = 1 → v = statVec τ T) ∧
    statVec τ T ᵥ* (phaseGen τ T - statMatrix τ T)⁻¹ = -statVec τ T := by
  exact g69d1_stationary τ T hrep

