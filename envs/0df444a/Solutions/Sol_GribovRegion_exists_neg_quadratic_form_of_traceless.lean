-- Prove2me | solution 1 for GribovRegion.exists_neg_quadratic_form_of_traceless
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T20:41:47.032872+00:00
-- url     : https://prove2.me/submissions/fe9ea973-348c-4887-a4ea-1f9f76e8d33f

import Definitions.Def_gribov_region_model

set_option linter.unusedSectionVars false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GribovLoc

open scoped Matrix
open Matrix GribovRegion

/-! ### Quadratic forms at one- and two-point vectors -/

theorem quad_single {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (Pi.single i (1 : ℝ)) ⬝ᵥ M *ᵥ (Pi.single i 1) = M i i := by
  simp

theorem quad_pair {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian)
    (i j : Fin n) (c : ℝ) :
    ((Pi.single i (1 : ℝ) : Fin n → ℝ) + (Pi.single j c : Fin n → ℝ)) ⬝ᵥ
        M *ᵥ ((Pi.single i (1 : ℝ) : Fin n → ℝ) + (Pi.single j c : Fin n → ℝ))
      = M i i + 2 * c * M i j + c ^ 2 * M j j := by
  have hji : M j i = M i j := by simpa using hM.apply i j
  simp [Matrix.mulVec, hji]
  ring

theorem single_add_single_ne_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : ℝ) :
    ((Pi.single i (1 : ℝ) : Fin n → ℝ) + (Pi.single j c : Fin n → ℝ)) ≠ 0 := by
  intro h
  have := congrFun h i
  simp [hij.symm] at this

/-! ### A nonzero traceless symmetric matrix has a negative direction -/

theorem exists_neg_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) (htr : M.trace = 0) (hne : M ≠ 0) :
    ∃ w : Fin n → ℝ, w ⬝ᵥ M *ᵥ w < 0 := by
  by_cases hdiag : ∃ i, M i i < 0
  · obtain ⟨i, hi⟩ := hdiag
    exact ⟨Pi.single i 1, by rw [quad_single]; exact hi⟩
  · push Not at hdiag
    have hzero : ∀ i, M i i = 0 := by
      intro i
      have hsum : ∑ k, M k k = 0 := htr
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => hdiag k)).1 hsum i (Finset.mem_univ i)
    obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (by ext i j; simpa using h i j)
    have hne' : i ≠ j := by
      rintro rfl
      exact hij (hzero i)
    refine ⟨(Pi.single i (1 : ℝ) : Fin n → ℝ) + (Pi.single j (-(M i j)) : Fin n → ℝ), ?_⟩
    rw [quad_pair M hM i j (-(M i j)), hzero i, hzero j]
    have h2 : (0 : ℝ) < M i j ^ 2 := by positivity
    nlinarith

/-! ### Basic structure of the Gribov region -/

theorem zero_mem_region {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) : (0 : V) ∈ region m := by
  simpa [region, fpOperator] using m.base_posDef

theorem fpOperator_convex_comb {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) (a b : ℝ) (hab : a + b = 1) (A₁ A₂ : V) :
    fpOperator m (a • A₁ + b • A₂) = a • fpOperator m A₁ + b • fpOperator m A₂ := by
  have hb : b = 1 - a := by linarith
  subst hb
  ext i j
  simp only [fpOperator, map_add, map_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem convex_region {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) : Convex ℝ (region m) := by
  rintro A₁ hA₁ A₂ hA₂ a b ha hb hab
  have hA₁' : (fpOperator m A₁).PosDef := hA₁
  have hA₂' : (fpOperator m A₂).PosDef := hA₂
  show (fpOperator m (a • A₁ + b • A₂)).PosDef
  rw [fpOperator_convex_comb m a b hab]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    rw [← ha0, hb1]
    simpa using hA₂'
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · have ha1 : a = 1 := by linarith
      rw [← hb0, ha1]
      simpa using hA₁'
    · exact (hA₁'.smul ha0).add (hA₂'.smul hb0)

/-! ### The region is bounded along every ray -/

theorem region_bounded_along_rays {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) (A : V) (hA : m.lin A ≠ 0) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, l₀ ≤ l → l • A ∉ region m := by
  obtain ⟨w, hw⟩ := exists_neg_quad (m.lin A) (m.lin_isHermitian A) (m.lin_trace_zero A) hA
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  set q : ℝ := w ⬝ᵥ (m.lin A) *ᵥ w with hq
  set p : ℝ := w ⬝ᵥ m.base *ᵥ w with hp
  refine ⟨max 1 (p / (-q)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro l hl hmem
  have hposdef : (fpOperator m (l • A)).PosDef := hmem
  have hval : w ⬝ᵥ (fpOperator m (l • A)) *ᵥ w = p + l * q := by
    simp only [fpOperator, map_smul]
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul]
    simp [hp, hq]
  have hpos : 0 < w ⬝ᵥ (fpOperator m (l • A)) *ᵥ w := by
    have := hposdef.dotProduct_mulVec_pos hw0
    simpa using this
  rw [hval] at hpos
  have hq0 : 0 < -q := by linarith
  have hle : p / (-q) ≤ l := le_trans (le_max_right _ _) hl
  rw [div_le_iff₀ hq0] at hle
  nlinarith

/-! ### Entrywise bounds for positive definite matrices -/

theorem trace_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : M.trace = ∑ k, M k k := rfl

theorem posDef_diag_le_trace {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (i : Fin n) : M i i ≤ M.trace := by
  rw [trace_eq_sum]
  exact Finset.single_le_sum (f := fun k => M k k)
    (fun k _ => (hM.diag_pos (i := k)).le) (Finset.mem_univ i)

theorem posDef_entry_abs_le_trace {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (i j : Fin n) : |M i j| ≤ M.trace := by
  have hT : ∀ k : Fin n, M k k ≤ M.trace := posDef_diag_le_trace hM
  have hdiag : ∀ k : Fin n, 0 < M k k := fun k => hM.diag_pos (i := k)
  rcases eq_or_ne i j with rfl | hij
  · rw [abs_of_pos (hdiag i)]; exact hT i
  · have hjj : 0 < M j j := hdiag j
    set c : ℝ := -(M i j) / M j j with hc
    have hquad : 0 < M i i + 2 * c * M i j + c ^ 2 * M j j := by
      have h0 := hM.dotProduct_mulVec_pos (single_add_single_ne_zero hij c)
      rw [show (star ((Pi.single i (1:ℝ) : Fin n → ℝ) + (Pi.single j c : Fin n → ℝ)))
          = (Pi.single i (1:ℝ) : Fin n → ℝ) + (Pi.single j c : Fin n → ℝ) from
        star_trivial _] at h0
      rwa [quad_pair M hM.isHermitian i j c] at h0
    have hcc : c * M j j = -(M i j) := by rw [hc]; field_simp
    have hkey : M i j ^ 2 < M i i * M j j := by nlinarith [hquad, hjj, hcc]
    have hii : M i i ≤ M.trace := hT i
    have hjj' : M j j ≤ M.trace := hT j
    nlinarith [abs_nonneg (M i j), sq_abs (M i j), hdiag i, hdiag j]

/-! ### The Gribov region is bounded -/

noncomputable def linVec {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) : V →ₗ[ℝ] (Fin n × Fin n → ℝ) where
  toFun := fun A p => m.lin A p.1 p.2
  map_add' := by intro A B; ext p; simp
  map_smul' := by intro a A; ext p; simp

theorem region_isBounded {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (m : FPModel V n)
    (hinj : Function.Injective m.lin) :
    Bornology.IsBounded (region m) := by
  have hker : LinearMap.ker (linVec m) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro A B h
    refine hinj ?_
    ext i j
    exact congrFun h (i, j)
  obtain ⟨K, -, hanti⟩ := (linVec m).exists_antilipschitzWith hker
  set bvec : Fin n × Fin n → ℝ := fun p => m.base p.1 p.2 with hbvec
  set T : ℝ := m.base.trace with hT
  have hT0 : 0 ≤ T := by
    rw [hT, trace_eq_sum]
    exact Finset.sum_nonneg fun k _ => (m.base_posDef.diag_pos (i := k)).le
  set C : ℝ := T + ‖bvec‖ with hC
  have hC0 : 0 ≤ C := by positivity
  refine Bornology.IsBounded.subset
    (hanti.isBounded_preimage
      (Metric.isBounded_closedBall (x := (0 : Fin n × Fin n → ℝ)) (r := C))) ?_
  intro A hA
  have hposdef : (fpOperator m A).PosDef := hA
  have htr : (fpOperator m A).trace = T := by
    simp [fpOperator, Matrix.trace_add, m.lin_trace_zero A, hT]
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg hC0]
  intro p
  have hentry : m.lin A p.1 p.2 = (fpOperator m A) p.1 p.2 - bvec p := by
    simp [fpOperator, hbvec]
  have h1 : |(fpOperator m A) p.1 p.2| ≤ T := by
    have h := posDef_entry_abs_le_trace hposdef p.1 p.2
    rwa [htr] at h
  have h2 : |bvec p| ≤ ‖bvec‖ := by
    have h := norm_le_pi_norm bvec p
    simpa using h
  have h3 : linVec m A p = (fpOperator m A) p.1 p.2 - bvec p := hentry
  rw [h3, hC, Real.norm_eq_abs]
  calc |(fpOperator m A) p.1 p.2 - bvec p| ≤ |(fpOperator m A) p.1 p.2| + |bvec p| :=
        abs_sub _ _
    _ ≤ T + ‖bvec‖ := add_le_add h1 h2

end GribovLoc

open scoped Matrix
open Matrix GribovRegion in
theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) (htr : M.trace = 0) (hne : M ≠ 0) :
    ∃ w : Fin n → ℝ, w ⬝ᵥ M *ᵥ w < 0 :=
  GribovLoc.exists_neg_quad M hM htr hne
