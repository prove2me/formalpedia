-- Prove2me | solution 1 for LogSobolevMC.Metropolis.example_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:16:49.703856+00:00
-- url     : https://prove2.me/submissions/b5744663-29d0-4c6f-859e-4c2599c689e8

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Setting
import Definitions.Def_LogSobolevMC_Metropolis_Chains



namespace LogSobolevMC.Metropolis

open MarkovMixing
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- row sums -/
lemma rowsum_one (K : Matrix V V ℝ) (hK : IsStochastic K) (x : V) : ∑ y, K x y = 1 := hK.2 x

lemma colsum_pi (K : Matrix V V ℝ) (π : V → ℝ) (hπ : IsStationary K π) (y : V) :
    ∑ x, π x * K x y = π y := by
  have h := congrFun hπ.2 y
  simpa [Matrix.vecMul, dotProduct] using h

lemma mulVec_apply' (K : Matrix V V ℝ) (f : V → ℝ) (x : V) :
    K.mulVec f x = ∑ y, K x y * f y := by
  simp [Matrix.mulVec, dotProduct]

/-- `2 ℰ(f,f) = Σ_x Σ_y π x K x y (f x - f y)^2`. -/
lemma two_dirichlet (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (f : V → ℝ) :
    2 * LogSobolevMC.ChiSquare.dirichlet K π f f = ∑ x, ∑ y, π x * K x y * (f x - f y) ^ 2 := by
  unfold LogSobolevMC.ChiSquare.dirichlet
  simp only [mulVec_apply']
  have e1 : ∀ x, ∑ y, π x * K x y * (f x - f y) ^ 2
      = π x * f x ^ 2 - 2 * (∑ y, K x y * f y) * f x * π x + ∑ y, π x * K x y * f y ^ 2 := by
    intro x
    have : ∑ y, π x * K x y * (f x - f y) ^ 2
        = ∑ y, (π x * f x ^ 2 * K x y - 2 * (K x y * f y) * f x * π x + π x * K x y * f y ^ 2) := by
      apply Finset.sum_congr rfl; intro y _; ring
    rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, rowsum_one K hK,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have e2 : ∀ y, ∑ x, π x * K x y * f y ^ 2 = π y * f y ^ 2 := by
    intro y
    rw [← Finset.sum_mul, colsum_pi K π hπ]
  simp only [e2]
  have e3 : ∀ x, (f x - ∑ y, K x y * f y) * f x * π x
      = π x * f x ^ 2 - (∑ y, K x y * f y) * f x * π x := by intro x; ring
  simp only [e3, Finset.sum_sub_distrib]
  have e4 : ∑ x, (2 * ∑ y, K x y * f y) * f x * π x = 2 * ∑ x, (∑ y, K x y * f y) * f x * π x := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  rw [e4]; ring

lemma dirichlet_nonneg (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ)
    (hπ : IsStationary K π) (f : V → ℝ) :
    0 ≤ LogSobolevMC.ChiSquare.dirichlet K π f f := by
  have h := two_dirichlet K hK π hπ f
  have : 0 ≤ ∑ x, ∑ y, π x * K x y * (f x - f y) ^ 2 := by
    apply Finset.sum_nonneg; intro x _; apply Finset.sum_nonneg; intro y _
    have := hπ.1.1 x; have := hK.1 x y; positivity
  linarith

/-- `‖f‖₂² = Σ |f x|² π x`. -/
lemma lpNorm_two_sq (π : V → ℝ) (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    LogSobolevMC.ChiSquare.lpNorm π 2 f ^ (2:ℝ) = ∑ x, |f x| ^ (2:ℝ) * π x := by
  unfold LogSobolevMC.ChiSquare.lpNorm
  have hs : 0 ≤ ∑ x, |f x| ^ (2:ℝ) * π x := by
    apply Finset.sum_nonneg; intro x _; have := hπ x; positivity
  rw [← Real.rpow_mul hs]; norm_num

lemma entL_nonneg (π : V → ℝ) (hπ : IsDist π) (hπpos : ∀ x, 0 < π x) (f : V → ℝ) :
    0 ≤ LogSobolevMC.ChiSquare.entL π f := by
  unfold LogSobolevMC.ChiSquare.entL
  rw [lpNorm_two_sq π hπ.1]
  set N := ∑ x, |f x| ^ (2:ℝ) * π x with hN
  have hN0 : 0 ≤ N := by
    apply Finset.sum_nonneg; intro x _; have := hπ.1 x; positivity
  have key : ∀ x, (|f x| ^ (2:ℝ) - N) * π x ≤ |f x| ^ (2:ℝ) * Real.log (|f x| ^ (2:ℝ) / N) * π x := by
    intro x
    apply mul_le_mul_of_nonneg_right _ (hπ.1 x)
    rcases (eq_or_lt_of_le (by positivity : (0:ℝ) ≤ |f x| ^ (2:ℝ))) with h | h
    · rw [← h]; simp; exact hN0
    · rcases (eq_or_lt_of_le hN0) with h2 | h2
      · exfalso
        -- N = 0 but term x positive
        have : |f x| ^ (2:ℝ) * π x ≤ N := by
          rw [hN]
          exact Finset.single_le_sum (f := fun x => |f x| ^ (2:ℝ) * π x)
            (fun y _ => by have := hπ.1 y; positivity) (Finset.mem_univ x)
        have hpx := hπpos x
        have : 0 < |f x| ^ (2:ℝ) * π x := mul_pos h hpx
        linarith
      · have hl := Real.one_sub_inv_le_log_of_pos (div_pos h h2)
        rw [inv_div] at hl
        have : |f x| ^ (2:ℝ) * (1 - N / |f x| ^ (2:ℝ)) = |f x| ^ (2:ℝ) - N := by
          field_simp
        calc |f x| ^ (2:ℝ) - N = |f x| ^ (2:ℝ) * (1 - N / |f x| ^ (2:ℝ)) := this.symm
          _ ≤ |f x| ^ (2:ℝ) * Real.log (|f x| ^ (2:ℝ) / N) :=
            mul_le_mul_of_nonneg_left hl h.le
  calc (0:ℝ) = ∑ x, (|f x| ^ (2:ℝ) - N) * π x := by
        simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ.2, mul_one]; ring
    _ ≤ _ := Finset.sum_le_sum (fun x _ => key x)

/-! ### The one-parameter family `1 + ε g` -/

/-- `S(ε) = Σ (1 + ε g x)^2 π x`. -/
noncomputable def Sf (π g : V → ℝ) (ε : ℝ) : ℝ := ∑ x, (1 + ε * g x) ^ 2 * π x

/-- `S'(ε)`. -/
noncomputable def Sd (π g : V → ℝ) (ε : ℝ) : ℝ := ∑ x, 2 * (1 + ε * g x) * g x * π x

/-- `L(ε) = ℒ(1 + ε g)` in the form `Σ φ(a) π − φ(S)`, `φ(u) = u log u`. -/
noncomputable def Lf (π g : V → ℝ) (ε : ℝ) : ℝ :=
  ∑ x, (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2) * π x - Sf π g ε * Real.log (Sf π g ε)

/-- `L'(ε)`. -/
noncomputable def Ld (π g : V → ℝ) (ε : ℝ) : ℝ :=
  ∑ x, (Real.log ((1 + ε * g x) ^ 2) + 1) * (2 * (1 + ε * g x) * g x) * π x
    - (Real.log (Sf π g ε) + 1) * Sd π g ε

lemma hasDerivAt_A (g : V → ℝ) (x : V) (ε : ℝ) :
    HasDerivAt (fun ε => (1 + ε * g x) ^ 2) (2 * (1 + ε * g x) * g x) ε := by
  have h : HasDerivAt (fun ε : ℝ => 1 + ε * g x) (g x) ε := by
    have := ((hasDerivAt_id ε).mul_const (g x)).const_add 1
    simpa using this
  exact (h.pow 2).congr_deriv (by norm_num)

lemma hasDerivAt_B (g : V → ℝ) (x : V) (ε : ℝ) :
    HasDerivAt (fun ε => 2 * (1 + ε * g x) * g x) (2 * g x * g x) ε := by
  have h : HasDerivAt (fun ε : ℝ => 1 + ε * g x) (g x) ε := by
    have := ((hasDerivAt_id ε).mul_const (g x)).const_add 1
    simpa using this
  have := (h.const_mul 2).mul_const (g x)
  convert this using 1

lemma hasDerivAt_Sf (π g : V → ℝ) (ε : ℝ) : HasDerivAt (Sf π g) (Sd π g ε) ε := by
  unfold Sf Sd
  apply HasDerivAt.fun_sum
  intro x _
  exact (hasDerivAt_A g x ε).mul_const (π x)

lemma hasDerivAt_Sd (π g : V → ℝ) (ε : ℝ) :
    HasDerivAt (Sd π g) (∑ x, 2 * g x * g x * π x) ε := by
  unfold Sd
  apply HasDerivAt.fun_sum
  intro x _
  exact (hasDerivAt_B g x ε).mul_const (π x)

lemma hasDerivAt_Lf (π g : V → ℝ) (ε : ℝ) (hpos : ∀ x, 0 < 1 + ε * g x) (hS : 0 < Sf π g ε) :
    HasDerivAt (Lf π g) (Ld π g ε) ε := by
  unfold Lf Ld
  apply HasDerivAt.sub
  · apply HasDerivAt.fun_sum
    intro x _
    have hA := hasDerivAt_A g x ε
    have hne : (1 + ε * g x) ^ 2 ≠ 0 := by have := hpos x; positivity
    exact ((Real.hasDerivAt_mul_log hne).comp ε hA).mul_const (π x)
  · exact (Real.hasDerivAt_mul_log hS.ne').comp ε (hasDerivAt_Sf π g ε)

lemma hasDerivAt_Ld_zero (π g : V → ℝ) (hπ : IsDist π) :
    HasDerivAt (Ld π g) (4 * distVar π g) 0 := by
  have hS0 : Sf π g 0 = 1 := by unfold Sf; simp [hπ.2]
  have hSd0 : Sd π g 0 = 2 * ∑ x, g x * π x := by
    unfold Sd; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  have h1 : HasDerivAt (fun ε => ∑ x, (Real.log ((1 + ε * g x) ^ 2) + 1) * (2 * (1 + ε * g x) * g x) * π x)
      (∑ x, ((2 * (1 + 0 * g x) * g x) / (1 + 0 * g x) ^ 2 * (2 * (1 + 0 * g x) * g x)
        + (Real.log ((1 + 0 * g x) ^ 2) + 1) * (2 * g x * g x)) * π x) 0 := by
    apply HasDerivAt.fun_sum
    intro x _
    have hA := hasDerivAt_A g x 0
    have hne : (1 + 0 * g x) ^ 2 ≠ 0 := by simp
    have hl := (hA.log hne).add_const 1
    exact (hl.mul (hasDerivAt_B g x 0)).mul_const (π x)
  have h2 : HasDerivAt (fun ε => (Real.log (Sf π g ε) + 1) * Sd π g ε)
      (Sd π g 0 / Sf π g 0 * Sd π g 0 + (Real.log (Sf π g 0) + 1) * ∑ x, 2 * g x * g x * π x) 0 := by
    have hl := ((hasDerivAt_Sf π g 0).log (by rw [hS0]; norm_num)).add_const 1
    exact hl.mul (hasDerivAt_Sd π g 0)
  refine (h1.sub h2).congr_deriv ?_
  rw [hS0, hSd0]
  simp only [zero_mul, add_zero, one_pow, Real.log_one, div_one, zero_add, one_mul]
  unfold distVar distExp
  have e1 : ∑ x, (g x - ∑ y, g y * π y) ^ 2 * π x
      = ∑ x, g x ^ 2 * π x - (∑ y, g y * π y) ^ 2 := by
    have : ∀ x, (g x - ∑ y, g y * π y) ^ 2 * π x
        = g x ^ 2 * π x - 2 * (∑ y, g y * π y) * (g x * π x) + (∑ y, g y * π y) ^ 2 * π x := by
      intro x; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ.2]
    ring
  rw [e1]
  have e2 : ∑ x, (2 * 1 * g x * (2 * 1 * g x) + 2 * g x * g x) * π x = 6 * ∑ x, g x ^ 2 * π x := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  have e3 : ∑ x, 2 * g x * g x * π x = 2 * ∑ x, g x ^ 2 * π x := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  rw [e2, e3]; ring

lemma Lf_zero (π g : V → ℝ) (hπ : IsDist π) : Lf π g 0 = 0 := by
  unfold Lf Sf; simp [hπ.2]

lemma Ld_zero (π g : V → ℝ) (hπ : IsDist π) : Ld π g 0 = 0 := by
  unfold Ld Sf Sd; simp [hπ.2, Finset.sum_mul]

lemma eventually_pos (g : V → ℝ) : ∀ᶠ ε in nhds (0:ℝ), ∀ x, 0 < 1 + ε * g x := by
  rw [Filter.eventually_all]
  intro x
  have hc : Continuous (fun ε : ℝ => 1 + ε * g x) := by fun_prop
  have := (hc.tendsto 0).eventually_const_lt (by simp : (0:ℝ) < 1 + 0 * g x)
  exact this

lemma Sf_pos (π g : V → ℝ) (hπ : IsDist π) (hπpos : ∀ x, 0 < π x) (ε : ℝ)
    (hpos : ∀ x, 0 < 1 + ε * g x) : 0 < Sf π g ε := by
  have hne : Nonempty V := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hπ.2
    simp at this
  unfold Sf
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro x _
  have := hpos x; have := hπpos x; positivity

/-- The key limit: `ℒ(1 + ε g)/ε² → 2 Var(g)`. -/
lemma tendsto_Lf (π g : V → ℝ) (hπ : IsDist π) (hπpos : ∀ x, 0 < π x) :
    Filter.Tendsto (fun ε => Lf π g ε / ε ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds (2 * distVar π g)) := by
  have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) {0}ᶜ, ∀ x, 0 < 1 + ε * g x :=
    (eventually_pos g).filter_mono nhdsWithin_le_nhds
  apply HasDerivAt.lhopital_zero_nhdsNE (f' := Ld π g) (g' := fun ε => 2 * ε)
  · filter_upwards [hev] with ε hε
    exact hasDerivAt_Lf π g ε hε (Sf_pos π g hπ hπpos ε hε)
  · filter_upwards with ε
    exact (hasDerivAt_pow 2 ε).congr_deriv (by norm_num)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hε
    exact mul_ne_zero two_ne_zero hε
  · have h0 := hasDerivAt_Lf π g 0 (by simp) (Sf_pos π g hπ hπpos 0 (by simp))
    have := h0.continuousAt.tendsto
    rw [Lf_zero π g hπ] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have : Filter.Tendsto (fun ε : ℝ => ε ^ 2) (nhds 0) (nhds ((0:ℝ) ^ 2)) :=
      (continuous_pow 2).tendsto 0
    simp at this
    exact this.mono_left nhdsWithin_le_nhds
  · have h := hasDerivAt_Ld_zero π g hπ
    rw [hasDerivAt_iff_tendsto_slope] at h
    have h2 := h.const_mul (1/2)
    refine (h2.congr ?_).trans ?_
    · intro ε
      rw [slope_def_field, Ld_zero π g hπ]
      ring
    · rw [show (1:ℝ)/2 * (4 * distVar π g) = 2 * distVar π g by ring]

/-- `ℒ(1 + ε g) = L(ε)` when `1 + ε g > 0`. -/
lemma entL_eq_Lf (π g : V → ℝ) (hπ : IsDist π) (hπpos : ∀ x, 0 < π x) (ε : ℝ)
    (hpos : ∀ x, 0 < 1 + ε * g x) :
    LogSobolevMC.ChiSquare.entL π (fun x => 1 + ε * g x) = Lf π g ε := by
  have hS := Sf_pos π g hπ hπpos ε hpos
  unfold LogSobolevMC.ChiSquare.entL
  rw [lpNorm_two_sq π hπ.1]
  have ha : ∀ x, |(fun x => 1 + ε * g x) x| ^ (2:ℝ) = (1 + ε * g x) ^ 2 := by
    intro x; simp only; rw [abs_of_pos (hpos x), Real.rpow_two]
  simp only [ha]
  unfold Lf
  have hSdef : Sf π g ε = ∑ x, (1 + ε * g x) ^ 2 * π x := rfl
  rw [← hSdef]
  have : ∀ x, (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2 / Sf π g ε) * π x
      = (1 + ε * g x) ^ 2 * Real.log ((1 + ε * g x) ^ 2) * π x
        - Real.log (Sf π g ε) * ((1 + ε * g x) ^ 2 * π x) := by
    intro x
    rw [Real.log_div (by have := hpos x; positivity) hS.ne']
    ring
  simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hSdef]
  ring

/-- `ℰ(1 + ε g, 1 + ε g) = ε² ℰ(g, g)`. -/
lemma dirichlet_affine (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ)
    (hπ : IsStationary K π) (g : V → ℝ) (ε : ℝ) :
    LogSobolevMC.ChiSquare.dirichlet K π (fun x => 1 + ε * g x) (fun x => 1 + ε * g x)
      = ε ^ 2 * LogSobolevMC.ChiSquare.dirichlet K π g g := by
  unfold LogSobolevMC.ChiSquare.dirichlet
  simp only [mulVec_apply']
  have h1 : ∀ x, ∑ y, K x y * (1 + ε * g y) = 1 + ε * ∑ y, K x y * g y := by
    intro x
    have : ∀ y, K x y * (1 + ε * g y) = K x y + ε * (K x y * g y) := by intro y; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, rowsum_one K hK]
  simp only [h1]
  have h2 : ∑ x, (g x - ∑ y, K x y * g y) * π x = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ y, ∑ x, K x y * g y * π x = g y * π y := by
      intro y
      rw [← colsum_pi K π hπ y, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _; ring
    simp only [this]; ring
  have h3 : ∀ x, (1 + ε * g x - (1 + ε * ∑ y, K x y * g y)) * (1 + ε * g x) * π x
      = ε * ((g x - ∑ y, K x y * g y) * π x) + ε ^ 2 * ((g x - ∑ y, K x y * g y) * g x * π x) := by
    intro x; ring
  simp only [h3, Finset.sum_add_distrib, ← Finset.mul_sum, h2]
  ring

/-- Main step: `2 α ≤ ℰ(g,g)/Var(g)` for every nonconstant `g`. -/
lemma two_alpha_le_ratio (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ)
    (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x) (g : V → ℝ) (hg : distVar π g ≠ 0) :
    2 * LogSobolevMC.ChiSquare.logSobolev K π
      ≤ LogSobolevMC.ChiSquare.dirichlet K π g g / distVar π g := by
  have hVar : 0 < distVar π g := by
    rcases (eq_or_lt_of_le (by
      unfold distVar; apply Finset.sum_nonneg; intro x _; have := hπ.1.1 x; positivity
      : (0:ℝ) ≤ distVar π g)) with h | h
    · exact absurd h.symm hg
    · exact h
  set α := LogSobolevMC.ChiSquare.logSobolev K π with hα
  set E := LogSobolevMC.ChiSquare.dirichlet K π g g with hE
  -- bounded below
  have hbdd : BddBelow {r : ℝ | ∃ f : V → ℝ, LogSobolevMC.ChiSquare.entL π f ≠ 0 ∧
      r = LogSobolevMC.ChiSquare.dirichlet K π f f / LogSobolevMC.ChiSquare.entL π f} := by
    refine ⟨0, ?_⟩
    rintro r ⟨f, hf, rfl⟩
    exact div_nonneg (dirichlet_nonneg K hK π hπ f) (entL_nonneg π hπ.1 hπpos f)
  -- α * (L ε / ε²) ≤ E eventually
  have hT := tendsto_Lf π g hπ.1 hπpos
  have hev1 : ∀ᶠ ε in nhdsWithin (0:ℝ) {0}ᶜ, distVar π g < Lf π g ε / ε ^ 2 :=
    hT.eventually_const_lt (by linarith)
  have hev2 : ∀ᶠ ε in nhdsWithin (0:ℝ) {0}ᶜ, ∀ x, 0 < 1 + ε * g x :=
    (eventually_pos g).filter_mono nhdsWithin_le_nhds
  have hev3 : ∀ᶠ ε in nhdsWithin (0:ℝ) {0}ᶜ, ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa using hε
  have hle : ∀ᶠ ε in nhdsWithin (0:ℝ) {0}ᶜ, α * (Lf π g ε / ε ^ 2) ≤ E := by
    filter_upwards [hev1, hev2, hev3] with ε h1 h2 h3
    have hL : 0 < Lf π g ε := by
      have hε2 : 0 < ε ^ 2 := by positivity
      have : 0 < Lf π g ε / ε ^ 2 := lt_trans hVar h1
      exact (div_pos_iff_of_pos_right hε2).1 this
    have hLe := entL_eq_Lf π g hπ.1 hπpos ε h2
    have hmem : E * ε ^ 2 / Lf π g ε ∈ {r : ℝ | ∃ f : V → ℝ, LogSobolevMC.ChiSquare.entL π f ≠ 0 ∧
        r = LogSobolevMC.ChiSquare.dirichlet K π f f / LogSobolevMC.ChiSquare.entL π f} := by
      refine ⟨fun x => 1 + ε * g x, ?_, ?_⟩
      · rw [hLe]; exact hL.ne'
      · rw [hLe, dirichlet_affine K hK π hπ g ε]; ring
    have hαle : α ≤ E * ε ^ 2 / Lf π g ε := csInf_le hbdd hmem
    have hε2 : 0 < ε ^ 2 := by positivity
    rw [le_div_iff₀ hL] at hαle
    calc α * (Lf π g ε / ε ^ 2) = α * Lf π g ε / ε ^ 2 := by ring
      _ ≤ E * ε ^ 2 / ε ^ 2 := by gcongr
      _ = E := by field_simp
  have hlim : Filter.Tendsto (fun ε => α * (Lf π g ε / ε ^ 2)) (nhdsWithin (0:ℝ) {0}ᶜ)
      (nhds (α * (2 * distVar π g))) := hT.const_mul α
  have hfinal : α * (2 * distVar π g) ≤ E := by
    exact le_of_tendsto hlim hle
  rw [le_div_iff₀ hVar]
  linarith

/-- Lemma 3.1: `2 α ≤ λ`. -/
theorem lemma_3_1_core {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) :
    2 * LogSobolevMC.ChiSquare.logSobolev K π ≤ LogSobolevMC.ChiSquare.gap K π := by
  unfold LogSobolevMC.ChiSquare.gap
  by_cases hne : ∃ g : V → ℝ, distVar π g ≠ 0
  · apply le_csInf
    · obtain ⟨g, hg⟩ := hne
      exact ⟨_, g, hg, rfl⟩
    · rintro r ⟨g, hg, rfl⟩
      exact two_alpha_le_ratio K hK π hπ hπpos g hg
  · push_neg at hne
    -- every function is constant, so every `ℒ(f) = 0` and `α = 0`
    have hconst : ∀ f : V → ℝ, ∀ x, f x = distExp π f := by
      intro f x
      have h := hne f
      unfold distVar at h
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by
        have := hπ.1.1 y; positivity)).1 h x (Finset.mem_univ x)
      have hp := hπpos x
      have : (f x - distExp π f) ^ 2 = 0 := by
        rcases mul_eq_zero.1 this with h' | h'
        · exact h'
        · exact absurd h' hp.ne'
      exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this)
    have hent : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.entL π f = 0 := by
      intro f
      unfold LogSobolevMC.ChiSquare.entL
      rw [lpNorm_two_sq π hπ.1.1]
      have hf : ∀ x, f x = distExp π f := hconst f
      have hN : ∑ x, |f x| ^ (2:ℝ) * π x = |distExp π f| ^ (2:ℝ) := by
        simp only [hf, ← Finset.mul_sum, hπ.1.2, mul_one]
      rw [hN]
      apply Finset.sum_eq_zero
      intro x _
      rw [hf x]
      by_cases hc : distExp π f = 0
      · rw [hc]; simp
      · rw [div_self (by positivity), Real.log_one]; ring
    have hα : LogSobolevMC.ChiSquare.logSobolev K π = 0 := by
      unfold LogSobolevMC.ChiSquare.logSobolev
      have : {r : ℝ | ∃ f : V → ℝ, LogSobolevMC.ChiSquare.entL π f ≠ 0 ∧
          r = LogSobolevMC.ChiSquare.dirichlet K π f f / LogSobolevMC.ChiSquare.entL π f} = ∅ := by
        ext r; simp [hent]
      rw [this, Real.sInf_empty]
    have : {r : ℝ | ∃ f : V → ℝ, distVar π f ≠ 0 ∧
        r = LogSobolevMC.ChiSquare.dirichlet K π f f / distVar π f} = ∅ := by
      ext r; simp [hne]
    rw [this, Real.sInf_empty, hα]; norm_num


/-! ### Lemma 3.3: comparison -/

lemma var_shift (π : V → ℝ) (hπ : IsDist π) (f : V → ℝ) (c : ℝ) :
    ∑ x, (f x - c) ^ 2 * π x = distVar π f + (distExp π f - c) ^ 2 := by
  unfold distVar
  have h2 : ∑ x, (f x - distExp π f) * π x = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ.2, mul_one]
    unfold distExp; ring
  have h1 : ∀ x, (f x - c) ^ 2 * π x = (f x - distExp π f) ^ 2 * π x
      + 2 * (distExp π f - c) * ((f x - distExp π f) * π x) + (distExp π f - c) ^ 2 * π x := by
    intro x; ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, hπ.2, mul_one, h2]
  ring

lemma distVar_nonneg (π : V → ℝ) (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) : 0 ≤ distVar π f := by
  unfold distVar; apply Finset.sum_nonneg; intro x _; have := hπ x; positivity

lemma var_compare (π π' : V → ℝ) (hπ : IsDist π) (hπ' : IsDist π') (a : ℝ) (ha : 0 < a)
    (hmeas : ∀ x, a * π x ≤ π' x) (f : V → ℝ) :
    a * distVar π f ≤ distVar π' f := by
  have h1 : distVar π' f = ∑ x, (f x - distExp π' f) ^ 2 * π' x := rfl
  have h2 : a * distVar π f ≤ a * ∑ x, (f x - distExp π' f) ^ 2 * π x := by
    rw [var_shift π hπ f (distExp π' f)]
    apply mul_le_mul_of_nonneg_left _ ha.le
    nlinarith [sq_nonneg (distExp π f - distExp π' f)]
  have h3 : a * ∑ x, (f x - distExp π' f) ^ 2 * π x ≤ ∑ x, (f x - distExp π' f) ^ 2 * π' x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    calc a * ((f x - distExp π' f) ^ 2 * π x) = (f x - distExp π' f) ^ 2 * (a * π x) := by ring
      _ ≤ (f x - distExp π' f) ^ 2 * π' x := mul_le_mul_of_nonneg_left (hmeas x) (sq_nonneg _)
  rw [h1]; exact h2.trans h3

/-- `φ(u, t) = u log(u/t) - u + t ≥ 0`. -/
lemma phi_nonneg (u t : ℝ) (hu : 0 ≤ u) (ht : 0 < t) : 0 ≤ u * Real.log (u / t) - u + t := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h]; simp; exact ht.le
  · have hl := Real.one_sub_inv_le_log_of_pos (div_pos h ht)
    rw [inv_div] at hl
    have : u * (1 - t / u) = u - t := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hl h.le]

/-- `ℒ_π(f)` in the form `Σ φ(f², N) π` with `N = Σ f² π`, in terms of real squares. -/
lemma entL_eq (π : V → ℝ) (hπ : IsDist π) (f : V → ℝ) :
    LogSobolevMC.ChiSquare.entL π f
      = ∑ x, (f x ^ 2 * Real.log (f x ^ 2 / ∑ y, f y ^ 2 * π y)) * π x := by
  unfold LogSobolevMC.ChiSquare.entL
  rw [lpNorm_two_sq π hπ.1]
  have ha : ∀ x, |f x| ^ (2:ℝ) = f x ^ 2 := by intro x; rw [Real.rpow_two, sq_abs]
  simp only [ha]

lemma entL_compare (π π' : V → ℝ) (hπ : IsDist π) (hπ' : IsDist π') (hπpos : ∀ x, 0 < π x)
    (hπ'pos : ∀ x, 0 < π' x) (a : ℝ) (ha : 0 < a)
    (hmeas : ∀ x, a * π x ≤ π' x) (f : V → ℝ) :
    a * LogSobolevMC.ChiSquare.entL π f ≤ LogSobolevMC.ChiSquare.entL π' f := by
  rw [entL_eq π hπ f, entL_eq π' hπ' f]
  set N := ∑ y, f y ^ 2 * π y with hN
  set N' := ∑ y, f y ^ 2 * π' y with hN'
  by_cases hf : ∀ x, f x = 0
  · simp [hf]
  push_neg at hf
  obtain ⟨x0, hx0⟩ := hf
  have hNpos : 0 < N := by
    rw [hN]
    apply lt_of_lt_of_le (b := f x0 ^ 2 * π x0)
    · have := hπpos x0; positivity
    · exact Finset.single_le_sum (f := fun y => f y ^ 2 * π y)
        (fun y _ => by have := hπpos y; positivity) (Finset.mem_univ x0)
  have hN'pos : 0 < N' := by
    rw [hN']
    apply lt_of_lt_of_le (b := f x0 ^ 2 * π' x0)
    · have := hπ'pos x0; positivity
    · exact Finset.single_le_sum (f := fun y => f y ^ 2 * π' y)
        (fun y _ => by have := hπ'pos y; positivity) (Finset.mem_univ x0)
  -- Σ φ(f², N') π' ≥ a Σ φ(f², N') π
  have step1 : a * ∑ x, (f x ^ 2 * Real.log (f x ^ 2 / N') - f x ^ 2 + N') * π x
      ≤ ∑ x, (f x ^ 2 * Real.log (f x ^ 2 / N') - f x ^ 2 + N') * π' x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    have hφ := phi_nonneg (f x ^ 2) N' (by positivity) hN'pos
    calc a * ((f x ^ 2 * Real.log (f x ^ 2 / N') - f x ^ 2 + N') * π x)
        = (f x ^ 2 * Real.log (f x ^ 2 / N') - f x ^ 2 + N') * (a * π x) := by ring
      _ ≤ (f x ^ 2 * Real.log (f x ^ 2 / N') - f x ^ 2 + N') * π' x :=
          mul_le_mul_of_nonneg_left (hmeas x) hφ
  have e1 : ∑ x, (f x ^ 2 * Real.log (f x ^ 2 / N') - f x ^ 2 + N') * π' x
      = ∑ x, (f x ^ 2 * Real.log (f x ^ 2 / N')) * π' x := by
    have : ∀ x, (f x ^ 2 * Real.log (f x ^ 2 / N') - f x ^ 2 + N') * π' x
        = (f x ^ 2 * Real.log (f x ^ 2 / N')) * π' x - f x ^ 2 * π' x + N' * π' x := by intro x; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ'.2, mul_one, ← hN']
    ring
  have e2 : ∑ x, (f x ^ 2 * Real.log (f x ^ 2 / N') - f x ^ 2 + N') * π x
      = ∑ x, (f x ^ 2 * Real.log (f x ^ 2 / N)) * π x + (N * Real.log (N / N') - N + N') := by
    have : ∀ x, (f x ^ 2 * Real.log (f x ^ 2 / N') - f x ^ 2 + N') * π x
        = (f x ^ 2 * Real.log (f x ^ 2 / N)) * π x + Real.log (N / N') * (f x ^ 2 * π x)
          - f x ^ 2 * π x + N' * π x := by
      intro x
      by_cases hfx : f x = 0
      · simp [hfx]
      · have : Real.log (f x ^ 2 / N') = Real.log (f x ^ 2 / N) + Real.log (N / N') := by
          rw [← Real.log_mul (by positivity) (by positivity)]
          congr 1; field_simp
        rw [this]; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ.2, mul_one, ← hN]
    ring
  have hφN := phi_nonneg N N' hNpos.le hN'pos
  rw [e1] at step1; rw [e2] at step1
  nlinarith

/-- If `ℒ_π` vanishes identically then `V` has at most one point. -/
lemma entL_zero_subsingleton (π : V → ℝ) (hπ : IsDist π) (hπpos : ∀ x, 0 < π x)
    (hent : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.entL π f = 0) : ∀ x y : V, x = y := by
  intro x y
  by_contra hxy
  have hlt : π x < 1 := by
    have h1 : ∑ z ∈ ({x, y} : Finset V), π z ≤ ∑ z, π z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => (hπpos z).le)
    rw [Finset.sum_pair hxy, hπ.2] at h1
    have := hπpos y; linarith
  have h := hent (fun z => if z = x then 1 else 0)
  rw [entL_eq π hπ] at h
  have hN : ∑ z, (if z = x then (1:ℝ) else 0) ^ 2 * π z = π x := by
    simp [Finset.sum_ite_eq']
  rw [hN] at h
  have h2 : ∑ z, (if z = x then (1:ℝ) else 0) ^ 2 * Real.log ((if z = x then (1:ℝ) else 0) ^ 2 / π x) * π z
      = Real.log (1 / π x) * π x := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro z _ hz; simp [hz]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  rw [h2] at h
  have hpos : 0 < Real.log (1 / π x) * π x := by
    apply mul_pos _ (hπpos x)
    apply Real.log_pos
    rw [lt_div_iff₀ (hπpos x)]; linarith
  linarith

lemma entL_zero_of_subsingleton (π : V → ℝ) (hπ : IsDist π) (hsub : ∀ x y : V, x = y)
    (f : V → ℝ) : LogSobolevMC.ChiSquare.entL π f = 0 := by
  rw [entL_eq π hπ]
  apply Finset.sum_eq_zero
  intro x _
  have hN : ∑ y, f y ^ 2 * π y = f x ^ 2 := by
    have : ∀ y, f y = f x := fun y => by rw [hsub y x]
    simp only [this, ← Finset.mul_sum, hπ.2, mul_one]
  rw [hN]
  by_cases hfx : f x = 0
  · simp [hfx]
  · rw [div_self (by positivity), Real.log_one]; ring

/-- Lemma 3.3. -/
theorem lemma_3_3_core {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (K' : Matrix V V ℝ) (hK' : MarkovMixing.IsStochastic K')
    (π' : V → ℝ) (hπ' : MarkovMixing.IsStationary K' π') (hπ'pos : ∀ x, 0 < π' x)
    (A a : ℝ) (hA : 0 < A) (ha : 0 < a)
    (hE : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.dirichlet K' π' f f ≤ A * LogSobolevMC.ChiSquare.dirichlet K π f f)
    (hmeas : ∀ x, a * π x ≤ π' x) :
    LogSobolevMC.ChiSquare.gap K' π' ≤ A / a * LogSobolevMC.ChiSquare.gap K π ∧
    LogSobolevMC.ChiSquare.logSobolev K' π' ≤ A / a * LogSobolevMC.ChiSquare.logSobolev K π := by
  have hAa : 0 < A / a := div_pos hA ha
  constructor
  · unfold LogSobolevMC.ChiSquare.gap
    set S := {r : ℝ | ∃ f : V → ℝ, distVar π f ≠ 0 ∧ r = LogSobolevMC.ChiSquare.dirichlet K π f f / distVar π f} with hS
    set S' := {r : ℝ | ∃ f : V → ℝ, distVar π' f ≠ 0 ∧ r = LogSobolevMC.ChiSquare.dirichlet K' π' f f / distVar π' f} with hS'
    have hbdd' : BddBelow S' := by
      refine ⟨0, ?_⟩
      rintro r ⟨f, hf, rfl⟩
      exact div_nonneg (dirichlet_nonneg K' hK' π' hπ' f) (distVar_nonneg π' hπ'.1.1 f)
    by_cases hne : S.Nonempty
    · rw [← div_le_iff₀' hAa]
      apply le_csInf hne
      rintro r ⟨f, hf, rfl⟩
      have hV : 0 < distVar π f := lt_of_le_of_ne (distVar_nonneg π hπ.1.1 f) (Ne.symm hf)
      have hV' : a * distVar π f ≤ distVar π' f := var_compare π π' hπ.1 hπ'.1 a ha hmeas f
      have hV'pos : 0 < distVar π' f := lt_of_lt_of_le (mul_pos ha hV) hV'
      have hmem : LogSobolevMC.ChiSquare.dirichlet K' π' f f / distVar π' f ∈ S' := ⟨f, hV'pos.ne', rfl⟩
      have h1 : sInf S' ≤ LogSobolevMC.ChiSquare.dirichlet K' π' f f / distVar π' f := csInf_le hbdd' hmem
      have h2 : LogSobolevMC.ChiSquare.dirichlet K' π' f f / distVar π' f
          ≤ A / a * (LogSobolevMC.ChiSquare.dirichlet K π f f / distVar π f) := by
        rw [div_le_iff₀ hV'pos]
        have hE0 := dirichlet_nonneg K hK π hπ f
        calc LogSobolevMC.ChiSquare.dirichlet K' π' f f ≤ A * LogSobolevMC.ChiSquare.dirichlet K π f f := hE f
          _ = A / a * (LogSobolevMC.ChiSquare.dirichlet K π f f / distVar π f) * (a * distVar π f) := by
              field_simp
          _ ≤ A / a * (LogSobolevMC.ChiSquare.dirichlet K π f f / distVar π f) * distVar π' f := by
              apply mul_le_mul_of_nonneg_left hV'
              exact mul_nonneg hAa.le (div_nonneg hE0 hV.le)
      rw [div_le_iff₀' hAa]
      exact h1.trans h2
    · -- S empty: all functions constant, so S' empty too
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have hconst : ∀ f : V → ℝ, distVar π f = 0 := by
        intro f
        by_contra h
        have : LogSobolevMC.ChiSquare.dirichlet K π f f / distVar π f ∈ S := ⟨f, h, rfl⟩
        rw [hne] at this; exact this
      have hconst' : ∀ f : V → ℝ, distVar π' f = 0 := by
        intro f
        have h1 : ∀ x, f x = distExp π f := by
          intro x
          have h := hconst f
          unfold distVar at h
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by
            have := hπ.1.1 y; positivity)).1 h x (Finset.mem_univ x)
          have hp := hπpos x
          have : (f x - distExp π f) ^ 2 = 0 := by
            rcases mul_eq_zero.1 this with h' | h'
            · exact h'
            · exact absurd h' hp.ne'
          exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this)
        have hm : distExp π' f = distExp π f := by
          unfold distExp; simp only [h1, ← Finset.mul_sum, hπ'.1.2, hπ.1.2, mul_one]
        unfold distVar; rw [hm]; simp [h1]
      have hS'e : S' = ∅ := by
        ext r; simp [hS', hconst']
      rw [hne, hS'e, Real.sInf_empty]; simp
  · unfold LogSobolevMC.ChiSquare.logSobolev
    set S := {r : ℝ | ∃ f : V → ℝ, LogSobolevMC.ChiSquare.entL π f ≠ 0 ∧ r = LogSobolevMC.ChiSquare.dirichlet K π f f / LogSobolevMC.ChiSquare.entL π f} with hS
    set S' := {r : ℝ | ∃ f : V → ℝ, LogSobolevMC.ChiSquare.entL π' f ≠ 0 ∧ r = LogSobolevMC.ChiSquare.dirichlet K' π' f f / LogSobolevMC.ChiSquare.entL π' f} with hS'
    have hbdd' : BddBelow S' := by
      refine ⟨0, ?_⟩
      rintro r ⟨f, hf, rfl⟩
      exact div_nonneg (dirichlet_nonneg K' hK' π' hπ' f) (entL_nonneg π' hπ'.1 hπ'pos f)
    by_cases hne : S.Nonempty
    · rw [← div_le_iff₀' hAa]
      apply le_csInf hne
      rintro r ⟨f, hf, rfl⟩
      have hV : 0 < LogSobolevMC.ChiSquare.entL π f := lt_of_le_of_ne (entL_nonneg π hπ.1 hπpos f) (Ne.symm hf)
      have hV' : a * LogSobolevMC.ChiSquare.entL π f ≤ LogSobolevMC.ChiSquare.entL π' f :=
        entL_compare π π' hπ.1 hπ'.1 hπpos hπ'pos a ha hmeas f
      have hV'pos : 0 < LogSobolevMC.ChiSquare.entL π' f := lt_of_lt_of_le (mul_pos ha hV) hV'
      have hmem : LogSobolevMC.ChiSquare.dirichlet K' π' f f / LogSobolevMC.ChiSquare.entL π' f ∈ S' := ⟨f, hV'pos.ne', rfl⟩
      have h1 : sInf S' ≤ LogSobolevMC.ChiSquare.dirichlet K' π' f f / LogSobolevMC.ChiSquare.entL π' f := csInf_le hbdd' hmem
      have h2 : LogSobolevMC.ChiSquare.dirichlet K' π' f f / LogSobolevMC.ChiSquare.entL π' f
          ≤ A / a * (LogSobolevMC.ChiSquare.dirichlet K π f f / LogSobolevMC.ChiSquare.entL π f) := by
        rw [div_le_iff₀ hV'pos]
        have hE0 := dirichlet_nonneg K hK π hπ f
        calc LogSobolevMC.ChiSquare.dirichlet K' π' f f ≤ A * LogSobolevMC.ChiSquare.dirichlet K π f f := hE f
          _ = A / a * (LogSobolevMC.ChiSquare.dirichlet K π f f / LogSobolevMC.ChiSquare.entL π f) * (a * LogSobolevMC.ChiSquare.entL π f) := by
              field_simp
          _ ≤ A / a * (LogSobolevMC.ChiSquare.dirichlet K π f f / LogSobolevMC.ChiSquare.entL π f) * LogSobolevMC.ChiSquare.entL π' f := by
              apply mul_le_mul_of_nonneg_left hV'
              exact mul_nonneg hAa.le (div_nonneg hE0 hV.le)
      rw [div_le_iff₀' hAa]
      exact h1.trans h2
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      have hconst : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.entL π f = 0 := by
        intro f
        by_contra h
        have : LogSobolevMC.ChiSquare.dirichlet K π f f / LogSobolevMC.ChiSquare.entL π f ∈ S := ⟨f, h, rfl⟩
        rw [hne] at this; exact this
      have hconst' : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.entL π' f = 0 := by
        intro f
        have hsub : ∀ x y : V, x = y := entL_zero_subsingleton π hπ.1 hπpos hconst
        exact entL_zero_of_subsingleton π' hπ'.1 hsub f
      have hS'e : S' = ∅ := by
        ext r; simp [hS', hconst']
      rw [hne, hS'e, Real.sInf_empty]; simp


/-! ### The two-point log-Sobolev inequality -/

/-- `L(b) = log 2 + 2 log b − log(a² + b²)` (equal to `log(2b²/(a²+b²))` for `b > 0`). -/
noncomputable def Lfn (a b : ℝ) : ℝ := Real.log 2 + 2 * Real.log b - Real.log (a ^ 2 + b ^ 2)

noncomputable def hfn (a b : ℝ) : ℝ := a - b + b * Lfn a b

noncomputable def Ffn (a b : ℝ) : ℝ := (a - b) ^ 2 - a ^ 2 * Lfn b a - b ^ 2 * Lfn a b

lemma Lfn_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) : Lfn a b = Real.log (2 * b ^ 2 / (a ^ 2 + b ^ 2)) := by
  unfold Lfn
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow]
  push_cast; ring

lemma hasDerivAt_Lfn (a b : ℝ) (hb : 0 < b) :
    HasDerivAt (Lfn a) (2 * b⁻¹ - 2 * b / (a ^ 2 + b ^ 2)) b := by
  have h1 : HasDerivAt (fun b : ℝ => Real.log b) b⁻¹ b := Real.hasDerivAt_log hb.ne'
  have h2 : HasDerivAt (fun b : ℝ => a ^ 2 + b ^ 2) (2 * b) b := by
    have := (hasDerivAt_pow 2 b).const_add (a ^ 2); simpa using this
  have h3 : HasDerivAt (fun b : ℝ => Real.log (a ^ 2 + b ^ 2)) (2 * b / (a ^ 2 + b ^ 2)) b :=
    h2.log (by positivity)
  exact ((h1.const_mul 2).const_add (Real.log 2)).sub h3

lemma hasDerivAt_Lfn' (a b : ℝ) (ha : 0 < a) :
    HasDerivAt (fun b => Lfn b a) (- (2 * b / (b ^ 2 + a ^ 2))) b := by
  unfold Lfn
  have h2 : HasDerivAt (fun b : ℝ => b ^ 2 + a ^ 2) (2 * b) b := by
    have := (hasDerivAt_pow 2 b).add_const (a ^ 2); simpa using this
  have h3 : HasDerivAt (fun b : ℝ => Real.log (b ^ 2 + a ^ 2)) (2 * b / (b ^ 2 + a ^ 2)) b :=
    h2.log (by positivity)
  have := (h3.const_sub (Real.log 2 + 2 * Real.log a))
  simpa using this

lemma hasDerivAt_hfn (a b : ℝ) (hb : 0 < b) :
    HasDerivAt (hfn a) (-1 + (1 * Lfn a b + b * (2 * b⁻¹ - 2 * b / (a ^ 2 + b ^ 2)))) b := by
  unfold hfn
  have h1 : HasDerivAt (fun b : ℝ => a - b) (-1) b := by
    have := (hasDerivAt_id b).const_sub a; simpa using this
  exact h1.add ((hasDerivAt_id b).mul (hasDerivAt_Lfn a b hb))

lemma deriv_hfn_nonpos (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    -1 + (1 * Lfn a b + b * (2 * b⁻¹ - 2 * b / (a ^ 2 + b ^ 2))) ≤ 0 := by
  rw [Lfn_eq a b ha hb]
  set w := 2 * b ^ 2 / (a ^ 2 + b ^ 2) with hw
  have hwpos : 0 < w := by positivity
  have hl := Real.log_le_sub_one_of_pos hwpos
  have : b * (2 * b⁻¹ - 2 * b / (a ^ 2 + b ^ 2)) = 2 - w := by
    rw [hw]; field_simp
  rw [this]; linarith

lemma hfn_self (a : ℝ) (ha : 0 < a) : hfn a a = 0 := by
  unfold hfn Lfn
  have : a ^ 2 + a ^ 2 = 2 * a ^ 2 := by ring
  rw [this, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  push_cast; ring

lemma hfn_nonneg (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) : 0 ≤ hfn a b := by
  have hanti : AntitoneOn (hfn a) (Set.Icc b a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc b a)
    · intro x hx
      exact (hasDerivAt_hfn a x (lt_of_lt_of_le hb hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_hfn a x (lt_trans hb hx.1)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_hfn a x (lt_trans hb hx.1)).deriv]
      exact deriv_hfn_nonpos a x ha.le (lt_trans hb hx.1)
  have := hanti (Set.left_mem_Icc.2 hba) (Set.right_mem_Icc.2 hba) hba
  rw [hfn_self a ha] at this
  exact this

lemma hasDerivAt_Ffn (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (Ffn a) (2 * (a - b) * (-1) - a ^ 2 * (- (2 * b / (b ^ 2 + a ^ 2)))
      - (2 * b * Lfn a b + b ^ 2 * (2 * b⁻¹ - 2 * b / (a ^ 2 + b ^ 2)))) b := by
  unfold Ffn
  have h1 : HasDerivAt (fun b : ℝ => a - b) (-1) b := by
    have := (hasDerivAt_id b).const_sub a; simpa using this
  have h1' : HasDerivAt (fun b : ℝ => (a - b) ^ 2) (2 * (a - b) * (-1)) b :=
    (h1.pow 2).congr_deriv (by push_cast; ring)
  have h2 : HasDerivAt (fun b : ℝ => a ^ 2 * Lfn b a) (a ^ 2 * (- (2 * b / (b ^ 2 + a ^ 2)))) b :=
    (hasDerivAt_Lfn' a b ha).const_mul (a ^ 2)
  have h3 : HasDerivAt (fun b : ℝ => b ^ 2 * Lfn a b)
      (2 * b * Lfn a b + b ^ 2 * (2 * b⁻¹ - 2 * b / (a ^ 2 + b ^ 2))) b := by
    have hp : HasDerivAt (fun b : ℝ => b ^ 2) (2 * b) b := by
      have := hasDerivAt_pow 2 b; simpa using this
    exact hp.mul (hasDerivAt_Lfn a b hb)
  exact (h1'.sub h2).sub h3

lemma deriv_Ffn_eq (a b : ℝ) (hb : 0 < b) :
    2 * (a - b) * (-1) - a ^ 2 * (- (2 * b / (b ^ 2 + a ^ 2)))
      - (2 * b * Lfn a b + b ^ 2 * (2 * b⁻¹ - 2 * b / (a ^ 2 + b ^ 2))) = -2 * hfn a b := by
  unfold hfn
  have h1 : b ^ 2 + a ^ 2 = a ^ 2 + b ^ 2 := by ring
  rw [h1]
  field_simp
  ring

lemma Lfn_self (a : ℝ) (ha : 0 < a) : Lfn a a = 0 := by
  unfold Lfn
  have : a ^ 2 + a ^ 2 = 2 * a ^ 2 := by ring
  rw [this, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  push_cast; ring

lemma Ffn_self (a : ℝ) (ha : 0 < a) : Ffn a a = 0 := by
  unfold Ffn; rw [Lfn_self a ha]; ring

lemma Ffn_nonneg (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) : 0 ≤ Ffn a b := by
  have hanti : AntitoneOn (Ffn a) (Set.Icc b a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc b a)
    · intro x hx
      exact (hasDerivAt_Ffn a x ha (lt_of_lt_of_le hb hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_Ffn a x ha (lt_trans hb hx.1)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_Ffn a x ha (lt_trans hb hx.1)).deriv, deriv_Ffn_eq a x (lt_trans hb hx.1)]
      have := hfn_nonneg a x ha (lt_trans hb hx.1) hx.2.le
      linarith
  have := hanti (Set.left_mem_Icc.2 hba) (Set.right_mem_Icc.2 hba) hba
  rw [Ffn_self a ha] at this
  exact this

/-- The two-point inequality for `0 ≤ b ≤ a`. -/
lemma key_ineq_aux (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    a ^ 2 * Real.log (2 * a ^ 2 / (a ^ 2 + b ^ 2)) + b ^ 2 * Real.log (2 * b ^ 2 / (a ^ 2 + b ^ 2))
      ≤ (a - b) ^ 2 := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb0 : b = 0 := le_antisymm (hba.trans_eq ha0.symm) hb
    rw [← ha0, hb0]; simp
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · rw [← hb0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero, zero_mul, sub_zero]
    have : 2 * a ^ 2 / a ^ 2 = 2 := by field_simp
    rw [this]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    nlinarith [sq_nonneg a]
  have hF := Ffn_nonneg a b ha0 hb0 hba
  unfold Ffn at hF
  rw [Lfn_eq a b ha hb0] at hF
  rw [Lfn_eq b a hb ha0] at hF
  have e : b ^ 2 + a ^ 2 = a ^ 2 + b ^ 2 := by ring
  rw [e] at hF
  linarith

lemma key_ineq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 * Real.log (2 * a ^ 2 / (a ^ 2 + b ^ 2)) + b ^ 2 * Real.log (2 * b ^ 2 / (a ^ 2 + b ^ 2))
      ≤ (a - b) ^ 2 := by
  rcases le_total b a with h | h
  · exact key_ineq_aux a b ha hb h
  · have := key_ineq_aux b a hb ha h
    have e : b ^ 2 + a ^ 2 = a ^ 2 + b ^ 2 := by ring
    rw [e] at this
    have e2 : (b - a) ^ 2 = (a - b) ^ 2 := by ring
    rw [e2] at this
    linarith


/-! ### Example 3.1 -/

lemma swap2_stochastic : IsStochastic swap2 := by
  constructor
  · intro x y; unfold swap2; split_ifs <;> norm_num
  · intro x; fin_cases x <;> simp [swap2, Fin.sum_univ_two]

lemma half_isDist : IsDist (fun _ : Fin 2 => (1/2:ℝ)) := by
  constructor
  · intro x; norm_num
  · norm_num [Fin.sum_univ_two]

lemma swap2_stationary : IsStationary swap2 (fun _ : Fin 2 => (1/2:ℝ)) := by
  refine ⟨half_isDist, ?_⟩
  ext y; fin_cases y <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, swap2] <;> norm_num

lemma swap2_dirichlet (f : Fin 2 → ℝ) :
    LogSobolevMC.ChiSquare.dirichlet swap2 (fun _ => (1/2:ℝ)) f f = (f 0 - f 1) ^ 2 / 2 := by
  simp [LogSobolevMC.ChiSquare.dirichlet, Matrix.mulVec, dotProduct, Fin.sum_univ_two, swap2]; ring

lemma swap2_var (f : Fin 2 → ℝ) : distVar (fun _ : Fin 2 => (1/2:ℝ)) f = (f 0 - f 1) ^ 2 / 4 := by
  simp [distVar, distExp, Fin.sum_univ_two]; ring

lemma swap2_entL (f : Fin 2 → ℝ) :
    LogSobolevMC.ChiSquare.entL (fun _ : Fin 2 => (1/2:ℝ)) f
      = (f 0 ^ 2 * Real.log (f 0 ^ 2 * 2 / (f 0 ^ 2 + f 1 ^ 2))
          + f 1 ^ 2 * Real.log (f 1 ^ 2 * 2 / (f 0 ^ 2 + f 1 ^ 2))) / 2 := by
  rw [entL_eq _ half_isDist]
  simp only [Fin.sum_univ_two]
  have e : f 0 ^ 2 * (1/2) + f 1 ^ 2 * (1/2) = (f 0 ^ 2 + f 1 ^ 2) / 2 := by ring
  rw [e, div_div_eq_mul_div, div_div_eq_mul_div]
  ring

lemma key_ineq' (x y : ℝ) :
    x ^ 2 * Real.log (x ^ 2 * 2 / (x ^ 2 + y ^ 2)) + y ^ 2 * Real.log (y ^ 2 * 2 / (x ^ 2 + y ^ 2))
      ≤ (x - y) ^ 2 := by
  have h := key_ineq |x| |y| (abs_nonneg x) (abs_nonneg y)
  simp only [sq_abs] at h
  have h2 : (|x| - |y|) ^ 2 ≤ (x - y) ^ 2 := by
    rw [← sq_abs (x - y)]
    apply sq_le_sq'
    · have := abs_sub_abs_le_abs_sub y x; rw [abs_sub_comm] at this; linarith
    · exact abs_sub_abs_le_abs_sub x y
  have e1 : 2 * x ^ 2 = x ^ 2 * 2 := by ring
  have e2 : 2 * y ^ 2 = y ^ 2 * 2 := by ring
  rw [e1, e2] at h
  linarith

lemma entL_le_dirichlet (f : Fin 2 → ℝ) :
    LogSobolevMC.ChiSquare.entL (fun _ : Fin 2 => (1/2:ℝ)) f
      ≤ LogSobolevMC.ChiSquare.dirichlet swap2 (fun _ => (1/2:ℝ)) f f := by
  rw [swap2_entL, swap2_dirichlet]
  have := key_ineq' (f 0) (f 1)
  linarith

theorem example_3_1_core :
    MarkovMixing.IsStationary swap2 (fun _ => (1 / 2 : ℝ)) ∧
    LogSobolevMC.ChiSquare.gap swap2 (fun _ => (1 / 2 : ℝ)) = 2 ∧
    LogSobolevMC.ChiSquare.logSobolev swap2 (fun _ => (1 / 2 : ℝ)) = LogSobolevMC.ChiSquare.gap swap2 (fun _ => (1 / 2 : ℝ)) / 2 ∧
    LogSobolevMC.ChiSquare.logSobolev swap2 (fun _ => (1 / 2 : ℝ)) = 1 := by
  have hstat := swap2_stationary
  have hgap : LogSobolevMC.ChiSquare.gap swap2 (fun _ => (1 / 2 : ℝ)) = 2 := by
    unfold LogSobolevMC.ChiSquare.gap
    have : {r : ℝ | ∃ f : Fin 2 → ℝ, distVar (fun _ => (1 / 2 : ℝ)) f ≠ 0 ∧
        r = LogSobolevMC.ChiSquare.dirichlet swap2 (fun _ => (1 / 2 : ℝ)) f f / distVar (fun _ => (1 / 2 : ℝ)) f} = {2} := by
      ext r; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨f, hf, rfl⟩
        rw [swap2_dirichlet, swap2_var]; rw [swap2_var] at hf
        have : (f 0 - f 1) ^ 2 ≠ 0 := by intro h; apply hf; rw [h]; norm_num
        have hne : f 0 - f 1 ≠ 0 := by intro h; apply this; rw [h]; ring
        field_simp; ring
      · rintro rfl
        refine ⟨![0, 1], ?_, ?_⟩
        · rw [swap2_var]; simp
        · rw [swap2_dirichlet, swap2_var]; norm_num
    rw [this, csInf_singleton]
  have hα : LogSobolevMC.ChiSquare.logSobolev swap2 (fun _ => (1 / 2 : ℝ)) = 1 := by
    apply le_antisymm
    · have := lemma_3_1_core swap2 swap2_stochastic (fun _ => (1 / 2 : ℝ)) hstat (fun _ => by norm_num)
      rw [hgap] at this; linarith
    · unfold LogSobolevMC.ChiSquare.logSobolev
      apply le_csInf
      · refine ⟨_, ![1, 0], ?_, rfl⟩
        rw [swap2_entL]; norm_num
      · rintro r ⟨f, hf, rfl⟩
        have hpos : 0 < LogSobolevMC.ChiSquare.entL (fun _ => (1 / 2 : ℝ)) f :=
          lt_of_le_of_ne (entL_nonneg _ half_isDist (fun _ => by norm_num) f) (Ne.symm hf)
        rw [le_div_iff₀ hpos, one_mul]; exact entL_le_dirichlet f
  exact ⟨hstat, hgap, by rw [hα, hgap]; norm_num, hα⟩

end LogSobolevMC.Metropolis

open LogSobolevMC.Metropolis
open MarkovMixing

theorem solution :
    MarkovMixing.IsStationary swap2 (fun _ => (1 / 2 : ℝ)) ∧
    LogSobolevMC.ChiSquare.gap swap2 (fun _ => (1 / 2 : ℝ)) = 2 ∧
    LogSobolevMC.ChiSquare.logSobolev swap2 (fun _ => (1 / 2 : ℝ)) = LogSobolevMC.ChiSquare.gap swap2 (fun _ => (1 / 2 : ℝ)) / 2 ∧
    LogSobolevMC.ChiSquare.logSobolev swap2 (fun _ => (1 / 2 : ℝ)) = 1 := by
  exact example_3_1_core
