-- Prove2me | solution 1 for LeastSquaresTD.Ergodic.lstd_converges_ergodic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:28:11.306031+00:00
-- url     : https://prove2.me/submissions/8c7bf4e8-ba78-4f8c-b0be-8d4ee99406b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain
import Definitions.Def_LeastSquaresTD_Ergodic_LSTD
import Theorems.Thm_LeastSquaresTD_Ergodic_eq12_theta_star_finite
import Theorems.Thm_LeastSquaresTD_Ergodic_lemma5Matrix_isUnit
import Theorems.Thm_LeastSquaresTD_Ergodic_visits_in_proportion_pi
import Theorems.Thm_LeastSquaresTD_Ergodic_lemma5

set_option autoImplicit false

open MeasureTheory Matrix Filter Topology

namespace LeastSquaresTD.Ergodic

/-- Every finite row-stochastic chain has a stationary distribution (proved inline). -/
theorem exists_stationary_of_chain {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) : ∃ π : X → ℝ, C.IsStationary π := by
  have hdet : (C.P - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have := congrFun h (Classical.arbitrary X)
      simp at this
    · ext x
      simp [Matrix.mulVec, dotProduct, C.row_sum x, Matrix.one_apply]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hvP : v ᵥ* C.P = v := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at hv
    exact hv
  have hcoord : ∀ y, v y = ∑ x, v x * C.P x y := by
    intro y
    have := congrFun hvP y
    rw [← this]
    rfl
  let w : X → ℝ := fun x => |v x|
  have hle : ∀ y, w y ≤ (w ᵥ* C.P) y := by
    intro y
    show |v y| ≤ ∑ x, |v x| * C.P x y
    rw [hcoord y]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [abs_mul, abs_of_nonneg (C.nonneg x y)]
  have hsum : ∑ y, (w ᵥ* C.P) y = ∑ y, w y := by
    show ∑ y, ∑ x, w x * C.P x y = ∑ y, w y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, C.row_sum x, mul_one]
  have heq : w ᵥ* C.P = w := by
    have h0 : ∑ y, ((w ᵥ* C.P) y - w y) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sub_nonneg.mpr (hle y))).mp h0
    funext y
    exact sub_eq_zero.mp (this y (Finset.mem_univ y))
  have hs : 0 < ∑ x, w x := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hv0
    exact Finset.sum_pos' (fun y _ => abs_nonneg _) ⟨x, Finset.mem_univ x, abs_pos.mpr hx⟩
  refine ⟨(∑ x, w x)⁻¹ • w, ?_, ?_, ?_⟩
  · intro x
    exact mul_nonneg (inv_nonneg.mpr hs.le) (abs_nonneg _)
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · rw [Matrix.smul_vecMul, heq]


theorem lstd_converges_ergodic_reduction {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (hC : C.IsErgodic) (R : X → X → ℝ)
    {m : ℕ} (φ : X → Fin m → ℝ) (hφ : LinearIndependent ℝ φ) (hm : m = Fintype.card X)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : X → ℝ) (hν : IsProbVec ν) (Z : ℕ → Ω → X) (hZ : IsMarkovLaw μ C ν Z) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k * ((C.P ^ k) *ᵥ C.rbar R) x)) ∧
      (∀ x, C.value R γ x = φ x ⬝ᵥ θstar) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun t : ℕ => lstdTheta φ R γ t (fun k => Z k ω)) atTop (𝓝 θstar) := by
  obtain ⟨θ, hsum, hval, hr⟩ := eq12_theta_star_finite C R φ hφ hm γ hγ0 hγ1
  obtain ⟨π, hπ⟩ := exists_stationary_of_chain C
  obtain ⟨-, hM⟩ := lemma5Matrix_isUnit C hC π hπ φ hφ hm γ hγ0 hγ1
  obtain ⟨h2, h3⟩ := visits_in_proportion_pi C hC π hπ μ ν hν Z hZ
  have hlim := lemma5 C R φ γ π μ ν hν Z hZ h2 h3 hM
  have hv : lemma5Vector C R φ π = lemma5Matrix C φ π γ *ᵥ θ := by
    unfold lemma5Vector lemma5Matrix
    rw [hr]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hid : (lemma5Matrix C φ π γ)⁻¹ *ᵥ lemma5Vector C R φ π = θ := by
    rw [hv, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hM), Matrix.one_mulVec]
  refine ⟨θ, hsum, hval, ?_⟩
  filter_upwards [hlim] with ω hω
  rwa [hid] at hω

end LeastSquaresTD.Ergodic


theorem solution {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : LeastSquaresTD.Ergodic.Chain X) (hC : C.IsErgodic) (R : X → X → ℝ)
    {m : ℕ} (φ : X → Fin m → ℝ) (hφ : LinearIndependent ℝ φ) (hm : m = Fintype.card X)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : X → ℝ) (hν : LeastSquaresTD.Ergodic.IsProbVec ν) (Z : ℕ → Ω → X) (hZ : LeastSquaresTD.Ergodic.IsMarkovLaw μ C ν Z) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k * ((C.P ^ k) *ᵥ C.rbar R) x)) ∧
      (∀ x, C.value R γ x = φ x ⬝ᵥ θstar) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun t : ℕ => LeastSquaresTD.Ergodic.lstdTheta φ R γ t (fun k => Z k ω)) atTop (𝓝 θstar) :=
  LeastSquaresTD.Ergodic.lstd_converges_ergodic_reduction C hC R φ hφ hm γ hγ0 hγ1 μ ν hν Z hZ
