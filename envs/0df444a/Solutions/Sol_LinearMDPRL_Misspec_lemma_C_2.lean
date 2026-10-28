-- Prove2me | solution 1 for LinearMDPRL.Misspec.lemma_C_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:50:18.978418+00:00
-- url     : https://prove2.me/submissions/90b82859-7deb-4aa0-83bb-8407d448b17b

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Misspec_ApproxLinearMDP

open MeasureTheory ProbabilityTheory

universe u v

namespace Aux_LinearMDPRL_Misspec_lemma_C_2

open LinearMDPRL.Linear LinearMDPRL.Misspec

lemma valueRem_bound {S : Type u} {A : Type v} [MeasurableSpace S] [MeasurableSpace A]
    (M : EpisodicMDP S A) (H : ℕ) (π : Policy S A) :
    ∀ n x, |valueRem M H π n x| ≤ n := by
  intro n
  induction n with
  | zero => intro x; simp [valueRem]
  | succ n ih =>
    intro x
    simp only [valueRem]
    haveI := M.isMarkov (H - n)
    have h1 : |M.r (H - n) x (π x (H - n))| ≤ 1 := by
      have := M.r_mem (H - n) x (π x (H - n))
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    have h2 : ‖∫ y, valueRem M H π n y ∂(M.P (H - n) (x, π x (H - n)))‖ ≤ n := by
      have := norm_integral_le_of_norm_le_const (μ := M.P (H - n) (x, π x (H - n)))
        (f := valueRem M H π n) (C := n) (Filter.Eventually.of_forall (fun y => by
          rw [Real.norm_eq_abs]; exact ih y))
      rw [probReal_univ, mul_one] at this
      exact this
    rw [Real.norm_eq_abs] at h2
    calc |M.r (H - n) x (π x (H - n)) + ∫ y, valueRem M H π n y ∂(M.P (H - n) (x, π x (H - n)))|
        ≤ |M.r (H - n) x (π x (H - n))| +
          |∫ y, valueRem M H π n y ∂(M.P (H - n) (x, π x (H - n)))| := abs_add_le _ _
      _ ≤ 1 + n := add_le_add h1 h2
      _ = ((n + 1 : ℕ) : ℝ) := by push_cast; ring

lemma V_bound {S : Type u} {A : Type v} [MeasurableSpace S] [MeasurableSpace A]
    (M : EpisodicMDP S A) (H : ℕ) (π : Policy S A) (h : ℕ) (x : S) :
    |V M H π h x| ≤ H := by
  unfold V
  split_ifs with hh
  · refine (valueRem_bound M H π _ x).trans ?_
    exact_mod_cast (by omega : H + 1 - h ≤ H)
  · simp

lemma signed_bound {S : Type u} [MeasurableSpace S] (μ : SignedMeasure S) (f : S → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ y, |f y| ≤ C) :
    |signedIntegral μ f| ≤ C * (μ.totalVariation Set.univ).toReal := by
  unfold signedIntegral SignedMeasure.totalVariation
  have h1 := norm_integral_le_of_norm_le_const (μ := μ.toJordanDecomposition.posPart) (f := f)
    (C := C) (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hf y))
  have h2 := norm_integral_le_of_norm_le_const (μ := μ.toJordanDecomposition.negPart) (f := f)
    (C := C) (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hf y))
  rw [Real.norm_eq_abs] at h1 h2
  rw [Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [Measure.real] at h1 h2
  calc |∫ y, f y ∂μ.toJordanDecomposition.posPart - ∫ y, f y ∂μ.toJordanDecomposition.negPart|
      ≤ |∫ y, f y ∂μ.toJordanDecomposition.posPart| +
        |∫ y, f y ∂μ.toJordanDecomposition.negPart| := abs_sub _ _
    _ ≤ C * (μ.toJordanDecomposition.posPart Set.univ).toReal +
        C * (μ.toJordanDecomposition.negPart Set.univ).toReal := add_le_add h1 h2
    _ = _ := by ring

end Aux_LinearMDPRL_Misspec_lemma_C_2

open Aux_LinearMDPRL_Misspec_lemma_C_2 in
open LinearMDPRL.Misspec in
theorem solution {S : Type u} {A : Type v} [MeasurableSpace S] [Fintype A] [Nonempty A] [MeasurableSpace A]
    [DiscreteMeasurableSpace A] (d H : ℕ) (M : LinearMDPRL.Linear.EpisodicMDP S A)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (ζ : ℝ) (hM : IsApproxLinearMDP M H d φ ζ)
    (mu : ℕ → Fin d → SignedMeasure S) (θ : ℕ → EuclideanSpace ℝ (Fin d))
    (hrep : ∀ h ∈ Finset.Icc 1 H, IsApproxRep M φ ζ h (mu h) (θ h))
    (π : LinearMDPRL.Linear.Policy S A) (hπ : LinearMDPRL.Linear.IsMeasurablePolicy π) :
    ∀ h ∈ Finset.Icc 1 H, ‖repWeight M H π mu θ h‖ ≤ 2 * H * Real.sqrt d := by
  intro h hh
  have hH : (1 : ℝ) ≤ H := by
    have := (Finset.mem_Icc.1 hh); exact_mod_cast (by omega : 1 ≤ H)
  obtain ⟨_, _, hθ, hmu⟩ := hrep h hh
  unfold repWeight
  set w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
    (fun i => signedIntegral (mu h i) (LinearMDPRL.Linear.V M H π (h + 1))) with hw
  have hwi : ∀ i, |w i| ≤ H * ((mu h i).totalVariation Set.univ).toReal := by
    intro i
    exact signed_bound _ _ _ (by positivity) (fun y => V_bound M H π (h + 1) y)
  have hwn : ‖w‖ ≤ H * Real.sqrt d := by
    rw [EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ i, ‖w i‖ ^ 2)
        ≤ Real.sqrt (∑ i, ((H : ℝ) * ((mu h i).totalVariation Set.univ).toReal) ^ 2) := by
          apply Real.sqrt_le_sqrt
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hwi i) 2
      _ = H * Real.sqrt (∑ i, (((mu h i).totalVariation Set.univ).toReal) ^ 2) := by
          simp_rw [mul_pow]
          rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ ≤ H * Real.sqrt d := mul_le_mul_of_nonneg_left hmu (by positivity)
  calc ‖θ h + w‖ ≤ ‖θ h‖ + ‖w‖ := norm_add_le _ _
    _ ≤ Real.sqrt d + H * Real.sqrt d := add_le_add hθ hwn
    _ ≤ 2 * H * Real.sqrt d := by
        have := Real.sqrt_nonneg (d : ℝ)
        nlinarith
