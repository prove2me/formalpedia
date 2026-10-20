-- Prove2me | solution 1 for OAI.Cotype.fixedCotypeBound_dual_l2Amplification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:17:19.537962+00:00
-- url     : https://prove2.me/submissions/d86f52dc-3f89-4778-baeb-0499d32bd118

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification

open OAI OAI.Cotype
open scoped BigOperators
open WithLp
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
theorem h50a_amp {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {m : ℕ} {D : ℝ}
    (h : FixedCotypeBound Y m D) : FixedCotypeBound (PiLp 2 (fun _ : Ω => Y)) m D := by
  obtain ⟨hD, hb⟩ := h
  refine ⟨hD, fun x => ?_⟩
  have hsq : ∀ a : Ω, ∑ i, ‖x i a‖ ^ 2 ≤ D ^ 2 * cubeL2 Y (rademacherSum Y (fun i => x i a)) ^ 2 := by
    intro a
    have := hb (fun i => x i a)
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), mul_pow] at h2
  have hrad : ∀ ε a, (rademacherSum (PiLp 2 (fun _ : Ω => Y)) x ε) a = rademacherSum Y (fun i => x i a) ε := by
    intro ε a
    simp [rademacherSum]
  have hL : ∑ i, ‖x i‖ ^ 2 = ∑ a, ∑ i, ‖x i a‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2]; rw [Finset.sum_comm]
  have hR : cubeL2 (PiLp 2 (fun _ : Ω => Y)) (rademacherSum _ x) ^ 2 =
      ∑ a, cubeL2 Y (rademacherSum Y (fun i => x i a)) ^ 2 := by
    simp only [cubeL2_sq, average, smul_eq_mul, PiLp.norm_sq_eq_of_L2, hrad, Finset.mul_sum]
    rw [Finset.sum_comm]
  have key : ∑ i, ‖x i‖ ^ 2 ≤ (D * cubeL2 (PiLp 2 (fun _ : Ω => Y)) (rademacherSum _ x)) ^ 2 := by
    rw [hL, mul_pow, hR, Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => hsq a
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt ((D * cubeL2 _ (rademacherSum _ x)) ^ 2) :=
        Real.sqrt_le_sqrt key
    _ = _ := Real.sqrt_sq (mul_nonneg hD (cubeL2_nonneg _))

omit [DecidableEq Ω] in
theorem h50a_eval (φ : X →L[ℝ] ℝ) {a : ℝ} (ha : a < ‖φ‖) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ a < φ x := by
  rcases lt_or_ge a 0 with h | h
  · exact ⟨0, by simp, by simpa using h⟩
  obtain ⟨x, hx1, hx2⟩ := φ.exists_lt_apply_of_lt_opNorm (r := a) ha
  rcases le_or_gt 0 (φ x) with h0 | h0
  · exact ⟨x, hx1.le, by rwa [Real.norm_eq_abs, abs_of_nonneg h0] at hx2⟩
  · refine ⟨-x, by rw [norm_neg]; exact hx1.le, ?_⟩
    rw [map_neg]
    rwa [Real.norm_eq_abs, abs_of_neg h0] at hx2

omit [DecidableEq Ω] in
theorem h50a_l2norm (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteL2Dual g‖ = ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ := by
  set N := ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ with hN
  have hN2 : N ^ 2 = ∑ a, ‖g a‖ ^ 2 := by
    rw [hN, PiLp.norm_sq_eq_of_L2]
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (finiteL2DualLinear_bound g)
  · set F := finiteL2Dual g
    have key : ∀ δ > 0, N ^ 2 ≤ ‖F‖ * N + δ := by
      intro δ hδ
      set S := ∑ a, ‖g a‖
      have hS : 0 ≤ S := Finset.sum_nonneg fun a _ => norm_nonneg _
      have he : 0 < δ / (S + 1) := by positivity
      choose x hx1 hx2 using fun a => h50a_eval (g a) (sub_lt_self (‖g a‖) he)
      let z : PiLp 2 (fun _ : Ω => X) := toLp 2 (fun a => ‖g a‖ • x a)
      have hz : ‖z‖ ≤ N := by
        rw [hN, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum; intro a _
        simp only [z, PiLp.toLp_apply, norm_smul, norm_norm]
        exact pow_le_pow_left₀ (by positivity)
          (by simpa using mul_le_mul_of_nonneg_left (hx1 a) (norm_nonneg (g a))) 2
      have hFz : F z ≤ ‖F‖ * N :=
        (Real.le_norm_self _).trans ((F.le_opNorm z).trans
          (mul_le_mul_of_nonneg_left hz (norm_nonneg _)))
      have hlow : ∑ a, ‖g a‖ * (‖g a‖ - δ / (S + 1)) ≤ F z := by
        simp only [F, finiteL2Dual_apply, z, PiLp.toLp_apply, map_smul, smul_eq_mul]
        exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hx2 a).le (norm_nonneg _)
      have hlow' : ∑ a, ‖g a‖ * (‖g a‖ - δ / (S + 1)) = N ^ 2 - S * (δ / (S + 1)) := by
        rw [hN2]; simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sq, S]
      have : S * (δ / (S + 1)) ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have h2 : N ^ 2 ≤ ‖F‖ * N := le_of_forall_pos_le_add fun δ hδ => key δ hδ
    rcases (norm_nonneg _ : (0:ℝ) ≤ N).eq_or_lt with h0 | h0
    · rw [hN, ← h0]; exact norm_nonneg _
    · nlinarith

def h50a_ins (a : Ω) : X →L[ℝ] PiLp 2 (fun _ : Ω => X) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Ω => X)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Ω => X) a)

theorem h50a_ins_apply (a : Ω) (v : X) (b : Ω) : h50a_ins a v b = (Pi.single a v : Ω → X) b := rfl

theorem h50a_decomp (φ : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) :
    φ = finiteL2Dual (fun a => φ.comp (h50a_ins a)) := by
  ext z
  rw [finiteL2Dual_apply]
  have hz : z = ∑ a, h50a_ins a (z a) := by
    ext b
    simp [h50a_ins_apply, Pi.single_apply]
  conv_lhs => rw [hz]
  rw [map_sum]
  rfl

theorem h50a_lin {m : ℕ} (c : Fin m → ℝ) (g : Fin m → Ω → (X →L[ℝ] ℝ)) :
    ∑ i, c i • finiteL2Dual (g i) = finiteL2Dual (fun a => ∑ i, c i • g i a) := by
  ext z
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, finiteL2Dual_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem solution {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) :
    FixedCotypeBound (PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) m D := by
  obtain ⟨hD0, hb⟩ := h50a_amp (Ω := Ω) hD
  refine ⟨hD0, fun x => ?_⟩
  set g : Fin m → Ω → (X →L[ℝ] ℝ) := fun i a => (x i).comp (h50a_ins a)
  have hx : ∀ i, x i = finiteL2Dual (g i) := fun i => h50a_decomp (x i)
  set y : Fin m → PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)) := fun i => toLp 2 (g i)
  have hb' := hb y
  have hn : ∀ i, ‖x i‖ = ‖y i‖ := fun i => by rw [hx i, h50a_l2norm]
  have hrad : ∀ ε, ‖rademacherSum _ x ε‖ = ‖rademacherSum _ y ε‖ := by
    intro ε
    have e1 : rademacherSum _ x ε = finiteL2Dual (fun a => ∑ i, sign (ε i) • g i a) := by
      simp only [rademacherSum]
      rw [← h50a_lin]
      exact Finset.sum_congr rfl fun i _ => by rw [hx i]
    have e2 : rademacherSum _ y ε = toLp 2 (fun a => ∑ i, sign (ε i) • g i a) := by
      ext a; simp [rademacherSum, y]
    rw [e1, e2, h50a_l2norm]
  have hc : cubeL2 _ (rademacherSum _ x) = cubeL2 _ (rademacherSum _ y) := by
    unfold cubeL2; simp only [hrad]
  simp only [hn, hc]
  exact hb'

