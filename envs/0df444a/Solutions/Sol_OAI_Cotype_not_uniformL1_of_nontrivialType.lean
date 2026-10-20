-- Prove2me | solution 1 for OAI.Cotype.not_uniformL1_of_nontrivialType
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:20:25.221088+00:00
-- url     : https://prove2.me/submissions/80f6073b-b0bb-41c9-a010-c06f1493b7e5

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
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem h50d_avg_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  have : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [average, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  field_simp

theorem h50d_l1_lower {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : ℕ} {x : Fin n → X} {c : ℝ} (hx : L1Family x c) :
    c * n ≤ cubeL2 X (rademacherSum X x) := by
  have h1 : ∀ ε : Cube n, c * n ≤ ‖rademacherSum X x ε‖ := by
    intro ε
    have := hx.2 (fun i => sign (ε i))
    have hs : ∀ i, |sign (ε i)| = 1 := by intro i; cases ε i <;> simp [sign]
    simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at this
    exact this
  calc c * n = average (fun _ : Cube n => c * n) := (h50d_avg_const _).symm
    _ ≤ average (fun ε => ‖rademacherSum X x ε‖) := average_mono h1
    _ ≤ _ := average_norm_le_cubeL2 _

theorem solution (ht : NontrivialType X) : ¬ UniformL1 X := by
  rintro ⟨c, hc, hU⟩
  obtain ⟨p, hp1, hp2, D, hD0, hD⟩ := ht
  set q : ℝ := 1 - 1 / p with hq
  have hp0 : 0 < p := by linarith
  have hqpos : 0 < q := by
    rw [hq]; have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp1
    linarith
  have ht : Filter.Tendsto (fun n : ℕ => ((n : ℝ) ^ q)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hqpos).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := ((ht.eventually_gt_atTop (D / c)).and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨x, hx⟩ := hU n
  have hlow := h50d_l1_lower hx
  have hup := hD n x
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.2
  have hsum : ∑ i, ‖x i‖ ^ p ≤ n := by
    calc ∑ i, ‖x i‖ ^ p ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Real.rpow_le_one (norm_nonneg _) (hx.1 i) hp0.le
      _ = n := by simp
  have hup2 : (∑ i, ‖x i‖ ^ p) ^ (1 / p) ≤ (n : ℝ) ^ (1 / p) :=
    Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity) hsum (by positivity)
  have hsplit : (n : ℝ) = (n : ℝ) ^ (1 / p) * (n : ℝ) ^ q := by
    rw [← Real.rpow_add hn0, hq]; simp
  have hnp : 0 < (n : ℝ) ^ (1 / p) := Real.rpow_pos_of_pos hn0 _
  have key : c * ((n : ℝ) ^ (1 / p) * (n : ℝ) ^ q) ≤ D * (n : ℝ) ^ (1 / p) := by
    rw [← hsplit]
    exact hlow.trans (hup.trans (mul_le_mul_of_nonneg_left hup2 hD0))
  have key2 : c * (n : ℝ) ^ q ≤ D := by
    have : (c * (n : ℝ) ^ q) * (n : ℝ) ^ (1 / p) ≤ D * (n : ℝ) ^ (1 / p) := by
      calc (c * (n : ℝ) ^ q) * (n : ℝ) ^ (1 / p) = c * ((n : ℝ) ^ (1 / p) * (n : ℝ) ^ q) := by ring
        _ ≤ _ := key
    exact le_of_mul_le_mul_right this hnp
  have := hn.1
  rw [div_lt_iff₀ hc] at this
  linarith [mul_comm c ((n : ℝ) ^ q)]

