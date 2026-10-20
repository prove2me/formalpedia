-- Prove2me | solution 2 for OAI.Cotype.not_uniformL1_of_nontrivialType
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:58:55.216984+00:00
-- url     : https://prove2.me/submissions/ea2d972a-9b79-4c49-8079-d6d3e5ee3856

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/TypeUniformL1.lean:L11-L59
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.not_uniformL1_of_nontrivialType. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.Cotype.VectorWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
theorem cubeL2_const {n : ℕ} (x : X) : cubeL2 X (fun _ : Cube n => x) = ‖x‖ := by
  simp [cubeL2, average, smul_eq_mul, Real.sqrt_sq (norm_nonneg x)]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem cubeL2_mono {n : ℕ} {f : Cube n → X} {g : Cube n → Y}
    (h : ∀ ε, ‖f ε‖ ≤ ‖g ε‖) : cubeL2 X f ≤ cubeL2 Y g := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun ε _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h ε))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.TypeUniformL1 ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem not_uniformL1_of_nontrivialType (ht : NontrivialType X) : ¬ UniformL1 X := by
  classical
  obtain ⟨p,hp,hp2,D,hD,ht⟩ := ht
  have hp0 : 0 < p := by linarith
  let α : ℝ := 1-1/p
  have hα : 0 < α := by
    dsimp [α]
    have hi : 1/p < (1 : ℝ) := (div_lt_one hp0).mpr hp
    linarith
  rintro ⟨c,hc,hx⟩
  let R : ℝ := (D/c+1)^(1/α)
  have hb0 : 0 < D/c+1 := by positivity
  have hR : 0 < R := Real.rpow_pos_of_pos hb0 _
  obtain ⟨n,hn⟩ := exists_nat_gt (max R 1)
  have hn0 : (0 : ℝ) < n := lt_trans (by norm_num : (0 : ℝ) < 1) ((le_max_right _ _).trans_lt hn)
  have hRn : R < n := (le_max_left _ _).trans_lt hn
  have hlarge : D/c+1 < (n : ℝ)^α := by
    have hh := Real.rpow_lt_rpow hR.le hRn hα
    have he : R^α = D/c+1 := by
      dsimp [R]
      rw [← Real.rpow_mul hb0.le,div_mul_cancel₀ 1 (ne_of_gt hα),Real.rpow_one]
    rwa [he] at hh
  obtain ⟨x,hx⟩ := hx n
  have hl (ε : Cube n) : c*n ≤ ‖rademacherSum X x ε‖ := by
    have hh := hx.2 (fun i => sign (ε i))
    have hs i : |sign (ε i)| = 1 := by cases ε i <;> norm_num
    simpa only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,rademacherSum] using hh
  have hlow : c*n ≤ cubeL2 X (rademacherSum X x) := by
    have hh := cubeL2_mono (fun ε : Cube n => show ‖(c*n : ℝ)‖ ≤ ‖rademacherSum X x ε‖ by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact hl ε)
    simpa only [cubeL2_const,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ c*n)] using hh
  have hmass : (∑ i, ‖x i‖^p) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => Real.rpow_le_one (norm_nonneg _) (hx.1 i) hp0.le)
      _ = _ := by simp
  have hu : c*n ≤ D*(n : ℝ)^(1/p) := hlow.trans ((ht n x).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (x i)) _)) hmass (by positivity)) hD))
  have he : (n : ℝ)^α*(n : ℝ)^(1/p) = n := by
    rw [← Real.rpow_add hn0]
    have hαeq : α+1/p = 1 := by dsimp [α]; ring
    rw [hαeq,Real.rpow_one]
  have hsmall : c*(n : ℝ)^α ≤ D := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hn0 (1/p))).mp
    rw [mul_assoc,he]
    exact hu
  have hsmall' : (n : ℝ)^α ≤ D/c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hsmall)
  linarith

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.not_uniformL1_of_nontrivialType := @_root_.OAI.Cotype.not_uniformL1_of_nontrivialType
