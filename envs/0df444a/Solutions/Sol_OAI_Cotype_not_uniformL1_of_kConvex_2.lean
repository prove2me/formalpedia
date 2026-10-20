-- Prove2me | solution 2 for OAI.Cotype.not_uniformL1_of_kConvex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:57:13.242375+00:00
-- url     : https://prove2.me/submissions/f1926bbc-1102-49fc-9109-930374bdbed4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/KConvexUniformL1.lean:L64-L78
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.not_uniformL1_of_kConvex. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_rademacher_L2_le_four_L1
import Theorems.Thm_OAI_Cotype_uniformL1_iff_cube

-- ---- from OAI.Analysis.Cotype.ScalarWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem scalar_rademacher_pairing {n : ℕ} (x y : Fin n → ℝ) :
    average (fun ε => rademacherSum ℝ x ε * rademacherSum ℝ y ε) =
      ∑ i, x i * y i := by
  simp only [rademacherSum, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [average_sum]
  simp_rw [average_sum]
  have he (i j : Fin n) :
      average (fun ε : Cube n => sign (ε i) * x i * (sign (ε j) * y j)) =
        (if i = j then 1 else 0) * (x i * y j) := by
    calc
      _ = average (fun ε : Cube n => (sign (ε i) * sign (ε j)) • (x i * y j)) := by
        congr 1
        funext ε
        simp only [smul_eq_mul]
        ring
      _ = _ := by rw [average_smul_const, coordinate_orthogonality, smul_eq_mul]
  simp_rw [he]
  simp

theorem scalar_rademacher_L2_sq {n : ℕ} (x : Fin n → ℝ) :
    cubeL2 ℝ (rademacherSum ℝ x) ^ 2 = ∑ i, x i ^ 2 := by
  rw [cubeL2_sq]
  simp only [Real.norm_eq_abs, sq_abs]
  simpa only [pow_two] using scalar_rademacher_pairing x x

end Cotype

end

end OAI

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

omit [NormedSpace ℝ X] in
theorem cubeL2_bound {n : ℕ} {f : Cube n → X} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ ε, ‖f ε‖ ≤ M) : cubeL2 X f ≤ M := by
  have h := cubeL2_mono (g := fun _ : Cube n => M) (by simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hf)
  simpa [cubeL2_const, Real.norm_eq_abs, abs_of_nonneg hM] using h

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.KConvexUniformL1 ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem radProjection_kernel {n : ℕ} (x : Cube n → X) (ε : Cube n) :
    radProjection X x ε = ∑ u : Cube n,
      ((Fintype.card (Cube n) : ℝ)⁻¹ * ∑ i, sign (ε i)*sign (u i)) • x u := by
  simp only [radProjection, rademacherSum, moment, average,
    Finset.smul_sum, smul_smul, Finset.sum_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

theorem scalar_sign_row_L2 {n : ℕ} (ε : Cube n) :
    cubeL2 ℝ (rademacherSum ℝ (fun i => sign (ε i))) = Real.sqrt n := by
  apply (sq_eq_sq₀ (cubeL2_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [scalar_rademacher_L2_sq, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp [pow_two, sign_sq]

theorem radProjection_l1Family_pointwise {n : ℕ} {x : Cube n → X} {c : ℝ}
    (hc : 0 ≤ c) (hx : L1Family x c) (ε : Cube n) :
    c * Real.sqrt n ≤ 4 * ‖radProjection X x ε‖ := by
  let a : Cube n → ℝ := fun u =>
    (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ i, sign (ε i)*sign (u i)
  have hsum : (∑ u, |a u|) =
      average (fun u => ‖rademacherSum ℝ (fun i => sign (ε i)) u‖) := by
    simp only [a, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card (Cube n) : ℝ)⁻¹ by positivity),
      ← Finset.mul_sum, average, smul_eq_mul, Real.norm_eq_abs, rademacherSum]
    congr 2
    funext u
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hl := hx.2 a
  rw [hsum, ← radProjection_kernel x ε] at hl
  have hk := rademacher_L2_le_four_L1 (fun i => sign (ε i))
  rw [scalar_sign_row_L2] at hk
  nlinarith [mul_le_mul_of_nonneg_left hk hc]

theorem sqrt_le_of_kBound_l1Family {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (h : ∀ (n : ℕ) (f : Cube n → X), cubeL2 X (radProjection X f) ≤ K*cubeL2 X f)
    {n : ℕ} {x : Cube n → X} (hx : L1Family x c) :
    c * Real.sqrt n ≤ 4*K := by
  have hl : c * Real.sqrt n / 4 ≤ cubeL2 X (radProjection X x) := by
    have hh := cubeL2_mono (fun ε : Cube n => show
        ‖(c * Real.sqrt n / 4 : ℝ)‖ ≤ ‖radProjection X x ε‖ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [radProjection_l1Family_pointwise hc.le hx ε])
    simpa only [cubeL2_const, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ c*Real.sqrt n/4)] using hh
  have hu := (h n x).trans (mul_le_of_le_one_right hK (cubeL2_bound (by norm_num) hx.1))
  linarith

theorem not_uniformL1_of_kConvex (h : KConvex X) : ¬ UniformL1 X := by
  obtain ⟨K,hK,h⟩ := h
  intro hu
  obtain ⟨L,hL,hx⟩ := uniformL1_iff_cube.mp hu
  obtain ⟨n,hn⟩ := exists_nat_gt ((4*K*L)^2)
  obtain ⟨x,hx⟩ := hx n
  have hb := sqrt_le_of_kBound_l1Family hK (inv_pos.mpr hL) h hx
  have he : L*(L⁻¹*Real.sqrt n) = Real.sqrt n := by field_simp
  have hb' : Real.sqrt n ≤ 4*K*L := by
    have hh := mul_le_mul_of_nonneg_left hb hL.le
    rw [he] at hh
    nlinarith
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hp : 0 ≤ 4*K*L := by positivity
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.not_uniformL1_of_kConvex := @_root_.OAI.Cotype.not_uniformL1_of_kConvex
