-- Prove2me | solution 1 for OAI.Cotype.exists_dual_moment_lift_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:28:19.082547+00:00
-- url     : https://prove2.me/submissions/45ad6cf3-49db-4b5d-9bae-3f97740077a8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/DualMomentLifts.lean:L68-L137
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_dual_moment_lift_of_bound. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_rademacher_L2_le_four_L1

-- ---- from OAI.Analysis.Cotype.NoiseHypercontractivity ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

theorem average_nonneg {α : Type*} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ average f := mul_nonneg (by positivity) (Finset.sum_nonneg (fun a _ => h a))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.RademacherComparison ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem rademacher_L2_le_twentyfour_L1 {n : ℕ} (x : Fin n → X) :
    cubeL2 X (rademacherSum X x) ≤ 24 * average (fun u => ‖rademacherSum X x u‖) := by
  have h := rademacher_L2_le_four_L1 x
  have hn := average_nonneg (fun u => norm_nonneg (rademacherSum X x u))
  linarith

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.DualMomentLifts ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem rademacherL1_lower {m : ℕ} {D : ℝ} (hD : FixedCotypeBound X m D)
    (z : PiLp 2 (fun _ : Fin m => X)) :
    ‖z‖ ≤ (24 * D * (Fintype.card (Cube m) : ℝ)⁻¹) * ‖rademacherL1Linear m z‖ := by
  have h := (hD.2 (fun i => z i)).trans
    (mul_le_mul_of_nonneg_left (rademacher_L2_le_twentyfour_L1 (fun i => z i)) hD.1)
  rw [← PiLp.norm_eq_of_L2] at h
  simpa only [rademacherL1Linear, LinearMap.coe_mk, AddHom.coe_mk, PiLp.norm_eq_of_L1,
    ofLp_toLp, average, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h

theorem finiteL2Dual_tuple_unit_bound {m : ℕ} (y : Fin m → (X →L[ℝ] ℝ))
    (hy : ∀ i, ‖y i‖ ≤ 1) :
    ‖(toLp 2 y : PiLp 2 (fun _ : Fin m => (X →L[ℝ] ℝ)))‖ ≤ Real.sqrt m := by
  rw [PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∑ _ : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
      simpa using (sq_le_sq₀ (norm_nonneg (y i)) (by positivity)).mpr (hy i))
    _ = _ := by simp

theorem exists_dual_moment_lift_of_bound {m : ℕ} {D c : ℝ}
    (hD : FixedCotypeBound X m D) (hc : 0 ≤ c)
    (hsize : c * Real.sqrt m * (24 * D) ≤ 1)
    (y : Fin m → (X →L[ℝ] ℝ)) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ∃ Z : Cube m → (X →L[ℝ] ℝ), (∀ u, ‖Z u‖ ≤ 1) ∧
      ∀ i, moment (X →L[ℝ] ℝ) Z i = c • y i := by
  let V := rademacherL1Linear (X := X) m
  let p := V.range
  let F : p →ₗ[ℝ] ℝ := c • (finiteL2DualLinear y).comp ((momentL1Linear m).comp p.subtype)
  let C := c * Real.sqrt m * (24 * D) * (Fintype.card (Cube m) : ℝ)⁻¹
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _))
    (mul_nonneg (by positivity) hD.1)) (by positivity)
  have hF (z : PiLp 2 (fun _ : Fin m => X)) (hz : V z ∈ p) :
      F ⟨V z, hz⟩ = c * finiteL2DualLinear y z := by
    change c • finiteL2DualLinear y (momentL1Linear m (rademacherL1Linear m z)) = _
    rw [momentL1_rademacherL1]
    rfl
  have hFbound (t : p) : ‖F t‖ ≤ C * ‖t‖ := by
    rcases t with ⟨_, z, rfl⟩
    erw [hF]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc]
    have hz := rademacherL1_lower hD z
    have hyz := (finiteL2DualLinear_bound y z).trans
      (mul_le_mul_of_nonneg_right (finiteL2Dual_tuple_unit_bound y hy) (norm_nonneg z))
    calc
      _ ≤ c * (Real.sqrt m * ‖z‖) := mul_le_mul_of_nonneg_left hyz hc
      _ ≤ c * (Real.sqrt m * ((24*D*(Fintype.card (Cube m) : ℝ)⁻¹) * ‖V z‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg _)) hc
      _ = _ := by dsimp [C]; ring
  let Fc := F.mkContinuous C hFbound
  obtain ⟨h, hext, hnorm⟩ := exists_extension_norm_eq p Fc
  have hn : ‖h‖ ≤ C := hnorm.le.trans (Fc.opNorm_le_bound hC hFbound)
  let Z : Cube m → (X →L[ℝ] ℝ) := fun u =>
    (Fintype.card (Cube m) : ℝ) • h.comp (singleL1 u)
  refine ⟨Z, ?_, ?_⟩
  · intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖(Fintype.card (Cube m) : ℝ) * h (singleL1 u x)‖ ≤ 1 * ‖x‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), one_mul]
    have hh := (h.le_opNorm (singleL1 u x)).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    simp only [singleL1_apply, PiLp.norm_single] at hh
    have hcard : (Fintype.card (Cube m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hcoeff : (Fintype.card (Cube m) : ℝ) * C ≤ 1 := by
      dsimp [C]
      convert hsize using 1
      field_simp
    exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)).trans (by
      nlinarith [mul_le_mul_of_nonneg_right hcoeff (norm_nonneg x)])
  · intro i
    ext x
    have hs : (∑ u : Cube m, sign (u i) • singleL1 u x) =
        V (PiLp.single 2 i x) := by
      ext v
      simp [singleL1_apply, PiLp.single_apply, V, rademacherL1Linear, rademacherSum, Pi.single_apply]
    have hh := hext ⟨V (PiLp.single 2 i x), ⟨PiLp.single 2 i x, rfl⟩⟩
    change h (V (PiLp.single 2 i x)) = F ⟨V (PiLp.single 2 i x), _⟩ at hh
    erw [hF] at hh
    have hcard : (Fintype.card (Cube m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    calc
      (moment (X →L[ℝ] ℝ) Z i) x = h (∑ u : Cube m, sign (u i) • singleL1 u x) := by
        simp only [moment, average, smul_apply, sum_apply, Z, ContinuousLinearMap.comp_apply,
          smul_eq_mul, map_sum, map_smul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        field_simp
      _ = c * y i x := by
        rw [hs, hh]
        simp [finiteL2DualLinear, PiLp.single_apply, apply_ite]
      _ = (c • y i) x := rfl

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.exists_dual_moment_lift_of_bound := @_root_.OAI.Cotype.exists_dual_moment_lift_of_bound
