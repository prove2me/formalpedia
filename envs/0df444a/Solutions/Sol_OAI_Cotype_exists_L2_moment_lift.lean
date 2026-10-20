-- Prove2me | solution 1 for OAI.Cotype.exists_L2_moment_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:22:45.196247+00:00
-- url     : https://prove2.me/submissions/58af5762-dc4e-4958-a8f4-a85d51d0ccb3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/L2MomentLifts.lean:L83-L102
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_L2_moment_lift. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts
import Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
import Theorems.Thm_OAI_Cotype_finiteL2Dual_norm

-- ---- from OAI.Analysis.Cotype.QuotientLifts ----
namespace OAI

noncomputable section
namespace Cotype
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

theorem quotient_lift_norm_lt (U : A →L[ℝ] B) (hU : Function.Surjective U)
    {D : ℝ} (hD : 0 ≤ D)
    (hdual : ∀ ψ : B →L[ℝ] ℝ, ‖ψ‖ ≤ D * ‖ψ.comp U‖)
    (b : B) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, U a = b ∧ ‖a‖ < D * ‖b‖ + ε := by
  let : IsClosed (U.ker : Set A) := U.isClosed_ker
  let V : (A ⧸ U.ker) →L[ℝ] B := U.ker.liftQL U le_rfl
  have hker : V.ker = ⊥ := Submodule.ker_liftQ_eq_bot U.ker U.toLinearMap le_rfl le_rfl
  have hrange : V.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro b
    obtain ⟨a, rfl⟩ := hU b
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  let e : (A ⧸ U.ker) ≃L[ℝ] B := ContinuousLinearEquiv.ofBijective V hker hrange
  have he (a : A) : e (Submodule.Quotient.mk a) = U a := rfl
  have hq : ‖e.symm b‖ ≤ D * ‖b‖ := by
    obtain ⟨φ, hφ, heval⟩ := exists_dual_vector'' ℝ (e.symm b)
    let ψ : B →L[ℝ] ℝ := φ.comp e.symm.toContinuousLinearMap
    have hψU (a : A) : (ψ.comp U) a = φ (Submodule.Quotient.mk a) := by
      change φ (e.symm (U a)) = _
      rw [← he, e.symm_apply_apply]
    have hψUnorm : ‖ψ.comp U‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro a
      rw [hψU, one_mul]
      exact (φ.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hφ).trans
        (Submodule.Quotient.norm_mk_le U.ker a))
    have hψ : ‖ψ‖ ≤ D := (hdual ψ).trans ((mul_le_mul_of_nonneg_left hψUnorm hD).trans_eq (mul_one D))
    have hv : ψ b = ‖e.symm b‖ := by exact_mod_cast heval
    calc
      _ = ‖ψ b‖ := by rw [hv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖ψ‖ * ‖b‖ := ψ.le_opNorm b
      _ ≤ _ := mul_le_mul_of_nonneg_right hψ (norm_nonneg b)
  obtain ⟨a, ha, hanorm⟩ := Submodule.Quotient.norm_mk_lt (e.symm b) hε
  refine ⟨a, ?_, by linarith⟩
  rw [← he, ha, e.apply_symm_apply]

theorem quotient_lift_norm_le_two (U : A →L[ℝ] B) (hU : Function.Surjective U)
    {D : ℝ} (hD : 0 < D)
    (hdual : ∀ ψ : B →L[ℝ] ℝ, ‖ψ‖ ≤ D * ‖ψ.comp U‖) (b : B) :
    ∃ a : A, U a = b ∧ ‖a‖ ≤ 2 * D * ‖b‖ := by
  by_cases hb : b = 0
  · subst b
    exact ⟨0, map_zero U, by simp⟩
  obtain ⟨a, ha, hanorm⟩ := quotient_lift_norm_lt U hU hD.le hdual b
    (mul_pos hD (norm_pos_iff.mpr hb))
  exact ⟨a, ha, by linarith⟩

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.PrimalMomentLifts ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem tupleDual_eq (ψ : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) :
    ψ = finiteL2Dual (tupleDualCoordinates ψ) := by
  ext z
  have hs : (∑ i : Ω, PiLp.single 2 i (z i)) = z := by ext j; simp
  simp only [finiteL2Dual_apply, tupleDualCoordinates, ContinuousLinearMap.comp_apply, singleL2_apply]
  rw [← map_sum, hs]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.FiniteL2DualNorm ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem tupleDualCoordinates_norm (ψ : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) :
    ‖(toLp 2 (tupleDualCoordinates ψ) : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ = ‖ψ‖ := by
  rw [← finiteL2Dual_norm]
  exact congrArg norm (tupleDual_eq ψ).symm

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.L2MomentLifts ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem momentL2_surjective (m : ℕ) : Function.Surjective (momentL2 (X := X) m) := by
  intro z
  refine ⟨toLp 2 (rademacherSum X (fun i => z i)), ?_⟩
  ext i
  exact moment_rademacherSum X (fun i => z i) i

theorem momentL2_adjoint (m : ℕ) (ψ : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ) :
    ψ.comp (momentL2 m) = (Fintype.card (Cube m) : ℝ)⁻¹ •
      finiteL2Dual (rademacherSum (X →L[ℝ] ℝ) (tupleDualCoordinates ψ)) := by
  ext f
  calc
    ψ (momentL2 m f) = finiteL2Dual (tupleDualCoordinates ψ) (momentL2 m f) :=
      congrArg (fun t : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ => t (momentL2 m f)) (tupleDual_eq ψ)
    _ = _ := by
      simp only [finiteL2Dual_apply, momentL2_apply, moment, average, map_smul, map_sum,
        smul_apply, rademacherSum, sum_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

theorem momentL2_dual_bound {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D)
    (ψ : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ) :
    ‖ψ‖ ≤ (D / Real.sqrt ((Fintype.card (Cube m) : ℝ)⁻¹)) * ‖ψ.comp (momentL2 m)‖ := by
  let q := Real.sqrt ((Fintype.card (Cube m) : ℝ)⁻¹)
  have hq : 0 < q := Real.sqrt_pos.mpr (inv_pos.mpr (by exact_mod_cast (Fintype.card_pos (α := Cube m))))
  have hq2 : q^2 = (Fintype.card (Cube m) : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have h := hD.2 (tupleDualCoordinates ψ)
  have he : Real.sqrt (∑ i, ‖tupleDualCoordinates ψ i‖ ^ 2) = ‖ψ‖ := by
    rw [← tupleDualCoordinates_norm ψ, PiLp.norm_eq_of_L2]
  rw [he, cubeL2_eq_piLp] at h
  rw [momentL2_adjoint, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (Fintype.card (Cube m) : ℝ)⁻¹), finiteL2Dual_norm]
  change ‖ψ‖ ≤ D/q * ((Fintype.card (Cube m) : ℝ)⁻¹ * _)
  rw [← hq2]
  change ‖ψ‖ ≤ D * (q * _) at h
  have heq (N : ℝ) : D / q * (q^2 * N) = D * (q * N) := by field_simp
  rw [heq]
  exact h

theorem exists_L2_moment_lift [CompleteSpace X] {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDp : 0 < D)
    (x : Fin m → X) :
    ∃ H : Cube m → X, (∀ i, moment X H i = x i) ∧
      cubeL2 X H ≤ 2 * D * Real.sqrt (∑ i, ‖x i‖^2) := by
  let q := Real.sqrt ((Fintype.card (Cube m) : ℝ)⁻¹)
  have hq : 0 < q := Real.sqrt_pos.mpr (inv_pos.mpr (by exact_mod_cast (Fintype.card_pos (α := Cube m))))
  obtain ⟨P, hP, hn⟩ := quotient_lift_norm_le_two (momentL2 (X := X) m)
    (momentL2_surjective m) (div_pos hDp hq) (momentL2_dual_bound hD)
    (toLp 2 x : PiLp 2 (fun _ : Fin m => X))
  refine ⟨fun u => P u, fun i => congrArg (fun w : PiLp 2 (fun _ : Fin m => X) => w i) hP, ?_⟩
  rw [cubeL2_eq_piLp, toLp_ofLp]
  have hh := mul_le_mul_of_nonneg_left hn hq.le
  change q * ‖P‖ ≤ _
  have he : q * (2 * (D/q) * ‖(toLp 2 x : PiLp 2 (fun _ : Fin m => X))‖) =
      2*D*Real.sqrt (∑ i, ‖x i‖^2) := by
    rw [PiLp.norm_eq_of_L2]
    simp only
    field_simp
  exact hh.trans_eq he

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.exists_L2_moment_lift := @_root_.OAI.Cotype.exists_L2_moment_lift
