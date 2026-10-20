-- Prove2me | solution 1 for OAI.Cotype.exists_primal_moment_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:33:57.602326+00:00
-- url     : https://prove2.me/submissions/fbd423ea-6a96-4b62-9b91-a21224a81deb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/PrimalMomentLifts.lean:L104-L131
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_primal_moment_lift. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_finiteSupDual_norm
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

-- ---- from OAI.Analysis.Cotype.FiniteL2Dual ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω]

theorem finiteL2Dual_norm_le (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteL2Dual g‖ ≤ ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ :=
  (finiteL2Dual g).opNorm_le_bound (norm_nonneg _) (finiteL2DualLinear_bound g)

end Cotype

end

end OAI

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

theorem momentSup_surjective (m : ℕ) : Function.Surjective (momentSup (X := X) m) := by
  intro z
  refine ⟨rademacherSum X (fun i => z i), ?_⟩
  ext i
  exact moment_rademacherSum X (fun i => z i) i

theorem momentSup_adjoint (m : ℕ) (ψ : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ) :
    ψ.comp (momentSup m) = (Fintype.card (Cube m) : ℝ)⁻¹ •
      finiteSupDual (rademacherSum (X →L[ℝ] ℝ) (tupleDualCoordinates ψ)) := by
  ext f
  calc
    ψ (momentSup m f) = finiteL2Dual (tupleDualCoordinates ψ) (momentSup m f) :=
      congrArg (fun t : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ => t (momentSup m f)) (tupleDual_eq ψ)
    _ = _ := by
      simp only [finiteL2Dual_apply, momentSup_apply, moment, average, map_smul, map_sum,
        smul_apply, finiteSupDual_apply, rademacherSum, sum_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

theorem momentSup_dual_bound {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D)
    (ψ : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ) :
    ‖ψ‖ ≤ (24*D) * ‖ψ.comp (momentSup m)‖ := by
  have hψ : ‖ψ‖ ≤ ‖(toLp 2 (tupleDualCoordinates ψ) : PiLp 2 (fun _ : Fin m => (X →L[ℝ] ℝ)))‖ := by
    calc
      _ = ‖finiteL2Dual (tupleDualCoordinates ψ)‖ := congrArg norm (tupleDual_eq ψ)
      _ ≤ _ := finiteL2Dual_norm_le _
  have h := (hD.2 (tupleDualCoordinates ψ)).trans
    (mul_le_mul_of_nonneg_left (rademacher_L2_le_twentyfour_L1 (tupleDualCoordinates ψ)) hD.1)
  rw [PiLp.norm_eq_of_L2] at hψ
  have hh := hψ.trans h
  rw [momentSup_adjoint, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (Fintype.card (Cube m) : ℝ)⁻¹), finiteSupDual_norm]
  simpa only [average, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hh

theorem exists_primal_moment_lift [CompleteSpace X] {m : ℕ} (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDone : 1 ≤ D)
    (x : Fin m → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ P : Cube m → X, (∀ u, ‖P u‖ ≤ 1) ∧
      ∀ i, moment X P i = (1 / (2 * 24 * D * Real.sqrt m)) • x i := by
  have hDp : 0 < D := lt_of_lt_of_le (by norm_num) hDone
  have hmp : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  let a : ℝ := 1 / (2 * 24 * D * Real.sqrt m)
  have ha : 0 < a := by dsimp [a]; positivity
  let z : PiLp 2 (fun _ : Fin m => X) := a • toLp 2 x
  obtain ⟨P, hP, hn⟩ := quotient_lift_norm_le_two (momentSup (X := X) m)
    (momentSup_surjective m) (show 0 < 24*D by positivity) (momentSup_dual_bound hD) z
  have hxnorm : ‖(toLp 2 x : PiLp 2 (fun _ : Fin m => X))‖ ≤ Real.sqrt m := by
    rw [PiLp.norm_eq_of_L2]
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ ∑ _ : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        simpa using (sq_le_sq₀ (norm_nonneg (x i)) (by positivity)).mpr (hx i))
      _ = _ := by simp
  have hz : ‖z‖ ≤ a * Real.sqrt m := by
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hxnorm ha.le
  have hcoeff : 2 * (24*D) * (a * Real.sqrt m) = 1 := by dsimp [a]; field_simp
  have hPn : ‖P‖ ≤ 1 := hn.trans ((mul_le_mul_of_nonneg_left hz (by positivity)).trans_eq hcoeff)
  refine ⟨P, fun u => (norm_le_pi_norm P u).trans hPn, ?_⟩
  intro i
  exact congrArg (fun w : PiLp 2 (fun _ : Fin m => X) => w i) hP

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.exists_primal_moment_lift := @_root_.OAI.Cotype.exists_primal_moment_lift
