-- Prove2me | solution 1 for OAI.Cotype.projectionLinearCoefficient_bound_of_power_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:14:12.586836+00:00
-- url     : https://prove2.me/submissions/80312b98-3c41-4ec9-90ac-3d8547bb45b5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CoefficientPowerGap.lean:L10-L39
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.projectionLinearCoefficient_bound_of_power_gap. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_complexProjectionPolynomial_spectral
import Theorems.Thm_OAI_Cotype_projectionSemigroup_hasDerivAt_zero
import Theorems.Thm_OAI_Cotype_uniform_projectionResolvent_bound_of_power_gap
import Theorems.Thm_OAI_finiteLaplaceSum_vertical_bound_of_sector_resolvent

-- ---- from OAI.Analysis.Cotype.ComplexProjectionPolynomial ----
namespace OAI

noncomputable section
namespace Cotype

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem complexProjectionProduct_differentiable {m : ℕ}
    (P : Fin m → ℂ → Z →L[ℂ] Z) (hP : ∀ i, Differentiable ℂ (P i)) :
    Differentiable ℂ (fun z => complexProjectionProduct (fun i => P i z)) := by
  induction m with
  | zero => exact differentiable_const _
  | succ m ih => exact (hP 0).mul (ih (fun i => P i.succ) (fun i => hP i.succ))

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem complexProjectionProduct_lift {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    complexProjectionProduct (fun i => complexDualLift (P i)) =
      complexDualLift (projectionProduct P) := by
  induction m with
  | zero => simp [complexProjectionProduct, projectionProduct]
  | succ m ih => simp [complexProjectionProduct, projectionProduct, ih]

theorem complexProjectionPolynomial_real {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (r : ℝ) :
    complexProjectionPolynomial P (r : ℂ) = complexDualLift (projectionSemigroup P r) := by
  unfold complexProjectionPolynomial projectionSemigroup
  rw [← complexProjectionProduct_lift]
  congr 1
  funext i
  simp only [complexDualLift_add, complexDualLift_smul, complexDualLift_sub, complexDualLift_one]
  congr 1

theorem complexProjectionPolynomial_differentiable {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    Differentiable ℂ (complexProjectionPolynomial P) := by
  apply complexProjectionProduct_differentiable
  intro i
  exact (differentiable_const _).add (differentiable_id.smul_const _)

theorem complexProjectionPolynomial_deriv_zero {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hc : ∀ i j, Commute (P i) (P j)) :
    deriv (complexProjectionPolynomial P) 0 = complexDualLift (projectionLinearCoefficient P) := by
  have hreal : HasDerivAt (fun r : ℝ => complexProjectionPolynomial P (r : ℂ))
      (complexDualLift (projectionLinearCoefficient P)) 0 := by
    have h := (complexDualLiftCLM (Y := Y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (projectionSemigroup_hasDerivAt_zero P hc)
    convert! h using 1
    funext r
    exact complexProjectionPolynomial_real P r
  have hd := (complexProjectionPolynomial_differentiable P).differentiableAt.hasDerivAt
    (x := (0 : ℂ))
  have hrestrict : HasDerivAt (fun r : ℝ => complexProjectionPolynomial P (r : ℂ))
      (deriv (complexProjectionPolynomial P) 0) 0 := by
    have hcomp := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
      (f := fun r : ℝ => (r : ℂ)) (0 : ℝ) Complex.ofRealCLM.hasDerivAt
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_zero, Complex.ofReal_one,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] using! hcomp
  exact (hreal.unique hrestrict).symm

theorem projectionLinearCoefficient_bound_of_complex_circle {R M : ℝ} (hR : 0 < R)
    {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (hc : ∀ i j, Commute (P i) (P j))
    (hcircle : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖complexProjectionPolynomial P z‖ ≤ M)
    (y : Y) : ‖projectionLinearCoefficient P y‖ ≤ (M/R)*‖y‖ := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
    (complexProjectionPolynomial_differentiable P).diffContOnCl hcircle
  rw [complexProjectionPolynomial_deriv_zero P hc, complexDualLift_norm] at h
  exact ContinuousLinearMap.le_of_opNorm_le _ h y

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.VerticalTimeCoefficient ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem complexProjectionTime_spectral {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (t : ℂ) :
    complexProjectionTime P t =
      ∑ ε : Cube m, Complex.exp (-(t * (projectionDegree ε : ℂ))) •
        complexDualLift (projectionPattern P ε) := by
  rw [complexProjectionTime, complexProjectionPolynomial_spectral]
  unfold complexSpectralEval
  apply Finset.sum_congr rfl
  intro ε _
  dsimp only
  rw [← Complex.exp_nat_mul]
  congr 2
  ring

theorem exists_vertical_time_for_circle {T : ℝ} (z : ℂ)
    (hz : ‖z‖ = Real.exp (-T)) :
    ∃ τ : ℝ, |τ| ≤ Real.pi ∧
      Complex.exp (-((T : ℂ) + (τ : ℂ)*Complex.I)) = z := by
  have hzne : z ≠ 0 := by
    intro h
    have := Real.exp_pos (-T)
    simp [h] at hz
    linarith
  refine ⟨-z.arg, by simpa using Complex.abs_arg_le_pi z, ?_⟩
  have he : (T : ℂ) + ((-z.arg : ℝ) : ℂ)*Complex.I = -Complex.log z := by
    apply Complex.ext
    · simp [Complex.log_re, hz, Real.log_exp]
    · simp [Complex.log_im]
  rw [he, neg_neg, Complex.exp_log hzne]

theorem projectionLinearCoefficient_bound_of_vertical_time
    {T B : ℝ} {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hc : ∀ i j, Commute (P i) (P j))
    (hvertical : ∀ τ : ℝ, |τ| ≤ Real.pi →
      ‖complexProjectionTime P ((T : ℂ) + (τ : ℂ)*Complex.I)‖ ≤ B)
    (y : Y) :
    ‖projectionLinearCoefficient P y‖ ≤ (B / Real.exp (-T))*‖y‖ := by
  apply projectionLinearCoefficient_bound_of_complex_circle (Real.exp_pos (-T)) P hc
  intro z hz
  have hn : ‖z‖ = Real.exp (-T) := by simpa [Metric.mem_sphere, dist_zero_right] using hz
  obtain ⟨τ, hτ, he⟩ := exists_vertical_time_for_circle z hn
  have hb := hvertical τ hτ
  simpa only [complexProjectionTime, he] using hb

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CoefficientPowerGap ----
namespace OAI

noncomputable section
namespace Cotype

theorem projectionLinearCoefficient_bound_of_power_gap
    {N : ℕ} (hN : 0 < N) {C : ℝ} (hC : 0 ≤ C)
    (hC2 : C < (2 : ℝ)^N) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [CompleteSpace Y] (m : ℕ) (P : Fin m → Y →L[ℝ] Y),
        (∀ i, P i * P i = P i) →
        (∀ i j, Commute (P i) (P j)) →
        (∀ i y, ‖P i y‖ ≤ ‖y‖) →
        (∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
          ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖) →
        ∀ y : Y, ‖projectionLinearCoefficient P y‖ ≤ K*‖y‖ := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨a, M, ha, hM, hres⟩ := uniform_projectionResolvent_bound_of_power_gap hC hC2
  obtain ⟨T, B, _hT, hB, hcontour⟩ :=
    finiteLaplaceSum_vertical_bound_of_sector_resolvent ha hM
  refine ⟨B / Real.exp (-T), div_nonneg hB (Real.exp_pos _).le, ?_⟩
  intro Y _ _ _ m P hp hc hP hgap y
  apply projectionLinearCoefficient_bound_of_vertical_time P hc
  intro τ hτ
  rw [complexProjectionTime_spectral]
  have hb := hcontour (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) (Cube m)
    (fun ε => (projectionDegree ε : ℝ))
    (fun ε => complexDualLift (projectionPattern P ε))
    (fun ε => Nat.cast_nonneg (projectionDegree ε))
    (by
      intro z hz hcone
      simpa only [projectionResolvent, complexSpectralEval, Complex.ofReal_natCast] using
        hres Y m P hp hc hP hgap z hz hcone) τ hτ
  simpa only [Complex.ofReal_natCast] using hb

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.projectionLinearCoefficient_bound_of_power_gap := @_root_.OAI.Cotype.projectionLinearCoefficient_bound_of_power_gap
