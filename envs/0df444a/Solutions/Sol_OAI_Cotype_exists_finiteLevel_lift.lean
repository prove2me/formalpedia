-- Prove2me | solution 1 for OAI.Cotype.exists_finiteLevel_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:24:37.597476+00:00
-- url     : https://prove2.me/submissions/da68674e-5630-41db-87a2-a17b88130e49

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FiniteLevelLift.lean:L26-L111
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_finiteLevel_lift. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_exists_L2_moment_lift

-- ---- from OAI.Analysis.Cotype.VectorWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
theorem cubeL2_add_le {n : ℕ} (f g : Cube n → X) :
    cubeL2 X (fun ε => f ε + g ε) ≤ cubeL2 X f + cubeL2 X g := by
  simp only [cubeL2_eq_piLp]
  have he : (toLp 2 (fun ε => f ε + g ε) : PiLp 2 (fun _ : Cube n => X)) =
      toLp 2 f + toLp 2 g := rfl
  rw [he, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)

theorem cubeL2_smul {n : ℕ} (a : ℝ) (f : Cube n → X) :
    cubeL2 X (fun ε => a • f ε) = |a| * cubeL2 X f := by
  simp only [cubeL2_eq_piLp]
  have he : (toLp 2 (fun ε => a • f ε) : PiLp 2 (fun _ : Cube n => X)) =
      a • toLp 2 f := rfl
  rw [he, norm_smul, Real.norm_eq_abs]
  ring

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

-- ---- from OAI.Analysis.Cotype.FiniteLevelLift ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem rademacherSum_L2_le {m : ℕ} (z : Fin m → X) :
    cubeL2 X (rademacherSum X z) ≤ Real.sqrt m * Real.sqrt (∑ i, ‖z i‖^2) := by
  apply cubeL2_bound (by positivity)
  intro ε
  calc
    _ ≤ ∑ i, ‖sign (ε i) • z i‖ := norm_sum_le _ _
    _ = ∑ i, ‖z i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : ε i <;> simp [sign]
    _ ≤ _ := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun _ : Fin m => (1 : ℝ)) (fun i => ‖z i‖)

theorem exists_finiteLevel_lift [CompleteSpace X] {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDp : 0 < D)
    (E : Submodule ℝ X) [FiniteDimensional ℝ E] :
    ∃ F : Submodule ℝ X, E ≤ F ∧ FiniteDimensional ℝ F ∧
      ∀ z : Fin m → E, ∃ H : Cube m → F,
        (∀ i, moment X (fun ε => (H ε : X)) i = (z i : X)) ∧
        cubeL2 F H ≤ 3 * D * Real.sqrt (∑ i, ‖z i‖^2) := by
  classical
  let Z := PiLp 2 (fun _ : Fin m => E)
  let η := D / (Real.sqrt m + 1)
  have hη : 0 < η := div_pos hDp (by positivity)
  obtain ⟨s, hs, hsf, hcover⟩ :=
    (isCompact_closedBall (0 : Z) 1).finite_cover_balls hη
  let : Fintype s := hsf.fintype
  have hlift (a : s) : ∃ H : Cube m → X,
      (∀ i, moment X H i = ((a.val i : E) : X)) ∧ cubeL2 X H ≤ 2 * D := by
    obtain ⟨H, hH, hn⟩ := exists_L2_moment_lift hD hDp (fun i => ((a.val i : E) : X))
    refine ⟨H, hH, hn.trans ?_⟩
    have ha : ‖a.val‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hs a.property
    have hn' : Real.sqrt (∑ i, ‖((a.val i : E) : X)‖^2) = ‖a.val‖ := by
      rw [PiLp.norm_eq_of_L2]; rfl
    rw [hn']
    exact mul_le_of_le_one_right (by positivity) ha
  choose lifts hmom hnorm using hlift
  let values : Set X := Set.range (fun p : s × Cube m => lifts p.1 p.2)
  let F := E ⊔ Submodule.span ℝ values
  have hEF : E ≤ F := le_sup_left
  have : FiniteDimensional ℝ (Submodule.span ℝ values) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hunit (z : Z) (hz : ‖z‖ ≤ 1) : ∃ H : Cube m → X,
      (∀ ε, H ε ∈ F) ∧ (∀ i, moment X H i = ((z i : E) : X)) ∧ cubeL2 X H ≤ 3 * D := by
    have hzmem : z ∈ Metric.closedBall (0 : Z) 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (hcover hzmem)
    let a' : s := ⟨a, ha⟩
    let e : Fin m → X := fun i => ((z i - a i : E) : X)
    refine ⟨fun ε => lifts a' ε + rademacherSum X e ε, ?_, ?_, ?_⟩
    · intro ε
      apply F.add_mem
      · exact (show Submodule.span ℝ values ≤ F from le_sup_right)
          (Submodule.subset_span ⟨(a', ε), rfl⟩)
      · apply hEF
        exact E.sum_mem (fun i _ => E.smul_mem _ (E.sub_mem (z i).property (a i).property))
    · intro i
      have he := moment_rademacherSum X e i
      simpa only [moment, average, smul_add, Finset.sum_add_distrib] using
        show moment X (fun ε => lifts a' ε) i + moment X (rademacherSum X e) i = ((z i : E) : X) by
          rw [hmom, he]; dsimp [e, a']; simp
    · have heN : Real.sqrt (∑ i, ‖e i‖^2) = ‖z - a‖ := by
        rw [PiLp.norm_eq_of_L2]; rfl
      have hdist : ‖z - a‖ < η := by
        change dist z a < η at hza
        rwa [show dist z a = ‖z-a‖ from dist_eq_norm z a] at hza
      have hηbound : Real.sqrt m * η ≤ D := by
        have heq : η * (Real.sqrt m + 1) = D := by dsimp [η]; field_simp
        nlinarith [Real.sqrt_nonneg (m : ℝ)]
      have hr : cubeL2 X (rademacherSum X e) ≤ D := by
        calc
          _ ≤ Real.sqrt m * ‖z-a‖ := by simpa [heN] using rademacherSum_L2_le e
          _ ≤ Real.sqrt m * η := mul_le_mul_of_nonneg_left hdist.le (Real.sqrt_nonneg _)
          _ ≤ D := hηbound
      exact (cubeL2_add_le _ _).trans (by linarith [hnorm a'])
  refine ⟨F, hEF, inferInstance, fun z => ?_⟩
  let z' : Z := toLp 2 z
  by_cases hz : z' = 0
  · have hzval (i : Fin m) : z i = 0 := congrArg (fun t : Z => t i) hz
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i; simp [moment, average, hzval]
    · simp [cubeL2, average, hzval]
  · have hzp : 0 < ‖z'‖ := norm_pos_iff.mpr hz
    obtain ⟨H, hHF, hHm, hHn⟩ := hunit (‖z'‖⁻¹ • z') (by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hzp, hzp.ne'])
    refine ⟨fun ε => ⟨‖z'‖ • H ε, F.smul_mem _ (hHF ε)⟩, ?_, ?_⟩
    · intro i
      change moment X (fun ε => ‖z'‖ • H ε) i = _
      have he : moment X (fun ε => ‖z'‖ • H ε) i = ‖z'‖ • moment X H i := by
        simp [moment, average, Finset.smul_sum, smul_smul, mul_comm, mul_assoc]
      rw [he, hHm]
      change ‖z'‖ • (‖z'‖⁻¹ • ((z i : E) : X)) = _
      rw [smul_smul, mul_inv_cancel₀ hzp.ne', one_smul]
    · have he : cubeL2 F (fun ε => (⟨‖z'‖ • H ε, F.smul_mem _ (hHF ε)⟩ : F)) =
          ‖z'‖ * cubeL2 X H := by
        change cubeL2 X (fun ε => ‖z'‖ • H ε) = _
        rw [cubeL2_smul, abs_of_nonneg (norm_nonneg _)]
      rw [he]
      have hn : ‖z'‖ = Real.sqrt (∑ i, ‖z i‖^2) := PiLp.norm_eq_of_L2 _
      nlinarith [mul_le_mul_of_nonneg_left hHn (norm_nonneg z')]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.exists_finiteLevel_lift := @_root_.OAI.Cotype.exists_finiteLevel_lift
