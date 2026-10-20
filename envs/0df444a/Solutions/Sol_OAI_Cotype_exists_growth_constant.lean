-- Prove2me | solution 1 for OAI.Cotype.exists_growth_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:22:02.531879+00:00
-- url     : https://prove2.me/submissions/cd8a2672-20ff-4ac2-9ab8-e56a51fecc41

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/GrowthTheorem.lean:L10-L47
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_growth_constant. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_FiniteLevelTower
import Definitions.Def_OAI_Analysis_Cotype_WeightedCompact
import Definitions.Def_OAI_Analysis_Cotype_CompactQuotient
import Definitions.Def_OAI_Analysis_Cotype_GrowthTuplePairing
import Definitions.Def_OAI_Analysis_Cotype_PatternPairing
import Definitions.Def_OAI_Analysis_Cotype_TaggedFrames
import Definitions.Def_OAI_Analysis_Cotype_CoefficientTarget
import Definitions.Def_OAI_Analysis_Cotype_DampedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_GroupedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ProjectionCoefficients
import Definitions.Def_OAI_Analysis_Cotype_PatternNormalization
import Definitions.Def_OAI_Analysis_Cotype_PatternProjections
import Definitions.Def_OAI_Analysis_Cotype_DeletedTail
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevBounds
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevTruncation
import Definitions.Def_OAI_Analysis_Cotype_BivariateSplit
import Definitions.Def_OAI_Analysis_Cotype_ProjectionDerivatives
import Definitions.Def_OAI_Analysis_Cotype_MixedDerivative
import Definitions.Def_OAI_Analysis_Cotype_CoefficientCompactness
import Definitions.Def_OAI_Analysis_Cotype_GrowthScalarData
import Definitions.Def_OAI_Analysis_Cotype_TaggedCoefficient
import Definitions.Def_OAI_Analysis_Cotype_RankWalsh
import Theorems.Thm_OAI_Cotype_GrowthPairingData_exists_fixed_lift_coefficient
import Theorems.Thm_OAI_Cotype_GrowthPairingData_normalized_scalar_admissible
import Theorems.Thm_OAI_Cotype_GrowthPairingData_tagged_coefficient_extraction
import Theorems.Thm_OAI_Cotype_average_norm_mul_le
import Theorems.Thm_OAI_Cotype_coefficientTarget_proved
import Theorems.Thm_OAI_Cotype_exists_dual_moment_lift_of_bound
import Theorems.Thm_OAI_Cotype_exists_exact_amplified_pairing
import Theorems.Thm_OAI_Cotype_exists_primal_moment_lift
import Theorems.Thm_OAI_Cotype_finiteL2Dual_norm
import Theorems.Thm_OAI_Cotype_finiteProbabilityVector_norm
import Theorems.Thm_OAI_Cotype_fixedCotypeBound_dual_l2Amplification
import Theorems.Thm_OAI_Cotype_fixedCotypeBound_l2Amplification
import Theorems.Thm_OAI_Cotype_orbitAverage_moment

-- ---- from OAI.Analysis.Cotype.VectorWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

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

theorem cubeL2_clm {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (fun ε => T (f ε)) ≤ ‖T‖ * cubeL2 X f := by
  have hh := cubeL2_mono (g := fun ε => ‖T‖ • f ε) (fun ε => by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)] using T.le_opNorm (f ε))
  simpa [cubeL2_smul, abs_of_nonneg (norm_nonneg T)] using hh

theorem vectorWalsh_L2_le {n : ℕ} (f : Cube n → X) :
    cubeL2 X (vectorWalsh f) ≤ cubeL2 X f :=
  cubeL2_bound (cubeL2_nonneg f) (vectorWalsh_bound f)

theorem operatorWalsh_L2_le {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤ ‖T‖ * cubeL2 X f :=
  (vectorWalsh_L2_le _).trans (cubeL2_clm T f)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshNorm ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem walshOutputs_zero (n : ℕ) (T : X →L[ℝ] Y) : 0 ∈ walshOutputs n T := by
  refine ⟨fun _ => 0, ?_, ?_⟩ <;> simp [operatorWalsh, vectorWalsh, average, cubeL2]

theorem walshOutputs_bddAbove (n : ℕ) (T : X →L[ℝ] Y) : BddAbove (walshOutputs n T) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact (operatorWalsh_L2_le T f).trans ((mul_le_mul_of_nonneg_left hf (norm_nonneg T)).trans_eq (mul_one _))

theorem walshNorm_nonneg (n : ℕ) (T : X →L[ℝ] Y) : 0 ≤ walshNorm n T :=
  le_csSup (walshOutputs_bddAbove n T) (walshOutputs_zero n T)

theorem le_walshNorm {n : ℕ} (T : X →L[ℝ] Y) {f : Cube n → X} (hf : cubeL2 X f ≤ 1) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T :=
  le_csSup (walshOutputs_bddAbove n T) ⟨f, hf, rfl⟩

theorem vectorWalsh_smul {n : ℕ} (a : ℝ) (f : Cube n → X) :
    vectorWalsh (fun u => a • f u) = fun v => a • vectorWalsh f v := by
  funext v
  simp only [vectorWalsh, average, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  ring

theorem operatorWalsh_smul {n : ℕ} (T : X →L[ℝ] Y) (a : ℝ) (f : Cube n → X) :
    operatorWalsh T (fun u => a • f u) = fun v => a • operatorWalsh T f v := by
  simp only [operatorWalsh, map_smul]
  exact vectorWalsh_smul a _

theorem operatorWalsh_le_walshNorm {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T * cubeL2 X f := by
  by_cases hz : cubeL2 X f = 0
  · simpa [hz] using operatorWalsh_L2_le T f
  · have hp : 0 < cubeL2 X f := lt_of_le_of_ne (cubeL2_nonneg f) (Ne.symm hz)
    have hin : cubeL2 X (fun u => (cubeL2 X f)⁻¹ • f u) ≤ 1 := by
      rw [cubeL2_smul, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hz]
    have hh := le_walshNorm T hin
    rw [operatorWalsh_smul, cubeL2_smul, abs_of_pos (inv_pos.mpr hp)] at hh
    calc
      _ = ((cubeL2 X f)⁻¹ * cubeL2 Y (operatorWalsh T f)) * cubeL2 X f := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hh hp.le

theorem walshNorm_le_of_bound {n : ℕ} (T : X →L[ℝ] Y) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ f : Cube n → X, cubeL2 Y (operatorWalsh T f) ≤ D * cubeL2 X f) :
    walshNorm n T ≤ D := by
  apply csSup_le ⟨0, walshOutputs_zero n T⟩
  rintro r ⟨f, hf, rfl⟩
  exact (h f).trans ((mul_le_mul_of_nonneg_left hf hD).trans_eq (mul_one D))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshCoordinates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem character_join {n j : ℕ} (a c : Cube n) (b d : Cube j) :
    character (cubeJoin n j (a,b)) (cubeJoin n j (c,d)) =
      character a c * character b d := by
  simp [character, Fin.prod_univ_add]

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → X) : average (fun a => f (e a)) = average f := by
  simp only [average, Fintype.card_congr e, Equiv.sum_comp]

theorem average_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → X) : average f = average (fun a => average (fun b => f (a,b))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, Finset.smul_sum, smul_smul]
  simp [mul_comm]

theorem average_join {n j : ℕ} (f : Cube (n+j) → X) :
    average f = average (fun a => average (fun b => f (cubeJoin n j (a,b)))) := by
  rw [← average_equiv (cubeJoin n j) f, average_prod]

theorem average_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → X) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  simp only [average, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

omit [NormedSpace ℝ X] in
theorem cubeL2_join {n j : ℕ} (f : Cube (n+j) → X) :
    cubeL2 X f = cubeL2 ℝ (fun a : Cube n => cubeL2 X
      (fun b : Cube j => f (cubeJoin n j (a,b)))) := by
  simp only [cubeL2, Real.norm_eq_abs, sq_abs]
  simp_rw [Real.sq_sqrt (show 0 ≤ average (fun b : Cube j =>
    ‖f (cubeJoin n j (_,b))‖ ^ 2) from by
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  rw [average_join]

omit [NormedSpace ℝ X] in
theorem cubeL2_comm {n j : ℕ} (f : Cube n → Cube j → X) :
    cubeL2 ℝ (fun a => cubeL2 X (f a)) =
      cubeL2 ℝ (fun b => cubeL2 X (fun a => f a b)) := by
  simp only [cubeL2, Real.norm_eq_abs, sq_abs]
  simp_rw [Real.sq_sqrt (show 0 ≤ average (fun b => ‖f _ b‖ ^ 2) from by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  simp_rw [Real.sq_sqrt (show 0 ≤ average (fun a => ‖f a _‖ ^ 2) from by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  rw [average_comm]

theorem vectorWalsh_join {n j : ℕ} (f : Cube (n+j) → X) (a : Cube n) (b : Cube j) :
    vectorWalsh f (cubeJoin n j (a,b)) =
      vectorWalsh (fun d : Cube j => vectorWalsh
        (fun c : Cube n => f (cubeJoin n j (c,d))) a) b := by
  unfold vectorWalsh
  rw [average_join, average_comm]
  simp only [character_join, average, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  ring

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshDuality ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem dualPairing_bound {n : ℕ} (f : Cube n → X) (g : Cube n → (X →L[ℝ] ℝ)) :
    |dualPairing f g| ≤ cubeL2 X f * cubeL2 (X →L[ℝ] ℝ) g := by
  calc
    _ ≤ average (fun u => |g u (f u)|) := by
      simpa only [dualPairing, Real.norm_eq_abs] using norm_average_le (fun u => g u (f u))
    _ ≤ average (fun u => ‖f u‖ * ‖g u‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun u _ => by
        simpa only [Real.norm_eq_abs, mul_comm] using (g u).le_opNorm (f u))
    _ ≤ _ := average_norm_mul_le f g

theorem walshBilinear_eq_pairing {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X)
    (g : Cube n → (Y →L[ℝ] ℝ)) :
    walshBilinear T f g = dualPairing (operatorWalsh T f) g := by
  rw [walshBilinear, average_comm]
  simp [dualPairing, operatorWalsh, vectorWalsh, average]

theorem walshBilinear_bound {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X)
    (g : Cube n → (Y →L[ℝ] ℝ)) :
    |walshBilinear T f g| ≤ walshNorm n T * cubeL2 X f * cubeL2 (Y →L[ℝ] ℝ) g := by
  rw [walshBilinear_eq_pairing]
  exact (dualPairing_bound _ _).trans
    (mul_le_mul_of_nonneg_right (operatorWalsh_le_walshNorm T f) (cubeL2_nonneg g))

theorem walshBilinear_unit_bound {n : ℕ} (T : X →L[ℝ] Y)
    {f : Cube n → X} {g : Cube n → (Y →L[ℝ] ℝ)}
    (hf : cubeL2 X f ≤ 1) (hg : cubeL2 (Y →L[ℝ] ℝ) g ≤ 1) :
    |walshBilinear T f g| ≤ walshNorm n T := by
  have h := walshBilinear_bound T f g
  have hfg : cubeL2 X f * cubeL2 (Y →L[ℝ] ℝ) g ≤ 1 :=
    (mul_le_mul hf hg (cubeL2_nonneg g) (by positivity)).trans_eq (one_mul 1)
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hfg (walshNorm_nonneg n T)])

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshMonotonicity ----
namespace OAI

noncomputable section
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem operatorWalsh_join {n j : ℕ} (T : X →L[ℝ] Y)
    (f : Cube (n+j) → X) (a : Cube n) (b : Cube j) :
    operatorWalsh T f (cubeJoin n j (a,b)) =
      vectorWalsh (fun d : Cube j => operatorWalsh T
        (fun c : Cube n => f (cubeJoin n j (c,d))) a) b :=
  vectorWalsh_join _ a b

theorem operatorWalsh_add_le {n j : ℕ} (T : X →L[ℝ] Y) (f : Cube (n+j) → X) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T * cubeL2 X f := by
  rw [cubeL2_join]
  simp_rw [operatorWalsh_join]
  calc
    _ ≤ cubeL2 ℝ (fun a : Cube n => cubeL2 Y (fun d : Cube j =>
        operatorWalsh T (fun c : Cube n => f (cubeJoin n j (c,d))) a)) := by
      apply cubeL2_mono
      intro a
      simpa only [Real.norm_eq_abs, abs_of_nonneg (cubeL2_nonneg _)] using
        vectorWalsh_L2_le (fun d : Cube j => operatorWalsh T
          (fun c : Cube n => f (cubeJoin n j (c,d))) a)
    _ = cubeL2 ℝ (fun d : Cube j => cubeL2 Y
        (operatorWalsh T (fun c : Cube n => f (cubeJoin n j (c,d))))) :=
      cubeL2_comm _
    _ ≤ cubeL2 ℝ (fun d : Cube j => walshNorm n T * cubeL2 X
        (fun c : Cube n => f (cubeJoin n j (c,d)))) := by
      apply cubeL2_mono
      intro d
      simpa only [Real.norm_eq_abs, abs_of_nonneg (cubeL2_nonneg _),
        abs_of_nonneg (mul_nonneg (walshNorm_nonneg n T) (cubeL2_nonneg _))] using
        operatorWalsh_le_walshNorm T (fun c : Cube n => f (cubeJoin n j (c,d)))
    _ = _ := by
      rw [show (fun d : Cube j => walshNorm n T * cubeL2 X
        (fun c : Cube n => f (cubeJoin n j (c,d)))) =
        (fun d : Cube j => walshNorm n T • cubeL2 X
        (fun c : Cube n => f (cubeJoin n j (c,d)))) from rfl]
      rw [cubeL2_smul, abs_of_nonneg (walshNorm_nonneg n T), cubeL2_comm]
      rw [← cubeL2_join]

theorem walshNorm_add_le (n j : ℕ) (T : X →L[ℝ] Y) :
    walshNorm (n+j) T ≤ walshNorm n T :=
  walshNorm_le_of_bound T (walshNorm_nonneg n T) (operatorWalsh_add_le T)

theorem walshNorm_antitone (T : X →L[ℝ] Y) : Antitone (fun n => walshNorm n T) := by
  intro n k h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  exact walshNorm_add_le n j T

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshAmplification ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [NormedSpace ℝ X] [DecidableEq Ω] in
theorem cubeL2_piLp_sq {n : ℕ} (f : Cube n → PiLp 2 (fun _ : Ω => X)) :
    cubeL2 (PiLp 2 (fun _ : Ω => X)) f ^ 2 =
      ∑ a : Ω, cubeL2 X (fun u => f u a) ^ 2 := by
  simp_rw [cubeL2_sq, PiLp.norm_sq_eq_of_L2]
  simp only [average, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq Ω] in
theorem operatorWalsh_amplification_bound {n : ℕ} (T : X →L[ℝ] Y)
    (f : Cube n → PiLp 2 (fun _ : Ω => X)) :
    cubeL2 (PiLp 2 (fun _ : Ω => Y)) (operatorWalsh (l2Amplification T) f) ≤
      walshNorm n T * cubeL2 (PiLp 2 (fun _ : Ω => X)) f := by
  apply (sq_le_sq₀ (cubeL2_nonneg _)
    (mul_nonneg (walshNorm_nonneg n T) (cubeL2_nonneg _))).mp
  rw [mul_pow, cubeL2_piLp_sq, cubeL2_piLp_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simp only [operatorWalsh_amplification_apply]
  simpa only [mul_pow] using (sq_le_sq₀ (cubeL2_nonneg _)
    (mul_nonneg (walshNorm_nonneg n T) (cubeL2_nonneg _))).mpr
      (operatorWalsh_le_walshNorm T (fun u => f u a))

omit [DecidableEq Ω] in
theorem walshNorm_amplification_le (n : ℕ) (T : X →L[ℝ] Y) :
    walshNorm n (l2Amplification (Ω := Ω) T) ≤ walshNorm n T :=
  walshNorm_le_of_bound _ (walshNorm_nonneg n T) (operatorWalsh_amplification_bound T)

omit [NormedSpace ℝ X] in
theorem cubeL2_piLp_single {n : ℕ} (a : Ω) (f : Cube n → X) :
    cubeL2 (PiLp 2 (fun _ : Ω => X)) (fun u => PiLp.single 2 a (f u)) = cubeL2 X f := by
  simp [cubeL2, PiLp.norm_single]

theorem operatorWalsh_amplification_single {n : ℕ} (T : X →L[ℝ] Y)
    (a : Ω) (f : Cube n → X) :
    operatorWalsh (l2Amplification T) (fun u => PiLp.single 2 a (f u)) =
      fun v => PiLp.single 2 a (operatorWalsh T f v) := by
  classical
  funext v
  ext b
  simp only [operatorWalsh_amplification_apply, PiLp.single, ofLp_toLp]
  by_cases h : b = a
  · subst b
    simp
  · simp [h, operatorWalsh, vectorWalsh, average]

theorem walshNorm_amplification [Nonempty Ω] (n : ℕ) (T : X →L[ℝ] Y) :
    walshNorm n (l2Amplification (Ω := Ω) T) = walshNorm n T := by
  apply (walshNorm_amplification_le n T).antisymm
  apply walshNorm_le_of_bound T (walshNorm_nonneg n _)
  intro f
  obtain ⟨a⟩ := ‹Nonempty Ω›
  have h := operatorWalsh_le_walshNorm (l2Amplification T)
    (fun u => PiLp.single 2 a (f u))
  simpa only [operatorWalsh_amplification_single, cubeL2_piLp_single] using h

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

theorem exists_dual_moment_lift {m : ℕ} (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound X m D) (hDone : 1 ≤ D)
    (y : Fin m → (X →L[ℝ] ℝ)) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ∃ Z : Cube m → (X →L[ℝ] ℝ), (∀ u, ‖Z u‖ ≤ 1) ∧
      ∀ i, moment (X →L[ℝ] ℝ) Z i = (1 / (2 * 24 * D * Real.sqrt m)) • y i := by
  have hDp : 0 < D := lt_of_lt_of_le (by norm_num) hDone
  have hmp : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  apply exists_dual_moment_lift_of_bound hD (by positivity) _ y hy
  have he : (1 / (2 * 24 * D * Real.sqrt m)) * Real.sqrt m * (24 * D) = (1/2 : ℝ) := by
    field_simp
  rw [he]
  norm_num

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshSymmetry ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

theorem symmetry_pairing {n : ℕ} (g : WalshSymmetry n) (u v : Cube n) :
    character (dualSymmetry g v) (primalSymmetry g u) = character v u := g.property u v

variable {Γ Ω X : Type*} [Fintype Ω] [NormedAddCommGroup X] [NormedSpace ℝ X]
open WithLp

variable [Group Γ] [Fintype Γ]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.EquivariantLifts ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Γ I X : Type*} [Group Γ] [Fintype Γ] [MulAction Γ I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [Fintype Γ] in
theorem isometryAction_mul (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (g h : Γ) (z : X) :
    ρ (g*h) z = ρ g (ρ h z) := by rw [map_mul]; rfl

theorem orbitAverage_equivariant (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (f : I → X)
    (h : Γ) (a : I) : orbitAverage ρ f (h • a) = ρ h (orbitAverage ρ f a) := by
  unfold orbitAverage
  rw [← average_equiv (Equiv.mulLeft h)]
  change average (fun g : Γ => ρ (h*g) (f ((h*g)⁻¹ • (h • a)))) = _
  simp only [mul_inv_rev, mul_smul, inv_smul_smul, isometryAction_mul]
  simp [average, map_smul, map_sum]

theorem orbitAverage_norm_le_one (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (f : I → X)
    (hf : ∀ a, ‖f a‖ ≤ 1) (a : I) : ‖orbitAverage ρ f a‖ ≤ 1 := by
  have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ average (fun g : Γ => ‖ρ g (f (g⁻¹ • a))‖) := norm_average_le _
    _ ≤ average (fun _ : Γ => (1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun g _ => by simpa using hf (g⁻¹ • a))
    _ = 1 := by simp [average, smul_eq_mul, hc]

theorem exists_equivariant_primal_lifts [CompleteSpace X] {m : ℕ} (hm : 0 < m)
    {D : ℝ} (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDone : 1 ≤ D)
    (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (x : I → Fin m → X)
    (hx : ∀ a i, ‖x a i‖ ≤ 1) (he : ∀ h a i, x (h • a) i = ρ h (x a i)) :
    ∃ P : I → Cube m → X, (∀ a ε, ‖P a ε‖ ≤ 1) ∧
      (∀ a i, moment X (P a) i = (1 / (2*24*D*Real.sqrt m)) • x a i) ∧
      ∀ h a ε, P (h • a) ε = ρ h (P a ε) := by
  choose P hn hp using (fun a => exists_primal_moment_lift hm hD hDone (x a) (hx a))
  exact ⟨fun a ε => orbitAverage ρ (fun b => P b ε) a,
    fun a ε => orbitAverage_norm_le_one ρ _ (fun b => hn b ε) a,
    orbitAverage_moment ρ x he _ P hp,
    fun h a ε => orbitAverage_equivariant ρ _ h a⟩

theorem exists_equivariant_dual_lifts {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : FixedCotypeBound Y m D) (hDone : 1 ≤ D)
    (ρ : Γ →* ((Y →L[ℝ] ℝ) ≃ₗᵢ[ℝ] (Y →L[ℝ] ℝ)))
    (y : I → Fin m → (Y →L[ℝ] ℝ)) (hy : ∀ a i, ‖y a i‖ ≤ 1)
    (he : ∀ h a i, y (h • a) i = ρ h (y a i)) :
    ∃ Z : I → Cube m → (Y →L[ℝ] ℝ), (∀ a ε, ‖Z a ε‖ ≤ 1) ∧
      (∀ a i, moment (Y →L[ℝ] ℝ) (Z a) i = (1 / (2*24*D*Real.sqrt m)) • y a i) ∧
      ∀ h a ε, Z (h • a) ε = ρ h (Z a ε) := by
  choose Z hn hp using (fun a => exists_dual_moment_lift hm hD hDone (y a) (hy a))
  exact ⟨fun a ε => orbitAverage ρ (fun b => Z b ε) a,
    fun a ε => orbitAverage_norm_le_one ρ _ (fun b => hn b ε) a,
    orbitAverage_moment ρ y he _ Z hp,
    fun h a ε => orbitAverage_equivariant ρ _ h a⟩

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.EquivariantPairing ----
namespace OAI

noncomputable section

open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem finiteProbabilityDual_norm (f : Ω → (Y →L[ℝ] ℝ)) (hf : ∀ a, ‖f a‖ ≤ 1) :
    ‖finiteProbabilityDual f‖ ≤ 1 := by
  classical
  have he : ‖finiteProbabilityDual f‖ = ‖finiteProbabilityVector f‖ := by
    simp only [finiteProbabilityDual, finiteProbabilityVector, norm_smul, finiteL2Dual_norm]
  rw [he]
  exact finiteProbabilityVector_norm f hf

variable {n : ℕ}
theorem symmetryDual_equivariant (y : Cube n → (Y →L[ℝ] ℝ)) (g : WalshSymmetry n) (v : Cube n) :
    dualAction (rightTranslation (X := Y)) g (symmetryDual y v) = symmetryDual y (dualSymmetry g v) := by
  ext z
  change Real.sqrt ((Fintype.card (WalshSymmetry n) : ℝ)⁻¹) *
    (∑ R : WalshSymmetry n, y (dualSymmetry R v) (z (R*g⁻¹))) =
      Real.sqrt ((Fintype.card (WalshSymmetry n) : ℝ)⁻¹) *
        ∑ R : WalshSymmetry n, y (dualSymmetry R (dualSymmetry g v)) (z R)
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight g)]
  apply Finset.sum_congr rfl
  intro R _
  change y (dualSymmetry (R*g) v) (z ((R*g)*g⁻¹)) = _
  simp only [mul_inv_cancel_right]
  rfl

theorem symmetry_exact_pairing (T : X →L[ℝ] Y) (x : Cube n → X)
    (y : Cube n → (Y →L[ℝ] ℝ)) (γ : ℝ)
    (hxy : ∀ u v, y v (T (x u)) = γ * character v u) (u v : Cube n) :
    symmetryDual y v (l2Amplification T (symmetryVector x u)) = γ * character v u := by
  let q := Real.sqrt ((Fintype.card (WalshSymmetry n) : ℝ)⁻¹)
  have hc : (Fintype.card (WalshSymmetry n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hq : q^2 = (Fintype.card (WalshSymmetry n) : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  change q * (∑ R : WalshSymmetry n, y (dualSymmetry R v) (T (q • x (primalSymmetry R u)))) = _
  simp only [map_smul, smul_eq_mul, hxy, symmetry_pairing, Finset.sum_const, nsmul_eq_mul]
  calc
    q * ((Fintype.card (WalshSymmetry n) : ℝ) * (q * (γ * character v u))) =
      (q^2 * (Fintype.card (WalshSymmetry n) : ℝ)) * (γ * character v u) := by ring
    _ = _ := by rw [hq, inv_mul_cancel₀ hc, one_mul]

theorem exists_equivariant_exact_pairing (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) :
    ∃ (γ : ℝ)
      (x : Cube n → SymmetryL2 n (PiLp 2 (fun _ : Cube (n+n) => X)))
      (y : Cube n → (SymmetryL2 n (PiLp 2 (fun _ : Cube (n+n) => Y)) →L[ℝ] ℝ)),
      walshNorm n T / 2 < γ ∧ 0 < γ ∧
      (∀ u, ‖x u‖ ≤ 1) ∧ (∀ v, ‖y v‖ ≤ 1) ∧
      (∀ u v, y v (l2Amplification (l2Amplification T) (x u)) = γ * character v u) ∧
      (∀ g u, rightTranslation g (x u) = x (primalSymmetry g u)) ∧
      (∀ g v, dualAction (rightTranslation (X := PiLp 2 (fun _ : Cube (n+n) => Y))) g (y v) = y (dualSymmetry g v)) ∧
      (∀ k, walshNorm k (l2Amplification (Ω := WalshSymmetry n)
        (l2Amplification (Ω := Cube (n+n)) T)) = walshNorm k T) := by
  obtain ⟨γ,x,y,hγ,hγp,hx,hy,hxy,hW⟩ := exists_exact_amplified_pairing n hT
  exact ⟨γ, symmetryVector x, symmetryDual y, hγ, hγp,
    fun u => finiteProbabilityVector_norm _ (fun R => hx _),
    fun v => finiteProbabilityDual_norm _ (fun R => hy _),
    symmetry_exact_pairing _ x y γ hxy,
    symmetryVector_equivariant x, symmetryDual_equivariant y,
    fun k => (walshNorm_amplification k _).trans (hW k)⟩

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.FrameLifts ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {n m : ℕ}

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_primal_tuple_lifts [CompleteSpace X] (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound (SymmetryL2 n X →L[ℝ] ℝ) m D) (hDone : 1 ≤ D)
    (x : Cube n → SymmetryL2 n X) (hx : ∀ u, ‖x u‖ ≤ 1)
    (he : ∀ g u, rightTranslation g (x u) = x (primalSymmetry g u)) :
    ∃ P : (Fin m → Cube n) → Cube m → SymmetryL2 n X,
      (∀ U ε, ‖P U ε‖ ≤ 1) ∧
      (∀ U i, moment (SymmetryL2 n X) (P U) i = (1/(2*24*D*Real.sqrt m)) • x (U i)) ∧
      ∀ g U ε, P (fun i => primalSymmetry g (U i)) ε = rightTranslation g (P U ε) := by
  let := primalTupleAction (n := n) (m := m)
  exact exists_equivariant_primal_lifts (Γ := WalshSymmetry n) (I := Fin m → Cube n)
    (X := SymmetryL2 n X) hm hD hDone rightTranslation
    (fun U i => x (U i)) (fun U i => hx (U i)) (fun g U i => (he g (U i)).symm)

theorem exists_dual_tuple_lifts (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound (SymmetryL2 n Y) m D) (hDone : 1 ≤ D)
    (y : Cube n → (SymmetryL2 n Y →L[ℝ] ℝ)) (hy : ∀ v, ‖y v‖ ≤ 1)
    (he : ∀ g v, dualAction (rightTranslation (X := Y)) g (y v) = y (dualSymmetry g v)) :
    ∃ Z : (Fin m → Cube n) → Cube m → (SymmetryL2 n Y →L[ℝ] ℝ),
      (∀ V δ, ‖Z V δ‖ ≤ 1) ∧
      (∀ V i, moment (SymmetryL2 n Y →L[ℝ] ℝ) (Z V) i = (1/(2*24*D*Real.sqrt m)) • y (V i)) ∧
      ∀ g V δ, Z (fun i => dualSymmetry g (V i)) δ =
        dualAction (rightTranslation (X := Y)) g (Z V δ) := by
  let := dualTupleAction (n := n) (m := m)
  exact exists_equivariant_dual_lifts (Γ := WalshSymmetry n) (I := Fin m → Cube n)
    (Y := SymmetryL2 n Y) hm hD hDone (dualAction rightTranslation)
    (fun V i => y (V i)) (fun V i => hy (V i)) (fun g V i => (he g (V i)).symm)

theorem exists_growthPairingData [CompleteSpace X] (n : ℕ) (hm : 0 < m)
    {Dg Df : ℝ} (hDg : FixedCotypeBound (X →L[ℝ] ℝ) m Dg)
    (hDf : FixedCotypeBound Y m Df) (hDg1 : 1 ≤ Dg) (hDf1 : 1 ≤ Df)
    {T : X →L[ℝ] Y} (hT : T ≠ 0) : Nonempty (GrowthPairingData T n m Dg Df) := by
  obtain ⟨γ,x,y,hγ,hγp,hx,hy,hxy,hxe,hye,hW⟩ := exists_equivariant_exact_pairing n hT
  have hG := fixedCotypeBound_dual_l2Amplification (Ω := WalshSymmetry n)
    (fixedCotypeBound_dual_l2Amplification (Ω := Cube (n+n)) hDg)
  have hF := fixedCotypeBound_l2Amplification (Ω := WalshSymmetry n)
    (fixedCotypeBound_l2Amplification (Ω := Cube (n+n)) hDf)
  obtain ⟨P,hPn,hPm,hPe⟩ := exists_primal_tuple_lifts hm hG hDg1 x hx hxe
  obtain ⟨Z,hZn,hZm,hZe⟩ := exists_dual_tuple_lifts hm hF hDf1 y hy hye
  exact ⟨⟨γ,hγ,hγp,x,y,P,Z,hx,hy,hPn,hZn,hxy,hPm,hZm,hxe,hye,hPe,hZe,hW⟩⟩

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.OddPatternBounds ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem walsh_amplitude_bound {k : ℕ} (T : X →L[ℝ] Y)
    (f : Cube k → X) (g : Cube k → (Y →L[ℝ] ℝ)) (a : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ 1) (hg : ∀ v, ‖g v‖ ≤ 1)
    (ha : ∀ u v, g v (T (f u)) = character v u * a) : |a| ≤ walshNorm k T := by
  have h := walshBilinear_unit_bound T (cubeL2_bound (by positivity) hf)
    (cubeL2_bound (by positivity) hg)
  have he : walshBilinear T f g = a := by
    simp only [walshBilinear, ha, ← mul_assoc, character_sq, one_mul]
    have hc : (Fintype.card (Cube k) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [average]
  rwa [he] at h

namespace GrowthPairingData
variable {k m : ℕ} {T : X →L[ℝ] Y} {Dg Df : ℝ}
variable (d : GrowthPairingData T (k+m+m) m Dg Df)

end GrowthPairingData

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.PatternNormalization ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {α : Type*} [Fintype α]

theorem average_const_real [Nonempty α] (c : ℝ) : average (fun _ : α => c) = c := by
  simp [average]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.GrowthCoefficient ----
namespace OAI

noncomputable section

namespace Cotype
variable {m : ℕ}

theorem abs_character_finite {ι : Type*} [Fintype ι] [DecidableEq ι] (P s : ι → Bool) :
    |character P s| = 1 := by
  rcases mul_self_eq_one_iff.mp (character_sq P s) with h | h <;> simp [h]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {n k : ℕ} {T : X →L[ℝ] Y} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

variable (d : GrowthPairingData T (k+m+m) m Dg Df)

end GrowthPairingData

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.TaggedCoefficient ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {k m : ℕ}

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T (k+m+m) m Dg Df)

theorem coefficientPrimal_norm (ε : Cube m) (u : Fin m → Cube k) :
    ‖d.coefficientPrimal ε u‖ ≤ 1 := d.P_norm _ _

theorem coefficientDual_norm (P : SignMatrix m) (δ : Cube m) (v : Fin m → Cube k) :
    ‖d.coefficientDual P δ v‖ ≤ 1 := by
  calc
    _ ≤ average (fun D : SignMatrix m => ‖character P D • d.Z (taggedDual v D) δ‖) := norm_average_le _
    _ ≤ average (fun _ : SignMatrix m => (1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_smul, Real.norm_eq_abs, abs_character_finite, one_mul]
      exact d.Z_norm _ _
    _ = 1 := average_const_real _

end GrowthPairingData

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.RankFactors ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix
namespace Cotype
variable {𝕜 : Type*} [Field 𝕜] {m : ℕ}

theorem exists_rank_pairing_factors (P : Matrix (Fin m) (Fin m) 𝕜) :
    ∃ I J : Matrix (Fin m) (Fin P.rank) 𝕜,
      ∀ l t, (∑ i, ∑ j, I i l * P i j * J j t) = if l = t then 1 else 0 := by
  obtain ⟨V,U,e,hV,hU,h⟩ := Matrix.exists_rank_normal_form P
  let I : Matrix (Fin m) (Fin P.rank) 𝕜 := fun i l => V (e.symm (Sum.inl l)) i
  let J : Matrix (Fin m) (Fin P.rank) 𝕜 := fun j t => U j (e.symm (Sum.inl t))
  refine ⟨I,J,?_⟩
  intro l t
  have hh := congrArg (fun A : Matrix (Fin m) (Fin m) 𝕜 =>
    A (e.symm (Sum.inl l)) (e.symm (Sum.inl t))) h
  simp only [Matrix.mul_apply, Finset.sum_mul] at hh
  rw [Finset.sum_comm] at hh
  simpa [I,J,Matrix.submatrix, Matrix.fromBlocks, Matrix.one_apply] using hh

theorem exists_rank_pairing_matrix (P : Matrix (Fin m) (Fin m) 𝕜) :
    ∃ I J : Matrix (Fin m) (Fin P.rank) 𝕜, I.transpose * P * J = 1 := by
  obtain ⟨I,J,h⟩ := exists_rank_pairing_factors P
  refine ⟨I,J,?_⟩
  ext l t
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Matrix.one_apply]
  rw [Finset.sum_comm]
  exact h l t

theorem rank_pairing_contract {r : ℕ} (P : Matrix (Fin m) (Fin m) 𝕜)
    (I J : Matrix (Fin m) (Fin r) 𝕜) (h : I.transpose * P * J = 1)
    (x y : Fin r → 𝕜) :
    coordinateDual (I.mulVec x) (P.mulVec (J.mulVec y)) = coordinateDual x y := by
  change (I *ᵥ x) ⬝ᵥ (P *ᵥ (J *ᵥ y)) = x ⬝ᵥ y
  rw [← Matrix.vecMul_transpose I x, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.RankWalsh ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {m r k : ℕ}

theorem character_binary_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (P s : ι → Bool) :
    character P s = binarySign (∑ i, binaryBit (P i) * binaryBit (s i)) := by
  rw [binarySign_sum]
  apply Finset.prod_congr rfl
  intro i hi
  cases P i <;> cases s i <;> simp [binaryBit, sign]

theorem rankSubstitute_character (P : SignMatrix m)
    (I J : Matrix (Fin m) (Fin r) (ZMod 2)) (hIJ : I.transpose * binaryMatrix P * J = 1)
    (ζ η : Cube (r*k)) :
    character P (freePairingPattern (rankSubstitute I ζ) (rankSubstitute J η)) = character η ζ := by
  rw [character_binary_sum, character_binary_sum]
  apply congrArg binarySign
  have hb (i j) : binaryBit (freePairingPattern (rankSubstitute I ζ) (rankSubstitute J η) (i,j)) =
      ∑ p, J.mulVec (blockCoordinates η p) j * I.mulVec (blockCoordinates ζ p) i := by
    change bitEquiv (bitEquiv.symm _) = _
    rw [Equiv.apply_symm_apply, coordinateDual_apply]
    simp
  calc
    _ = ∑ i, ∑ j, ∑ p, I.mulVec (blockCoordinates ζ p) i *
        (binaryMatrix P i j * J.mulVec (blockCoordinates η p) j) := by
      simp only [Fintype.sum_prod_type, hb, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro p hp
      change binaryBit (P (i,j)) * (_ * _) = _ * (binaryBit (P (i,j)) * _)
      ring
    _ = ∑ p, ∑ i, ∑ j, I.mulVec (blockCoordinates ζ p) i *
        (binaryMatrix P i j * J.mulVec (blockCoordinates η p) j) := by
      calc
        _ = ∑ i, ∑ p, ∑ j, I.mulVec (blockCoordinates ζ p) i *
            (binaryMatrix P i j * J.mulVec (blockCoordinates η p) j) := by
          apply Finset.sum_congr rfl; intro i hi
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ p, coordinateDual (I.mulVec (blockCoordinates ζ p))
        ((binaryMatrix P).mulVec (J.mulVec (blockCoordinates η p))) := by
      simp only [coordinateDual_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ = ∑ p, coordinateDual (blockCoordinates ζ p) (blockCoordinates η p) := by
      simp_rw [rank_pairing_contract _ I J hIJ]
    _ = ∑ q, binaryBit (η q) * binaryBit (ζ q) := by
      rw [← Equiv.sum_comp finProdFinEquiv (fun q => binaryBit (η q) * binaryBit (ζ q))]
      simp only [coordinateDual_apply, blockCoordinates, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l hl
      apply Finset.sum_congr rfl; intro p hp
      ring

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T (k+m+m) m Dg Df)

theorem coefficient_rank_walsh_bound (hn : m+m ≤ k+m+m)
    (P : SignMatrix m) (ε δ : Cube m) :
    |fourier (fun S => d.patternPairing hn S ε δ) P| ≤ walshNorm ((binaryMatrix P).rank*k) T := by
  obtain ⟨I,J,hIJ⟩ := exists_rank_pairing_matrix (binaryMatrix P)
  have h := walsh_amplitude_bound d.amplifiedOperator
    (fun ζ => d.coefficientPrimal ε (rankSubstitute I ζ))
    (fun η => d.coefficientDual P δ (rankSubstitute J η))
    (fourier (fun S => d.patternPairing hn S ε δ) P)
    (fun ζ => d.coefficientPrimal_norm ε _) (fun η => d.coefficientDual_norm P δ _)
    (fun ζ η => by rw [d.tagged_coefficient_extraction hn, rankSubstitute_character P I J hIJ, mul_comm])
  exact h.trans_eq (d.walsh_norms _)

end GrowthPairingData

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.GrowthTheorem ----
namespace OAI

noncomputable section

universe u v
namespace Cotype

theorem exists_growth_constant (m : ℕ) (Dg Df : ℝ)
    (hDg1 : 1 ≤ Dg) (hDf1 : 1 ≤ Df)
    (hcut : 4 ≤ degreeCutoff m) (hcutm : degreeCutoff m < m)
    (hsize : 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
      min ((m : ℝ)*(1/(2*24*Dg*Real.sqrt m))) ((m : ℝ)*(1/(2*24*Df*Real.sqrt m)))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1/2 ∧
      ∀ (X : Type u) (Y : Type v) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y),
        FixedCotypeBound (X →L[ℝ] ℝ) m Dg → FixedCotypeBound Y m Df → T ≠ 0 →
        ∀ n : ℕ, 4*m < n → walshNorm (n-2*m) T ≤ 2*walshNorm n T →
          c₁ * walshNorm n T ≤ walshNorm (2*(n-2*m)) T := by
  have hm : 0 < m := by omega
  have hmg : 0 < 1/(2*24*Dg*Real.sqrt m) := by
    have : 0 < Dg := by linarith
    positivity
  have hmf : 0 < 1/(2*24*Df*Real.sqrt m) := by
    have : 0 < Df := by linarith
    positivity
  obtain ⟨c,hc,hall⟩ := coefficientTarget_proved m _ _ hcut hcutm hmg hmf hsize
  refine ⟨min (1/2) (c/2), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro X Y _ _ _ _ _ T hDg hDf hT n hn hslow
  obtain ⟨k,rfl⟩ : ∃ k, n = k+m+m := ⟨n-2*m, by omega⟩
  have he : k+m+m-2*m = k := by omega
  rw [he] at hslow ⊢
  obtain ⟨d⟩ := exists_growthPairingData (k+m+m) hm hDg hDf hDg1 hDf1 hT
  have hnm : m+m ≤ k+m+m := by omega
  have hnp : m+1 ≤ k+m+m := by omega
  have hnd : 1+m ≤ k+m+m := by omega
  obtain ⟨P,hPr,hPc⟩ := hall (d.normalizedMatrix hnm) (d.normalizedPrimal hnp)
    (d.normalizedDual hnd) (d.normalized_scalar_admissible hm hnm hnp hnd hslow)
  obtain ⟨ε,δ,hfix⟩ := d.exists_fixed_lift_coefficient hnm P hc hPc
  have hrank := d.coefficient_rank_walsh_bound hnm P ε δ
  have hmono := walshNorm_antitone T (Nat.mul_le_mul_right k hPr)
  have hcg : c*d.gamma ≤ walshNorm (2*k) T := hfix.trans (hrank.trans hmono)
  have hc1 := min_le_right (1/2 : ℝ) (c/2)
  have hn0 := walshNorm_nonneg (k+m+m) T
  have hhalf := d.gamma_half
  nlinarith [mul_le_mul_of_nonneg_right hc1 hn0]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution.{u,v} : type_of% @_root_.OAI.Cotype.exists_growth_constant.{u,v} := @_root_.OAI.Cotype.exists_growth_constant.{u,v}
