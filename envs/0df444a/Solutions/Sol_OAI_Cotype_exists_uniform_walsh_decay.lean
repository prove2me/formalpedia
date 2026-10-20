-- Prove2me | solution 1 for OAI.Cotype.exists_uniform_walsh_decay
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:26:40.060077+00:00
-- url     : https://prove2.me/submissions/60806a85-15d9-44da-947a-a2050b165058

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/UniformDecay.lean:L49-L97
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_uniform_walsh_decay. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_UniformDecay
import Theorems.Thm_OAI_Cotype_exists_growth_constant
import Theorems.Thm_OAI_Cotype_parseval
import Theorems.Thm_OAI_Cotype_uniform_drop_of_growth

-- ---- from OAI.Analysis.Cotype.ScalarWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem scalarWalsh_L2_sq {n : ℕ} (f : Cube n → ℝ) :
    cubeL2 ℝ (scalarWalsh f) ^ 2 = (2 : ℝ)⁻¹ ^ n * cubeL2 ℝ f ^ 2 := by
  rw [cubeL2_sq, cubeL2_sq]
  simp only [Real.norm_eq_abs, sq_abs, scalarWalsh, average, smul_eq_mul]
  rw [parseval]
  simp [average, Cube, inv_pow]

theorem scalarWalsh_L2 {n : ℕ} (f : Cube n → ℝ) :
    cubeL2 ℝ (scalarWalsh f) = Real.sqrt ((2 : ℝ)⁻¹ ^ n) * cubeL2 ℝ f := by
  apply (sq_eq_sq₀ (cubeL2_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (cubeL2_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), scalarWalsh_L2_sq]

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
theorem cubeL2_add_le {n : ℕ} (f g : Cube n → X) :
    cubeL2 X (fun ε => f ε + g ε) ≤ cubeL2 X f + cubeL2 X g := by
  simp only [cubeL2_eq_piLp]
  have he : (toLp 2 (fun ε => f ε + g ε) : PiLp 2 (fun _ : Cube n => X)) =
      toLp 2 f + toLp 2 g := rfl
  rw [he, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)

omit [NormedSpace ℝ X] in
theorem cubeL2_sum_le {n : ℕ} {α : Type*} (s : Finset α) (f : α → Cube n → X) :
    cubeL2 X (fun ε => ∑ a ∈ s, f a ε) ≤ ∑ a ∈ s, cubeL2 X (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cubeL2, average]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (cubeL2_add_le _ _).trans (add_le_add le_rfl ih)

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

-- ---- from OAI.Analysis.Cotype.FiniteRankWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem cubeL2_smul_const {n : ℕ} (g : Cube n → ℝ) (y : Y) :
    cubeL2 Y (fun ε => g ε • y) = cubeL2 ℝ g * ‖y‖ := by
  apply (sq_eq_sq₀ (cubeL2_nonneg _) (mul_nonneg (cubeL2_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, cubeL2_sq, cubeL2_sq]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, average, smul_eq_mul,
    ← Finset.sum_mul, mul_assoc]

theorem vectorWalsh_smul_const {n : ℕ} (g : Cube n → ℝ) (y : Y) :
    vectorWalsh (fun ε => g ε • y) = fun v => scalarWalsh g v • y := by
  funext v
  simp only [vectorWalsh, smul_smul, average_smul_const]
  congr 1
  simp only [scalarWalsh, fourier, mul_comm]

theorem vectorWalsh_finset_sum {n : ℕ} {α : Type*} (s : Finset α) (f : α → Cube n → Y) :
    vectorWalsh (fun ε => ∑ i ∈ s, f i ε) = fun v => ∑ i ∈ s, vectorWalsh (f i) v := by
  funext v
  simp only [vectorWalsh, average, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem finiteRank_expansion (T : X →L[ℝ] Y)
    (hT : FiniteDimensional ℝ (LinearMap.range T.toLinearMap)) :
    ∃ (r : ℕ) (φ : Fin r → X →L[ℝ] ℝ) (y : Fin r → Y),
      ∀ x, T x = ∑ i, φ i x • y i := by
  let := hT
  let b := Module.finBasis ℝ (LinearMap.range T.toLinearMap)
  let R : X →L[ℝ] LinearMap.range T.toLinearMap :=
    T.codRestrict _ (fun x => ⟨x, rfl⟩)
  let φ := fun i => ((b.coord i).toContinuousLinearMap).comp R
  refine ⟨Module.finrank ℝ (LinearMap.range T.toLinearMap), φ, fun i => (b i : Y), ?_⟩
  intro x
  have he := congrArg (fun z : LinearMap.range T.toLinearMap => (z : Y)) (b.sum_repr (R x))
  change T x = ∑ i, b.repr (R x) i • (b i : Y)
  simpa [R] using he.symm

theorem operatorWalsh_expansion {r n : ℕ} (T : X →L[ℝ] Y)
    (φ : Fin r → X →L[ℝ] ℝ) (y : Fin r → Y)
    (hT : ∀ x, T x = ∑ i, φ i x • y i) (f : Cube n → X) :
    operatorWalsh T f = fun v => ∑ i, scalarWalsh (fun u => φ i (f u)) v • y i := by
  unfold operatorWalsh
  simp_rw [hT]
  rw [vectorWalsh_finset_sum]
  simp_rw [vectorWalsh_smul_const]

theorem finite_expansion_Walsh_bound {r n : ℕ} (T : X →L[ℝ] Y)
    (φ : Fin r → X →L[ℝ] ℝ) (y : Fin r → Y)
    (hT : ∀ x, T x = ∑ i, φ i x • y i) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤
      (∑ i, ‖φ i‖ * ‖y i‖) * Real.sqrt ((2 : ℝ)⁻¹ ^ n) * cubeL2 X f := by
  rw [operatorWalsh_expansion T φ y hT f]
  apply (cubeL2_sum_le _ _).trans
  calc
    _ = ∑ i, (Real.sqrt ((2 : ℝ)⁻¹ ^ n) * cubeL2 ℝ (fun u => φ i (f u))) * ‖y i‖ := by
      simp_rw [cubeL2_smul_const, scalarWalsh_L2]
    _ ≤ ∑ i, (Real.sqrt ((2 : ℝ)⁻¹ ^ n) * (‖φ i‖ * cubeL2 X f)) * ‖y i‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (cubeL2_clm (φ i) f) (Real.sqrt_nonneg _)) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem finiteRank_Walsh_decay (T : X →L[ℝ] Y)
    (hT : FiniteDimensional ℝ (LinearMap.range T.toLinearMap)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (n : ℕ) (f : Cube n → X),
      cubeL2 Y (operatorWalsh T f) ≤ D * Real.sqrt ((2 : ℝ)⁻¹ ^ n) * cubeL2 X f := by
  obtain ⟨r, φ, y, he⟩ := finiteRank_expansion T hT
  exact ⟨∑ i, ‖φ i‖ * ‖y i‖, Finset.sum_nonneg (fun i _ => by positivity),
    fun _ f => finite_expansion_Walsh_bound T φ y he f⟩

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

theorem walshNorm_le (n : ℕ) (T : X →L[ℝ] Y) : walshNorm n T ≤ ‖T‖ := by
  apply csSup_le ⟨0, walshOutputs_zero n T⟩
  rintro r ⟨f, hf, rfl⟩
  exact (operatorWalsh_L2_le T f).trans ((mul_le_mul_of_nonneg_left hf (norm_nonneg T)).trans_eq (mul_one _))

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

theorem finiteRank_walshNorm_decay (T : X →L[ℝ] Y)
    (hT : FiniteDimensional ℝ (LinearMap.range T.toLinearMap)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, walshNorm n T ≤ D * Real.sqrt ((2 : ℝ)⁻¹ ^ n) := by
  obtain ⟨D, hD, h⟩ := finiteRank_Walsh_decay T hT
  exact ⟨D, hD, fun n => walshNorm_le_of_bound T (mul_nonneg hD (Real.sqrt_nonneg _)) (h n)⟩

theorem operatorWalsh_zero_const (T : X →L[ℝ] Y) (x : X) :
    operatorWalsh (n := 0) T (fun _ => x) = fun _ => T x := by
  funext v
  simp [operatorWalsh, vectorWalsh, character, average]

theorem walshNorm_zero (T : X →L[ℝ] Y) : walshNorm 0 T = ‖T‖ := by
  apply (walshNorm_le 0 T).antisymm
  apply T.opNorm_le_bound (walshNorm_nonneg 0 T)
  intro x
  have h := operatorWalsh_le_walshNorm (n := 0) T (fun _ => x)
  simpa only [operatorWalsh_zero_const, cubeL2_const] using h

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

-- ---- from OAI.Analysis.Cotype.WalshLower ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
theorem cubeL2_single {n : ℕ} (p : Cube n) (x : X) :
    cubeL2 X (fun u => if u = p then x else 0) =
      Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) * ‖x‖ := by
  unfold cubeL2 average
  simp only [smul_eq_mul, apply_ite, norm_zero, ite_pow, zero_pow (by omega : 2 ≠ 0),
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg x)]

theorem operatorWalsh_single {n : ℕ} (T : X →L[ℝ] Y) (p v : Cube n) (x : X) :
    operatorWalsh T (fun u => if u = p then x else 0) v =
      ((Fintype.card (Cube n) : ℝ)⁻¹ * character v p) • T x := by
  simp [operatorWalsh, vectorWalsh, average, apply_ite, smul_smul]

theorem operatorWalsh_single_L2 {n : ℕ} (T : X →L[ℝ] Y) (p : Cube n) (x : X) :
    cubeL2 Y (operatorWalsh T (fun u => if u = p then x else 0)) =
      (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖ := by
  have hn (v : Cube n) : ‖operatorWalsh T (fun u => if u = p then x else 0) v‖ =
      (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖ := by
    rw [operatorWalsh_single, norm_smul, Real.norm_eq_abs, abs_mul, abs_character,
      abs_of_nonneg (by positivity : 0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹), mul_one]
  have he : cubeL2 Y (operatorWalsh T (fun u => if u = p then x else 0)) =
      cubeL2 ℝ (fun _ : Cube n => (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖) := by
    simp only [cubeL2, hn, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖)]
  rw [he, cubeL2_const, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem walshNorm_lower (n : ℕ) (T : X →L[ℝ] Y) :
    Real.sqrt ((2 : ℝ)⁻¹ ^ n) * ‖T‖ ≤ walshNorm n T := by
  let q : ℝ := Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹)
  have hq : 0 < q := Real.sqrt_pos.mpr (inv_pos.mpr (by exact_mod_cast (Fintype.card_pos (α := Cube n))))
  have hq2 : q^2 = (Fintype.card (Cube n) : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have hop : ‖T‖ ≤ walshNorm n T / q := by
    apply T.opNorm_le_bound (div_nonneg (walshNorm_nonneg n T) hq.le)
    intro x
    have h := operatorWalsh_le_walshNorm T (fun u : Cube n => if u = (fun _ => false) then x else 0)
    rw [operatorWalsh_single_L2, cubeL2_single] at h
    change (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖ ≤ walshNorm n T * (q * ‖x‖) at h
    rw [← hq2] at h
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hq).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hop hq.le
  have he : q = Real.sqrt ((2 : ℝ)⁻¹ ^ n) := by simp [q, Cube, inv_pow]
  rw [show q * (walshNorm n T / q) = walshNorm n T by field_simp] at hh
  simpa [he] using hh

theorem walshNorm_pos (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) : 0 < walshNorm n T :=
  (mul_pos (Real.sqrt_pos.mpr (by positivity)) (norm_pos_iff.mpr hT)).trans_le (walshNorm_lower n T)

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

-- ---- from OAI.Analysis.Cotype.UniformDecay ----
namespace OAI

noncomputable section

universe u v
namespace Cotype

theorem sequence_drop_rate (w : ℕ → ℝ) (m n₀ : ℕ) (hm : 0 < m)
    (hanti : Antitone w) (hdrop : ∀ n, n₀ ≤ n → w n ≤ (1/2)*w (n-2*m)) :
    ∀ N, w N ≤ (1/2 : ℝ)^((N-n₀)/(2*m))*w 0 := by
  have hsteps : ∀ j, w (n₀+2*m*j) ≤ (1/2 : ℝ)^j*w 0 := by
    intro j
    induction j with
    | zero => simpa using hanti (Nat.zero_le n₀)
    | succ j ih =>
      have h := hdrop (n₀+2*m*(j+1)) (by omega)
      have he : n₀+2*m*(j+1)-2*m = n₀+2*m*j := by
        simp only [Nat.mul_add, Nat.mul_one]; omega
      rw [he] at h
      calc
        _ ≤ (1/2)*w (n₀+2*m*j) := h
        _ ≤ (1/2)*((1/2 : ℝ)^j*w 0) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  intro N
  by_cases hN : n₀ ≤ N
  · have he : n₀+2*m*((N-n₀)/(2*m)) ≤ N := by
      have h := (Nat.le_div_iff_mul_le (Nat.mul_pos (by decide : 0 < 2) hm)).mp
        (le_refl ((N-n₀)/(2*m)))
      rw [Nat.mul_comm ((N-n₀)/(2*m)) (2*m)] at h
      omega
    exact (hanti he).trans (hsteps _)
  · simpa [Nat.sub_eq_zero_of_le (le_of_not_ge hN)] using hanti (Nat.zero_le N)

theorem uniformDecayRate_tendsto (m n₀ : ℕ) (hm : 0 < m) :
    Filter.Tendsto (uniformDecayRate m n₀) Filter.atTop (nhds 0) := by
  apply (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)).comp
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [Filter.eventually_ge_atTop (n₀+2*m*b)] with N hN
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2*m)).mpr
  rw [Nat.mul_comm b (2*m)]
  omega

theorem exists_uniform_walsh_decay (m : ℕ) (Dg Df : ℝ)
    (hDg1 : 1 ≤ Dg) (hDf1 : 1 ≤ Df)
    (hcut : 4 ≤ degreeCutoff m) (hcutm : degreeCutoff m < m)
    (hsize : 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
      min ((m : ℝ)*(1/(2*24*Dg*Real.sqrt m))) ((m : ℝ)*(1/(2*24*Df*Real.sqrt m)))) :
    ∃ n₀ : ℕ, 4*m < n₀ ∧
      Filter.Tendsto (uniformDecayRate m n₀) Filter.atTop (nhds 0) ∧
      ∀ (X : Type u) (Y : Type v) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y),
        FixedCotypeBound (X →L[ℝ] ℝ) m Dg → FixedCotypeBound Y m Df →
        FiniteDimensional ℝ (LinearMap.range T.toLinearMap) →
        (∀ n, n₀ ≤ n → walshNorm n T ≤ (1/2)*walshNorm (n-2*m) T) ∧
        ∀ N, walshNorm N T ≤ uniformDecayRate m n₀ N * ‖T‖ := by
  have hm : 0 < m := by omega
  obtain ⟨c,hc,hc1,hgrowth⟩ := exists_growth_constant.{u,v} m Dg Df hDg1 hDf1 hcut hcutm hsize
  let q := Real.sqrt ((2 : ℝ)⁻¹)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  obtain ⟨n₀,hn₀,hdrop⟩ := uniform_drop_of_growth m hm c q hc hq0 hq1
  refine ⟨n₀,hn₀,uniformDecayRate_tendsto m n₀ hm,?_⟩
  intro X Y _ _ _ _ _ T hDg hDf hfin
  have hd : ∀ n, n₀ ≤ n → walshNorm n T ≤ (1/2)*walshNorm (n-2*m) T := by
    by_cases hT : T = 0
    · subst T; intro n hn
      have h := walshNorm_le n (0 : X →L[ℝ] Y)
      have h0 := walshNorm_nonneg (n-2*m) (0 : X →L[ℝ] Y)
      simp only [norm_zero] at h
      linarith
    obtain ⟨D,hD,hDn⟩ := finiteRank_walshNorm_decay T hfin
    have hbound : ∃ D : ℝ, ∀ n, walshNorm n T ≤ D*q^n := by
      refine ⟨D,?_⟩
      intro n
      have hs : ∀ l : ℕ, Real.sqrt ((2 : ℝ)⁻¹ ^ l) = q^l := by
        intro l
        induction l with
        | zero => simp
        | succ l ih =>
          rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
      simpa only [hs] using hDn n
    intro n hn
    have h := hdrop (fun n => walshNorm n T) (fun n => walshNorm_pos n hT)
      (walshNorm_antitone T) hbound (hgrowth X Y T hDg hDf hT) n hn
    linarith
  refine ⟨hd,?_⟩
  intro N
  have h := sequence_drop_rate (fun n => walshNorm n T) m n₀ hm (walshNorm_antitone T) hd N
  simpa [uniformDecayRate, walshNorm_zero] using h

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution.{u,v} : type_of% @_root_.OAI.Cotype.exists_uniform_walsh_decay.{u,v} := @_root_.OAI.Cotype.exists_uniform_walsh_decay.{u,v}
