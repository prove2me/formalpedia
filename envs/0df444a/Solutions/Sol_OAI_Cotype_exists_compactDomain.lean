-- Prove2me | solution 1 for OAI.Cotype.exists_compactDomain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:31:29.400581+00:00
-- url     : https://prove2.me/submissions/efe761f5-cd0a-4f33-ba5a-25d0d64cf0fb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CompactDomain.lean:L61-L76
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_compactDomain. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_CompactDomain
import Theorems.Thm_OAI_Cotype_exists_finiteLevel_tower
import Theorems.Thm_OAI_Cotype_exists_levelSum_moment_lift
import Theorems.Thm_OAI_Cotype_fixedCotypeBound_dual_of_L2_lifts
import Theorems.Thm_OAI_Cotype_quotientFactor_compact
import Theorems.Thm_OAI_Cotype_quotientFactor_norm

-- ---- from OAI.Analysis.Cotype.VectorWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem cubeL2_mono {n : ℕ} {f : Cube n → X} {g : Cube n → Y}
    (h : ∀ ε, ‖f ε‖ ≤ ‖g ε‖) : cubeL2 X f ≤ cubeL2 Y g := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun ε _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h ε))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WeightedCompact ----
namespace OAI

noncomputable section

open scoped BigOperators Topology ENNReal
open Filter
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (A : ℕ → Submodule ℝ X)

omit [CompleteSpace X] in
theorem levelTerm_norm (l : ℕ) : ‖levelTerm A l‖ ≤ (1/2 : ℝ)^l := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1/2 : ℝ)^l)] using
    mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) z l)
      (by positivity : 0 ≤ (1/2 : ℝ)^l)

omit [CompleteSpace X] in
theorem levelTerm_summable_norm : Summable (fun l => ‖levelTerm A l‖) :=
  Summable.of_nonneg_of_le (fun l => norm_nonneg (levelTerm A l)) (levelTerm_norm A)
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1))

theorem levelTerm_summable : Summable (levelTerm A) := Summable.of_norm (f := levelTerm A) (levelTerm_summable_norm A)

omit [CompleteSpace X] in
theorem weightedMap_norm : ‖weightedMap A‖ ≤ 2 := by
  calc
    _ ≤ ∑' l, ‖levelTerm A l‖ := norm_tsum_le_tsum_norm (f := levelTerm A) (levelTerm_summable_norm A)
    _ ≤ ∑' l : ℕ, (1/2 : ℝ)^l := (levelTerm_summable_norm A).tsum_le_tsum (levelTerm_norm A)
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1))
    _ = 2 := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]; norm_num

theorem weightedMap_apply (z : LevelSum A) :
    weightedMap A z = ∑' l, (1/2 : ℝ)^l • (z l : X) := by
  exact ((ContinuousLinearMap.apply ℝ X z).map_tsum (levelTerm_summable A))

omit [CompleteSpace X] in
theorem levelTerm_compact (hA : ∀ l, FiniteDimensional ℝ (A l)) (l : ℕ) :
    IsCompactOperator (levelTerm A l) := by
  let := hA l
  exact ((isCompactOperator_of_locallyCompactSpace_rng (A l).subtypeL).comp_clm
    (lp.evalCLM ℝ (fun l => A l) 2 l)).smul _

theorem weightedMap_compact (hA : ∀ l, FiniteDimensional ℝ (A l)) :
    IsCompactOperator (weightedMap A) := by
  apply isCompactOperator_of_tendsto (levelTerm_summable A).hasSum
  apply Filter.Eventually.of_forall
  intro s
  exact (compactOperator (RingHom.id ℝ) (LevelSum A) X).sum_mem (fun l _ => levelTerm_compact A hA l)

theorem weightedMap_single_zero (x : A 0) :
    weightedMap A (lp.single 2 0 x) = (x : X) := by
  rw [weightedMap_apply, tsum_eq_single 0]
  · simp
  · intro l hl
    simp [lp.single_apply, hl]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CompactQuotient ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem quotientFactor_injective (j : H →L[ℝ] X) : Function.Injective (quotientFactor j) := by
  apply (quotientFactor j).ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨z,rfl⟩ := j.ker.mkQ_surjective g
  change j z = 0 at hg
  change j.ker.mkQ z ∈ (⊥ : Submodule ℝ (KernelQuotient j))
  change (Submodule.Quotient.mk z : KernelQuotient j) = 0
  exact (Submodule.Quotient.mk_eq_zero j.ker).mpr hg

theorem quotient_representative_two (j : H →L[ℝ] X) (g : KernelQuotient j) :
    ∃ z : H, j.ker.mkQL z = g ∧ ‖z‖ ≤ 2 * ‖g‖ := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg], by simp [hg]⟩
  · obtain ⟨z,hz,hn⟩ := Submodule.Quotient.norm_mk_lt g (norm_pos_iff.mpr hg)
    exact ⟨z,hz, by linarith⟩

variable [CompleteSpace X] (A : ℕ → Submodule ℝ X)

omit [CompleteSpace X] in
theorem compactInclusion_norm : ‖compactInclusion A‖ ≤ 1 := by
  apply (compactInclusion A).opNorm_le_bound zero_le_one
  intro x
  change ‖(Submodule.Quotient.mk (lp.single 2 0 x) : KernelQuotient (weightedMap A))‖ ≤ 1 * ‖x‖
  simpa only [lp.norm_single (by norm_num : (0 : ENNReal) < 2), one_mul] using
    Submodule.Quotient.norm_mk_le (weightedMap A).ker (lp.single 2 0 x)

theorem quotientFactor_compactInclusion (x : A 0) :
    quotientFactor (weightedMap A) (compactInclusion A x) = (x : X) :=
  weightedMap_single_zero A x

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CompactMomentAssembly ----
namespace OAI

noncomputable section

open scoped BigOperators ENNReal
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (A : ℕ → Submodule ℝ X)

theorem moment_clm {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {m : ℕ}
    (T : Y →L[ℝ] Z) (f : Cube m → Y) (i : Fin m) :
    T (moment Y f i) = moment Z (fun ε => T (f ε)) i := by
  simp [moment, average]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CompactDomain ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (A : ℕ → Submodule ℝ X)
attribute [local instance] OAI.Cotype.instIsClosedLevelSumCoeSubmoduleRealKerWeightedMap
attribute [local instance] OAI.Cotype.instNormedAddCommGroupKernelQuotientLevelSumWeightedMap
theorem exists_quotient_moment_lift {m : ℕ} {D : ℝ} (hD : 0 < D)
    (hL : ∀ l, FiniteLevelLift m D (A l) (A (l+1)))
    (g : Fin m → KernelQuotient (weightedMap A)) :
    ∃ H : Cube m → KernelQuotient (weightedMap A),
      (∀ i, moment (KernelQuotient (weightedMap A)) H i = g i) ∧
      cubeL2 (KernelQuotient (weightedMap A)) H ≤ 12*D*Real.sqrt (∑ i, ‖g i‖^2) := by
  choose z hz hzn using (fun i => quotient_representative_two (weightedMap A) (g i))
  obtain ⟨H, hHm, hHn⟩ := exists_levelSum_moment_lift A hD hL z
  let Q : LevelSum A →L[ℝ] KernelQuotient (weightedMap A) := (weightedMap A).ker.mkQL
  refine ⟨fun ε => Q (H ε), ?_, ?_⟩
  · intro i
    apply quotientFactor_injective (weightedMap A)
    rw [← moment_clm Q H i, quotientFactor_mk, ← hz i, quotientFactor_mk]
    exact hHm i
  · have hQ : cubeL2 (KernelQuotient (weightedMap A)) (fun ε => Q (H ε)) ≤ cubeL2 (LevelSum A) H :=
      cubeL2_mono (fun ε => Submodule.Quotient.norm_mk_le (weightedMap A).ker (H ε))
    have hzN : Real.sqrt (∑ i, ‖z i‖^2) ≤ 2 * Real.sqrt (∑ i, ‖g i‖^2) := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), mul_pow,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => by
        simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg (z i)) (by positivity)).mpr (hzn i))
    exact hQ.trans (hHn.trans (by nlinarith [mul_le_mul_of_nonneg_left hzN (by positivity : 0 ≤ 6*D)]))

theorem quotient_dual_fixedCotype {m : ℕ} {D : ℝ} (hD : 0 < D)
    (hL : ∀ l, FiniteLevelLift m D (A l) (A (l+1))) :
    FixedCotypeBound (KernelQuotient (weightedMap A) →L[ℝ] ℝ) m (12*D) :=
  fixedCotypeBound_dual_of_L2_lifts (X := KernelQuotient (weightedMap A))
    (by positivity) (exists_quotient_moment_lift A hD hL)

theorem exists_compactDomain {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDp : 0 < D)
    (E : Submodule ℝ X) [FiniteDimensional ℝ E] :
    Nonempty (CompactDomainWitness E m D) := by
  obtain ⟨A,hA0,hmono,hAfin,hL⟩ := exists_finiteLevel_tower hD hDp E
  let (l : ℕ) : FiniteDimensional ℝ (A l) := hAfin l
  subst E
  exact ⟨{ G := KernelQuotient (weightedMap A)
           J := quotientFactor (weightedMap A)
           iota := compactInclusion A
           injective := quotientFactor_injective _
           compact := quotientFactor_compact _ (weightedMap_compact A hAfin)
           norm_J := (quotientFactor_norm _).trans (weightedMap_norm A)
           norm_iota := compactInclusion_norm A
           factor := quotientFactor_compactInclusion A
           dual_cotype := quotient_dual_fixedCotype A hDp hL }⟩

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
attribute [local instance] OAI.Cotype.instIsClosedLevelSumCoeSubmoduleRealKerWeightedMap
attribute [local instance] OAI.Cotype.instNormedAddCommGroupKernelQuotientLevelSumWeightedMap


theorem solution.{u} : type_of% @_root_.OAI.Cotype.exists_compactDomain.{u} := @_root_.OAI.Cotype.exists_compactDomain.{u}
