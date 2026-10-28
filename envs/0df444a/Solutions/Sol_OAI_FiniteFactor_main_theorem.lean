-- Prove2me | solution 1 for OAI.FiniteFactor.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:36:50.232047+00:00
-- url     : https://prove2.me/submissions/3b52e4ce-1934-4475-95f2-6be11ca1b068

import Mathlib
import Definitions.Def_FiniteFactor
import Definitions.Def_OAIQ3Ff001
import Definitions.Def_OAIQ3Ff002
import Theorems.Thm_OAI_FiniteFactor_exists_source_prepared_finite
import Theorems.Thm_OAI_FiniteFactor_sourceInvariantProjection_trivial

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BoundedMatrixOperator
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped ENNReal Topology
noncomputable section

theorem fiberFiniteEmbedding_single (n : ℤ) (c : ℂ) :
    fiberFiniteEmbedding (Finsupp.single n c) = lp.single 2 n c := by
  simp [fiberFiniteEmbedding, ← lp.single_smul]

theorem fiberFiniteEmbedding_sum (a : ℤ →₀ ℂ) :
    fiberFiniteEmbedding a = ∑ n ∈ a.support, lp.single 2 n (a n) := by
  simp [fiberFiniteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum, ← lp.single_smul]

theorem fiberFiniteEmbedding_norm_sq (a : ℤ →₀ ℂ) :
    ‖fiberFiniteEmbedding a‖ ^ 2 = ∑ n ∈ a.support, ‖a n‖ ^ 2 := by
  rw [fiberFiniteEmbedding_sum]
  simpa using lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) a a.support

theorem fiberFiniteEmbedding_dense : DenseRange fiberFiniteEmbedding := by
  intro x
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ n ∈ s, Finsupp.single n (x n), ?_⟩
  simp [fiberFiniteEmbedding_single]

/-- Every bounded operator is determined by its coordinate matrix. -/
theorem fiberOperator_ext {A B : SourceFiberHilbert →L[ℂ] SourceFiberHilbert}
    (h : ∀ k n : ℤ, (A (lp.single 2 n (1 : ℂ))) k = (B (lp.single 2 n (1 : ℂ))) k) : A = B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  intro n
  apply ContinuousLinearMap.ext
  intro c
  apply Subtype.ext
  funext k
  change (A (lp.single 2 n c)) k = (B (lp.single 2 n c)) k
  have he : lp.single 2 n c = c • (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) := by
    simp [← lp.single_smul]
  rw [he, map_smul, map_smul]
  change c * (A (lp.single 2 n 1)) k = c * (B (lp.single 2 n 1)) k
  rw [h]

theorem fiberOperator_hasSum (A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (v : SourceFiberHilbert) :
    HasSum (fun n : ℤ => v n • A (lp.single 2 n (1 : ℂ))) (A v) := by
  convert (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) v).map A A.continuous using 1
  funext n
  have he : lp.single 2 n (v n) = v n • (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) := by
    simp [← lp.single_smul]
  change v n • A (lp.single 2 n (1 : ℂ)) = A (lp.single 2 n (v n))
  rw [he, map_smul]

theorem fiberOperator_action (A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (v : SourceFiberHilbert) (k : ℤ) :
    (A v) k = ∑' n : ℤ, (A (lp.single 2 n (1 : ℂ))) k * v n := by
  have h := (fiberOperator_hasSum A v).map
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k) (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous
  have he := h.tsum_eq.symm
  change (A v) k = ∑' n : ℤ, v n * (A (lp.single 2 n (1 : ℂ))) k at he
  simpa only [mul_comm] using he

variable (m : ℤ → ℤ → ℂ) (C : ℝ)
variable (hb : ∀ (s t : Finset ℤ) (a : ℤ → ℂ),
  (∑ k ∈ t, ‖∑ n ∈ s, a n * m k n‖ ^ 2) ≤ C ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2)

theorem fiberMatrixFinite_norm_le (hC : 0 ≤ C) (a : ℤ →₀ ℂ) :
    ‖fiberMatrixFinite m C hb a‖ ≤ C * ‖fiberFiniteEmbedding a‖ := by
  have he : ‖fiberMatrixFinite m C hb a‖ ^ 2 =
      ∑' k, ‖fiberMatrixLinear m a k‖ ^ 2 := by
    simpa [fiberMatrixFinite] using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
      (fiberMatrixFinite m C hb a)
  have hsum : (∑' k, ‖fiberMatrixLinear m a k‖ ^ 2) ≤
      C ^ 2 * ∑ n ∈ a.support, ‖a n‖ ^ 2 := by
    apply Real.tsum_le_of_sum_le
    · intro k; positivity
    · intro t; simpa [fiberMatrixLinear_apply] using hb a.support t a
  rw [← he, ← fiberFiniteEmbedding_norm_sq] at hsum
  have hpos := mul_nonneg hC (norm_nonneg (fiberFiniteEmbedding a))
  nlinarith [norm_nonneg (fiberMatrixFinite m C hb a)]

theorem boundedMatrixOperator_entry (hC : 0 ≤ C) (k n : ℤ) :
    (boundedMatrixOperator m C hb (lp.single 2 n (1 : ℂ))) k = m k n := by
  rw [← fiberFiniteEmbedding_single n 1]
  change ((fiberMatrixFinite m C hb).extendOfNorm fiberFiniteEmbedding
    (fiberFiniteEmbedding (Finsupp.single n 1))) k = _
  rw [LinearMap.extendOfNorm_eq fiberFiniteEmbedding_dense
    ⟨C, fiberMatrixFinite_norm_le m C hb hC⟩]
  change fiberMatrixLinear m (Finsupp.single n 1) k = _
  simp [fiberMatrixLinear]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FreeRotation
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem SourceRationalIndependent.mul_ne_integer {θ : SourceCoordinate → ℝ}
    (hθ : SourceRationalIndependent θ) (i : SourceCoordinate) (k : ℤ) (hk : k ≠ 0) (c : ℤ) :
    (k : ℝ)*θ i ≠ (c : ℝ) := by
  intro he
  have hh := (hθ (Finsupp.single i k) c (by simpa using he)).1
  have hz := congrArg (fun v : SourceCoordinate →₀ ℤ => v i) hh
  exact hk (by simpa using hz)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_GeneratedAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Pointwise
noncomputable section

theorem mem_sourceGeneratedVonNeumann {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Set (H →L[ℂ] H)) {T : H →L[ℂ] H} (hT : T ∈ S) :
    T ∈ sourceGeneratedVonNeumann S := by
  have he : (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier =
      Set.centralizer (Set.centralizer (S ∪ star S)) :=
    StarSubalgebra.coe_centralizer_centralizer ℂ S
  change T ∈ (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier
  rw [he]
  exact Set.subset_centralizer_centralizer (Or.inl hT)

theorem sourcePi_mem (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    sourcePi θ g ∈ sourceAlgebra θ :=
  mem_sourceGeneratedVonNeumann _ (Or.inr ⟨g,rfl⟩)

theorem sourceShift_mem (θ : SourceCoordinate → ℝ) :
    sourceShift SourceCoordinate ∈ sourceAlgebra θ :=
  mem_sourceGeneratedVonNeumann _ (Or.inl rfl)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Entries
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- A product almost-everywhere identity holds on every integer fiber. -/
theorem source_ae_all_fibers {p : (SourceCoordinate → ℝ) × ℤ → Prop}
    (hp : ∀ᵐ z ∂sourceMeasure SourceCoordinate, p z) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ, p (x,n) := by
  exact (Measure.ae_ae_of_ae_prod hp).mono fun x hx => Measure.ae_count_iff.mp hx

theorem sourceBasis_coe (n : ℤ) : sourceBasis n =ᵐ[sourceMeasure SourceCoordinate]
    fun z => if z.2 = n then 1 else 0 := by
  filter_upwards [sourceFiberIndicator_coe Set.univ MeasurableSet.univ n] with z hz
  rw [show (sourceBasis n) z = _ from hz]
  by_cases hn : z.2 = n <;> simp [hn]

theorem sourceScalar_apply_ae (g : SourceBaseFunction) (f : SourceHilbert SourceCoordinate) :
    sourceScalar g f =ᵐ[sourceMeasure SourceCoordinate] fun z => g.toFun z.1 * f z := by
  filter_upwards [sourcePi_apply_ae (fun _ => 0) g f, sourceHilbert_cube] with z hz hc
  change (sourcePi (fun _ => 0) g f) z = _
  rw [hz]
  have he : coordinateRotate (fun _ : SourceCoordinate => 0) z.2 z.1 = z.1 := by
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  simp [sourcePiSymbol, he]

theorem sourceScalar_indicator_basis (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (n : ℤ) : sourceScalar (sourceBaseIndicator A hA) (sourceBasis n) =
      sourceFiberIndicator A hA n := by
  apply Lp.ext
  filter_upwards [sourceScalar_apply_ae (sourceBaseIndicator A hA) (sourceBasis n),
    sourceBasis_coe n, sourceFiberIndicator_coe A hA n] with z hs hb hi
  rw [hs, hb, hi]
  by_cases ha : z.1 ∈ A <;> by_cases hn : z.2 = n <;> simp [sourceBaseIndicator, ha, hn]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiberEnergy
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem source_norm_sq_integrable (f : SourceHilbert SourceCoordinate) :
    Integrable (fun z => ‖f z‖ ^ 2) (sourceMeasure SourceCoordinate) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

theorem sourceFiberEnergy_integrable (f : SourceHilbert SourceCoordinate) :
    Integrable (sourceFiberEnergy f) sourceBaseMeasure :=
  (source_norm_sq_integrable f).integral_prod_left

theorem source_norm_sq_integral (f : SourceHilbert SourceCoordinate) :
    ‖f‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂sourceMeasure SourceCoordinate := by
  calc
    ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := InnerProductSpace.norm_sq_eq_re_inner f
    _ = ∫ z, RCLike.re (inner ℂ (f z) (f z)) ∂sourceMeasure SourceCoordinate :=
      (integral_re (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = _ := by simp_rw [← InnerProductSpace.norm_sq_eq_re_inner]

theorem source_norm_sq_energy (f : SourceHilbert SourceCoordinate) :
    ‖f‖ ^ 2 = ∫ x, sourceFiberEnergy f x ∂sourceBaseMeasure := by
  rw [source_norm_sq_integral, integral_prod _ (source_norm_sq_integrable f)]
  rfl

/-- Measurable localization commutes with taking the squared fiber norm. -/
theorem sourceFiberEnergy_indicator (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (f : SourceHilbert SourceCoordinate) :
    sourceFiberEnergy (sourceScalar (sourceBaseIndicator A hA) f) =ᵐ[sourceBaseMeasure]
      A.indicator (sourceFiberEnergy f) := by
  filter_upwards [source_ae_all_fibers
    (sourceScalar_apply_ae (sourceBaseIndicator A hA) f)] with x hx
  unfold sourceFiberEnergy
  by_cases ha : x ∈ A
  · simp only [Set.indicator_of_mem ha]
    apply integral_congr_ae
    exact Eventually.of_forall fun n => by dsimp only; rw [hx]; simp [sourceBaseIndicator, ha]
  · simp only [Set.indicator_of_notMem ha]
    have he : (fun n : ℤ => ‖(sourceScalar (sourceBaseIndicator A hA) f) (x,n)‖ ^ 2) =
        fun _ => (0 : ℝ) := by
      funext n
      rw [hx]
      simp [sourceBaseIndicator, ha]
    rw [he, integral_zero]

theorem sourceScalar_indicator_norm_sq (A : Set (SourceCoordinate → ℝ))
    (hA : MeasurableSet A) (f : SourceHilbert SourceCoordinate) :
    ‖sourceScalar (sourceBaseIndicator A hA) f‖ ^ 2 =
      ∫ x in A, sourceFiberEnergy f x ∂sourceBaseMeasure := by
  rw [source_norm_sq_energy, integral_congr_ae (sourceFiberEnergy_indicator A hA f),
    integral_indicator hA]

theorem sourceAlgebra_fiberEnergy_le (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceFiberEnergy (H f) x ≤ ‖H‖ ^ 2 * sourceFiberEnergy f x := by
  apply ae_le_of_forall_setIntegral_le (sourceFiberEnergy_integrable (H f))
    ((sourceFiberEnergy_integrable f).const_mul (‖H‖ ^ 2))
  intro A hA _
  rw [← sourceScalar_indicator_norm_sq A hA, integral_const_mul,
    ← sourceScalar_indicator_norm_sq A hA]
  have he : sourceScalar (sourceBaseIndicator A hA) (H f) =
      H (sourceScalar (sourceBaseIndicator A hA) f) :=
    congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate => T f)
      (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))
  rw [he]
  have hb := H.le_opNorm (sourceScalar (sourceBaseIndicator A hA) f)
  have hn := norm_nonneg (H (sourceScalar (sourceBaseIndicator A hA) f))
  have hp := mul_nonneg (norm_nonneg H)
    (norm_nonneg (sourceScalar (sourceBaseIndicator A hA) f))
  nlinarith [sq_nonneg (‖H‖ * ‖sourceScalar (sourceBaseIndicator A hA) f‖ -
    ‖H (sourceScalar (sourceBaseIndicator A hA) f)‖)]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiniteVectors
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceHilbert_sum_coe {ι : Type*} (s : Finset ι)
    (f : ι → SourceHilbert SourceCoordinate) :
    ⇑(∑ i ∈ s, f i : SourceHilbert SourceCoordinate) =ᵐ[sourceMeasure SourceCoordinate] fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 (sourceMeasure SourceCoordinate)] with z hz
    exact hz
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with z ha hs
    simp only [ha, Pi.add_apply, hs]

theorem sourceFiniteVector_coe (s : Finset ℤ) (a : ℤ → ℂ) :
    sourceFiniteVector s a =ᵐ[sourceMeasure SourceCoordinate]
      fun z => if z.2 ∈ s then a z.2 else 0 := by
  have hs : ∀ᵐ z ∂sourceMeasure SourceCoordinate, ∀ n : ℤ,
      (a n • sourceBasis n) z = a n * (if z.2 = n then 1 else 0) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (a n) (sourceBasis n), sourceBasis_coe n] with z hc hb
    simp only [hc, Pi.smul_apply, smul_eq_mul, hb]
  filter_upwards [sourceHilbert_sum_coe s (fun n => a n • sourceBasis n), hs] with z hz hs
  change (∑ n ∈ s, a n • sourceBasis n) z = _
  rw [hz]
  simp_rw [hs, mul_ite, mul_one, mul_zero]
  simp

theorem sourceFiniteVector_image_coe
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (s : Finset ℤ) (a : ℤ → ℂ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      (H (sourceFiniteVector s a)) (x,k) = ∑ n ∈ s, a n * sourceMatrixEntry H k n x := by
  have hs : ∀ᵐ z ∂sourceMeasure SourceCoordinate, ∀ n : ℤ,
      (a n • H (sourceBasis n)) z = a n * (H (sourceBasis n)) z := by
    rw [ae_all_iff]
    intro n
    exact Lp.coeFn_smul (a n) (H (sourceBasis n))
  have he : H (sourceFiniteVector s a) = ∑ n ∈ s, a n • H (sourceBasis n) := by
    simp [sourceFiniteVector]
  rw [he]
  filter_upwards [source_ae_all_fibers (sourceHilbert_sum_coe s (fun n => a n • H (sourceBasis n))),
    source_ae_all_fibers hs] with x he hs k
  rw [he]
  exact Finset.sum_congr rfl fun n _ => hs k n

theorem sourceFiniteVector_energy (s : Finset ℤ) (a : ℤ → ℂ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceFiberEnergy (sourceFiniteVector s a) x = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  filter_upwards [source_ae_all_fibers (sourceFiniteVector_coe s a)] with x hx
  unfold sourceFiberEnergy
  have he : (fun n : ℤ => ‖(sourceFiniteVector s a) (x,n)‖ ^ 2) =
      (s : Set ℤ).indicator (fun n => ‖a n‖ ^ 2) := by
    funext n
    rw [hx]
    by_cases hn : n ∈ s <;> simp [hn]
  rw [he, integral_indicator s.measurableSet, setIntegral_finset]
  · simp [measureReal_def]
  · rw [← (s : Set ℤ).biUnion_of_singleton]
    simp [integrableOn_finset_iUnion, integrableOn_singleton_iff]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Bounds
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Continuity in a separable parameter lets a countable dense family of
almost-everywhere inequalities determine every parameter on one conull set. -/
theorem ae_forall_le_of_continuous {X E : Type*} [MeasurableSpace X]
    (μ : Measure X) [TopologicalSpace E] [TopologicalSpace.SeparableSpace E]
    (f g : E → X → ℝ) (hf : ∀ x, Continuous (fun e => f e x))
    (hg : ∀ x, Continuous (fun e => g e x))
    (h : ∀ e, ∀ᵐ x ∂μ, f e x ≤ g e x) :
    ∀ᵐ x ∂μ, ∀ e, f e x ≤ g e x := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense E
  have hs : ∀ᵐ x ∂μ, ∀ e ∈ s, f e x ≤ g e x :=
    (ae_ball_iff hsc).mpr fun e _ => h e
  filter_upwards [hs] with x hx e
  exact le_on_closure hx (hf x).continuousOn (hg x).continuousOn (hsd e)

theorem sourceFiberEnergy_finite_le (f : SourceHilbert SourceCoordinate) (s : Finset ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∑ n ∈ s, ‖f (x,n)‖ ^ 2 ≤ sourceFiberEnergy f x := by
  filter_upwards [(source_norm_sq_integrable f).prod_right_ae] with x hx
  have h := setIntegral_le_integral (μ := Measure.count) (s := (s : Set ℤ))
    hx (Eventually.of_forall fun n => sq_nonneg ‖f (x,n)‖)
  rw [setIntegral_finset s hx.integrableOn] at h
  simpa [measureReal_def, sourceFiberEnergy] using h

/-- Each finite scalar matrix compression satisfies the actual operator norm bound. -/
theorem sourceMatrix_finite_bound (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (s t : Finset ℤ) (a : ℤ → ℂ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2) ≤
        ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  filter_upwards [sourceFiniteVector_image_coe H s a,
    sourceFiniteVector_energy s a,
    sourceFiberEnergy_finite_le (H (sourceFiniteVector s a)) t,
    sourceAlgebra_fiberEnergy_le θ hH (sourceFiniteVector s a)] with x hc he hf hh
  calc
    _ = ∑ k ∈ t, ‖(H (sourceFiniteVector s a)) (x,k)‖ ^ 2 := by simp_rw [hc]
    _ ≤ sourceFiberEnergy (H (sourceFiniteVector s a)) x := hf
    _ ≤ ‖H‖ ^ 2 * sourceFiberEnergy (sourceFiniteVector s a) x := hh
    _ = _ := by rw [he]

/-- One conull set works for every complex finite input vector and every finite
output truncation. No field or boundedness hypothesis has been substituted. -/
theorem sourceMatrix_finite_bound_all (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ (s t : Finset ℤ) (a : ℤ → ℂ),
      (∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2) ≤
        ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  rw [ae_all_iff]
  intro s
  rw [ae_all_iff]
  intro t
  apply ae_forall_le_of_continuous (E := ℤ → ℂ) sourceBaseMeasure
    (fun a x => ∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2)
    (fun a _ => ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2)
  · intro x; fun_prop
  · intro x; fun_prop
  · exact sourceMatrix_finite_bound θ hH s t

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Integrals
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

theorem source_fiber_restrict (A : Set (SourceCoordinate → ℝ)) (n : ℤ) :
    (sourceMeasure SourceCoordinate).restrict (A ×ˢ {n}) =
      (sourceBaseMeasure.restrict A).map (fun x => (x,n)) := by
  rw [← Measure.prod_restrict]
  simp only [Measure.restrict_singleton, Measure.count_singleton, one_smul]
  exact Measure.prod_dirac _

theorem source_fiber_integral (f : SourceHilbert SourceCoordinate)
    (A : Set (SourceCoordinate → ℝ)) (n : ℤ) :
    ∫ z in A ×ˢ {n}, f z ∂sourceMeasure SourceCoordinate =
      ∫ x in A, f (x,n) ∂sourceBaseMeasure := by
  rw [source_fiber_restrict]
  exact integral_map (measurable_id.prodMk measurable_const).aemeasurable
    (Lp.stronglyMeasurable f).aestronglyMeasurable

theorem source_fiber_integrable (f : SourceHilbert SourceCoordinate) (n : ℤ) :
    Integrable (fun x => f (x,n)) sourceBaseMeasure := by
  have hi := integrableOn_Lp_of_measure_ne_top f (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (sourceFiberMeasure_ne_top Set.univ n)
  rw [IntegrableOn, source_fiber_restrict, Measure.restrict_univ] at hi
  exact (integrable_map_measure (Lp.stronglyMeasurable f).aestronglyMeasurable
    (measurable_id.prodMk measurable_const).aemeasurable).mp hi

theorem sourceMatrixEntry_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Measurable (sourceMatrixEntry H k n) :=
  (Lp.stronglyMeasurable (H (sourceBasis n))).measurable.comp
    (measurable_id.prodMk measurable_const)

theorem sourceMatrixEntry_integrable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Integrable (sourceMatrixEntry H k n) sourceBaseMeasure :=
  source_fiber_integrable _ _

theorem sourceMatrixEntry_setIntegral
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (k n : ℤ) :
    ∫ x in A, sourceMatrixEntry H k n x ∂sourceBaseMeasure =
      inner ℂ (sourceFiberIndicator A hA k) (H (sourceBasis n)) := by
  rw [sourceFiberIndicator, L2.inner_indicatorConstLp_one, source_fiber_integral]
  rfl

/-- The displayed trace integral is the actual previously proved normal state. -/
theorem sourceVacuumFunctional_matrixIntegral
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    sourceVacuumFunctional H = ∫ x, sourceMatrixEntry H 0 0 x ∂sourceBaseMeasure := by
  rw [← setIntegral_univ, sourceMatrixEntry_setIntegral H Set.univ MeasurableSet.univ]
  rfl

/-- Adjoint matrix coefficients agree almost everywhere, on the actual source base. -/
theorem sourceMatrixEntry_star (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (k n : ℤ) :
    sourceMatrixEntry (star H) k n =ᵐ[sourceBaseMeasure]
      fun x => star (sourceMatrixEntry H n k x) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (sourceMatrixEntry_integrable _ _ _)
    (Complex.conjCLE.integrable_comp_iff.mpr (sourceMatrixEntry_integrable H n k))
  intro A hA _
  change (∫ x in A, sourceMatrixEntry (star H) k n x ∂sourceBaseMeasure) =
    ∫ x in A, conj (sourceMatrixEntry H n k x) ∂sourceBaseMeasure
  rw [sourceMatrixEntry_setIntegral _ A hA, integral_conj, sourceMatrixEntry_setIntegral _ A hA,
    inner_conj_symm]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have he : H (sourceFiberIndicator A hA k) =
      sourceScalar (sourceBaseIndicator A hA) (H (sourceBasis k)) := by
    rw [← sourceScalar_indicator_basis]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceBasis k)) (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))).symm
  rw [he]
  have hs : star (sourceScalar (sourceBaseIndicator A hA)) =
      sourceScalar (sourceBaseIndicator A hA) := by
    rw [sourceScalar_star]
    congr 1
    unfold sourceBaseStar sourceBaseIndicator
    congr 1
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    hs, sourceScalar_indicator_basis]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OperatorField
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceFieldGoodSet_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    MeasurableSet (sourceFieldGoodSet H) := (measurableSet_toMeasurable _ _).compl

theorem sourceFieldGoodSet_ae (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) : ∀ᵐ x ∂sourceBaseMeasure, x ∈ sourceFieldGoodSet H := by
  have hb : ∀ᵐ x ∂sourceBaseMeasure, sourceMatrixGood H x := sourceMatrix_finite_bound_all θ hH
  rw [ae_iff] at hb ⊢
  simpa [sourceFieldGoodSet, measure_toMeasurable] using hb

theorem sourceOperatorField_entry
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) (x) :
    (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k =
      (sourceFieldGoodSet H).indicator (sourceMatrixEntry H k n) x := by
  classical
  unfold sourceOperatorField
  split_ifs with hx
  · rw [Set.indicator_of_mem hx]
    exact boundedMatrixOperator_entry _ _ _ (norm_nonneg H) k n
  · simp [hx]

theorem sourceOperatorField_entry_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Measurable (fun x => (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k) := by
  simp_rw [sourceOperatorField_entry]
  exact (sourceMatrixEntry_measurable H k n).indicator (sourceFieldGoodSet_measurable H)

/-- Field entries recover the original coefficients on one conull set. -/
theorem sourceOperatorField_entries_ae (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k n : ℤ,
      (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k = sourceMatrixEntry H k n x := by
  filter_upwards [sourceFieldGoodSet_ae θ hH] with x hx k n
  rw [sourceOperatorField_entry, Set.indicator_of_mem hx]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Action
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceFiberInner_integrable (f g : SourceHilbert SourceCoordinate) :
    Integrable (sourceFiberInner f g) sourceBaseMeasure :=
  (L2.integrable_inner (𝕜 := ℂ) f g).integral_prod_left

theorem source_inner_fiber (f g : SourceHilbert SourceCoordinate) :
    inner ℂ f g = ∫ x, sourceFiberInner f g x ∂sourceBaseMeasure :=
  integral_prod _ (L2.integrable_inner (𝕜 := ℂ) f g)

theorem sourceScalar_indicator_inner (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (f g : SourceHilbert SourceCoordinate) :
    inner ℂ (sourceScalar (sourceBaseIndicator A hA) f) g =
      ∫ x in A, sourceFiberInner f g x ∂sourceBaseMeasure := by
  rw [source_inner_fiber, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [source_ae_all_fibers (sourceScalar_apply_ae (sourceBaseIndicator A hA) f)] with x hx
  unfold sourceFiberInner
  by_cases ha : x ∈ A
  · simp only [Set.indicator_of_mem ha]
    apply integral_congr_ae
    exact Eventually.of_forall fun n => by dsimp only; rw [hx]; simp [sourceBaseIndicator, ha]
  · simp only [Set.indicator_of_notMem ha]
    have he : (fun n : ℤ => inner ℂ ((sourceScalar (sourceBaseIndicator A hA) f) (x,n)) (g (x,n))) =
        fun _ => (0 : ℂ) := by
      funext n
      rw [hx]
      simp [sourceBaseIndicator, ha]
    rw [he, integral_zero]

/-- The scalar distribution identity determining every output coordinate of H. -/
theorem source_coordinate_action_inner (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    (fun x => (H f) (x,k)) =ᵐ[sourceBaseMeasure]
      sourceFiberInner ((star H) (sourceBasis k)) f := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (source_fiber_integrable _ _)
    (sourceFiberInner_integrable _ _)
  intro A hA _
  rw [← source_fiber_integral, ← L2.inner_indicatorConstLp_one]
  change inner ℂ (sourceFiberIndicator A hA k) (H f) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint]
  have he : (star H) (sourceFiberIndicator A hA k) =
      sourceScalar (sourceBaseIndicator A hA) ((star H) (sourceBasis k)) := by
    rw [← sourceScalar_indicator_basis]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceBasis k)) (sourceAlgebra_commutes_scalar θ (star_mem hH)
      (sourceBaseIndicator A hA))).symm
  rw [he, sourceScalar_indicator_inner]

/-- Actual action on arbitrary L2 input, expressed through the constructed
matrix entries. The counting integral is an absolutely convergent series a.e. -/
theorem sourceMatrix_action (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    (fun x => (H f) (x,k)) =ᵐ[sourceBaseMeasure]
      fun x => ∫ n : ℤ, sourceMatrixEntry H k n x * f (x,n) ∂Measure.count := by
  have hs : ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ,
      sourceMatrixEntry (star H) n k x = star (sourceMatrixEntry H k n x) := by
    rw [ae_all_iff]
    intro n
    exact sourceMatrixEntry_star θ hH n k
  filter_upwards [source_coordinate_action_inner θ hH f k, hs] with x hx hs
  rw [hx]
  unfold sourceFiberInner
  apply integral_congr_ae
  exact Eventually.of_forall fun n => by
    change inner ℂ (sourceMatrixEntry (star H) n k x) (f (x,n)) = _
    rw [hs]
    simp [RCLike.inner_apply, mul_comm]

/-- The matrix action is absolutely integrable over the counting measure. -/
theorem sourceMatrix_action_integrable (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      Integrable (fun n : ℤ => sourceMatrixEntry H k n x * f (x,n)) Measure.count := by
  have hs : ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ,
      sourceMatrixEntry (star H) n k x = star (sourceMatrixEntry H k n x) := by
    rw [ae_all_iff]
    intro n
    exact sourceMatrixEntry_star θ hH n k
  filter_upwards [(L2.integrable_inner (𝕜 := ℂ) ((star H) (sourceBasis k)) f).prod_right_ae,
    hs] with x hi hs
  apply hi.congr
  exact Eventually.of_forall fun n => by
    change inner ℂ (sourceMatrixEntry (star H) n k x) (f (x,n)) = _
    rw [hs]
    simp [RCLike.inner_apply, mul_comm]

theorem sourceMatrix_action_tsum (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (H f) (x,k) = ∑' n : ℤ, sourceMatrixEntry H k n x * f (x,n) := by
  filter_upwards [sourceMatrix_action θ hH f k, sourceMatrix_action_integrable θ hH f k]
    with x hx hi
  rw [hx, integral_countable hi]
  simp [measureReal_def]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FieldRepresentation
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Fubini puts almost every actual L2 section in l2(Z). -/
theorem source_fiber_memℓp (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure, Memℓp (fun n : ℤ => f (x,n)) 2 := by
  filter_upwards [(source_norm_sq_integrable f).prod_right_ae] with x hx
  apply memℓp_gen
  have hs := integrable_count_iff.mp hx
  simpa only [norm_pow, norm_norm, ENNReal.toReal_ofNat, Real.rpow_two] using hs

theorem sourceFiberVector_coe (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ, sourceFiberVector f x n = f (x,n) := by
  filter_upwards [source_fiber_memℓp f] with x hx n
  simp [sourceFiberVector, hx]

/-- The constructed field acts as the original operator on every source L2
vector. Neither decomposability nor a replacement representation is assumed. -/
theorem sourceOperatorField_represents (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceFiberVector (H f) x = sourceOperatorField H x (sourceFiberVector f x) := by
  have ha : ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      (H f) (x,k) = ∑' n : ℤ, sourceMatrixEntry H k n x * f (x,n) := by
    rw [ae_all_iff]
    exact sourceMatrix_action_tsum θ hH f
  filter_upwards [sourceFiberVector_coe f, sourceFiberVector_coe (H f),
    sourceOperatorField_entries_ae θ hH, ha] with x hf hHf he ha
  apply Subtype.ext
  funext k
  rw [hHf, fiberOperator_action]
  simp_rw [he, hf]
  exact ha k

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FieldAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceFiberVector_basis (n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceFiberVector (sourceBasis n) x = lp.single 2 n (1 : ℂ) := by
  filter_upwards [sourceFiberVector_coe (sourceBasis n), source_ae_all_fibers (sourceBasis_coe n)]
    with x hf hb
  apply Subtype.ext
  funext k
  rw [hf, hb]
  by_cases hk : k = n
  · subst k; simp [lp.single_apply]
  · simp [lp.single_apply, hk]

theorem sourceOperatorField_mul (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A * B) x = sourceOperatorField A x * sourceOperatorField B x := by
  have h (n : ℤ) : ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A * B) x (lp.single 2 n (1 : ℂ)) =
        sourceOperatorField A x (sourceOperatorField B x (lp.single 2 n (1 : ℂ))) := by
    filter_upwards [sourceOperatorField_represents θ (mul_mem hA hB) (sourceBasis n),
      sourceOperatorField_represents θ hA (B (sourceBasis n)),
      sourceOperatorField_represents θ hB (sourceBasis n), sourceFiberVector_basis n]
      with x hab ha hb he
    rw [he] at hab hb
    change sourceFiberVector (A (B (sourceBasis n))) x = _ at hab
    rw [ha, hb] at hab
    exact hab.symm
  filter_upwards [ae_all_iff.mpr h] with x hx
  apply fiberOperator_ext
  intro k n
  exact congrArg (fun v : SourceFiberHilbert => v k) (hx n)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Covariance
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceCommutantRotation_basis (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    sourceCommutantRotation θ n (sourceBasis m) = sourceBasis (m+n) := by
  apply Lp.ext
  have hb := (sourceTransportIndex_preserving θ n n).quasiMeasurePreserving.ae
    (sourceBasis_coe m)
  filter_upwards [sourceTransport_apply_ae θ n n (sourceBasis m), hb,
    sourceBasis_coe (m+n)] with z ht hb he
  change (sourceTransport θ n n (sourceBasis m)) z = _
  rw [ht, hb, he]
  simp only [sourceTransportIndex]
  simp only [sub_eq_iff_eq_add]

/-- Matrix form of H(sigma^r x) = S^(-r) H(x) S^r, for the original
regular representation and every integer power of the base rotation. -/
theorem sourceMatrixEntry_covariance (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (r n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry H k n (coordinateRotate θ r x) =
        sourceMatrixEntry H (k+r) (n+r) x := by
  have he : H (sourceBasis (n+r)) = sourceCommutantRotation θ r (H (sourceBasis n)) := by
    rw [← sourceCommutantRotation_basis θ r n]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceBasis n)) (sourceAlgebra_commutes_rotation θ hH r)).symm
  have ht := source_ae_all_fibers (sourceTransport_apply_ae θ r r (H (sourceBasis n)))
  filter_upwards [ht] with x hx k
  unfold sourceMatrixEntry
  rw [he]
  change _ = (sourceTransport θ r r (H (sourceBasis n))) (x,k+r)
  rw [hx]
  simp [sourceTransportIndex]

/-- All countably many covariance identities hold on one conull base set. -/
theorem sourceMatrixEntry_covariance_all (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ r n k : ℤ,
      sourceMatrixEntry H k n (coordinateRotate θ r x) =
        sourceMatrixEntry H (k+r) (n+r) x := by
  rw [ae_all_iff]
  intro r
  rw [ae_all_iff]
  exact sourceMatrixEntry_covariance θ hH r

/-- Matrix entries of the actual multiplication generators. -/
theorem sourceMatrixEntry_pi (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) (n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry (sourcePi θ g) k n x =
        if k = n then g.toFun (coordinateRotate θ n x) else 0 := by
  filter_upwards [source_ae_all_fibers (sourcePi_apply_ae θ g (sourceBasis n)),
    source_ae_all_fibers (sourceBasis_coe n)] with x hp hb k
  unfold sourceMatrixEntry
  rw [hp, hb]
  by_cases hk : k = n <;> simp [hk, sourcePiSymbol]

/-- Matrix entries of the original fiber shift. -/
theorem sourceMatrixEntry_shift (n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry (sourceShift SourceCoordinate) k n x =
        if k = n+1 then 1 else 0 := by
  have hb := (sourceShiftIndex_preserving SourceCoordinate).quasiMeasurePreserving.ae
    (sourceBasis_coe n)
  filter_upwards [source_ae_all_fibers (sourceShift_apply_ae (sourceBasis n)),
    source_ae_all_fibers hb] with x hs hb k
  unfold sourceMatrixEntry
  rw [hs, hb]
  simp only [sourceShiftIndex]
  simp only [sub_eq_iff_eq_add]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_WeightedShiftField
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Covariance for the actual field's matrix, with all integer indices on one
conull set. This is the coordinate form of conjugation by the fiber shift. -/
theorem sourceOperatorField_covariance (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ r n k : ℤ,
      (sourceOperatorField H (coordinateRotate θ r x) (lp.single 2 n (1 : ℂ))) k =
        (sourceOperatorField H x (lp.single 2 (n+r) (1 : ℂ))) (k+r) := by
  have he : ∀ᵐ x ∂sourceBaseMeasure, ∀ r : ℤ, ∀ k n : ℤ,
      (sourceOperatorField H (coordinateRotate θ r x) (lp.single 2 n (1 : ℂ))) k =
        sourceMatrixEntry H k n (coordinateRotate θ r x) := by
    rw [ae_all_iff]
    intro r
    exact (coordinateRotate_preserving θ r).quasiMeasurePreserving.ae
      (sourceOperatorField_entries_ae θ hH)
  filter_upwards [he, sourceOperatorField_entries_ae θ hH,
    sourceMatrixEntry_covariance_all θ hH] with x he hx hc r n k
  rw [he, hx, hc]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CentralDiagonal
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceFirstMultiplier_distinct (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (x : SourceCoordinate → ℝ)
    (n k : ℤ) (hnk : n ≠ k) :
    sourceFirstMultiplier.toFun (coordinateRotate θ n x) ≠
      sourceFirstMultiplier.toFun (coordinateRotate θ k x) := by
  intro he
  have he' := Complex.ofReal_injective he
  change Int.fract (x sourceFirstCoordinate+(n : ℝ)*θ sourceFirstCoordinate) =
    Int.fract (x sourceFirstCoordinate+(k : ℝ)*θ sourceFirstCoordinate) at he'
  rw [Int.fract,Int.fract] at he'
  apply hr.mul_ne_integer sourceFirstCoordinate (n-k) (sub_ne_zero.mpr hnk)
    (Int.floor (x sourceFirstCoordinate+(n : ℝ)*θ sourceFirstCoordinate) -
      Int.floor (x sourceFirstCoordinate+(k : ℝ)*θ sourceFirstCoordinate))
  push_cast
  nlinarith

/-- The field of pi(g) has its actual diagonal action on every vector. -/
theorem sourceOperatorField_pi_action (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ (v : SourceFiberHilbert) (k : ℤ),
      sourceOperatorField (sourcePi θ g) x v k = g.toFun (coordinateRotate θ k x) * v k := by
  have hm := ae_all_iff.mpr (sourceMatrixEntry_pi θ g)
  filter_upwards [hm,sourceOperatorField_entries_ae θ (sourcePi_mem θ g)] with x hm he v k
  rw [fiberOperator_action]
  simp_rw [he,hm]
  have hs : (fun n : ℤ => (if k = n then g.toFun (coordinateRotate θ n x) else 0) * v n) =
      fun n => if n = k then g.toFun (coordinateRotate θ k x) * v k else 0 := by
    funext n
    by_cases hn : n = k
    · subst n; simp
    · simp [hn,Ne.symm hn]
  rw [hs]
  simp

/-- Commutation in the source algebra passes to the actual fields. -/
theorem sourceOperatorField_commute (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) (hAB : A*B = B*A) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField A x * sourceOperatorField B x =
      sourceOperatorField B x * sourceOperatorField A x := by
  filter_upwards [sourceOperatorField_mul θ hA hB,sourceOperatorField_mul θ hB hA] with x h₁ h₂
  rw [← h₁,← h₂,hAB]

/-- Distinct diagonal eigenvalues force every off-diagonal matrix coefficient
of a commuting bounded operator to vanish. -/
theorem fiber_commuting_diagonal_entry
    (A G : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (d : ℤ → ℂ)
    (hG : ∀ v k, G v k = d k * v k) (hAG : A*G = G*A)
    (n k : ℤ) (hd : d n ≠ d k) : A (lp.single 2 n (1 : ℂ)) k = 0 := by
  have hsingle : G (lp.single 2 n (1 : ℂ)) = d n • lp.single 2 n (1 : ℂ) := by
    classical
    apply Subtype.ext
    funext j
    change G (lp.single 2 n (1 : ℂ)) j = d n * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) j
    rw [hG]
    by_cases hj : n = j
    · subst j; rfl
    · simp [lp.single_apply,hj]
  have he := congrArg (fun T : SourceFiberHilbert →L[ℂ] SourceFiberHilbert =>
    T (lp.single 2 n (1 : ℂ)) k) hAG
  change A (G (lp.single 2 n (1 : ℂ))) k = G (A (lp.single 2 n (1 : ℂ))) k at he
  rw [hsingle,map_smul,hG] at he
  change d n * A (lp.single 2 n (1 : ℂ)) k = d k * A (lp.single 2 n (1 : ℂ)) k at he
  exact (mul_eq_mul_right_iff.mp he).resolve_left hd

theorem sourceCentral_offDiagonal_zero (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ)
    (hcentral : ∀ B ∈ sourceAlgebra θ, A*B = B*A) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n k : ℤ, n ≠ k →
      sourceOperatorField A x (lp.single 2 n (1 : ℂ)) k = 0 := by
  filter_upwards [sourceOperatorField_pi_action θ sourceFirstMultiplier,
    sourceOperatorField_commute θ hA (sourcePi_mem θ sourceFirstMultiplier)
      (hcentral _ (sourcePi_mem θ sourceFirstMultiplier))] with x hG hc n k hnk
  exact fiber_commuting_diagonal_entry _ _ _ hG hc n k (sourceFirstMultiplier_distinct θ hr x n k hnk)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_Shift
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped ENNReal
noncomputable section

theorem fiberShift_single (n m : ℤ) (c : ℂ) :
    fiberShift n (lp.single 2 m c) = lp.single 2 (m+n) c := by
  classical
  apply Subtype.ext
  funext k
  change (lp.single 2 m c : SourceFiberHilbert) (k-n) =
    (lp.single 2 (m+n) c : SourceFiberHilbert) k
  by_cases h : m = k-n
  · simp [lp.single_apply, h]
  · have hh : m+n ≠ k := by omega
    simp [lp.single_apply, h, hh]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CentralScalarField
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceOperatorField_shift (θ : SourceCoordinate → ℝ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField (sourceShift SourceCoordinate) x = fiberShift 1 := by
  classical
  have hm := ae_all_iff.mpr sourceMatrixEntry_shift
  filter_upwards [hm,sourceOperatorField_entries_ae θ (sourceShift_mem θ)] with x hm he
  apply fiberOperator_ext
  intro k n
  rw [he,hm]
  rw [fiberShift_single]
  by_cases hk : k = n+1
  · subst k; simp [lp.single_apply]
  · simp [lp.single_apply,hk]

/-- Commutation with the bilateral shift makes all diagonal coefficients equal. -/
theorem fiber_commuting_shift_diagonal (A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hc : A*fiberShift 1 = fiberShift 1*A) (n : ℤ) :
    A (lp.single 2 n (1 : ℂ)) n = A (lp.single 2 0 (1 : ℂ)) 0 := by
  have hperiod : Function.Periodic
      (fun k : ℤ => A (lp.single 2 k (1 : ℂ)) k) 1 := by
    intro k
    have he := congrArg (fun T : SourceFiberHilbert →L[ℂ] SourceFiberHilbert =>
      T (lp.single 2 k (1 : ℂ)) (k+1)) hc
    change A (fiberShift 1 (lp.single 2 k (1 : ℂ))) (k+1) =
      (fiberShift 1 (A (lp.single 2 k (1 : ℂ)))) (k+1) at he
    simpa only [fiberShift_single,fiberShift_apply,add_sub_cancel_right] using he
  simpa using hperiod.int_mul_eq n

theorem sourceCentralCoefficient_measurable
    (A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    Measurable (sourceCentralCoefficient A) := sourceOperatorField_entry_measurable A 0 0

/-- Every central element of the original algebra is a scalar field. The
scalar may still depend on x; ergodicity is needed to make it constant. -/
theorem sourceCentral_scalar_field (θ : SourceCoordinate → ℝ) (hr : SourceRationalIndependent θ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ)
    (hcentral : ∀ B ∈ sourceAlgebra θ, A*B = B*A) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField A x = sourceCentralCoefficient A x • (1 : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) := by
  filter_upwards [sourceCentral_offDiagonal_zero θ hr hA hcentral,sourceOperatorField_shift θ,
    sourceOperatorField_commute θ hA (sourceShift_mem θ) (hcentral _ (sourceShift_mem θ))]
    with x hd hs hc
  rw [hs] at hc
  apply fiberOperator_ext
  intro k n
  change sourceOperatorField A x (lp.single 2 n (1 : ℂ)) k =
    sourceCentralCoefficient A x * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) k
  by_cases hnk : n = k
  · subst k
    simpa [lp.single_apply,sourceCentralCoefficient] using fiber_commuting_shift_diagonal _ hc n
  · rw [hd n k hnk]
    simp [lp.single_apply,hnk]

/-- Covariance makes the actual scalar field invariant under every integer
rotation. No ergodicity hypothesis or constant-value conclusion is inserted. -/
theorem sourceCentralCoefficient_rotation_invariant
    (θ : SourceCoordinate → ℝ) (hr : SourceRationalIndependent θ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ)
    (hcentral : ∀ B ∈ sourceAlgebra θ, A*B = B*A) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ,
      sourceCentralCoefficient A (coordinateRotate θ n x) = sourceCentralCoefficient A x := by
  filter_upwards [sourceOperatorField_covariance θ hA,sourceCentral_scalar_field θ hr hA hcentral]
    with x hc hs n
  change sourceOperatorField A (coordinateRotate θ n x) (lp.single 2 0 (1 : ℂ)) 0 = _
  rw [hc,zero_add,hs]
  change sourceCentralCoefficient A x * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) n = _
  simp [lp.single_apply]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiberSeparable
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Set TopologicalSpace
noncomputable section

/-- Separability of the actual l2(Z) fiber, from its countable coordinate basis. -/
instance sourceFiber_separable : TopologicalSpace.SeparableSpace SourceFiberHilbert := by
  let b : ℤ → SourceFiberHilbert := fun n => lp.single 2 n (1 : ℂ)
  let S := Submodule.span ℂ (Set.range b)
  have hmem (a : ℤ →₀ ℂ) : fiberFiniteEmbedding a ∈ S := by
    change (∑ n ∈ a.support, a n • b n) ∈ S
    exact Submodule.sum_mem S fun n _ => Submodule.smul_mem S (a n) (Submodule.subset_span ⟨n,rfl⟩)
  have hd : Dense (S : Set SourceFiberHilbert) := by
    intro x
    exact closure_mono (by rintro _ ⟨a,rfl⟩; exact hmem a) (fiberFiniteEmbedding_dense x)
  have hs : IsSeparable (closure (S : Set SourceFiberHilbert)) :=
    (Set.countable_range b).isSeparable.span.closure
  rw [hd.closure_eq] at hs
  exact isSeparable_univ_iff.mp hs

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Measures
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

theorem sourceSamplingHaar_cube : ∀ᵐ x ∂sourceSamplingHaar,
    ∀ i : SourceCoordinate, x i ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  have hh : ∀ᵐ t ∂sourceSamplingHaar.map (fun x => x i), t ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Measure.infinitePi_map_eval]
    exact ae_restrict_mem measurableSet_Ico
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ico).mp hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusModel
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

theorem sourceTorusRepresentative_preserving :
    MeasurePreserving sourceTorusRepresentative sourceTorusHaar sourceSamplingHaar := by
  refine ⟨Measurable.of_eval (fun i => sourceCircleRepresentative_measurable.comp (measurable_pi_apply i)),?_⟩
  unfold sourceTorusRepresentative
  rw [Measure.infinitePi_map_pi _ (fun _ => sourceCircleRepresentative_measurable)]
  simp only [sourceCircleRepresentative_preserving.map_eq]

theorem sourceTorusQuotient_representative (z : SourceTorus) :
    sourceTorusQuotient (sourceTorusRepresentative z) = z := by
  funext i
  exact (AddCircle.equivIco 1 0).symm_apply_apply (z i)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusCharacters
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set Algebra Submodule
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceCharacterAlgebra_span :
    sourceCharacterAlgebra.toSubalgebra.toSubmodule = span ℂ (range sourceCharacter) := by
  apply adjoin_eq_span_of_subset
  refine .trans (fun x => Submonoid.closure_induction (fun _ => id) ⟨0,sourceCharacter_zero⟩ ?_) subset_span
  rintro _ _ _ _ ⟨v,rfl⟩ ⟨w,rfl⟩
  exact ⟨v+w,sourceCharacter_add v w⟩

theorem sourceCharacter_single (i : SourceCoordinate) (x : SourceTorus) :
    sourceCharacter (Finsupp.single i 1) x = fourier 1 (x i) := by
  simp [sourceCharacter, Finsupp.sum_single_index]

theorem sourceCharacterAlgebra_separates : sourceCharacterAlgebra.SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_,⟨sourceCharacter (Finsupp.single i 1),subset_adjoin ⟨_,rfl⟩,rfl⟩,?_⟩
  dsimp only
  rw [sourceCharacter_single,sourceCharacter_single,fourier_one,fourier_one,Ne,Circle.coe_inj]
  exact fun he => hi (AddCircle.injective_toCircle one_ne_zero he)

/-- Uniform density on the full countable product, with no finite-dimensional truncation assumption. -/
theorem sourceCharacter_span_dense :
    (span ℂ (range sourceCharacter)).topologicalClosure = ⊤ := by
  rw [← sourceCharacterAlgebra_span]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      sourceCharacterAlgebra_separates)

theorem sourceCharacterL2_span_dense :
    (span ℂ (range sourceCharacterL2)).topologicalClosure = ⊤ := by
  simpa only [map_span,ContinuousLinearMap.coe_coe,← range_comp,Function.comp_def] using
    (ContinuousMap.toLp_denseRange ℂ sourceTorusHaar ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).topologicalClosure_map_submodule
      sourceCharacter_span_dense

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusRotation
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceCharacter_translate (v : SourceCoordinate →₀ ℤ) (x y : SourceTorus) :
    sourceCharacter v (x+y) = sourceCharacter v x * sourceCharacter v y := by
  simp only [sourceCharacter, ContinuousMap.coe_mk,Pi.add_apply,smul_add,Finsupp.sum,
    Finset.sum_add_distrib]
  simp [fourier,AddCircle.toCircle_add]

/-- Rational independence rules out every nonconstant character eigenvalue 1. -/
theorem sourceCharacter_nonresonant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (v : SourceCoordinate →₀ ℤ) (hv : v ≠ 0) :
    sourceCharacter v (sourceTorusQuotient θ) ≠ 1 := by
  intro h
  have hz : v.sum (fun i n => n • (θ i : UnitAddCircle)) = 0 := by
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa [sourceCharacter,fourier,sourceTorusQuotient] using h
  have he : ((v.sum fun i n => (n : ℝ)*θ i : ℝ) : UnitAddCircle) =
      v.sum (fun i n => n • (θ i : UnitAddCircle)) := by
    unfold Finsupp.sum
    induction v.support using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi,AddCircle.coe_add,ih]
      congr 1
      simpa only [zsmul_eq_mul] using (AddCircle.coe_zsmul (1 : ℝ) (n := v i) (x := θ i))
  rw [← he,AddCircle.coe_eq_zero_iff] at hz
  obtain ⟨c,hc⟩ := hz
  exact hv (hr v c (by simpa using hc.symm)).1

theorem sourceCharacterL2_rotation (θ : SourceCoordinate → ℝ) (v : SourceCoordinate →₀ ℤ) :
    Lp.compMeasurePreserving (sourceTorusRotationStep θ) (sourceTorusRotationStep_preserving θ)
      (sourceCharacterL2 v) = sourceCharacter v (sourceTorusQuotient θ) • sourceCharacterL2 v := by
  apply Lp.ext
  have he := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ℝ≥0∞)) sourceTorusHaar (sourceCharacter v)
  filter_upwards [Lp.coeFn_compMeasurePreserving (sourceCharacterL2 v) (sourceTorusRotationStep_preserving θ),
    (sourceTorusRotationStep_preserving θ).quasiMeasurePreserving.ae he,he,
    Lp.coeFn_smul (sourceCharacter v (sourceTorusQuotient θ)) (sourceCharacterL2 v)]
    with x hc ht hx hs
  rw [hc,Function.comp_apply,ht,hs,Pi.smul_apply,smul_eq_mul,hx]
  exact (sourceCharacter_translate v x (sourceTorusQuotient θ)).trans (mul_comm _ _)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusErgodic
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set Submodule
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceCharacterL2_zero_inner :
    inner ℂ (sourceCharacterL2 0) (sourceCharacterL2 0) = 1 := by
  rw [ContinuousMap.inner_toLp]
  simp [sourceCharacter_zero]

theorem sourceRotationL2_zero_character (θ : SourceCoordinate → ℝ) :
    sourceRotationL2 θ (sourceCharacterL2 0) = sourceCharacterL2 0 := by
  change Lp.compMeasurePreserving _ _ _ = _
  rw [sourceCharacterL2_rotation,sourceCharacter_zero]
  simp

/-- An invariant vector orthogonal to the constant character is zero. -/
theorem sourceRotationL2_fixed_orthogonal_zero (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (f : Lp ℂ 2 sourceTorusHaar)
    (hf : sourceRotationL2 θ f = f) (h0 : inner ℂ (sourceCharacterL2 0) f = 0) : f = 0 := by
  have hchar (v : SourceCoordinate →₀ ℤ) : inner ℂ f (sourceCharacterL2 v) = 0 := by
    by_cases hv : v = 0
    · subst v
      exact inner_eq_zero_symm.mpr h0
    · have he := (sourceRotationL2 θ).inner_map_map f (sourceCharacterL2 v)
      rw [hf] at he
      change inner ℂ f (Lp.compMeasurePreserving _ _ _) = _ at he
      rw [sourceCharacterL2_rotation,inner_smul_right] at he
      have hn := sourceCharacter_nonresonant θ hr v hv
      by_contra hz
      exact hn (mul_right_cancel₀ hz (he.trans (one_mul _).symm))
  have hs : span ℂ (range sourceCharacterL2) ≤ (innerSL ℂ f).ker := by
    apply span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact hchar v
  have ht : (span ℂ (range sourceCharacterL2)).topologicalClosure ≤ (innerSL ℂ f).ker :=
    Submodule.topologicalClosure_minimal _ hs (innerSL ℂ f).isClosed_ker
  rw [sourceCharacterL2_span_dense] at ht
  have hh : inner ℂ f f = 0 := ht (show f ∈ (⊤ : Submodule ℂ (Lp ℂ 2 sourceTorusHaar)) from trivial)
  exact inner_self_eq_zero.mp hh

theorem sourceRotationL2_fixed_constant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (f : Lp ℂ 2 sourceTorusHaar)
    (hf : sourceRotationL2 θ f = f) :
    ∃ c : ℂ, f = c • sourceCharacterL2 0 := by
  let c := inner ℂ (sourceCharacterL2 0) f
  refine ⟨c,sub_eq_zero.mp (sourceRotationL2_fixed_orthogonal_zero θ hr
    (f-c • sourceCharacterL2 0) ?_ ?_)⟩
  · rw [map_sub,map_smul,hf,sourceRotationL2_zero_character]
  · rw [inner_sub_right,inner_smul_right,sourceCharacterL2_zero_inner,mul_one]
    exact sub_self _

theorem sourceTorus_invariant_memLp_constant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) {f : SourceTorus → ℂ}
    (hf : MemLp f 2 sourceTorusHaar)
    (hinv : f ∘ sourceTorusRotationStep θ =ᵐ[sourceTorusHaar] f) :
    ∃ c : ℂ, f =ᵐ[sourceTorusHaar] fun _ => c := by
  have hfix : sourceRotationL2 θ (hf.toLp f) = hf.toLp f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (hf.toLp f) (sourceTorusRotationStep_preserving θ),
      (sourceTorusRotationStep_preserving θ).quasiMeasurePreserving.ae hf.coeFn_toLp,
      hf.coeFn_toLp,hinv] with x hc ht hx hi
    exact hc.trans (ht.trans (hi.trans hx.symm))
  obtain ⟨c,hc⟩ := sourceRotationL2_fixed_constant θ hr (hf.toLp f) hfix
  refine ⟨c,?_⟩
  have he := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ℝ≥0∞)) sourceTorusHaar (sourceCharacter 0)
  filter_upwards [hf.coeFn_toLp,Lp.coeFn_smul c (sourceCharacterL2 0),he] with x hx hs he
  rw [hc,hs,Pi.smul_apply,smul_eq_mul,he,sourceCharacter_zero] at hx
  simpa using hx.symm

/-- Ergodicity of the constructed countable-torus rotation itself. -/
theorem sourceTorusRotationStep_ergodic (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) : Ergodic (sourceTorusRotationStep θ) sourceTorusHaar := by
  classical
  refine ⟨sourceTorusRotationStep_preserving θ,⟨fun s hs hi => ?_⟩⟩
  have hm : MemLp (s.indicator (fun _ : SourceTorus => (1 : ℂ))) 2 sourceTorusHaar :=
    (memLp_const (1 : ℂ)).indicator hs
  have hinv : (s.indicator (fun _ : SourceTorus => (1 : ℂ))) ∘ sourceTorusRotationStep θ =ᵐ[sourceTorusHaar]
      s.indicator (fun _ : SourceTorus => (1 : ℂ)) := by
    apply Eventually.of_forall
    intro x
    have hh : sourceTorusRotationStep θ x ∈ s ↔ x ∈ s := by
      change x ∈ (sourceTorusRotationStep θ) ⁻¹' s ↔ x ∈ s
      rw [hi]
    by_cases hx : x ∈ s
    · simp [Function.comp_apply,hx,hh.mpr hx]
    · have ht : sourceTorusRotationStep θ x ∉ s := fun h => hx (hh.mp h)
      simp [Function.comp_apply,hx,ht]
  obtain ⟨c,hc⟩ := sourceTorus_invariant_memLp_constant θ hr hm hinv
  rw [Filter.eventuallyConst_set']
  by_cases h1 : c = 1
  · right
    filter_upwards [hc] with x hx
    apply propext
    show x ∈ s ↔ x ∈ (Set.univ : Set SourceTorus)
    by_cases hxs : x ∈ s
    · simp [hxs]
    · simp [hxs,h1] at hx
  · left
    filter_upwards [hc] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs] at hx
      exact (h1 hx.symm).elim
    · apply propext
      show x ∈ s ↔ x ∈ (∅ : Set SourceTorus)
      simp [hxs]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_RotationErgodic
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceTorusRepresentative_rotationStep (θ : SourceCoordinate → ℝ) (z : SourceTorus) :
    sourceTorusRepresentative (sourceTorusRotationStep θ z) =
      coordinateRotate θ 1 (sourceTorusRepresentative z) := by
  funext i
  have hz : ((sourceTorusRepresentative z i : ℝ) : UnitAddCircle) = z i :=
    congrFun (sourceTorusQuotient_representative z) i
  change sourceCircleRepresentative (z i + (θ i : UnitAddCircle)) =
    Int.fract (sourceTorusRepresentative z i + (1 : ℤ) * θ i)
  rw [← hz,← AddCircle.coe_add,sourceCircleRepresentative_coe]
  norm_num

/-- Ergodicity for the exact real-coordinate model used by the original algebra. -/
theorem coordinateRotate_ergodic (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) :
    Ergodic (coordinateRotate θ 1) sourceSamplingHaar :=
  sourceTorusRepresentative_preserving.ergodic_of_ergodic_semiconj
    (sourceTorusRotationStep_ergodic θ hr) (coordinateRotate_preserving θ 1).measurable
    (sourceTorusRepresentative_rotationStep θ)

theorem sourceRotation_invariant_constant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) {f : (SourceCoordinate → ℝ) → ℂ}
    (hf : Measurable f) (hi : f ∘ coordinateRotate θ 1 =ᵐ[sourceSamplingHaar] f) :
    ∃ c : ℂ, f =ᵐ[sourceSamplingHaar] fun _ => c :=
  (coordinateRotate_ergodic θ hr).ae_eq_const_of_ae_eq_comp₀ hf.nullMeasurable hi

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ScalarCenter
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Constancy of the representing field is equality of the original operators. -/
theorem sourceOperator_eq_scalar_of_field (θ : SourceCoordinate → ℝ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (c : ℂ)
    (hc : ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField A x =
      c • (1 : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)) :
    A = c • (1 : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) := by
  apply ContinuousLinearMap.ext
  intro f
  change A f = c • f
  apply Lp.ext
  have he : ∀ᵐ z ∂sourceMeasure SourceCoordinate, (A f) z = c * f z := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (Lp.stronglyMeasurable (A f)).measurable
        (measurable_const.mul (Lp.stronglyMeasurable f).measurable))).mpr
    filter_upwards [sourceOperatorField_represents θ hA f,sourceFiberVector_coe (A f),
      sourceFiberVector_coe f,hc] with x ha hAf hf hx
    apply Eventually.of_forall
    intro k
    have hk := congrArg (fun v : SourceFiberHilbert => v k) ha
    rw [hx] at hk
    change sourceFiberVector (A f) x k = c * sourceFiberVector f x k at hk
    simpa only [hAf,hf,Pi.mul_apply] using hk
  filter_upwards [he,Lp.coeFn_smul c f] with z hz hs
  simpa only [hs,Pi.smul_apply,smul_eq_mul] using hz

theorem sourceCentralCoefficient_constant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hcentral : ∀ B ∈ sourceAlgebra θ, A*B = B*A) :
    ∃ c : ℂ, sourceCentralCoefficient A =ᵐ[sourceBaseMeasure] fun _ => c := by
  apply sourceRotation_invariant_constant θ hr (sourceCentralCoefficient_measurable A)
  filter_upwards [sourceCentralCoefficient_rotation_invariant θ hr hA hcentral] with x hx
  exact hx 1

theorem sourceAlgebra_hasScalarCenter (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) : HasScalarCenter (sourceAlgebra θ) := by
  intro A hA hcentral
  obtain ⟨c,hc⟩ := sourceCentralCoefficient_constant θ hr hA hcentral
  refine ⟨c,sourceOperator_eq_scalar_of_field θ hA c ?_⟩
  filter_upwards [sourceCentral_scalar_field θ hr hA hcentral,hc] with x hx hc
  rw [hx,hc]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_SmallPartitionSets
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem unitInterval_partition_unique (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
    ∃! j : Fin n, t ∈ Set.Ico ((j : ℝ)/(n : ℝ)) (((j : ℝ)+1)/(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnt : 0 ≤ (n : ℝ)*t := mul_nonneg hnR.le ht.1
  have hlt : Nat.floor ((n : ℝ)*t) < n :=
    (Nat.floor_lt hnt).mpr (by nlinarith [ht.2])
  let k : Fin n := ⟨Nat.floor ((n : ℝ)*t),hlt⟩
  have he (j : Fin n) : t ∈ Set.Ico ((j : ℝ)/(n : ℝ)) (((j : ℝ)+1)/(n : ℝ)) ↔
      Nat.floor ((n : ℝ)*t) = j.val := by
    rw [Nat.floor_eq_iff hnt]
    change _ ≤ t ∧ t < _ ↔ _ ≤ _ ∧ _ < _
    rw [div_le_iff₀ hnR,lt_div_iff₀ hnR]
    simp only [mul_comm]
  refine ⟨k,(he k).mpr rfl,?_⟩
  intro j hj
  exact Fin.ext ((he j).mp hj).symm

theorem sourceSmallPartition_indicator_sum (n : ℕ) (hn : 0 < n)
    (x : SourceCoordinate → ℝ) (hx : x sourceFirstCoordinate ∈ Set.Ico 0 1) :
    ∑ j : Fin n, (sourceSmallPartitionSet n j).indicator (fun _ => (1 : ℂ)) x = 1 := by
  classical
  obtain ⟨k,hk,hunique⟩ := unitInterval_partition_unique n hn (x sourceFirstCoordinate) hx
  have hk' : x ∈ sourceSmallPartitionSet n k := hk
  rw [Finset.sum_eq_single k]
  · exact Set.indicator_of_mem hk' _
  · intro j _ hj
    exact Set.indicator_of_notMem (s := sourceSmallPartitionSet n j) (a := x)
      (fun h => hj (hunique j h)) (fun _ => (1 : ℂ))
  · simp

/-- Every cell has mass at most 1/n under the actual product Haar measure. -/
theorem sourceSmallPartitionSet_measure_le (n : ℕ) (_hn : 0 < n) (j : Fin n) :
    sourceSamplingHaar (sourceSmallPartitionSet n j) ≤ ENNReal.ofReal (1/(n : ℝ)) := by
  change sourceSamplingHaar ((fun x => x sourceFirstCoordinate) ⁻¹'
    Set.Ico ((j : ℝ)/(n : ℝ)) (((j : ℝ)+1)/(n : ℝ))) ≤ _
  rw [← Measure.map_apply (measurable_pi_apply sourceFirstCoordinate) measurableSet_Ico,
    Measure.infinitePi_map_eval]
  calc
    unitIntervalMeasure _ ≤ volume (Set.Ico ((j : ℝ)/(n : ℝ)) (((j : ℝ)+1)/(n : ℝ))) :=
      Measure.restrict_apply_le _ _
    _ = _ := by
      rw [Real.volume_Ico]
      congr 1
      ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_IndicatorProjection
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceIndicatorProjection_mem (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    sourceIndicatorProjection θ A hA ∈ sourceAlgebra θ := sourcePi_mem θ _

theorem sourceIndicatorProjection_projection (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    IsStarProjection (sourceIndicatorProjection θ A hA) := by
  classical
  let g := sourceBaseIndicator A hA
  constructor
  · apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [sourcePi_apply_ae θ g (sourcePi θ g f),sourcePi_apply_ae θ g f] with z hh hf
    change (sourcePi θ g (sourcePi θ g f)) z = (sourcePi θ g f) z
    rw [hh,hf]
    by_cases hz : coordinateRotate θ z.2 z.1 ∈ A <;> simp [sourcePiSymbol,g,sourceBaseIndicator,hz]
  · change star (sourcePi θ g) = sourcePi θ g
    rw [sourcePi_star]
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [sourcePi_apply_ae θ (sourceBaseStar g) f,sourcePi_apply_ae θ g f] with z hs hf
    rw [hs,hf]
    by_cases hz : coordinateRotate θ z.2 z.1 ∈ A <;> simp [sourcePiSymbol,sourceBaseStar,g,sourceBaseIndicator,hz]

/-- The projection's trace is the measure of its original base event. -/
theorem sourceIndicatorProjection_trace (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    sourceVacuumFunctional (sourceIndicatorProjection θ A hA) =
      ((sourceBaseMeasure A).toReal : ℂ) := by
  rw [sourceVacuumFunctional_matrixIntegral]
  have he : sourceMatrixEntry (sourceIndicatorProjection θ A hA) 0 0 =ᵐ[sourceBaseMeasure]
      A.indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [sourceMatrixEntry_pi θ (sourceBaseIndicator A hA) 0,sourceSamplingHaar_cube] with x hx hc
    have hr : coordinateRotate θ 0 x = x := by
      funext i
      simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
    simpa [sourceIndicatorProjection,sourceBaseIndicator,hr] using hx 0
  rw [integral_congr_ae he,integral_indicator hA]
  simp [measureReal_def]

/-- A genuine finite partition of the identity inside the original algebra. -/
theorem sourceIndicatorProjection_partition_sum (θ : SourceCoordinate → ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ j : Fin n, sourceIndicatorProjection θ (sourceSmallPartitionSet n j)
      (sourceSmallPartitionSet_measurable n j)) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change (∑ j : Fin n, sourceIndicatorProjection θ (sourceSmallPartitionSet n j)
      (sourceSmallPartitionSet_measurable n j)) f = f
  rw [sum_apply]
  apply Lp.ext
  have hall := ae_all_iff.mpr (fun j : Fin n =>
    sourcePi_apply_ae θ (sourceBaseIndicator (sourceSmallPartitionSet n j)
      (sourceSmallPartitionSet_measurable n j)) f)
  filter_upwards [sourceHilbert_sum_coe Finset.univ (fun j : Fin n =>
    sourceIndicatorProjection θ (sourceSmallPartitionSet n j) (sourceSmallPartitionSet_measurable n j) f),hall]
    with z hs ha
  rw [hs]
  change (∑ j : Fin n, (sourcePi θ (sourceBaseIndicator (sourceSmallPartitionSet n j)
    (sourceSmallPartitionSet_measurable n j)) f) z) = f z
  simp_rw [ha]
  change (∑ j : Fin n, (sourceSmallPartitionSet n j).indicator (fun _ => (1 : ℂ))
    (coordinateRotate θ z.2 z.1) * f z) = f z
  rw [← Finset.sum_mul,sourceSmallPartition_indicator_sum n hn _
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩,one_mul]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Diffuse_OperatorCesaro
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma pow_norm_le_one [CompleteSpace H] (S : H →L[ℂ] H) (hS : ‖S‖≤1) (k : ℕ) : ‖S^k‖≤1 :=
by
  induction k with
  | zero =>
    rw [pow_zero]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  | succ k ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (S^k),norm_nonneg S])

lemma cesaro_norm_le_one (S : H →L[ℂ] H) (hS : ‖S‖≤1) (n : ℕ) : ‖cesaro S n‖≤1 := by
  have hn : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hs : ‖∑ k ∈ Finset.range (n+1), S^k‖≤(n+1:ℕ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), ‖S^k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (n+1), (1:ℝ) := Finset.sum_le_sum (fun k _ => pow_norm_le_one S hS k)
      _ = _ := by simp
  rw [cesaro,norm_smul,norm_inv]
  simp only [Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)).trans_eq (inv_mul_cancel₀ hn.ne')

lemma cesaro_apply_norm_le (S : H →L[ℂ] H) (hS : ‖S‖≤1) (n : ℕ) (x : H) :
    ‖cesaro S n x‖≤‖x‖ :=
  ((cesaro S n).le_opNorm x).trans (by nlinarith [cesaro_norm_le_one S hS n,norm_nonneg x])

omit [CompleteSpace H] in
lemma cesaro_mul_sub [CompleteSpace H] (S : H →L[ℂ] H) (n : ℕ) :
    cesaro S n*(1-S)=((n+1:ℕ):ℂ)⁻¹ • (1-S^(n+1)) := by
  rw [cesaro,smul_mul_assoc,geom_sum_mul_neg]

lemma cesaro_range_bound (S : H →L[ℂ] H) (hS : ‖S‖≤1) (n : ℕ) (x : H) :
    ‖cesaro S n ((1-S) x)‖≤((n+1:ℕ):ℝ)⁻¹*(2*‖x‖) := by
  have hn : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hp : ‖(S^(n+1)) x‖≤‖x‖ :=
    ((S^(n+1)).le_opNorm x).trans (by nlinarith [pow_norm_le_one S hS (n+1),norm_nonneg x])
  have he := congrArg (fun T:H→L[ℂ]H => T x) (cesaro_mul_sub S n)
  simp only [mul_apply_eq_comp,smul_apply] at he
  rw [he,norm_smul,norm_inv]
  simp only [Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
  change ‖x-(S^(n+1)) x‖≤_
  exact (norm_sub_le _ _).trans (by linarith)

lemma cesaro_on_range (S : H →L[ℂ] H) (hS : ‖S‖≤1) (x : H) :
    Tendsto (fun n => cesaro S n ((1-S) x)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).mul_const (2*‖x‖)
  simp only [zero_mul,one_div] at ht
  apply squeeze_zero (fun n=>norm_nonneg _) (cesaro_range_bound S hS · x)
  simpa only [Nat.cast_add,Nat.cast_one] using ht

end Nonhyperlinear.Diffuseness

end

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Diffuse_OperatorMeanErgodic
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cesaro_on_closedRange (S : H →L[ℂ] H) (hS : ‖S‖≤1) (x : H)
    (hx : x∈(1-S).range.topologicalClosure) :
    Tendsto (fun n=>cesaro S n x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hcl : x∈closure ((1-S).range : Set H) := hx
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hcl (ε/2) (by positivity)
  obtain ⟨z,rfl⟩ := hy
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (cesaro_on_range S hS z) (ε/2) (by positivity)
  refine ⟨N,fun n hn=>?_⟩
  rw [dist_zero_right]
  have he : cesaro S n x = cesaro S n (x-(1-S) z)+cesaro S n ((1-S) z) := by
    rw [map_sub]; abel
  rw [he]
  have hh := hN n hn
  rw [dist_zero_right] at hh
  rw [dist_eq_norm] at hxy
  change ‖x-(1-S) z‖<ε/2 at hxy
  exact (norm_add_le _ _).trans_lt (by linarith [cesaro_apply_norm_le S hS n (x-(1-S) z)])

omit [CompleteSpace H] in
lemma cesaro_fixed [CompleteSpace H] (S : H →L[ℂ] H) (n : ℕ) (x : H) (hx : S x=x) :
    cesaro S n x=x := by
  have hp : ∀k:ℕ,(S^k) x=x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ',mul_apply_eq_comp,ih,hx]
  simp only [cesaro,smul_apply,sum_apply,hp,
    Finset.sum_const,Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n),one_smul]

/-- The Hilbert mean ergodic theorem for a selfadjoint contraction, proved
using telescoping on the dense range and the fixed-space orthogonal projection. -/
theorem cesaro_tendsto_fixedProjection (S : H →L[ℂ] H)
    (hS : ‖S‖≤1) (hstar : star S=S) (x : H) :
    Tendsto (fun n=>cesaro S n x) atTop (𝓝 ((1-S).ker.starProjection x)) := by
  let K := (1-S).ker
  let : CompleteSpace K := (1-S).isClosed_ker.completeSpace_coe
  have hP : S (K.starProjection x)=K.starProjection x := by
    have h := K.starProjection_apply_mem x
    change (K.starProjection x)-S (K.starProjection x)=0 at h
    exact (sub_eq_zero.mp h).symm
  have hk : Kᗮ=(1-S).range.topologicalClosure := by
    have hh := ContinuousLinearMap.orthogonal_ker (1-S)
    rw [←ContinuousLinearMap.star_eq_adjoint] at hh
    simpa only [star_sub,star_one,hstar] using hh
  have hr : x-K.starProjection x∈(1-S).range.topologicalClosure := by
    rw [←hk]
    exact K.sub_starProjection_mem_orthogonal x
  have ht := (cesaro_on_closedRange S hS (x-K.starProjection x) hr).add_const (K.starProjection x)
  simp only [zero_add] at ht
  convert ht using 1
  funext n
  rw [map_sub,cesaro_fixed S n _ hP,sub_add_cancel]

end Nonhyperlinear.Diffuseness

end

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Diffuse_OperatorSupport
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma rangeSupport_projection (T : H →L[ℂ] H) : IsStarProjection (rangeSupport T) :=
  isStarProjection_starProjection

lemma rangeSupport_range (T : H →L[ℂ] H) :
    (rangeSupport T).range=T.range.topologicalClosure :=
  Submodule.range_starProjection _

lemma rangeSupport_mul_self (T : H →L[ℂ] H) : rangeSupport T*T=T := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact Submodule.le_topologicalClosure _ ⟨x,rfl⟩

lemma rangeSupport_ne_zero {T : H →L[ℂ] H} (hT:T≠0) : rangeSupport T≠0 := by
  intro h
  have he:=rangeSupport_mul_self T
  rw [h,zero_mul] at he
  exact hT he.symm

/-- Closed range support belongs to the same concrete von Neumann algebra. -/
theorem rangeSupport_mem (M : VonNeumannAlgebra H) {T:H→L[ℂ]H} (hT:T∈M) :
    rangeSupport T∈M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff (rangeSupport_projection T) M).mpr
  intro y hy
  rw [rangeSupport_range]
  apply Submodule.topologicalClosure_mem_invtSubmodule
  intro x hx
  obtain ⟨z,rfl⟩:=hx
  refine ⟨y z,?_⟩
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp hy T hT
  exact congrArg (fun A:H→L[ℂ]H=>A z) hc

lemma projection_mul_rangeSupport {p T:H→L[ℂ]H} (hp:IsStarProjection p) (h:p*T=T) :
    p*rangeSupport T=rangeSupport T := by
  have hs : Set.EqOn p id (T.range:Set H) := by
    rintro _ ⟨x,rfl⟩
    have hx : T x ∈ p.range := ⟨T x, congrArg (fun A:H→L[ℂ]H=>A x) h⟩
    obtain ⟨y,hy⟩ := hx
    change p (T x) = T x
    rw [← hy]
    exact congrArg (fun A:H→L[ℂ]H=>A y) hp.isIdempotentElem.eq
  have hc : Set.EqOn p id (closure (T.range:Set H)) :=
    hs.closure p.continuous continuous_id
  ext x
  exact hc (T.range.topologicalClosure.starProjection_apply_mem x)

lemma rangeSupport_mul_projection {p T:H→L[ℂ]H} (hp:IsStarProjection p) (h:p*T=T) :
    rangeSupport T*p=rangeSupport T := by
  have he:=congrArg star (projection_mul_rangeSupport hp h)
  simpa only [star_mul,hp.isSelfAdjoint.star_eq,(rangeSupport_projection T).isSelfAdjoint.star_eq] using he

end Nonhyperlinear.Diffuseness

end

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Diffuse_ProjectionTrace
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projection_vector_trace (v:H) {p:H→L[ℂ]H} (hp:IsStarProjection p) :
    inner ℂ v (p v)=(‖p v‖:ℂ)^2 := by
  have he : (star p)*(p)=p := by rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  calc
    inner ℂ v (p v)=inner ℂ v ((star p) (p v)) := congrArg (fun A:H→L[ℂ]H=>inner ℂ v (A v)) he.symm
    _ = _ := by
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
        inner_self_eq_norm_sq_to_K]
      norm_cast

lemma projection_vector_trace_nonneg (v:H) {p:H→L[ℂ]H} (hp:IsStarProjection p) :
    0≤(inner ℂ v (p v)).re := by
  rw [projection_vector_trace v hp]
  simp only [←Complex.ofReal_pow,Complex.ofReal_re]
  positivity

lemma projection_difference {p q:H→L[ℂ]H} (hp:IsStarProjection p) (hq:IsStarProjection q)
    (hqp:q*p=q) : IsStarProjection (p-q) := by
  have hpq:p*q=q := by
    have hh:=congrArg star hqp
    simpa only [star_mul,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq] using hh
  apply isStarProjection_iff'.mpr
  constructor
  · calc
      (p-q)*(p-q)=p*p-p*q-q*p+q*q := by noncomm_ring
      _ = p-q := by rw [hp.isIdempotentElem.eq,hq.isIdempotentElem.eq,hpq,hqp]; abel
  · simp only [star_sub,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq]

lemma projection_vector_trace_mono (v:H) {p q:H→L[ℂ]H}
    (hp:IsStarProjection p) (hq:IsStarProjection q) (hqp:q*p=q) :
    (inner ℂ v (q v)).re≤(inner ℂ v (p v)).re := by
  have hh:=projection_vector_trace_nonneg v (projection_difference hp hq hqp)
  change 0≤(inner ℂ v (p v-q v)).re at hh
  rw [inner_sub_right,Complex.sub_re] at hh
  linarith

end Nonhyperlinear.Diffuseness

end

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Diffuse_SupportLimit
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma one_sub_star_mul_contraction (T:H→L[ℂ]H) (hT:‖T‖≤1) :
    ‖1-star T*T‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x-(star T) (T x)‖≤1*‖x‖
  rw [one_mul]
  have ht : ‖star T‖≤1 := by simpa [ContinuousLinearMap.star_eq_adjoint] using hT
  have hb : ‖(star T) (T x)‖≤‖T x‖ := by
    calc
      _ ≤ ‖star T‖*‖T x‖ := (star T).le_opNorm _
      _ ≤ 1*‖T x‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ = _ := one_mul _
  have hi : RCLike.re (inner ℂ x ((star T) (T x)))=‖T x‖^2 := by
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜:=ℂ) _
  have he := norm_sub_sq (𝕜:=ℂ) x ((star T) (T x))
  rw [hi] at he
  nlinarith [norm_nonneg (x-(star T) (T x)),norm_nonneg x,norm_nonneg (T x),
    norm_nonneg ((star T) (T x))]

lemma rangeSupport_eq_one_sub_kernel (T:H→L[ℂ]H) :
    rangeSupport T=1-(star T).ker.starProjection := by
  have h := ContinuousLinearMap.orthogonal_ker (star T)
  rw [←ContinuousLinearMap.star_eq_adjoint,star_star] at h
  change T.range.topologicalClosure.starProjection = ContinuousLinearMap.id ℂ H - (star T).ker.starProjection
  simpa only [h] using (Submodule.starProjection_orthogonal (star T).ker)

lemma cesaro_star_mul_tendsto (T:H→L[ℂ]H) (hT:‖T‖≤1) (x:H) :
    Tendsto (fun n=>cesaro (1-star T*T) n x) atTop
      (𝓝 (T.ker.starProjection x)) := by
  have hstar : star (1-star T*T)=1-star T*T := by simp
  have hker : (1-(1-star T*T)).ker=T.ker := by
    rw [sub_sub_cancel]
    exact ContinuousLinearMap.ker_adjoint_comp_self T
  simpa only [hker] using cesaro_tendsto_fixedProjection (1-star T*T)
    (one_sub_star_mul_contraction T hT) hstar x

end Nonhyperlinear.Diffuseness

end

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Diffuse_TracePowers
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Nonhyperlinear.Diffuseness

/-- Cyclicity equates every polynomial defect moment; no spectral assumption is used. -/
theorem trace_defect_pow {A:Type*} [Ring A] [Algebra ℂ A]
    (f:A→ₗ[ℂ]ℂ) (hf:∀a b,f (a*b)=f (b*a)) (a b:A) (n:ℕ) :
    f ((1-a*b)^n)=f ((1-b*a)^n) := by
  have hsem : SemiconjBy b (1-a*b) (1-b*a) := by
    change b*(1-a*b)=(1-b*a)*b
    noncomm_ring
  induction n with
  | zero => simp
  | succ n ih =>
    have hp:= (hsem.pow_right n).eq
    have he : (1-a*b)^(n+1)=(1-a*b)^n-a*(b*(1-a*b)^n) := by
      rw [pow_succ']
      noncomm_ring
    have he' : (1-b*a)^(n+1)=(1-b*a)^n-((1-b*a)^n*b)*a := by
      rw [pow_succ]
      noncomm_ring
    rw [he,he',map_sub,map_sub,ih,hp,hf a]

end Nonhyperlinear.Diffuseness

end

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Diffuse_SupportTrace
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem support_trace_eq (M:VonNeumannAlgebra H) (v:H)
    (hcyclic:∀a b:M.toStarSubalgebra,
      inner ℂ v (((a*b:M.toStarSubalgebra):H→L[ℂ]H) v)=
      inner ℂ v (((b*a:M.toStarSubalgebra):H→L[ℂ]H) v))
    (T:M.toStarSubalgebra) (hT:‖(T:H→L[ℂ]H)‖≤1) :
    inner ℂ v (rangeSupport (T:H→L[ℂ]H) v)=
      inner ℂ v (rangeSupport (star (T:H→L[ℂ]H)) v) := by
  let t:H→L[ℂ]H := T
  let f:M.toStarSubalgebra→ₗ[ℂ]ℂ :=
    (vectorFunctional v).comp M.toStarSubalgebra.toSubmodule.subtype
  have hf : ∀a b,f (a*b)=f (b*a) := hcyclic
  have he : ∀n, inner ℂ v (cesaro (1-t*star t) n v)=
      inner ℂ v (cesaro (1-star t*t) n v) := by
    intro n
    change vectorFunctional v (cesaro (1-t*star t) n)=
      vectorFunctional v (cesaro (1-star t*t) n)
    simp only [cesaro,map_smul,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact trace_defect_pow f hf T (star T) k
  have hts : ‖star t‖≤1 := by simpa [t,ContinuousLinearMap.star_eq_adjoint] using hT
  have hl := Filter.Tendsto.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=v)) (cesaro_star_mul_tendsto (star t) hts v)
  have hr := Filter.Tendsto.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=v)) (cesaro_star_mul_tendsto t hT v)
  have hlim : inner ℂ v ((star t).ker.starProjection v)=
      inner ℂ v (t.ker.starProjection v) := by
    apply tendsto_nhds_unique hl
    apply hr.congr'
    exact Filter.Eventually.of_forall (fun n=>by simpa only [star_star] using (he n).symm)
  change inner ℂ v (rangeSupport t v)=inner ℂ v (rangeSupport (star t) v)
  rw [rangeSupport_eq_one_sub_kernel,rangeSupport_eq_one_sub_kernel,star_star]
  change inner ℂ v (v-(star t).ker.starProjection v)=inner ℂ v (v-t.ker.starProjection v)
  rw [inner_sub_right,inner_sub_right,hlim]

end Nonhyperlinear.Diffuseness

end

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Diffuse_SmallPartitions
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A faithful tracial concrete algebra with finite identity partitions of
arbitrarily small projection trace has no minimal projection. -/
theorem no_minimal_projection_of_small_partitions (M:VonNeumannAlgebra H) (v:H)
    (hcyclic:∀a b:M.toStarSubalgebra,
      inner ℂ v (((a*b:M.toStarSubalgebra):H→L[ℂ]H) v)=
      inner ℂ v (((b*a:M.toStarSubalgebra):H→L[ℂ]H) v))
    (hfaithful:∀T:M.toStarSubalgebra,(T:H→L[ℂ]H) v=0→T=0)
    (hpart:∀ε:ℝ,0<ε→∃n:ℕ,∃e:Fin n→M.toStarSubalgebra,
      (∀j,IsStarProjection (e j:H→L[ℂ]H)) ∧ (∑j,e j)=1 ∧
      ∀j,(inner ℂ v ((e j:H→L[ℂ]H) v)).re<ε)
    (p:M.toStarSubalgebra) (hps:star p=p) (hpi:p*p=p) (hp0:p≠0) :
    ∃q:M.toStarSubalgebra,star q=q ∧ q*q=q ∧ q≠0 ∧ q≠p ∧ q*p=q := by
  classical
  have hpp:IsStarProjection (p:H→L[ℂ]H) :=
    isStarProjection_iff'.mpr ⟨congrArg Subtype.val hpi,congrArg Subtype.val hps⟩
  have hpv:(p:H→L[ℂ]H) v≠0 := fun hz=>hp0 (hfaithful p hz)
  have htpos:0<(inner ℂ v ((p:H→L[ℂ]H) v)).re := by
    rw [projection_vector_trace v hpp]
    simp only [←Complex.ofReal_pow,Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hpv)
  obtain ⟨n,e,hep,hes,het⟩:=hpart _ htpos
  obtain ⟨j,hj⟩:∃j,p*e j≠0 := by
    by_contra hn
    have hh:∀j,p*e j=0 := by simpa only [not_exists,not_not] using hn
    apply hp0
    calc
      p=p*1 := (mul_one p).symm
      _=p*(∑j,e j) := by rw [hes]
      _=∑j,p*e j := Finset.mul_sum _ _ _
      _=0 := by simp [hh]
  by_contra hnone
  let T:H→L[ℂ]H := (p*e j:M.toStarSubalgebra)
  have hT0:T≠0 := fun hh=>hj (Subtype.ext hh)
  have hTnorm:‖T‖≤1 := by
    exact (norm_mul_le (p:H→L[ℂ]H) (e j:H→L[ℂ]H)).trans
      ((mul_le_mul (IsStarProjection.norm_le _ hpp) (IsStarProjection.norm_le _ (hep j))
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hpT:(p:H→L[ℂ]H)*T=T := by
    change ((p*p)*e j:M.toStarSubalgebra).val=(p*e j).val
    rw [hpi]
  let q:M.toStarSubalgebra := ⟨rangeSupport T,rangeSupport_mem M (p*e j).property⟩
  have hqp:q*p=q := Subtype.ext (rangeSupport_mul_projection hpp hpT)
  have hq0:q≠0 := fun hh=>rangeSupport_ne_zero hT0 (congrArg Subtype.val hh)
  have hqeq:q=p := by
    by_contra hh
    exact hnone ⟨q,Subtype.ext (rangeSupport_projection T).isSelfAdjoint.star_eq,
      Subtype.ext (rangeSupport_projection T).isIdempotentElem.eq,hq0,hh,hqp⟩
  have heT:(e j:H→L[ℂ]H)*star T=star T := by
    change (e j:H→L[ℂ]H)*star ((p:H→L[ℂ]H)*(e j:H→L[ℂ]H))=star ((p:H→L[ℂ]H)*(e j:H→L[ℂ]H))
    rw [star_mul,hpp.isSelfAdjoint.star_eq,(hep j).isSelfAdjoint.star_eq,←mul_assoc,
      (hep j).isIdempotentElem.eq]
  have hright:=rangeSupport_mul_projection (hep j) heT
  have hle:=projection_vector_trace_mono v (hep j) (rangeSupport_projection (star T)) hright
  have heq:=support_trace_eq M v hcyclic (p*e j) hTnorm
  have hleft:rangeSupport T=(p:H→L[ℂ]H) := congrArg Subtype.val hqeq
  change inner ℂ v (rangeSupport T v)=inner ℂ v (rangeSupport (star T) v) at heq
  rw [hleft] at heq
  rw [←heq] at hle
  exact (not_lt_of_ge hle) (het j)

end Nonhyperlinear.Diffuseness

end

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_NoMinimalProjection
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- The original algebra has identity partitions of arbitrarily small trace,
using equal intervals of its first Haar coordinate. -/
theorem sourceAlgebra_small_trace_partitions (θ : SourceCoordinate → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ e : Fin n → (sourceAlgebra θ).toStarSubalgebra,
      (∀ j, IsStarProjection (e j : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)) ∧
      (∑ j, e j) = 1 ∧
      ∀ j, (sourceVacuumFunctional (e j)).re < ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (1 : ℝ) (1/ε))
  have hnR : (0 : ℝ) < n := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hn)
  have hnN : 0 < n := by exact_mod_cast hnR
  have hsmall : 1/(n : ℝ) < ε := by
    have hh : 1 < (n : ℝ)*ε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn)
    exact (div_lt_iff₀ hnR).mpr (by nlinarith)
  let e : Fin n → (sourceAlgebra θ).toStarSubalgebra := fun j =>
    ⟨sourceIndicatorProjection θ (sourceSmallPartitionSet n j) (sourceSmallPartitionSet_measurable n j),
      sourceIndicatorProjection_mem θ _ _⟩
  refine ⟨n,e,fun j => sourceIndicatorProjection_projection θ _ _,?_,?_⟩
  · apply Subtype.ext
    simpa [e] using sourceIndicatorProjection_partition_sum θ n hnN
  · intro j
    change (sourceVacuumFunctional (sourceIndicatorProjection θ (sourceSmallPartitionSet n j)
      (sourceSmallPartitionSet_measurable n j))).re < ε
    rw [sourceIndicatorProjection_trace,Complex.ofReal_re]
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ 1/(n : ℝ))
      (sourceSmallPartitionSet_measure_le n hnN j)).trans_lt hsmall

/-- Actual nonzero proper subprojections of every nonzero projection in the
original algebra. The support construction is internal to this same algebra. -/
theorem sourceAlgebra_hasNoMinimalProjection (θ : SourceCoordinate → ℝ) :
    HasNoMinimalProjection (sourceAlgebra θ) := by
  intro p hp hproj hp0
  let p' : (sourceAlgebra θ).toStarSubalgebra := ⟨p,hp⟩
  obtain ⟨q,hqs,hqi,hq0,hqne,hqp⟩ :=
    Nonhyperlinear.Diffuseness.no_minimal_projection_of_small_partitions
      (sourceAlgebra θ) sourceVacuum
      (fun A B => sourceVacuumFunctional_tracial θ A.property B.property)
      (fun A hz => Subtype.ext (sourceVacuum_separating θ A.property hz))
      (sourceAlgebra_small_trace_partitions θ)
      p' (Subtype.ext hproj.isSelfAdjoint.star_eq) (Subtype.ext hproj.isIdempotentElem)
      (fun hz => hp0 (congrArg Subtype.val hz))
  refine ⟨q,q.property,⟨congrArg Subtype.val hqi,congrArg Subtype.val hqs⟩,?_,?_,congrArg Subtype.val hqp⟩
  · exact fun hz => hq0 (Subtype.ext hz)
  · exact fun hz => hqne (Subtype.ext hz)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_NormalFunctionalSpace
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open TopologicalSpace
noncomputable section

theorem sourceVectorFunctional_continuous (θ : SourceCoordinate → ℝ) :
    Continuous (fun z : SourceHilbert SourceCoordinate × SourceHilbert SourceCoordinate =>
      sourceVectorFunctional θ z.1 z.2) := by
  unfold sourceVectorFunctional
  fun_prop

instance sourceNormalFunctionalSpace_separable (θ : SourceCoordinate → ℝ) :
    SeparableSpace (sourceNormalFunctionalSpace θ) := by
  let : NormedAddCommGroup (StrongDual ℂ (SourceAlgebraSpace θ)) := inferInstance
  apply TopologicalSpace.IsSeparable.separableSpace
  change IsSeparable (closure (Submodule.span ℂ (Set.range
    (fun z : SourceHilbert SourceCoordinate × SourceHilbert SourceCoordinate =>
      sourceVectorFunctional θ z.1 z.2)) : Set (StrongDual ℂ (SourceAlgebraSpace θ))))
  exact (isSeparable_range (sourceVectorFunctional_continuous θ)).span.closure

instance sourceNormalPredualSpace_separable (θ : SourceCoordinate → ℝ) :
    SeparableSpace (SourceNormalPredualSpace θ) :=
  inferInstanceAs (SeparableSpace (sourceNormalFunctionalSpace θ))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PredualIdentification
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open TopologicalSpace
noncomputable section

theorem sourceAlgebra_hasSeparablePredual (θ : SourceCoordinate → ℝ) :
    HasSeparablePredual (sourceAlgebra θ) := by
  refine ⟨SourceNormalPredualSpace θ,inferInstance,inferInstance,inferInstance,inferInstance,?_⟩
  exact ⟨sourcePredualIdentification θ⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PreparedErgodic
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The actual source construction now includes proved ergodicity, scalar center,
finiteness and the exact separable predual. No minimal-projection or arbitrary
invariant-projection conclusion is asserted here. -/
theorem exists_source_prepared_ergodic : ∃ θ : SourceCoordinate → ℝ,
    SourceRationalIndependent θ ∧
    (∃ j : ℕ, SourceSecondPhasesFrom θ j) ∧
    SourceOrderedTorusSampling θ ∧
    Ergodic (coordinateRotate θ 1) sourceBaseMeasure ∧
    HasScalarCenter (sourceAlgebra θ) ∧
    IsFiniteAlgebra (sourceAlgebra θ) ∧
    HasSeparablePredual (sourceAlgebra θ) ∧
    ∃ hθ : SourceAngles θ,
      let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
      T ∈ sourceAlgebra θ ∧ T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
        Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  obtain ⟨θ,hr,hphase,hs,_hm,_hfree,hfinite,_htrace,hT⟩ := exists_source_prepared_finite
  exact ⟨θ,hr,hphase,hs,coordinateRotate_ergodic θ hr,sourceAlgebra_hasScalarCenter θ hr,
    hfinite,sourceAlgebra_hasSeparablePredual θ,hT⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PreparedFactor
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem exists_source_prepared_factor : ∃ θ : SourceCoordinate → ℝ,
    SourceRationalIndependent θ ∧
    (∃ j : ℕ, SourceSecondPhasesFrom θ j) ∧
    SourceOrderedTorusSampling θ ∧
    Ergodic (coordinateRotate θ 1) sourceBaseMeasure ∧
    HasScalarCenter (sourceAlgebra θ) ∧
    IsFiniteAlgebra (sourceAlgebra θ) ∧
    HasNoMinimalProjection (sourceAlgebra θ) ∧
    HasSeparablePredual (sourceAlgebra θ) ∧
    ∃ hθ : SourceAngles θ,
      let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
      T ∈ sourceAlgebra θ ∧ T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
        Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  obtain ⟨θ,hr,hphase,hs,he,hcenter,hfinite,hpredual,hT⟩ := exists_source_prepared_ergodic
  exact ⟨θ,hr,hphase,hs,he,hcenter,hfinite,sourceAlgebra_hasNoMinimalProjection θ,hpredual,hT⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem main_theorem_oai : MainTarget.{0} := by
  obtain ⟨θ,hr,hphase,hs,_he,hcenter,hfinite,hminimal,hpredual,hθ,hT,hT0,_hinj,_hcontract,hqn⟩ :=
    exists_source_prepared_factor
  refine ⟨SourceHilbert SourceCoordinate,inferInstance,inferInstance,inferInstance,sourceAlgebra θ,
    hcenter,hfinite,hminimal,hpredual,
    sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg,hT,hT0,hqn,?_⟩
  intro p hp hproj hinv
  exact sourceInvariantProjection_trivial θ hθ hr hs hphase hp hproj hinv

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.main_theorem_oai := @OAI.FiniteFactor.main_theorem_oai
