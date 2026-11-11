-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.correctedDdc_off_source_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:37:28.123232+00:00
-- url     : https://prove2.me/submissions/0d533a2d-eaf6-4c9b-b34f-67e83dedee0e

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc034
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_closedLift_scaled_basis_local_bound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_geometric_center_local_energy_two_jet
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_harmonic_schwartz_seminorm_bound

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JAction
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
namespace TamingCompatibility

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma invariantPart_add_antiInvariantPart (J : AlmostComplexStructure X) (α : TwoForm X) :
    invariantPart J α + antiInvariantPart J α = α := by
  unfold invariantPart antiInvariantPart
  module

end TamingCompatibility

open scoped Manifold ContDiff Topology
open Filter Set

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_VariationalResolvent
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped RealInnerProductSpace

namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

lemma mem_nullspace_iff (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) :
    f ∈ Fredholm.nullspace (resolvent i D hc) ↔ ∃ u : V, i u = f ∧ D u = 0 := by
  rw [Fredholm.mem_nullspace]
  constructor
  · intro hf
    refine ⟨weakSolution i D hc f, hf, ?_⟩
    have he := weakSolution_identity i D hc f (weakSolution i D hc f)
    change i (weakSolution i D hc f) = f at hf
    rw [hf] at he
    have hz : ⟪D (weakSolution i D hc f), D (weakSolution i D hc f)⟫ = 0 := by linarith
    exact inner_self_eq_zero.mp hz
  · rintro ⟨u, rfl, hu⟩
    have he : weakSolution i D hc (i u) = u := by
      apply hc.continuousLinearEquivOfBilin.injective
      apply ext_inner_right ℝ
      intro v
      rw [hc.continuousLinearEquivOfBilin_apply,
        hc.continuousLinearEquivOfBilin_apply, energy_apply, energy_apply,
        weakSolution_identity, hu, inner_zero_left, add_zero]
    change i (weakSolution i D hc (i u)) = i u
    rw [he]

end TamingCompatibility.Variational

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFredholm
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma mem_harmonicAnti (f : L2 A J α hs ht true) :
    f ∈ harmonicAnti A J α hs ht ↔ ∃ u : antiEnergy A J α hs ht,
      energyInclusion A J α hs ht u = f ∧ weakDelta A J α hs ht u = 0 :=
  Variational.mem_nullspace_iff (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (graphEnergy_coercive A J α hs ht) f

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma pairLinear_eq_make (p : A.centers) (a : smoothForms X 2) :
    pairLinear A J α ht D hD p a = ScalarPair.make
      (scalarSchwartz A J α ht D hD p a.val a.property 2)
      (scalarSchwartz A J α ht D hD p a.val a.property 3) := rfl
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [CompactSpace X] in
lemma scalar_eq_weight (p : A.centers) (a : TwoForm X) (j : Fin 4)
    {z : Space} (hz : z ∈ (D p).domain) :
    scalar A J α ht D p a j z = coordinateWeight A p z * rawScalar J α ht p.val (D p) a j z := by
  unfold scalar localizedFunction
  rw [indicator_of_mem hz,indicator_of_mem ((D p).domain_subset hz)]
  rfl

lemma realPairSchwartz_apply (p : A.centers) (a : smoothForms X 2) (z : Space) :
    realPairSchwartz A J α ht D hD p a z =
      EuclideanEnergy.pair (scalar A J α ht D p a.val 2 z) (scalar A J α ht D p a.val 3 z) := by
  ext i
  fin_cases i <;> simp [realPairSchwartz,pairLinear_eq_make,ScalarPair.make_apply,EuclideanEnergy.pair] <;> rfl

lemma realPairSchwartz_raw (p : A.centers) (a : smoothForms X 2)
    {z : Space} (hz : z ∈ (D p).domain) :
    realPairSchwartz A J α ht D hD p a z =
      coordinateWeight A p z • rawPair J α ht p.val (D p) a.val z := by
  rw [realPairSchwartz_apply,scalar_eq_weight A J α ht D p a.val 2 hz,
    scalar_eq_weight A J α ht D p a.val 3 hz]
  ext i
  fin_cases i <;> rfl

lemma cutoff_realPair_raw (p : A.centers) (a : smoothForms X 2) (τ : 𝓢(Space,ℝ))
    {z : Space} (hz : z ∈ (D p).domain) (hτ : τ z * coordinateWeight A p z = 1) :
    SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p a) z =
      rawPair J α ht p.val (D p) a.val z := by
  rw [SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth]
  rw [realPairSchwartz_raw A J α ht D hD p a hz,smul_smul,hτ,one_smul]
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothUnitEvaluation
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility
open Bundle Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]
attribute [local instance] unitMeasurable unitBorel 

lemma eval_antiInvariantPart_complexLine (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (v : TangentSpace Model x) :
    eval (antiInvariantPart J α) x v (J.endomorphism x v) = 0 := by
  have h := congrArg (fun β => eval β x v (J.endomorphism x v))
    (invariantPart_add_antiInvariantPart J α)
  change eval (invariantPart J α) x v (J.endomorphism x v) +
    eval (antiInvariantPart J α) x v (J.endomorphism x v) = _ at h
  rw [eval_invariantPart_complexLine] at h
  linarith

end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedLiftData
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma closedLiftOfInverse_apply
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) :
    (closedLiftOfInverse A J α hs ht H Gs f).val =
      (fun a b : TwoForm X => a+b) (exteriorDerivative (codifferential J α ht (Gs f).val.val)) (H f).val.val := rfl

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma closedLiftOfInverse_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) (x : X) (v : TangentSpace Model x) :
    eval (closedLiftOfInverse A J α hs ht H Gs f).val x v (J.endomorphism x v) =
      eval (exteriorDerivative (codifferential J α ht (Gs f).val.val)) x v (J.endomorphism x v) := by
  rw [closedLiftOfInverse_apply]
  change eval (exteriorDerivative (codifferential J α ht (Gs f).val.val)) x v (J.endomorphism x v) +
    eval (H f).val.val x v (J.endomorphism x v) = _
  rw [← (H f).property,eval_antiInvariantPart_complexLine,add_zero]

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma closedLiftOfInverse_pullback_sub
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) (p : X) (z : Space) :
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val (extChartAt Model p).symm z -
      ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p).symm z =
      ManifoldForms.pullback (exteriorDerivative (codifferential J α ht (Gs f).val.val))
        (extChartAt Model p).symm z := by
  rw [closedLiftOfInverse_apply,ManifoldForms.pullback_add]
  exact add_sub_cancel_right _ _
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalDDStarEstimate
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume GeometricAdjoint
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma weightedRawRHS_spec (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (f : antiPre A J α hs ht) {z : Space} (hz : z ∈ (D p).domain)
    (hτ : τ z * coordinateWeight A p z = 1) (hρ : ρ z = chartDensity J α p.val z) :
    weightedRawRHS A J α hs ht D hD p τ ρ f z =
      (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z := by
  simp only [weightedRawRHS,smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply ρ.hasTemperateGrowth,
    cutoff_realPair_raw A J α ht D hD p f.val τ hz hτ,hρ,smul_smul]

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ShrinkingCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open Set Filter
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma normalizedCutoff_apply (L : E ≃L[ℝ] E) (q y : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) : normalizedCutoff L q r hr χ y = χ (r⁻¹ • L y - r⁻¹ • L q) := by
  rw [normalizedCutoff,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    affineSchwartz_apply,sub_eq_add_neg]

lemma normalizedCutoff_support (L : E ≃L[ℝ] E) (q : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) : tsupport (normalizedCutoff L q r hr χ) ⊆
      (fun y => r⁻¹ • L y - r⁻¹ • L q) ⁻¹' tsupport χ := by
  apply closure_minimal ?_ ((isClosed_tsupport _).preimage (by fun_prop))
  intro y hy
  apply subset_tsupport χ
  simpa only [Function.mem_support,normalizedCutoff_apply] using hy

lemma normalizedCutoff_eventually_support (L : E ≃L[ℝ] E) (q₀ : E)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    {W : Set E} (hW : IsOpen W) (hq : q₀ ∈ W) :
    ∀ᶠ t : ℝ × E in 𝓝 (0,q₀), ∀ hr : t.1 ≠ 0,
      tsupport (normalizedCutoff L t.2 t.1 hr χ) ⊆ W := by
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hW q₀ hq
  obtain ⟨R,hR⟩ := hχ.exists_bound_of_continuousOn (f := fun x : E => x) continuous_id.continuousOn
  let B := max R 0
  have hB : 0 ≤ B := le_max_right _ _
  have hc : Continuous (fun t : ℝ × E => ‖t.2-q₀‖+|t.1| *‖(L.symm : E →L[ℝ] E)‖*B) := by fun_prop
  have ht : ∀ᶠ t : ℝ × E in 𝓝 (0,q₀), ‖t.2-q₀‖+|t.1| *‖(L.symm : E →L[ℝ] E)‖*B < δ :=
    (isOpen_lt hc continuous_const).mem_nhds (by simpa using hδ)
  filter_upwards [ht] with t ht
  intro hr y hy
  let z := t.1⁻¹ • L y - t.1⁻¹ • L t.2
  have hz : z ∈ tsupport χ := normalizedCutoff_support L t.2 t.1 hr χ hy
  have hze : ‖z‖ ≤ B := (hR z hz).trans (le_max_left _ _)
  have he : y-t.2 = t.1 • L.symm z := by
    apply L.injective
    simp only [map_sub,map_smul,ContinuousLinearEquiv.apply_symm_apply,z,
      smul_sub,smul_smul,mul_inv_cancel₀ hr,one_smul]
  have hnorm : ‖y-t.2‖ ≤ |t.1| *‖(L.symm : E →L[ℝ] E)‖*B := by
    rw [he,norm_smul,Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left ((L.symm : E →L[ℝ] E).le_opNorm z) (abs_nonneg _)).trans
    calc
      _ ≤ |t.1| *(‖(L.symm : E →L[ℝ] E)‖*B) := by gcongr
      _ = _ := by ring
  apply hball
  rw [Metric.mem_ball,dist_eq_norm]
  calc
    ‖y-q₀‖ = ‖(y-t.2)+(t.2-q₀)‖ := by congr 1; abel
    _ ≤ ‖y-t.2‖+‖t.2-q₀‖ := norm_add_le _ _
    _ ≤ |t.1| *‖(L.symm : E →L[ℝ] E)‖*B+‖t.2-q₀‖ := add_le_add hnorm le_rfl
    _ < δ := by linarith
end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HarmonicSeminormBound
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

include hD in
lemma harmonic_schwartz_derivative_bound
    (F₀ : antiPre A J α hs ht →ₗ[ℝ] 𝓢(E,F)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ∀ n ≤ N, ∀ v : Fin n → E, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (F₀ h)) x‖ ≤ C * ‖smoothL2 A J α hs ht true f.val‖ := by
  classical
  choose C hC hb using fun n => harmonic_schwartz_seminorm_bound A J α hs ht D hD F₀ 0 n
  refine ⟨∑ n ∈ Finset.range (N+1), C n,Finset.sum_nonneg (fun n _ => hC n),fun f h hh n hn v hv x => ?_⟩
  have hN : C n ≤ ∑ n ∈ Finset.range (N+1), C n :=
    Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (by omega))
  have hd : ‖(∂^{v} (F₀ h)) x‖ ≤ SchwartzMap.seminorm ℝ 0 n (F₀ h) := by
    rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    calc
      _ ≤ ‖iteratedFDeriv ℝ n (F₀ h) x‖ * ∏ i, ‖v i‖ := (iteratedFDeriv ℝ n (F₀ h) x).le_opNorm v
      _ ≤ ‖iteratedFDeriv ℝ n (F₀ h) x‖ * 1 := by
        apply mul_le_mul_of_nonneg_left (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hv i)) (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ n (F₀ h) x‖ := mul_one _
      _ ≤ _ := (F₀ h).norm_iteratedFDeriv_le_seminorm ℝ n x
  exact hd.trans ((hb n f h hh).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg _)))
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HarmonicDualBound
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

omit [T2Space X] in

lemma harmonicAnti_dual_bound (f : L2 A J α hs ht true) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ v : antiEnergy A J α hs ht,
      |⟪f,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) :
    ‖(harmonicAnti A J α hs ht).starProjection f‖ ≤ M := by
  let K := harmonicAnti A J α hs ht
  obtain ⟨v,hv,hd⟩ := (mem_harmonicAnti A J α hs ht (K.starProjection f)).mp
    (K.starProjection_apply_mem f)
  have hn : ‖v‖ = ‖K.starProjection f‖ := by
    have hg := WithLp.prod_norm_sq_eq_of_L2 v.val
    change ‖v‖^2 = ‖energyInclusion A J α hs ht v‖^2 + ‖weakDelta A J α hs ht v‖^2 at hg
    rw [hv,hd,norm_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero] at hg
    nlinarith [norm_nonneg v,norm_nonneg (K.starProjection f)]
  have hp : K.starProjection (K.starProjection f) = K.starProjection f :=
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem f)
  have hi : ⟪f,K.starProjection f⟫ = ‖K.starProjection f‖^2 := by
    have h := K.inner_starProjection_left_eq_right f (K.starProjection f)
    rw [hp,real_inner_self_eq_norm_sq] at h
    exact h.symm
  have h := hb v
  rw [hv,hn,hi,abs_of_nonneg (sq_nonneg _)] at h
  change ‖K.starProjection f‖ ≤ M
  by_cases hz : ‖K.starProjection f‖ = 0
  · rw [hz]; exact hM
  · have hp : 0 < ‖K.starProjection f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

variable (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

include hD in

lemma harmonic_schwartz_dual_derivative_bound
    (F₀ : antiPre A J α hs ht →ₗ[ℝ] 𝓢(E,F)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      ∀ n ≤ N, ∀ v : Fin n → E, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (F₀ h)) x‖ ≤ C*M := by
  obtain ⟨C,hC,hbound⟩ := harmonic_schwartz_derivative_bound A J α hs ht D hD F₀ N
  refine ⟨C,hC,fun f h hh M hM hb n hn v hv x => ?_⟩
  have hself : smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
      (smoothL2 A J α hs ht true h.val) := by
    rw [hh,(harmonicAnti A J α hs ht).starProjection_eq_self_iff.mpr
      ((harmonicAnti A J α hs ht).starProjection_apply_mem _)]
  have hp := harmonicAnti_dual_bound A J α hs ht _ M hM hb
  rw [← hh] at hp
  exact (hbound h h hself n hn v hv x).trans (mul_le_mul_of_nonneg_left hp hC)
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_NormalizedHarmonicRHS
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma normalizedRawRHSMap_apply (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (L : Space ≃L[ℝ] Space)
    (f : antiPre A J α hs ht) :
    normalizedRawRHSMap A J α hs ht D hD p τ ρ L f =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) (weightedRawRHS A J α hs ht D hD p τ ρ f)) := rfl

include hD in

lemma normalized_harmonic_rhs_bound (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (L : Space ≃L[ℝ] Space) (N : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      ∀ n ≤ N, ∀ v : Fin n → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (SchwartzMap.postcompCLM (embed 2) (weightedRawRHS A J α hs ht D hD p τ ρ h)))) x‖ ≤ C₀*M := by
  obtain ⟨C₀,hC,hb⟩ := harmonic_schwartz_dual_derivative_bound A J α hs ht D hD
    (normalizedRawRHSMap A J α hs ht D hD p τ ρ L) N
  exact ⟨C₀,hC,by simpa only [normalizedRawRHSMap_apply] using hb⟩
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawPairLinear
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

lemma rawPair_sub (a b : TwoForm X) (z : Space) :
    rawPair J α ht p D (a-b) z = rawPair J α ht p D a z - rawPair J α ht p D b z := by
  ext i
  fin_cases i <;> rfl
end TamingCompatibility.GeometricChart

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HarmonicOffJet
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

theorem geometric_off_source_two_jet (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (q : Space) (hq : q ∈ U)
    (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
    (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ η : 𝓢(Space,ℂ), HasCompactSupport (η : Space → ℂ) ∧ (∀ x ∈ V, η x = 1) ∧
      ∃ L : Space ≃L[ℝ] Space, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (hr : 0 < t.1),
      t.1 ≤ 1 → ∀ (f h a : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      (∃ O : Set Space, IsOpen O ∧ O ⊆ W ∧
        (∀ n ≤ 3, tsupport (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1))) ⊆ O) ∧
        ∀ z ∈ O, rawPair J α ht p.val (D p) f.val.val z = 0) →
      (∀ v : antiEnergy A J α hs ht,
        ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true (f-h).val,energyInclusion A J α hs ht v⟫) →
      let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (localizedRawSchwartz A J α hs ht D hD p τ η a)
      ∀ x : Space, ((χ 4 : Space → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖u (t.1 • x+L t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i} u) (t.1 • x+L t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ Space j} (∂_{stdOrthonormalBasis ℝ Space i} u)) (t.1 • x+L t.2)‖ ≤
        C₀*(M*t.1^3 + ‖antiToEnergy A J α hs ht a‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_center_local_energy_two_jet A J α hs ht D hD p τ hU hUD hτ q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨K,hK,harm⟩ := normalized_harmonic_rhs_bound A J α hs ht D hD p τ ρ L 3
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C*(K+1),by positivity,?_⟩
  filter_upwards [hest] with t hh
  intro hr hr1 f h a M hM hproj hdual hzero heq
  obtain ⟨O,hO,hOW,hχO,hfO⟩ := hzero
  let g := -weightedRawRHS A J α hs ht D hD p τ ρ h
  have hg : ∀ z ∈ O, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) (f-h).val.val z := by
    intro z hz
    change -(weightedRawRHS A J α hs ht D hD p τ ρ h z) = _
    rw [weightedRawRHS_spec A J α hs ht D hD p τ ρ h (hUD (hWU (hOW hz)))
      (hτ z (hWU (hOW hz))) (hρ z (hWU (hOW hz)))]
    change _ = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) (f.val.val-h.val.val) z
    rw [rawPair_sub,hfO z hz,zero_sub,smul_neg]
  have hd : ∀ k ≤ 3, ∀ v : Fin k → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
      ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) g))) x‖ ≤ (K*M)/t.1^k := by
    intro k hk v hv x
    have hb := harm f h hproj M hM hdual k hk v hv x
    have he : ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) g))) x‖ =
      ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) (weightedRawRHS A J α hs ht D hD p τ ρ h)))) x‖ := by
      simp only [g,map_neg,LineDeriv.iteratedLineDerivOp_neg,neg_apply,norm_neg]
    rw [he]
    apply hb.trans
    apply (le_div_iff₀ (pow_pos hr k)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1) (mul_nonneg hK hM)
  have hb := hh hr (f-h) a g (K*M) (mul_nonneg hK hM)
    ⟨O,hO,hOW,hχO,hg⟩ hd heq
  dsimp only
  intro x hx
  apply (hb x hx).trans
  have hm : 0 ≤ M*t.1^3 := mul_nonneg hM (pow_nonneg hr.le _)
  nlinarith [norm_nonneg (antiToEnergy A J α hs ht a),mul_nonneg hC hm,
    mul_nonneg hK (norm_nonneg (antiToEnergy A J α hs ht a))]
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RadialOperatorCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Metric
open scoped ContDiff Topology SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

lemma complexScaledCutoff_support (r : ℝ) (hr : 0 < r) :
    tsupport (complexScaledCutoff (E := E) r hr) ⊆ closedBall 0 (2*r) :=
  (tsupport_comp_subset Complex.ofReal_zero (scaledCutoff r)).trans (scaledCutoff_tsupport hr)

lemma complexScaledCutoff_compact (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (complexScaledCutoff (E := E) r hr : E → ℂ) :=
  (isCompact_closedBall 0 (2*r)).of_isClosed_subset (isClosed_tsupport _)
    (complexScaledCutoff_support r hr)

lemma complexScaledCutoff_one (r : ℝ) (hr : 0 < r) {z : E} (hz : ‖z‖ ≤ r) :
    complexScaledCutoff r hr z = 1 := by
  change (scaledCutoff r z : ℂ) = 1
  rw [scaledCutoff_one hr hz,Complex.ofReal_one]

lemma complexScaledCutoff_one_nhds (r : ℝ) (hr : 0 < r) {z : E} (hz : ‖z‖ < r) :
    (complexScaledCutoff r hr : E → ℂ) =ᶠ[𝓝 z] fun _ => 1 := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with y hy
  exact complexScaledCutoff_one r hr (le_of_lt hy)

theorem exists_normalized_operator_cutoffs :
    ∃ (ζ : 𝓢(E,ℂ)) (χ : ℕ → 𝓢(E,ℂ)),
      HasCompactSupport (ζ : E → ℂ) ∧
      (∀ n ≤ 3, HasCompactSupport (χ (n+1) : E → ℂ)) ∧
      (∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1) ∧
      (∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) ∧
      ((χ 4 : E → ℂ) =ᶠ[𝓝 0] fun _ => 1) := by
  let r := fun n : ℕ => ((4:ℝ)^n)⁻¹
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r] <;> positivity
  have hr1 : ∀ n, r n ≤ 1 := by
    intro n
    exact (inv_le_one₀ (by positivity : 0 < (4:ℝ)^n)).mpr (one_le_pow₀ (by norm_num))
  have hstep : ∀ n, 2*r (n+1) < r n := by
    intro n
    dsimp [r]
    rw [pow_succ,mul_inv_rev]
    have hp : 0 < ((4:ℝ)^n)⁻¹ := by positivity
    nlinarith
  let χ := fun n => complexScaledCutoff (E := E) (r n) (hr n)
  refine ⟨complexScaledCutoff 2 (by norm_num),χ,complexScaledCutoff_compact 2 (by norm_num),
    fun n _ => complexScaledCutoff_compact (r (n+1)) (hr (n+1)),?_,?_,?_⟩
  · intro n _ x hx
    have hh := complexScaledCutoff_support (r (n+1)) (hr (n+1)) hx
    simp only [mem_closedBall,dist_zero_right] at hh
    exact complexScaledCutoff_one_nhds (r n) (hr n) (hh.trans_lt (hstep n))
  · intro n _ x hx
    apply complexScaledCutoff_one
    have hh := complexScaledCutoff_support (r (n+1)) (hr (n+1)) hx
    simp only [mem_closedBall,dist_zero_right] at hh
    exact hh.trans (by linarith [hr1 (n+1)])
  · exact complexScaledCutoff_one_nhds (r 4) (hr 4) (by simpa only [norm_zero] using hr 4)

end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialGeometricCoefficient
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma complexDifferential_zero_of_eventually (J : AlmostComplexStructure X)
    {f : X → ℝ} {x : X} (hf : f =ᶠ[𝓝 x] fun _ => 0) : complexDifferential J f x = 0 := by
  have he := hf.mfderiv_eq (I := Model) (I' := 𝓘(ℝ,ℝ))
  rw [mfderiv_const] at he
  ext v
  change -(mfderiv Model 𝓘(ℝ,ℝ) f x) (J.endomorphism x (v 0)) = 0
  rw [he]
  change -(0:ℝ) = 0
  exact neg_zero

lemma anti_ddc_zero_off (J : AlmostComplexStructure X) (f : X → ℝ)
    {x : X} (hx : x ∉ tsupport f) :
    antiInvariantPart J (exteriorDerivative (complexDifferential J f)) x = 0 := by
  have hd : exteriorDerivative (complexDifferential J f) x = 0 := by
    apply exteriorDerivative_eq_zero_of_eventually
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    apply complexDifferential_zero_of_eventually J
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hy] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  ext v
  simp [antiInvariantPart,TamingCompatibility.jAction,hd]

end TamingCompatibility.ManifoldForms

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCoefficientBounds
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_complexLine (J : AlmostComplexStructure X) (β : TwoForm X) (p : X)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback β (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      eval β ((extChartAt Model p).symm y) (mfderiv Model Model (extChartAt Model p).symm y v)
        (J.endomorphism _ (mfderiv Model Model (extChartAt Model p).symm y v)) := by
  have hi := coordinateJ_intertwine J p hy v
  change (inverseChartEquiv p y hy).toContinuousLinearMap (coordinateJ J p y v) =
    J.endomorphism _ ((inverseChartEquiv p y hy).toContinuousLinearMap v) at hi
  rw [inverseChartEquiv_coe] at hi
  change β _ ((mfderiv Model Model (extChartAt Model p).symm y) ∘ ![v,coordinateJ J p y v]) = _
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact hi

end TamingCompatibility.GeometricChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ContinuousAlternatingMap
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma closedLift_pullback_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (a : antiPre A J α hs ht) (p : X) {y : Space}
    (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs a).val
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      nonharmonicCorrectionLM A J α hs ht Gs p y a ![v,coordinateJ J p y v] := by
  change _ = ManifoldForms.pullback
    (exteriorDerivative (codifferential J α ht (Gs a).val.val)) (extChartAt Model p).symm y _
  rw [pullback_complexLine J _ p hy,pullback_complexLine J _ p hy]
  exact closedLiftOfInverse_complexLine A J α hs ht H Gs a _ _

lemma correctedDdc_pullback_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (p : X) {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback (correctedDdc A J α hs ht H Gs hf).val
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
    ManifoldForms.pullback (exteriorDerivative (complexDifferential J f))
      (extChartAt Model p).symm y ![v,coordinateJ J p y v] -
      nonharmonicCorrectionLM A J α hs ht Gs p y
        (smoothAntiProjection A J α hs ht (smoothDdc J hf)) ![v,coordinateJ J p y v] := by
  change ManifoldForms.pullback (_-_) _ _ _ = _
  change ManifoldForms.pullback (smoothDdc J hf).val _ _ _ -
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs
      (smoothAntiProjection A J α hs ht (smoothDdc J hf))).val _ _ _ = _
  rw [closedLift_pullback_complexLine A J α hs ht H Gs _ p hy]
  rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Hermitian
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma ddc_zero_off (J : AlmostComplexStructure X) {f : X → ℝ} {x : X}
    (hx : x ∉ tsupport f) : exteriorDerivative (complexDifferential J f) x = 0 := by
  apply exteriorDerivative_eq_zero_of_eventually
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  apply complexDifferential_zero_of_eventually J
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hy] with z hz
  exact image_eq_zero_of_notMem_tsupport hz

end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

lemma rawPair_zero_of_zero {a : TwoForm X} {z : Space}
    (ha : a ((extChartAt Model p).symm z) = 0) : rawPair J α ht p D a z = 0 := by
  have hr (j : Fin 4) : rawScalar J α ht p D a j z = 0 := by
    change a ((extChartAt Model p).symm z) _ = 0
    rw [ha]
    rfl
  ext i
  fin_cases i <;> simp only [rawPair,EuclideanEnergy.pair,hr] <;> rfl

end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_CorrectedDdcOff
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)

lemma correctedDdc_norm_off_source {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (p : X) {y : Space} (hy : y ∈ (extChartAt Model p).target)
    (hx : (extChartAt Model p).symm y ∉ tsupport f) (v : Space) :
    ‖ManifoldForms.pullback (correctedDdc A J α hs ht H Gs hf).val
      (extChartAt Model p).symm y ![v,coordinateJ J p y v]‖ =
      ‖nonharmonicCorrectionLM A J α hs ht Gs p y
        (smoothAntiProjection A J α hs ht (smoothDdc J hf)) ![v,coordinateJ J p y v]‖ := by
  rw [correctedDdc_pullback_complexLine A J α hs ht H Gs hf p hy]
  have he : ManifoldForms.pullback (exteriorDerivative (complexDifferential J f))
        (extChartAt Model p).symm y ![v,coordinateJ J p y v] = 0 := by
    change exteriorDerivative (complexDifferential J f) ((extChartAt Model p).symm y) _ = 0
    rw [ddc_zero_off J hx]
    rfl
  rw [he,zero_sub,norm_neg]
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCombinedForms
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem nonharmonicCorrection_off_source_uniform
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (q : Space) (hq : q ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      (∀ z ∈ U, rawPair J α ht p.val (D p) f.val.val z = 0) →
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y f‖ ≤ C*M := by
  obtain ⟨ζ,χ,hζ,hcχ,hχ,hζχ,hχ0⟩ := exists_normalized_operator_cutoffs (E := Space)
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_off_source_two_jet A J α hs ht D hD p τ ρ hU hUD hτ hρ q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  have hKV : Metric.closedBall q (ε/2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεV
  obtain ⟨C₀,hC₀,hout⟩ := closedLift_scaled_basis_local_bound A J α hs ht D hD
    (stdOrthonormalBasis ℝ Space).toBasis p τ η L
    hV (hVW.trans (hWU.trans hUD))
    (fun z hz => hτ z (hWU (hVW hz))) hηone (isCompact_closedBall q (ε/2)) hKV
  have htK : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), t.2 ∈ Metric.closedBall q (ε/2) :=
    (continuous_snd.tendsto (0,q)).eventually (Metric.closedBall_mem_nhds q (by positivity))
  have hshrink : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), ∀ n : Fin 4, ∀ hr : t.1 ≠ 0,
      tsupport (normalizedCutoff L t.2 t.1 hr (χ (n.val+1))) ⊆ W := by
    apply (Filter.eventually_all.mpr ?_)
    intro n
    exact normalizedCutoff_eventually_support L q (χ (n.val+1)) (hcχ n.val (by omega)) hW hqW
  have hevent : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), ∀ (hr : 0 < t.1), t.1 ≤ 1 →
      ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      (∀ z ∈ U, rawPair J α ht p.val (D p) f.val.val z = 0) →
      t.1^3*‖nonharmonicCorrectionLM A J α hs ht Gs p.val t.2 f‖ ≤ C₀*C*(1+B)*M := by
    filter_upwards [hest,htK,hshrink] with t hh htK hsupport
    intro hr hr1 f M hM hdu hfzero
    have hj := hh hr hr1 f (H f) (Gs f) M hM (hH f) hdu
      ⟨W,hW,Subset.rfl,fun n hn => hsupport ⟨n,by omega⟩ hr.ne',
        fun z hz => hfzero z (hWU hz)⟩ (hweak f) 0 hχ0
    have hj' : t.1*‖SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
            (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f)) (L t.2)‖ +
        t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i}
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
            (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f)))) (L t.2)‖ +
        t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ Space j}
            (∂_{stdOrthonormalBasis ℝ Space i}
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
            (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f))))) (L t.2)‖ ≤ C*(1+B)*M := by
      simp only [smul_zero,zero_add] at hj
      apply hj.trans
      have ha := hdual f M hM hdu
      have hp := mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1 : t.1^3 ≤ 1) hM
      nlinarith [mul_nonneg hC (sub_nonneg.mpr ha),mul_nonneg hC (sub_nonneg.mpr hp)]
    have ho := hout H Gs f t.2 htK t.1 (C*(1+B)*M) hr hr1 (by
      simpa only [OrthonormalBasis.coe_toBasis] using hj')
    rw [closedLiftOfInverse_pullback_sub] at ho
    change t.1^3*‖nonharmonicCorrectionLM A J α hs ht Gs p.val t.2 f‖ ≤ _ at ho
    exact ho.trans_eq (by ring)
  obtain ⟨r₀,hr₀,he⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ := min r₀ 1
  have hδ : 0 < δ := lt_min hr₀ (by norm_num)
  let r := δ/2
  have hr : 0 < r := by positivity
  have hr1 : r ≤ 1 := by dsimp [r] <;> linarith [min_le_right r₀ (1:ℝ)]
  refine ⟨δ,hδ,C₀*C*(1+B)/r^3,by positivity,?_⟩
  intro y hy f M hM hd hz
  have hp : dist (r,y) (0,q) < r₀ := by
    rw [Prod.dist_eq,dist_zero_right,Real.norm_of_nonneg hr.le]
    apply max_lt
    · dsimp [r] <;> linarith [min_le_left r₀ (1:ℝ)]
    · exact (show dist y q < δ from hy).trans_le (min_le_left _ _)
  have hu := he hp hr hr1 f M hM hd hz
  calc
    _ ≤ (C₀*C*(1+B)*M)/r^3 := (le_div_iff₀ (pow_pos hr 3)).mpr (by simpa only [mul_comm] using hu)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactPositiveBilinear
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Set

lemma compact_positive_bilinear_bounds {Y E : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
    {K : Set Y} (hK : IsCompact K) {g : Y → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContinuousOn g K) (hpos : ∀ z ∈ K, ∀ v : E, v ≠ 0 → 0 < g z v v) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : E,
      m*‖v‖^2 ≤ g z v v ∧ g z v v ≤ M*‖v‖^2 := by
  by_cases hne : K.Nonempty
  · let q : Y × E → ℝ := fun x => g x.1 x.2 x.2
    have hq : ContinuousOn q (K ×ˢ Metric.sphere (0:E) 1) :=
      ((hg.comp continuousOn_fst (fun _ hx => hx.1)).clm_apply continuousOn_snd).clm_apply
        continuousOn_snd
    obtain ⟨x,hx,hmin⟩ := (hK.prod (isCompact_sphere (0:E) 1)).exists_isMinOn
      (hne.prod (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1))) hq
    have hxnorm : ‖x.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx.2
    have hqx : 0 < q x := hpos x.1 hx.1 x.2 (by intro h; simp [h] at hxnorm)
    obtain ⟨y,hy,hmax⟩ := (hK.prod (isCompact_sphere (0:E) 1)).exists_isMaxOn
      (hne.prod (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1))) hq
    refine ⟨q x,max (q y) 1,hqx,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
    intro z hz v
    by_cases hv : v = 0
    · simp [hv]
    · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      let w := ‖v‖⁻¹ • v
      have hw : w ∈ Metric.sphere (0:E) 1 := by
        simp [w,norm_smul,inv_mul_cancel₀ hnv]
      have hid : g z w w * ‖v‖^2 = g z v v := by
        simp only [w,map_smul,_root_.smul_apply,smul_eq_mul]
        field_simp
      have hlo := mul_le_mul_of_nonneg_right (hmin (show (z,w) ∈ K ×ˢ Metric.sphere (0:E) 1 from ⟨hz,hw⟩)) (sq_nonneg ‖v‖)
      have hup := mul_le_mul_of_nonneg_right
        ((hmax (show (z,w) ∈ K ×ˢ Metric.sphere (0:E) 1 from ⟨hz,hw⟩)).trans (le_max_left (q y) 1)) (sq_nonneg ‖v‖)
      change q x * ‖v‖^2 ≤ g z w w * ‖v‖^2 at hlo
      change g z w w * ‖v‖^2 ≤ max (q y) 1 * ‖v‖^2 at hup
      rw [hid] at hlo hup
      exact ⟨hlo,hup⟩
  · refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    intro z hz
    exact (hne ⟨z,hz⟩).elim
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactUniformBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Topology

theorem IsCompact.exists_uniform_monotone_bound {Y : Type*} [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) (P : Y → ℝ → Prop)
    (hmono : ∀ y a b, a ≤ b → P y a → P y b)
    (hlocal : ∀ q ∈ K, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 q, P y C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, P y C := by
  classical
  have hloc : ∀ q : K, ∃ C : ℝ, ∃ U : Set Y,
      0 ≤ C ∧ IsOpen U ∧ q.val ∈ U ∧ ∀ y ∈ U, P y C := by
    intro q
    obtain ⟨C,hC,hq⟩ := hlocal q.val q.property
    obtain ⟨U,hUP,hU,hqU⟩ := mem_nhds_iff.mp hq
    exact ⟨C,U,hC,hU,hqU,hUP⟩
  choose C U hC hU hqU hUP using hloc
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hqU ⟨y,hy⟩⟩)
  refine ⟨∑ q ∈ s, C q, Finset.sum_nonneg (fun q _ => hC q), ?_⟩
  intro y hy
  obtain ⟨q,hq,hyq⟩ := mem_iUnion₂.mp (hs hy)
  exact hmono y (C q) _ (Finset.single_le_sum (fun r _ => hC r) hq) (hUP q y hyq)

end


end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianUnitMetric
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldVolume
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J)

include hs ht in
lemma chartMetric_compact_bounds (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : Space,
      m*‖v‖^2 ≤ chartMetric J α p z v v ∧ chartMetric J α p z v v ≤ M*‖v‖^2 :=
  compact_positive_bilinear_bounds hK (((hs.invariantPart J).metricCoords J p).continuousOn.mono hKT)
    (fun _z hz v hv => chartMetric_pos J α ht p (hKT hz) v hv)

include hs ht in
lemma chartMetric_unit_norm_bounds (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : Space,
      chartMetric J α p z v v = 1 → m ≤ ‖v‖^2 ∧ ‖v‖^2 ≤ M := by
  obtain ⟨a,b,ha,hb,hbound⟩ := chartMetric_compact_bounds J α hs ht p hK hKT
  refine ⟨1/b,1/a,by positivity,by positivity,?_⟩
  intro z hz v hv
  obtain ⟨hlo,hup⟩ := hbound z hz v
  rw [hv] at hlo hup
  exact ⟨(div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hup),
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hlo)⟩

include ht in
lemma chartMetric_hermitian (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    chartMetric J α p z (coordinateJ J p z u) (coordinateJ J p z v) =
      chartMetric J α p z u v := by
  have h := coordinateMetric_hermitian J α ht p hz u v
  simpa only [coordinateMetric_bilinear J α ht p hz] using h

include hs ht in
lemma form_unit_line_bound (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ K, ∀ v : Space, chartMetric J α p z v v = 1 →
      ∀ β : MetricForms.Form Space 2, ‖β ![v,coordinateJ J p z v]‖ ≤ ‖β‖*M := by
  obtain ⟨m,M,_,hM,hbound⟩ := chartMetric_unit_norm_bounds J α hs ht p hK hKT
  refine ⟨M,hM,?_⟩
  intro z hz v hv β
  have hnv := (hbound z hz v hv).2
  have hnJ := (hbound z hz (coordinateJ J p z v)
    ((chartMetric_hermitian J α ht p (hKT hz) v v).trans hv)).2
  have hprod : ‖v‖*‖coordinateJ J p z v‖ ≤ M := by
    nlinarith [sq_nonneg (‖v‖-‖coordinateJ J p z v‖)]
  calc
    _ ≤ ‖β‖*(‖v‖*‖coordinateJ J p z v‖) := by
      simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
        using β.le_opNorm ![v,coordinateJ J p z v]
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)

end TamingCompatibility.ManifoldVolume

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricOffCompact
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem nonharmonicCorrection_off_source_compact
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ f : antiPre A J α hs ht,
      (∀ z ∈ U, rawPair J α ht p.val (D p) f.val.val z = 0) →
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y f‖ ≤
        C*‖antiEnergyDualLM A J α hs ht f‖ := by
  apply _root_.OAI.IsCompact.exists_uniform_monotone_bound hK
  · intro y a b hab ha f hf
    exact (ha f hf).trans (mul_le_mul_of_nonneg_right hab (ContinuousLinearMap.opNorm_nonneg _))
  · intro q hq
    obtain ⟨δ,hδ,C,hC,hest⟩ := nonharmonicCorrection_off_source_uniform
      A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ q (hKU hq)
    refine ⟨C,hC,?_⟩
    filter_upwards [Metric.ball_mem_nhds q hδ] with y hy
    intro f hf
    exact hest y hy f ‖antiEnergyDualLM A J α hs ht f‖ (ContinuousLinearMap.opNorm_nonneg _)
      (fun v => (antiEnergyDualLM A J α hs ht f).le_opNorm v) hf
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CorrectedDdcOffCompact
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem correctedDdc_off_source_compact_oai
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ v : Space,
      chartMetric J α p.val y v v = 1 →
      ∀ (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f),
      (∀ z ∈ U, (extChartAt Model p.val).symm z ∉ tsupport f) →
      ‖ManifoldForms.pullback (correctedDdc A J α hs ht H Gs hf).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]‖ ≤
        C*‖antiEnergyDualLM A J α hs ht
          (smoothAntiProjection A J α hs ht (smoothDdc J hf))‖ := by
  obtain ⟨C,hC,hest⟩ := nonharmonicCorrection_off_source_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU
  have hKT : K ⊆ (extChartAt Model p.val).target := hKU.trans (hUD.trans (D p).domain_subset)
  obtain ⟨M,hM,hunit⟩ := form_unit_line_bound J α hs ht p.val hK hKT
  refine ⟨C*M,by positivity,?_⟩
  intro y hy v hv f hf hoff
  rw [correctedDdc_norm_off_source A J α hs ht H Gs hf p.val (hKT hy) (hoff y (hKU hy)) v]
  have he := hest y hy (smoothAntiProjection A J α hs ht (smoothDdc J hf)) (by
    intro z hz
    apply rawPair_zero_of_zero
    exact anti_ddc_zero_off J f (hoff z hz))
  exact (hunit y hy v hv _).trans (by
    nlinarith [mul_le_mul_of_nonneg_right he hM.le])
end TamingCompatibility.GeometricHilbert

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.correctedDdc_off_source_compact_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.correctedDdc_off_source_compact_oai.{u_1}
