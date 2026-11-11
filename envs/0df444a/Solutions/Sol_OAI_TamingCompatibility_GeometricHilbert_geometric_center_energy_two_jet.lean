-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.geometric_center_energy_two_jet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:33:29.059515+00:00
-- url     : https://prove2.me/submissions/d4eebf15-89a3-4d92-8484-36d80ca613e3

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028
import Definitions.Def_OAIQ239Tc029
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_actual_localized_square_source
import Theorems.Thm_OAI_TamingCompatibility_HilbertSobolev_linear_center_energy_two_jet

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LinearTransport
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace F] in
lemma linearDistribution_schwartz (L : E ≃L[ℝ] E) (f : 𝓢(E,F)) :
    linearDistribution L (f : 𝓢'(E,F)) =
      ((|(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| •
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f : 𝓢(E,F)) : 𝓢'(E,F)) := by
  ext φ
  rw [linearDistribution_apply]
  simp only [SchwartzMap.coe_apply]
  let c : ℝ := |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹|
  have hm := L.toHomeomorph.measurableEmbedding.integral_map
    (μ := (volume : Measure E)) (fun y => φ y • f (L.symm y))
  change (∫ y, φ y • f (L.symm y) ∂Measure.map L volume) =
    ∫ x, φ (L x) • f (L.symm (L x)) at hm
  rw [show Measure.map L volume = ENNReal.ofReal c • volume from
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.toLinearEquiv.isUnit_det'.ne_zero,
    integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)] at hm
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hm
  change (∫ x, φ (L x) • f x) = ∫ y, φ y • (c • f (L.symm y))
  rw [← hm,← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact smul_comm c (φ y) _

end TamingCompatibility.EuclideanSobolevOperators

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalMatrixOperator
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
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy
open scoped ContDiff RealInnerProductSpace SchwartzMap

lemma combine_apply {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (u v : D) (q : Pair) :
    combine u v q = q 0 • u + q 1 • v := rfl

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalSymbol
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy
open scoped RealInnerProductSpace

lemma normalSymbol_polarized (ξ η : V) (q r : Pair) :
    ⟪normalSymbol ξ q,normalSymbol η r⟫ +
      ⟪normalSymbol η q,normalSymbol ξ r⟫ = 2 * ⟪ξ,η⟫ * ⟪q,r⟫ := by
  simp only [PiLp.inner_apply]
  simp [normalSymbol,combine_apply,Fin.sum_univ_succ]
  ring

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.ComplexMatrix.componentTest_apply _root_.OAI.TamingCompatibility.ComplexMatrix.realComponent_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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

lemma realPairSchwartz_apply (p : A.centers) (a : smoothForms X 2) (z : Space) :
    realPairSchwartz A J α ht D hD p a z =
      EuclideanEnergy.pair (scalar A J α ht D p a.val 2 z) (scalar A J α ht D p a.val 3 z) := by
  ext i
  fin_cases i <;> simp [realPairSchwartz,pairLinear_eq_make,ScalarPair.make_apply,EuclideanEnergy.pair] <;> rfl

lemma realPairSchwartz_embed (p : A.centers) (a : smoothForms X 2) :
    SchwartzMap.postcompCLM (embed 2) (realPairSchwartz A J α ht D hD p a) =
      pairLinear A J α ht D hD p a := by
  ext z i
  fin_cases i <;> simp [realPairSchwartz_apply,pairLinear_eq_make,ScalarPair.make_apply,EuclideanEnergy.pair] <;> rfl

end TamingCompatibility.GeometricChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart _root_.MeasureTheory ComplexMatrix
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma scalarDistribution_smooth (p : A.centers) (a : antiPre A J α hs ht) :
    scalarDistribution A J α hs ht D hD p (antiToEnergy A J α hs ht a) =
      (pairLinear A J α ht D hD p a.val : 𝓢'(Space,ScalarPair.F)) := by
  change ScalarPair.jetDistribution none
    (energyToScalarJet A J α hs ht D hD p (antiToEnergy A J α hs ht a)) = _
  rw [energyToScalarJet_smooth]
  exact ScalarPair.jetDistribution_jet _ none

lemma rawDistribution_smooth (p : A.centers) (τ : 𝓢(Space,ℝ)) (a : antiPre A J α hs ht) :
    rawDistribution A J α hs ht D hD p τ (antiToEnergy A J α hs ht a) =
      (SchwartzMap.postcompCLM (embed 2)
        (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p a.val)) :
          𝓢'(Space,ScalarPair.F)) := by
  change smulLeftCLM ScalarPair.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
    (scalarDistribution A J α hs ht D hD p (antiToEnergy A J α hs ht a)) = _
  rw [scalarDistribution_smooth,product_schwartz]
  congr 1
  rw [← realPairSchwartz_embed A J α ht D hD p a.val]
  ext z i
  simp only [SchwartzMap.smulLeftCLM_apply (SchwartzMap.postcompCLM Complex.ofRealCLM τ).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply τ.hasTemperateGrowth,SchwartzMap.postcompCLM_apply,embed_apply,
    PiLp.smul_apply,Complex.ofRealCLM_apply,smul_eq_mul,Complex.ofReal_mul]
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SquarePrincipal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} {m n : ℕ}

lemma principalScalar_apply (a : ι → 𝓢(D,R 2 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2)) (i j : ι) (x : D) :
    principalScalar a ρ i j x = (g i j x : ℂ) := by
  have he := entry_polarized (h i j x) (0 : Fin 2) (0 : Fin 2)
  simp only [ite_true, if_true,mul_one] at he
  simp only [principalScalar,_root_.smul_apply,_root_.add_apply,principalMatrix_apply,
    smul_eq_mul,← Complex.ofReal_add,he,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

lemma principalMatrix_scalar (a : ι → 𝓢(D,R 2 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2)) (i j : ι) (k l : Fin 2) :
    principalMatrix a ρ i j k l + principalMatrix a ρ j i k l =
      scalarMatrix 2 (principalScalar a ρ i j + principalScalar a ρ i j) k l := by
  ext x
  have he := entry_polarized (h i j x) k l
  simp only [_root_.add_apply,principalMatrix_apply,← Complex.ofReal_add]
  rw [show entry k l ((ρ x • a i x).adjoint ∘L a j x) +
    entry k l ((ρ x • a j x).adjoint ∘L a i x) = (2*g i j x)*(if k=l then 1 else 0) from he]
  by_cases hkl : k=l
  · simp only [scalarMatrix,ite_eq_left hkl,_root_.add_apply,principalScalar_apply a ρ g h,
      mul_one,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  · simp only [scalarMatrix,ite_eq_right hkl,_root_.zero_apply,mul_zero,Complex.ofReal_zero]

end TamingCompatibility.ComplexMatrix

namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy
open scoped RealInnerProductSpace
lemma normalSymbol_weighted_polarized (ρ c : ℝ) (ξ η : V) :
    (ρ • (c • normalSymbol ξ)).adjoint ∘L (c • normalSymbol η) +
      (ρ • (c • normalSymbol η)).adjoint ∘L (c • normalSymbol ξ) =
        (2 * (ρ*c*c*⟪ξ,η⟫)) • ContinuousLinearMap.id ℝ Pair := by
  apply ContinuousLinearMap.ext
  intro q
  apply ext_inner_left ℝ
  intro r
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,inner_add_right,
    ContinuousLinearMap.adjoint_inner_right,_root_.smul_apply,real_inner_smul_left,
    real_inner_smul_right,ContinuousLinearMap.id_apply]
  calc
    _ = (ρ*c*c) * (⟪normalSymbol ξ r,normalSymbol η q⟫ +
        ⟪normalSymbol η r,normalSymbol ξ q⟫) := by ring
    _ = _ := by rw [normalSymbol_polarized]; ring
end TamingCompatibility.LocalMatrixOperator

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScalarSquare
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
variable {ι : Type*} [Fintype ι] {m : ℕ}

lemma square_scalar_expansion (e : ι → D) (a : ι → 𝓢(D,R 2 →L[ℝ] R m))
    (b : 𝓢(D,R 2 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ)) (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2)) (u : 𝓢'(D,C 2)) :
    square e a b ρ u =
      -(∑ i, ∑ j, smulLeftCLM (C 2) (principalScalar a ρ i j) (∂_{e i} (∂_{e j} u))) +
      (∑ j, multiply (squareFirst e (fun i => coefficient (a i)) (coefficient b)
        (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b) j) (∂_{e j} u)) +
      multiply (squareZero e (coefficient b) (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)) u := by
  simp only [square,formalAdjoint,firstOrder,_root_.add_apply,_root_.neg_apply,
    _root_.sum_apply,ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply]
  rw [divergence_square_expansion]
  have hp := symmetrized_principal e (principalMatrix a ρ) (principalScalar a ρ)
    (principalMatrix_scalar a ρ g h) u
  simp only [principalMatrix] at hp
  rw [hp]
  rfl

end TamingCompatibility.ComplexMatrix

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge LocalMatrixOperator ComplexMatrix
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

lemma patchA_polarized (ρ : 𝓢(Space,ℝ)) (i j : Fin 4) (z : Space) :
    (ρ z • patchA J α ht p D hφ hc hφD i z).adjoint ∘L patchA J α ht p D hφ hc hφD j z +
      (ρ z • patchA J α ht p D hφ hc hφD j z).adjoint ∘L patchA J α ht p D hφ hc hφD i z =
    (2*(ρ z*φ z*φ z*normalMetric J α ht p D i j z)) • ContinuousLinearMap.id ℝ EuclideanEnergy.Pair :=
  normalSymbol_weighted_polarized (ρ z) (φ z) _ _

end TamingCompatibility.GeometricChart

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_CriticalRescaleH1
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
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance instFactLeENNRealOfNat_solutions_1_r8756e0_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
lemma schwartzToH_zero (f : 𝓢(E,F)) : schwartzToH 0 f = f.toLp 2 (volume : Measure E) := by
  simp [schwartzToH]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_LinearCenterEnergy
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {m : ℕ}

local instance instFactLeENNRealOfNat_solutions_r8756e0_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
theorem metric_square_center_energy_two_jet
    (p₀ : V) (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 2 →L[ℝ] R m)) (b : 𝓢(V,R 2 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p₀ = c * ∑ t, frame t i * frame t j)
    (ζ : 𝓢(V,ℂ)) (hζ : HasCompactSupport (ζ : V → ℂ))
    (χ : ℕ → 𝓢(V,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ A : V ≃L[ℝ] V, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ t in 𝓝 (0,p₀), ∀ (hr : 0 < t.1),
      ∀ (u f : 𝓢(V,C 2)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ q : Fin k → V, (∀ i, ‖q i‖ ≤ 1) → ∀ x,
        ‖(∂^{q} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm f)) x‖ ≤ M/t.1^k) →
      (∀ n ≤ 3, smulLeftCLM (C 2)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
        (square e a b ρ (u : 𝓢'(V,C 2))) =
        smulLeftCLM (C 2) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
          (f : 𝓢'(V,C 2))) →
      let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u
      ∀ x : V, ((χ 4 : V → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖U (t.1 • x+A t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ V i} U) (t.1 • x+A t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ V j} (∂_{stdOrthonormalBasis ℝ V i} U)) (t.1 • x+A t.2)‖ ≤
        C₀*(M*t.1^3 + ‖U.toLp 4 (volume : Measure V)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ V i} U).toLp 2 (volume : Measure V)‖) := by
  let G := principalScalar a ρ
  have hg : ∀ i j, G i j p₀ = (c * ∑ t, frame t i * frame t j : ℝ) := by
    intro i j
    rw [principalScalar_apply a ρ g ha,hgp]
  obtain ⟨A,hA⟩ := exists_principal_normalization metric frame hframe c ((2*Real.pi)^2)⁻¹ hc
    (by positivity) G p₀ hg
  let B := squareFirst e (fun i => coefficient (a i)) (coefficient b)
    (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)
  let Cc := squareZero e (coefficient b) (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)
  obtain ⟨C₀,hC,hest⟩ := linear_center_energy_two_jet (F := C 2) (by norm_num [V]) e G p₀ A hA
    (fun q : Fin 4 × Fin 2 × Fin 2 => B q.1 q.2.1 q.2.2)
    (fun q => unit 2 2 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 2 × Fin 2 => Cc q.1 q.2) (fun q => unit 2 2 q.1 q.2) ζ hζ χ hχ hζχ
  refine ⟨A,C₀,hC,?_⟩
  filter_upwards [hest] with t hh
  intro hr u f M hM hf heq
  apply hh hr u f M hM hf
  intro n hn
  have he := heq n hn
  rw [square_scalar_expansion e a b ρ g ha,add_assoc,entries_lowerOrder] at he
  exact he
end TamingCompatibility.ComplexMatrix

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_CriticalH1Linear
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
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance localInst_r8756e0_1 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
lemma schwartz_derivative_L2_H1 (f : 𝓢(E,F)) (v : E) :
    ‖(∂_{v} f).toLp 2 (volume : Measure E)‖ ≤ ‖derivative (F := F) 1 v‖ * ‖schwartzToH 1 f‖ := by
  have h := (derivative (F := F) 1 v).le_opNorm (schwartzToH 1 f)
  rw [← schwartzToH_derivative] at h
  rw [show (1:ℝ)-1=0 by ring] at h
  simpa only [schwartzToH_zero] using h

lemma critical_norm_H1 (hdim : Module.finrank ℝ E = 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(E,F), HasCompactSupport f →
      ‖f.toLp 4 (volume : Measure E)‖ +
        ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖ ≤
          C * ‖schwartzToH 1 f‖ := by
  classical
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  let c := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure E) 2
  let D := ∑ i, ‖derivative (F := F) 1 (stdOrthonormalBasis ℝ E i)‖
  refine ⟨((c:ℝ)+1)*D,by dsimp only [D] <;> positivity,fun f hf => ?_⟩
  have hd : eLpNorm (fderiv ℝ f) 2 (volume : Measure E) ≤
      ∑ i, eLpNorm (∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)) 2 volume := by
    calc
      _ ≤ eLpNorm (fun x => ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)) x‖) 2 volume := by
        apply eLpNorm_mono_ae_real
        exact Filter.Eventually.of_forall (fun x => by
          simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
            CriticalSobolev.opNorm_le_sum_basis (fderiv ℝ f x))
      _ ≤ ∑ i, eLpNorm (fun x => ‖(∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)) x‖) 2 volume := by
        simpa only [Finset.sum_fn] using eLpNorm_sum_le (hfs := fun _ _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | exact MemLp.aestronglyMeasurable (by assumption) | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (μ := (volume : Measure E))
          (f := fun index point => ‖(∂_{stdOrthonormalBasis ℝ E index} f : 𝓢(E,F)) point‖)
          (by norm_num : (1:ℝ≥0∞) ≤ 2)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index _
        exact eLpNorm_norm _
  have hgns := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure E)
    (f.smooth 1) hf (p := (2:ℝ≥0)) (p' := (4:ℝ≥0)) (by norm_num)
    (by rw [hdim]; norm_num) (by rw [hdim]; norm_num)
  have hh := hgns.trans (mul_le_mul_of_nonneg_left hd (zero_le))
  have he : (∑ i, eLpNorm (∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)) 2 volume) ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ((∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)).memLp 2 volume).eLpNorm_ne_top
  have ht := ENNReal.toReal_mono (by finiteness) hh
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,ENNReal.toReal_sum (fun i _ =>
    ((∂_{stdOrthonormalBasis ℝ E i} f : 𝓢(E,F)).memLp 2 volume).eLpNorm_ne_top)] at ht
  have hb : (∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖) ≤
      D * ‖schwartzToH 1 f‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => schwartz_derivative_L2_H1 f _)
  have h₄ : ‖f.toLp 4 (volume : Measure E)‖ ≤
      (c:ℝ) * ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖ := by
    simpa [SchwartzMap.norm_toLp,c] using ht
  calc
    _ ≤ ((c:ℝ)+1) * ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f).toLp 2 (volume : Measure E)‖ := by linarith
    _ ≤ ((c:ℝ)+1) * (D * ‖schwartzToH 1 f‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

lemma linearH_spec (n : ℕ) (L : E ≃L[ℝ] E) (u : H E F n) :
    toDistribution E F n (linearH n L u) = linearDistribution L (toDistribution E F n u) :=
  toDistribution_liftOperator _ _ _

lemma linearH_schwartz (n : ℕ) (L : E ≃L[ℝ] E) (f : 𝓢(E,F)) :
    linearH n L (schwartzToH n f) =
      |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| •
        schwartzToH n (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f) := by
  apply toDistribution_injective n
  rw [linearH_spec,schwartzToH_spec,ContinuousLinearMap.map_smul_of_tower,
    schwartzToH_spec,linearDistribution_schwartz]
  exact ContinuousLinearMap.map_smul_of_tower _ _ _

lemma linear_schwartz_H_bound (n : ℕ) (L : E ≃L[ℝ] E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : 𝓢(E,F),
      ‖schwartzToH n (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f)‖ ≤
        K * ‖schwartzToH n f‖ := by
  let d := |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹|
  have hd : 0 < d := abs_pos.mpr (inv_ne_zero L.toLinearEquiv.isUnit_det'.ne_zero)
  refine ⟨d⁻¹ * ‖linearH (F := F) n L‖,by positivity,fun f => ?_⟩
  have h := (linearH (F := F) n L).le_opNorm (schwartzToH n f)
  rw [linearH_schwartz,norm_smul,Real.norm_eq_abs,abs_abs] at h
  have hb := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hd.le)
  change d⁻¹ * (d * _) ≤ _ at hb
  simpa only [← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul] using hb
end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance localInst_r8756e0_2 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
lemma critical_linear_H1 (hdim : Module.finrank ℝ E = 4) (L : E ≃L[ℝ] E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : 𝓢(E,F), HasCompactSupport f →
      let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f
      ‖u.toLp 4 (volume : Measure E)‖ +
        ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖ ≤
          B * ‖schwartzToH 1 f‖ := by
  obtain ⟨C,hC,hbound⟩ := critical_norm_H1 (F := F) hdim
  obtain ⟨B,hB,hlinear⟩ := linear_schwartz_H_bound (F := F) 1 L
  refine ⟨C*B,mul_nonneg hC hB,fun f hf => ?_⟩
  dsimp only
  have hc := hf.comp_homeomorph L.symm.toHomeomorph
  apply (hbound (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f) hc).trans
  have hb := hlinear f
  simpa only [schwartzToH,Nat.cast_one] using
    (mul_le_mul_of_nonneg_left hb hC).trans_eq (mul_assoc _ _ _).symm
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_MetricSquareEstimate
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

include hs in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_geometric_square_data (p : A.centers)
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (q : Space) (hq : q ∈ U) : Nonempty (SquareData A J α ht D p U q) := by
  obtain ⟨φ,hφ,hφU,W,hW,hqW,hWU,hφone⟩ := SchwartzCutoff.exists_one_near hU hq
  have hφD := hφU.trans hUD
  let a := patchA J α ht p.val (D p) (φ.smooth ⊤) hφ hφD
  let b := patchB J α hs ht p.val (D p) (φ.smooth ⊤) hφ hφD
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset) (φ.smooth ⊤) hφ hφD
  have ha : ∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p) i z := by
    intro z hz i
    simp only [a,patchA,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hb : ∀ z ∈ W, b z = normalB J α ht p.val (D p) z := by
    intro z hz
    simp only [b,patchB,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hρ : ∀ z ∈ W, ρ z = chartDensity J α p.val z := by
    intro z hz
    simp only [ρ,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  let G := fun i j z => ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p.val (D p) i j z
  have hG : ∀ i j, G i j q = chartDensity J α p.val q * ∑ t, (D p).frame t q i * (D p).frame t q j := by
    intro i j
    simp only [G,hρ q hqW,hφone q hqW,one_mul,GeometricChart.normalMetric,
      LocalMatrixOperator.frameCovector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      star_trivial,mul_comm]
  refine ⟨{ W := W
            openW := hW
            qW := hqW
            WU := hWU
            a := a
            b := b
            ρ := ρ
            g := G
            agreeA := ha
            agreeB := hb
            agreeρ := hρ
            polarized := ?_
            center := hG }⟩
  exact patchA_polarized J α ht p.val (D p) (φ.smooth ⊤) hφ hφD ρ

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_RawH1Bound
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart _root_.MeasureTheory ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma rawH1_spec (p : A.centers) (τ : 𝓢(Space,ℝ)) (u : antiEnergy A J α hs ht) :
    toDistribution Space ScalarPair.F 1 (rawH1 A J α hs ht D hD p τ u) =
      rawDistribution A J α hs ht D hD p τ u :=
  by
    change ((toDistribution Space ScalarPair.F 1).restrictScalars ℝ)
      (rawH1 A J α hs ht D hD p τ u) = _
    exact InjectiveLinearLift.continuousLift_spec _ _ _ _ _

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_InteriorEstimateApply
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma localizedRawSchwartz_spec (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (a : antiPre A J α hs ht) :
    (localizedRawSchwartz A J α hs ht D hD p τ χ a : 𝓢'(Space,C 2)) =
      smulLeftCLM (C 2) χ (rawDistribution A J α hs ht D hD p τ
        (antiToEnergy A J α hs ht a)) := by
  rw [rawDistribution_smooth,product_schwartz]
  rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_RawCriticalNorm
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
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
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

local instance instFactLeENNRealOfNat_solutions_r8756e0_2 : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
lemma localizedRawSchwartz_H1 (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (a : antiPre A J α hs ht) :
    schwartzToH 1 (localizedRawSchwartz A J α hs ht D hD p τ χ a) =
      product 1 χ (rawH1 A J α hs ht D hD p τ (antiToEnergy A J α hs ht a)) := by
  apply toDistribution_injective 1
  rw [schwartzToH_spec,localizedRawSchwartz_spec]
  have h := toDistribution_product (E := Space) (F := C 2) 1 χ
    (rawH1 A J α hs ht D hD p τ (antiToEnergy A J α hs ht a))
  have hraw := rawH1_spec A J α hs ht D hD p τ (antiToEnergy A J α hs ht a)
  simp only [toDistribution,Nat.cast_one] at h hraw ⊢
  rw [hraw] at h
  exact h.symm

omit [MeasurableSpace X] [BorelSpace X] in
lemma localizedRawSchwartz_compact (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (hc : HasCompactSupport (χ : Space → ℂ)) (a : antiPre A J α hs ht) :
    HasCompactSupport (localizedRawSchwartz A J α hs ht D hD p τ χ a : Space → C 2) := by
  have he : (localizedRawSchwartz A J α hs ht D hD p τ χ a : Space → C 2) =
      (χ : Space → ℂ) • (SchwartzMap.postcompCLM (embed 2)
        (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p a.val)) : Space → C 2) := by
    funext x
    exact SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth _ x
  rw [he]
  exact hc.smul_right

lemma localizedRawSchwartz_H1_bound (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (a : antiPre A J α hs ht) :
    ‖schwartzToH 1 (localizedRawSchwartz A J α hs ht D hD p τ χ a)‖ ≤
      (‖product (F := C 2) 1 χ‖ * ‖rawH1 A J α hs ht D hD p τ‖) *
        ‖antiToEnergy A J α hs ht a‖ := by
  rw [localizedRawSchwartz_H1]
  apply ((product (F := C 2) 1 χ).le_opNorm _).trans
  have h := mul_le_mul_of_nonneg_left
    ((rawH1 A J α hs ht D hD p τ).le_opNorm (antiToEnergy A J α hs ht a))
    (norm_nonneg (product (F := C 2) 1 χ))
  simpa only [mul_assoc] using h

lemma raw_critical_norm (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (hc : HasCompactSupport (χ : Space → ℂ)) (L : Space ≃L[ℝ] Space) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : antiPre A J α hs ht,
      let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (localizedRawSchwartz A J α hs ht D hD p τ χ a)
      ‖u.toLp 4 (volume : Measure Space)‖ +
        ∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i} u).toLp 2 (volume : Measure Space)‖ ≤
          K * ‖antiToEnergy A J α hs ht a‖ := by
  obtain ⟨B,hB,hbound⟩ := critical_linear_H1 (F := C 2)
    (by simp [Space] : Module.finrank ℝ Space = 4) L
  let K := ‖product (F := C 2) 1 χ‖ * ‖rawH1 A J α hs ht D hD p τ‖
  refine ⟨B*K,by dsimp [K] <;> positivity,fun a => ?_⟩
  dsimp only
  have hb := hbound (localizedRawSchwartz A J α hs ht D hD p τ χ a)
    (localizedRawSchwartz_compact A J α hs ht D hD p τ χ hc a)
  have hk := localizedRawSchwartz_H1_bound A J α hs ht D hD p τ χ a
  apply hb.trans
  have h := mul_le_mul_of_nonneg_left hk hB
  simpa only [mul_assoc,K] using h
end TamingCompatibility.GeometricHilbert

end
end

end
end
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

lemma normalizedCutoff_compact (L : E ≃L[ℝ] E) (q : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) (hc : HasCompactSupport (χ : E → ℂ)) :
    HasCompactSupport (normalizedCutoff L q r hr χ : E → ℂ) := by
  have hk := hc.image (show Continuous (fun z => r • L.symm z+q) by fun_prop)
  apply hk.of_isClosed_subset (isClosed_tsupport _)
  intro y hy
  let z := r⁻¹ • L y-r⁻¹ • L q
  refine ⟨z,normalizedCutoff_support L q r hr χ hy,?_⟩
  apply L.injective
  simp only [map_add,map_smul,ContinuousLinearEquiv.apply_symm_apply,z,
    smul_sub,smul_smul,mul_inv_cancel₀ hr,one_smul,sub_add_cancel]

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedLiftBasisBound
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
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

theorem geometric_center_energy_two_jet_oai (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U)
    (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
    (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ η : 𝓢(Space,ℂ), HasCompactSupport (η : Space → ℂ) ∧ (∀ x ∈ V, η x = 1) ∧
      ∃ L : Space ≃L[ℝ] Space, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (_hr : 0 < t.1),
      ∀ (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair)) (M : ℝ), 0 ≤ M →
      (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
      (∀ k ≤ 3, ∀ v : Fin k → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (SchwartzMap.postcompCLM (embed 2) g))) x‖ ≤ M/t.1^k) →
      (∀ v : antiEnergy A J α hs ht,
        ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
      let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (localizedRawSchwartz A J α hs ht D hD p τ η a)
      ∀ x : Space, ((χ 4 : Space → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖u (t.1 • x+L t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i} u) (t.1 • x+L t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ Space j} (∂_{stdOrthonormalBasis ℝ Space i} u)) (t.1 • x+L t.2)‖ ≤
        C₀*(M*t.1^3 + ‖antiToEnergy A J α hs ht a‖) := by
  obtain ⟨d⟩ := exists_geometric_square_data A J α hs ht D p hU hUD q hq
  obtain ⟨η₀,hη₀,hηW,V,hV,hqV,hVW,hηone⟩ := SchwartzCutoff.exists_one_near d.openW d.qW
  let η := SchwartzMap.postcompCLM Complex.ofRealCLM η₀
  have hηs : tsupport η ⊆ tsupport η₀ := tsupport_comp_subset (map_zero Complex.ofRealCLM) η₀
  have hηc : HasCompactSupport (η : Space → ℂ) := hη₀.of_isClosed_subset (isClosed_tsupport η) hηs
  have hη (z) (hz : z ∈ V) : η z = 1 := by
    simp only [η,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,hηone z hz,Complex.ofReal_one]
  obtain ⟨L,C₀,hC,hest⟩ := metric_square_center_energy_two_jet q (coordinateMetric J α ht p.val q)
    (fun i => (D p).frame i q) (fun i j => (D p).frame_gram q (hUD hq) i j)
    d.a d.b d.ρ d.g d.polarized (chartDensity J α p.val q)
    (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hq))) d.center ζ hζ χ hχ hζχ
  obtain ⟨K,hK,hcritical⟩ := raw_critical_norm A J α hs ht D hD p τ η hηc L
  have hshrink : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), ∀ n : Fin 4, ∀ hr : t.1 ≠ 0,
      tsupport (normalizedCutoff L t.2 t.1 hr (χ (n.val+1))) ⊆ V := by
    apply (Filter.eventually_all.mpr ?_)
    intro n
    exact normalizedCutoff_eventually_support L q (χ (n.val+1)) (hcχ n.val (by omega)) hV hqV
  refine ⟨d.W,V,d.openW,d.qW,d.WU,hV,hqV,hVW,η,hηc,hη,L,C₀*(K+1),by positivity,?_⟩
  filter_upwards [hest,hshrink] with t hh hsupport
  intro hr f a g M hM hg hderiv heq
  dsimp only
  have hPDE : ∀ n ≤ 3, smulLeftCLM (C 2) (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1)))
      (square EuclideanEnergy.e d.a d.b d.ρ (localizedRawSchwartz A J α hs ht D hD p τ η a : 𝓢'(Space,C 2))) =
      smulLeftCLM (C 2) (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1)))
        (SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2)) := by
    intro n hn
    have hv := hsupport ⟨n,by omega⟩ hr.ne'
    apply actual_localized_square_source A J α hs ht D hD p τ hUD hτ d η _
      (normalizedCutoff_compact L t.2 t.1 hr.ne' _ (hcχ n hn)) (hv.trans hVW) ?_ f a g hg heq
    intro z hz
    filter_upwards [hV.mem_nhds (hv hz)] with y hy
    exact hη y hy
  have hb := hh hr (localizedRawSchwartz A J α hs ht D hD p τ η a)
    (SchwartzMap.postcompCLM (embed 2) g) M hM hderiv hPDE
  intro x hx
  apply (hb x hx).trans
  have hk := hcritical a
  have hpow : 0 ≤ M*t.1^3 := mul_nonneg hM (pow_nonneg hr.le _)
  calc
    _ ≤ C₀*(M*t.1^3+K*‖antiToEnergy A J α hs ht a‖) :=
      mul_le_mul_of_nonneg_left (by linarith only [hk]) hC
    _ ≤ C₀*(K+1)*(M*t.1^3+‖antiToEnergy A J α hs ht a‖) := by
      nlinarith [norm_nonneg (antiToEnergy A J α hs ht a),mul_nonneg hK hpow]
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.geometric_center_energy_two_jet_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.geometric_center_energy_two_jet_oai.{u_1}
