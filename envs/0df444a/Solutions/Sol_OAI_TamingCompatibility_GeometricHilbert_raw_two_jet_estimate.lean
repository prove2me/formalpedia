-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:32:26.664462+00:00
-- url     : https://prove2.me/submissions/88e96894-4899-4c7e-a62d-945b176f3b18

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028
import Definitions.Def_OAIQ239Tc029
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_raw_square_source

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedGraphLift
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section


namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter Set
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma mem_localSolutionSpace_iff (U : Set E) (n : ℕ)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) (u : H E F 1 × H E F n) :
    u ∈ localSolutionSpace U n P ↔
      ∀ (g : 𝓢(E,ℂ)), HasCompactSupport (g : E → ℂ) → tsupport g ⊆ U →
        smulLeftCLM F g (P (toDistribution E F 1 u.1)) =
        smulLeftCLM F g (toDistribution E F n u.2) := by
  simp only [localSolutionSpace,Submodule.mem_iInf,LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,
    sub_apply,ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd',map_sub,sub_eq_zero]

lemma interiorLift_spec (U : Set E) (n : ℕ) (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (g : 𝓢(E,ℂ))
    (h : ∀ u : localSolutionSpace U n P,
      MemSobolev ((n:ℝ)+2) 2 (smulLeftCLM F g (toDistribution E F 1 u.val.1)))
    (u : localSolutionSpace U n P) :
    toDistribution E F ((n:ℝ)+2) (interiorLift U n P g h u) =
      smulLeftCLM F g (toDistribution E F 1 u.val.1) :=
  InjectiveLinearLift.continuousLift_spec _ _ _ _ _
end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SobolevBounded
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
open _root_.MeasureTheory TemperedDistribution EuclideanSobolev
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartz_sobolev_bound (s : ℝ) (hs : Module.finrank ℝ E < 2*s) (f : 𝓢(E,F)) (x : E) :
    ‖f x‖ ≤ ‖sobolevToBounded (E := E) (F := F) s hs‖ * ‖schwartzToH s f‖ := by
  calc
    ‖f x‖ ≤ ‖f.toBoundedContinuousFunction‖ := f.toBoundedContinuousFunction.norm_coe_le_norm x
    _ = ‖sobolevToBounded s hs (schwartzToH s f)‖ := congrArg norm (sobolevToBounded_schwartz s hs f).symm
    _ ≤ _ := (sobolevToBounded (E := E) (F := F) s hs).le_opNorm (schwartzToH s f)

lemma schwartz_second_derivative_bound (s : ℝ)
    (hs : Module.finrank ℝ E < 2*(s-1-1)) (v w : E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : 𝓢(E,F)) (x : E),
      ‖(∂_{w} (∂_{v} f)) x‖ ≤ K * ‖schwartzToH s f‖ := by
  let T := (sobolevToBounded (E := E) (F := F) (s-1-1) hs).comp
    ((derivative (s-1) w).comp (derivative s v))
  refine ⟨‖T‖,norm_nonneg T,fun f x => ?_⟩
  have he : sobolevToBounded (s-1-1) hs
      (derivative (s-1) w (derivative s v (schwartzToH s f))) =
      (∂_{w} (∂_{v} f)).toBoundedContinuousFunction := by
    rw [← schwartzToH_derivative,← schwartzToH_derivative]
    exact sobolevToBounded_schwartz (s-1-1) hs _
  calc
    ‖(∂_{w} (∂_{v} f)) x‖ ≤ ‖(∂_{w} (∂_{v} f)).toBoundedContinuousFunction‖ :=
      (∂_{w} (∂_{v} f)).toBoundedContinuousFunction.norm_coe_le_norm x
    _ = ‖T (schwartzToH s f)‖ := congrArg norm he.symm
    _ ≤ _ := T.le_opNorm _

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolev
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartz_two_jet_bound {ι : Type*} [Fintype ι] (v : ι → E) (s : ℝ)
    (hs : Module.finrank ℝ E < 2*(s-1-1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : 𝓢(E,F)) (x : E),
      ‖f x‖ + ∑ i, ‖(∂_{v i} f) x‖ + ∑ i, ∑ j, ‖(∂_{v j} (∂_{v i} f)) x‖ ≤
        K * ‖schwartzToH s f‖ := by
  classical
  have hs₀ : Module.finrank ℝ E < 2*s := by linarith
  have hs₁ : Module.finrank ℝ E < 2*(s-1) := by linarith
  let C := ‖sobolevToBounded (E := E) (F := F) s hs₀‖
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  choose K₁ hK₁ hb₁ using fun i => schwartz_first_derivative_bound (F := F) s hs₁ (v i)
  choose K₂ hK₂ hb₂ using fun i j => schwartz_second_derivative_bound (F := F) s hs (v i) (v j)
  refine ⟨C + ∑ i, K₁ i + ∑ i, ∑ j, K₂ i j,
    add_nonneg (add_nonneg hC (Finset.sum_nonneg (fun i _ => hK₁ i)))
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hK₂ i j))),fun f x => ?_⟩
  have h0 := schwartz_sobolev_bound s hs₀ f x
  have h1 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb₁ i f x)
  have h2 := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb₂ i j f x))
  calc
    _ ≤ C * ‖schwartzToH s f‖ + (∑ i, K₁ i * ‖schwartzToH s f‖) +
        ∑ i, ∑ j, K₂ i j * ‖schwartzToH s f‖ := add_le_add (add_le_add h0 h1) h2
    _ = _ := by simp only [add_mul,Finset.sum_mul]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_LinearUniform
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
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

lemma metric_square_uniform_regular
    {U : Set V} (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 2 →L[ℝ] R m)) (b : 𝓢(V,R 2 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p = c * ∑ t, frame t i * frame t j)
    : ∃ W : Set V, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ (n : ℕ) (u : 𝓢'(V,C 2)),
      MemSobolevLoc U 1 u → MemSobolevLoc U n (square e a b ρ u) →
      MemSobolevLoc W ((n:ℝ)+2) u := by
  let G := principalScalar a ρ
  have hg : ∀ i j, G i j p = (c * ∑ t, frame t i * frame t j : ℝ) := by
    intro i j
    rw [principalScalar_apply a ρ g ha,hgp]
  have hk : 0 < ((2*Real.pi)^2)⁻¹ := by positivity
  obtain ⟨A,hA⟩ := exists_principal_normalization metric frame hframe c _ hc hk G p hg
  let B := squareFirst e (fun i => coefficient (a i)) (coefficient b)
    (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)
  let Cc := squareZero e (coefficient b) (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)
  obtain ⟨W,hW,hpW,hWU,hall⟩ := linearly_normalized_uniform_regular hU p hp e G A hA
    (fun q : Fin 4 × Fin 2 × Fin 2 => B q.1 q.2.1 q.2.2)
    (fun q => unit 2 2 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 2 × Fin 2 => Cc q.1 q.2) (fun q => unit 2 2 q.1 q.2)
  refine ⟨W,hW,hpW,hWU,?_⟩
  intro n u hu hf
  apply hall n u hu
  have h := hf
  rw [square_scalar_expansion e a b ρ g ha] at h
  rw [add_assoc,entries_lowerOrder] at h
  exact h

end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter Set
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma localSolutionSpace.source_regular (U : Set E) (n : ℕ)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) (u : localSolutionSpace U n P) :
    MemSobolevLoc U n (P (toDistribution E F 1 u.val.1)) := by
  intro ψ hψ hψU
  rw [(mem_localSolutionSpace_iff U n P u.val).mp u.property ψ hψ hψU]
  exact memSobolev_nat_product n ψ (toDistribution_memSobolev n u.val.2)

lemma localSolutionSpace.solution_regular (U : Set E) (n : ℕ)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) (u : localSolutionSpace U n P) :
    MemSobolevLoc U 1 (toDistribution E F 1 u.val.1) := by
  exact memSobolevLoc_one_of_global (toDistribution_memSobolev 1 u.val.1) U

theorem local_regular_estimate (U W : Set E) (n : ℕ)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (hreg : ∀ u, MemSobolevLoc U 1 u → MemSobolevLoc U n (P u) →
      MemSobolevLoc W ((n:ℝ)+2) u)
    (g : 𝓢(E,ℂ)) (hg : HasCompactSupport (g : E → ℂ)) (hgW : tsupport g ⊆ W) :
    ∃ T : localSolutionSpace U n P →L[ℂ] H E F ((n:ℝ)+2),
      ∀ u, toDistribution E F ((n:ℝ)+2) (T u) =
        smulLeftCLM F g (toDistribution E F 1 u.val.1) := by
  have hr (u : localSolutionSpace U n P) :
      MemSobolev ((n:ℝ)+2) 2 (smulLeftCLM F g (toDistribution E F 1 u.val.1)) :=
    hreg _ (localSolutionSpace.solution_regular U n P u)
      (localSolutionSpace.source_regular U n P u) g hg hgW
  exact ⟨interiorLift U n P g hr,interiorLift_spec U n P g hr⟩
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
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

lemma metric_square_uniform_estimate
    {U : Set V} (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 2 →L[ℝ] R m)) (b : 𝓢(V,R 2 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p = c * ∑ t, frame t i * frame t j) :
    ∃ W : Set V, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ (n : ℕ)
      (χ : 𝓢(V,ℂ)), HasCompactSupport (χ : V → ℂ) → tsupport χ ⊆ W →
      ∃ T : localSolutionSpace U n (square e a b ρ) →L[ℂ] H V (C 2) ((n:ℝ)+2),
      ∀ u, toDistribution V (C 2) ((n:ℝ)+2) (T u) =
        smulLeftCLM (C 2) χ (toDistribution V (C 2) 1 u.val.1) := by
  obtain ⟨W,hW,hpW,hWU,hreg⟩ := metric_square_uniform_regular hU p hp metric frame hframe
    a b ρ g ha c hc hgp
  refine ⟨W,hW,hpW,hWU,fun n χ hχ hχW => ?_⟩
  exact local_regular_estimate U W n (square e a b ρ) (hreg n) χ hχ hχW

end TamingCompatibility.ComplexMatrix

end
end

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
lemma exists_geometric_square_estimate (p : A.centers)
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (q : Space) (hq : q ∈ U) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
        (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (ρ : 𝓢(Space,ℝ)),
        (∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p) i z) ∧
        (∀ z ∈ W, b z = normalB J α ht p.val (D p) z) ∧
        (∀ z ∈ W, ρ z = chartDensity J α p.val z) ∧
        ∀ (n : ℕ) (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
          ∃ T : localSolutionSpace W n (square EuclideanEnergy.e a b ρ) →L[ℂ] H Space (C 2) ((n:ℝ)+2),
            ∀ u, toDistribution Space (C 2) ((n:ℝ)+2) (T u) =
              smulLeftCLM (C 2) χ (toDistribution Space (C 2) 1 u.val.1) := by
  obtain ⟨d⟩ := exists_geometric_square_data A J α hs ht D p hU hUD q hq
  obtain ⟨V,hV,hqV,hVW,hest⟩ := metric_square_uniform_estimate (m := 4) d.openW q d.qW
    (coordinateMetric J α ht p.val q) (fun i => (D p).frame i q)
    ((D p).frame_gram q (hUD hq)) d.a d.b d.ρ d.g
    d.polarized
    (chartDensity J α p.val q) (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hq))) d.center
  refine ⟨d.W,V,d.openW,d.qW,d.WU,hV,hqV,hVW,?_⟩
  refine ⟨d.a,d.b,d.ρ,d.agreeA,d.agreeB,d.agreeρ,?_⟩
  simpa only [Space,EuclideanEnergy.V] using hest

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
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Set
open scoped SchwartzMap
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma interior_estimate_apply (U : Set E) (n : ℕ) (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (χ : 𝓢(E,ℂ)) (T : localSolutionSpace U n P →L[ℂ] H E F ((n:ℝ)+2))
    (hT : ∀ w, toDistribution E F ((n:ℝ)+2) (T w) =
      smulLeftCLM F χ (toDistribution E F 1 w.val.1))
    (j : Z →L[ℝ] H E F 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Z) (f : H E F n),
      (∀ ψ : 𝓢(E,ℂ), HasCompactSupport (ψ : E → ℂ) → tsupport ψ ⊆ U →
        smulLeftCLM F ψ (P (toDistribution E F 1 (j u))) =
          smulLeftCLM F ψ (toDistribution E F n f)) →
      ∃ v : H E F ((n:ℝ)+2),
        toDistribution E F ((n:ℝ)+2) v = smulLeftCLM F χ (toDistribution E F 1 (j u)) ∧
        ‖v‖ ≤ C * (‖u‖+‖f‖) := by
  refine ⟨‖T‖ * max ‖j‖ 1,by positivity,fun u f heq => ?_⟩
  let w : localSolutionSpace U n P := ⟨(j u,f), (mem_localSolutionSpace_iff U n P (j u,f)).mpr heq⟩
  refine ⟨T w,hT w,?_⟩
  have hj := j.le_opNorm u
  have hju : ‖j u‖ ≤ max ‖j‖ 1 * (‖u‖+‖f‖) := by
    calc
      ‖j u‖ ≤ ‖j‖ * ‖u‖ := hj
      _ ≤ max ‖j‖ 1 * ‖u‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max ‖j‖ 1 * (‖u‖+‖f‖) := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (norm_nonneg _)) (le_trans (norm_nonneg j) (le_max_left ‖j‖ 1))
  have hf : ‖f‖ ≤ max ‖j‖ 1 * (‖u‖+‖f‖) := by
    calc
      ‖f‖ ≤ 1 * (‖u‖+‖f‖) := by nlinarith [norm_nonneg u]
      _ ≤ max ‖j‖ 1 * (‖u‖+‖f‖) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  calc
    ‖T w‖ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
    _ ≤ ‖T‖ * (max ‖j‖ 1 * (‖u‖+‖f‖)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
      change max ‖j u‖ ‖f‖ ≤ _
      exact max_le hju hf
    _ = _ := by ring

end TamingCompatibility.HilbertSobolev

end
end

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
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma raw_uniform_estimate (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∀ (n : ℕ) (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
        (g : 𝓢(Space,EuclideanEnergy.Pair)),
        (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
        (∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
        ∃ v : H Space (C 2) ((n:ℝ)+2),
          toDistribution Space (C 2) ((n:ℝ)+2) v =
            smulLeftCLM (C 2) χ (rawDistribution A J α hs ht D hD p τ u) ∧
          ‖v‖ ≤ K * (‖u‖+‖schwartzToH (n:ℝ) (SchwartzMap.postcompCLM (embed 2) g)‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,a,b,ρ,ha,hb,hρ,hest⟩ :=
    exists_geometric_square_estimate A J α hs ht D p hU hUD q hq
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,fun n χ hc hχV => ?_⟩
  obtain ⟨T,hT⟩ := hest n χ hc hχV
  obtain ⟨K,hK,hbound⟩ := interior_estimate_apply W n (square EuclideanEnergy.e a b ρ) χ T hT
    (rawH1 A J α hs ht D hD p τ)
  refine ⟨K,hK,fun f u g hg heq => ?_⟩
  have he : ∀ ψ : 𝓢(Space,ℂ), HasCompactSupport (ψ : Space → ℂ) → tsupport ψ ⊆ W →
      smulLeftCLM (C 2) ψ (square EuclideanEnergy.e a b ρ
        (toDistribution Space (C 2) 1 (rawH1 A J α hs ht D hD p τ u))) =
      smulLeftCLM (C 2) ψ (toDistribution Space (C 2) n
        (schwartzToH n (SchwartzMap.postcompCLM (embed 2) g))) := by
    intro ψ hψ hψW
    rw [rawH1_spec,schwartzToH_spec]
    exact raw_square_source A J α hs ht D hD p τ hW (hWU.trans hUD)
      (fun z hz => hτ z (hWU hz)) a b ρ ha hb hρ f u heq g hg ψ hψ hψW
  have hb := hbound u (schwartzToH n (SchwartzMap.postcompCLM (embed 2) g))
  dsimp only [Space,EuclideanEnergy.V,ScalarPair.F,C] at hb he
  obtain ⟨v,hv,hvb⟩ := hb he
  rw [rawH1_spec] at hv
  exact ⟨v,hv,hvb⟩

end TamingCompatibility.GeometricHilbert

end
end

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

lemma raw_schwartz_estimate (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∀ (n : ℕ) (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair)),
        (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
        (∀ v : antiEnergy A J α hs ht,
          ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
            ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
        ‖schwartzToH ((n:ℝ)+2) (localizedRawSchwartz A J α hs ht D hD p τ χ a)‖ ≤
          K * (‖antiToEnergy A J α hs ht a‖+‖schwartzToH (n:ℝ) (SchwartzMap.postcompCLM (embed 2) g)‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,hest⟩ :=
    raw_uniform_estimate A J α hs ht D hD p τ hU hUD hτ q hq
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,fun n χ hc hχV => ?_⟩
  obtain ⟨K,hK,hbound⟩ := hest n χ hc hχV
  refine ⟨K,hK,fun f a g hg heq => ?_⟩
  obtain ⟨v,hv,hvb⟩ := hbound f (antiToEnergy A J α hs ht a) g hg heq
  have he : schwartzToH ((n:ℝ)+2) (localizedRawSchwartz A J α hs ht D hD p τ χ a) = v := by
    apply toDistribution_injective ((n:ℝ)+2)
    rw [schwartzToH_spec,localizedRawSchwartz_spec,hv]
  rw [he]
  exact hvb

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawJetEstimate
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
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

lemma coordinateTwoJet_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : 𝓢(Space,ComplexMatrix.C 2)) (x : Space),
    coordinateTwoJet u x ≤ C * ‖schwartzToH (5:ℝ) u‖ := by
  have hd : Module.finrank ℝ Space < 2*((5:ℝ)-1-1) := by norm_num [Space]
  exact schwartz_two_jet_bound EuclideanEnergy.e 5 hd

lemma raw_two_jet_estimate_oai (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∀ (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair)),
        (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
        (∀ v : antiEnergy A J α hs ht,
          ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
            ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
        ∀ x : Space, coordinateTwoJet (localizedRawSchwartz A J α hs ht D hD p τ χ a) x ≤
          K * (‖antiToEnergy A J α hs ht a‖ +
            ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2) g)‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,hest⟩ :=
    raw_schwartz_estimate A J α hs ht D hD p τ hU hUD hτ q hq
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,fun χ hc hχV => ?_⟩
  obtain ⟨K,hK,hbound⟩ := hest 3 χ hc hχV
  obtain ⟨C,hC,hjet⟩ := coordinateTwoJet_bound
  refine ⟨C*K,mul_nonneg hC hK,fun f a g hg heq x => ?_⟩
  have hb := hbound f a g hg heq
  have h5 : ((3:ℕ):ℝ)+2 = 5 := by norm_num
  rw [h5] at hb
  simp only [Nat.cast_ofNat] at hb
  dsimp only [Space,EuclideanEnergy.V,ScalarPair.F,ComplexMatrix.C] at hb hjet ⊢
  have hj := hjet (localizedRawSchwartz A J α hs ht D hD p τ χ a) x
  have hm := mul_le_mul_of_nonneg_left hb hC
  have hf := hj.trans hm
  simpa only [mul_assoc] using hf

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.raw_two_jet_estimate_oai.{u_1}
