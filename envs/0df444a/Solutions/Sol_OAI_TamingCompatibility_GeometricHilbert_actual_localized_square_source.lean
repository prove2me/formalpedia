-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:33:27.849581+00:00
-- url     : https://prove2.me/submissions/d496ee24-acde-49bc-9db0-4d4e9be0a5d7

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028
import Definitions.Def_OAIQ239Tc029
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_raw_square_source

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

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScalarSquare
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

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_SquareCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution Filter
open scoped SchwartzMap LineDeriv Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {m : ℕ}

lemma square_cutoff_locality (v : ι → E) (a : ι → 𝓢(E,R 2 →L[ℝ] R m))
    (b : 𝓢(E,R 2 →L[ℝ] R m)) (ρ : 𝓢(E,ℝ)) (G : ι → ι → E → ℝ)
    (hG : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*G i j x) • ContinuousLinearMap.id ℝ (R 2))
    (g h : 𝓢(E,ℂ)) (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,C 2)) :
    smulLeftCLM (C 2) g (square v a b ρ (smulLeftCLM (C 2) h u)) =
      smulLeftCLM (C 2) g (square v a b ρ u) := by
  rw [square_scalar_expansion v a b ρ G hG,square_scalar_expansion v a b ρ G hG,
    add_assoc,add_assoc,entries_lowerOrder,entries_lowerOrder]
  simp only [map_add,map_neg]
  rw [show (∑ i,∑ j,smulLeftCLM (C 2) (principalScalar a ρ i j)
      (∂_{v i} (∂_{v j} (smulLeftCLM (C 2) h u)))) =
      directionalPrincipal v (principalScalar a ρ) (smulLeftCLM (C 2) h u) from rfl,
    directionalPrincipal_locality v (principalScalar a ρ) g h hh u,
    matrixLowerOrder_locality _ _ _ _ _ g h hh u]
  rfl
end TamingCompatibility.ComplexMatrix

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricLocalPDE
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

lemma actual_localized_square_source_oai (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    {q : Space} (d : SquareData A J α ht D p U q)
    (η χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχ : tsupport χ ⊆ d.W)
    (hη : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1)
    (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair))
    (hg : ∀ z ∈ d.W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z)
    (heq : ∀ v : antiEnergy A J α hs ht,
      ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
        ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
    smulLeftCLM (C 2) χ (square EuclideanEnergy.e d.a d.b d.ρ
      (localizedRawSchwartz A J α hs ht D hD p τ η a : 𝓢'(Space,C 2))) =
    smulLeftCLM (C 2) χ (SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2)) := by
  rw [localizedRawSchwartz_spec]
  rw [square_cutoff_locality EuclideanEnergy.e d.a d.b d.ρ d.g d.polarized χ η hη
    (rawDistribution A J α hs ht D hD p τ (antiToEnergy A J α hs ht a))]
  exact raw_square_source A J α hs ht D hD p τ d.openW (d.WU.trans hUD)
    (fun z hz => hτ z (d.WU hz)) d.a d.b d.ρ d.agreeA d.agreeB d.agreeρ
    f (antiToEnergy A J α hs ht a) heq g hg χ hc hχ

end TamingCompatibility.GeometricHilbert

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.actual_localized_square_source_oai.{u_1}
