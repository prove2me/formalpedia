-- Prove2me | solution 1 for OAI.PlanarFalconer.restoredTwoRootCandidate_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:41:38.146342+00:00
-- url     : https://prove2.me/submissions/ed8d4c41-aaa8-4dfa-a596-d0316cacae00

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Definitions.Def_OAIQ088F000

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicClasses
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem normalizedClass_apply (Q : DyadicSquare) (μ : Measure Plane)
    (L : Finset (List (Bool × Bool))) (f : List (Bool × Bool) → List ℕ) (T : List ℕ)
    (S : Set Plane) :
    normalizedClass Q μ L f T S =
      (μ (leafUnion Q (classLeaves L f T)))⁻¹ *
        μ (S ∩ leafUnion Q (classLeaves L f T)) := by
  simp only [normalizedClass, classMeasure, univ_inter,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (leafUnion_measurable Q _)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_ActualAngularTests
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem stripCount_neg {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) (ω : Plane) :
    stripCount S v W (-ω) = stripCount S v W ω := by
  classical
  have he (i : ι) : planeDot (v i) (-ω) = -planeDot (v i) ω := by simp [planeDot]; ring
  simp only [stripCount,he,abs_neg]

theorem parallelTestCount_neg (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) :
    parallelTestCount Q ρ g p P W (-ω) = parallelTestCount Q ρ g p P W ω := by
  have he : quarterTurn (-ω) = -quarterTurn ω := by ext i; fin_cases i <;> simp [quarterTurn]
  unfold parallelTestCount
  rw [he,stripCount_neg]

theorem projectionTestCount_neg (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) :
    projectionTestCount Q ρ p u P W (-ω) = projectionTestCount Q ρ p u P W ω :=
  stripCount_neg _ _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngleMaskPeriodicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem thickening_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (r x : ℝ) :
    x+T ∈ thickening r G ↔ x ∈ thickening r G := by
  constructor
  · intro hx
    obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
    refine mem_thickening_iff.mpr ⟨z-T,?_,?_⟩
    · exact (hG (z-T)).mp (by simpa using hz)
    · simpa only [Real.dist_eq] using (show |x-(z-T)| < r by
        convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [Real.dist_eq]; congr 1; ring))
  · intro hx
    obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
    exact mem_thickening_iff.mpr ⟨z+T,(hG z).mpr hz,by simpa using hd⟩

theorem thickenedIndicator_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (η : ℝ) :
    Function.Periodic (thickenedIndicator G η) T := by
  intro x
  classical
  simp only [thickenedIndicator,Set.indicator_apply,thickening_periodic hG]

theorem smoothAngleMask_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (η : ℝ) (hη : 0 < η) :
    Function.Periodic (smoothAngleMask G η hη) T := by
  intro x
  unfold smoothAngleMask
  simp only [convolution_def]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp := thickenedIndicator_periodic hG η (x-t)
  rw [show x+T-t = (x-t)+T by ring,hp]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CircleMaskCoordinates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_periodic (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Function.Periodic (sourceTestMask G d hd) (2*Real.pi) := by
  apply smoothAngleMask_periodic
  intro θ
  have he : sourceUnitDirection (θ+2*Real.pi) = sourceUnitDirection θ := by
    apply Subtype.ext
    simp only [sourceUnitDirection,sourceDirection,Real.cos_add_two_pi,Real.sin_add_two_pi]
  simp only [mem_preimage,he]

theorem circleTestMask_comp (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (θ : ℝ) :
    circleTestMask G d hd (sourceUnitDirection θ) = sourceTestMask G d hd θ := by
  unfold circleTestMask
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := (sourceTestMask_periodic G d hd).int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm,add_comm] using hp θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CircleMaskSupport
attribute [-instance] _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem circleTestMask_antipodal {G : Set UnitCircle}
    (hG : ∀ dir : UnitCircle, circleAntipode dir ∈ G ↔ dir ∈ G)
    (d : ℝ) (hd : 0 < d) (dir : UnitCircle) :
    circleTestMask G d hd (circleAntipode dir) = circleTestMask G d hd dir := by
  have hp : Function.Periodic (sourceTestMask G d hd) Real.pi := by
    apply smoothAngleMask_periodic
    intro θ
    simpa only [mem_preimage,sourceUnitDirection_add_pi] using hG (sourceUnitDirection θ)
  rw [← sourceUnitDirection_sourceAngle dir,← sourceUnitDirection_add_pi,
    circleTestMask_comp,circleTestMask_comp,hp]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ActualClassMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem coe_actualClassMass (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) :
    (actualClassMass Q μ N B T : ENNReal) = μ (actualClassDomain Q μ N B T) :=
  ENNReal.coe_toNNReal (measure_ne_top μ _)

instance actualClassMeasure_instFinite (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) : IsFiniteMeasure (actualClassMeasure Q μ N B T) := by
  constructor
  change (normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T) univ < ∞
  rw [normalizedClass_apply,univ_inter]
  change (μ (actualClassDomain Q μ N B T))⁻¹ * μ (actualClassDomain Q μ N B T) < ∞
  by_cases h : μ (actualClassDomain Q μ N B T) = 0
  · simp [h]
  · rw [ENNReal.inv_mul_cancel h (measure_ne_top μ _)]
    exact ENNReal.one_lt_top

theorem actualClassMass_smul_measure (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) :
    actualClassMass Q μ N B T • actualClassMeasure Q μ N B T =
      μ.restrict (actualClassDomain Q μ N B T) := by
  rw [ENNReal.smul_def,coe_actualClassMass]
  simp only [actualClassMeasure,normalizedClass,classMeasure,Measure.restrict_apply_univ]
  change μ (actualClassDomain Q μ N B T) •
    ((μ (actualClassDomain Q μ N B T))⁻¹ • μ.restrict (actualClassDomain Q μ N B T)) = _
  by_cases h : μ (actualClassDomain Q μ N B T) = 0
  · rw [h,zero_smul,Measure.restrict_eq_zero.mpr h]
  · rw [smul_smul,ENNReal.mul_inv_cancel h (measure_ne_top μ _),one_smul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_DescriptorMaskSymmetry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem descriptorGoodSet_antipodal (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (b : PolicyDescriptor) (dir : UnitCircle) :
    circleAntipode dir ∈ descriptorGoodSet Q ρ m N lam sig J i P b ↔
      dir ∈ descriptorGoodSet Q ρ m N lam sig J i P b := by
  cases b with
  | parallel g p =>
    change (parallelTestCount Q ρ g p P _ (-(dir:Plane)):ℝ) ≤ _ ↔ _
    rw [parallelTestCount_neg]
    rfl
  | projection p u =>
    change (projectionTestCount Q ρ p u P _ (-(dir:Plane)):ℝ) ≤ _ ↔ _
    rw [projectionTestCount_neg]
    rfl

theorem spatialAnchorMask_antipodal (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d)
    (hG : ∀ P : CellPath, ∀ dir : UnitCircle, circleAntipode dir ∈ G P ↔ dir ∈ G P)
    (x : Plane) (dir : UnitCircle) :
    spatialAnchorMask Q ρ n G d hd x (circleAntipode dir) = spatialAnchorMask Q ρ n G d hd x dir := by
  classical
  unfold spatialAnchorMask
  apply Finset.sum_congr rfl
  intro P _
  rw [circleTestMask_antipodal (hG P)]

theorem descriptorSpatialMask_antipodal (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (dir : UnitCircle) :
    descriptorSpatialMask Q ρ m N lam sig J i b x (circleAntipode dir) =
      descriptorSpatialMask Q ρ m N lam sig J i b x dir :=
  spatialAnchorMask_antipodal Q ρ _ _ _ _ (fun P dir => descriptorGoodSet_antipodal Q ρ m N lam sig J i P b dir) x dir

theorem descriptorListMask_antipodal (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (S : Finset PolicyDescriptor) (x : Plane) (dir : UnitCircle) :
    descriptorListMask Q ρ m N lam sig J i S x (circleAntipode dir) =
      descriptorListMask Q ρ m N lam sig J i S x dir := by
  unfold descriptorListMask
  apply Finset.prod_congr rfl
  intro b _
  exact descriptorSpatialMask_antipodal Q ρ m N lam sig J i b x dir

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OuterRootEquation21
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

namespace RootShellData

theorem ofOuter_measure (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam₁ lam₂ sig kap : ℝ) (c : ℕ) (U V : DyadicSquare) :
    (ofOuter Q₁ Q₂ ρ ν m₁ m₂ N lam₁ lam₂ sig kap c U V).measure =
      Measure.map (fun z : Plane × Plane => dist z.1 z.2)
        ((ρ.prod ν).withDensity (fun z => ENNReal.ofReal
          ((dist z.1 z.2)^(-(1/2:ℝ)) *
            (outerEndpointMask Q₁ ρ m₁ N lam₁ sig kap c z.1 (sourceRadialUnit z.2 z.1) *
             outerEndpointMask Q₂ ν m₂ N lam₂ sig kap c z.2 (sourceRadialUnit z.2 z.1))))) := rfl

end RootShellData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RestoredMaskCoverage
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem sourceRadialUnit_swap {x y : Plane} (hxy : x ≠ y) :
    sourceRadialUnit y x = circleAntipode (sourceRadialUnit x y) := by
  apply Subtype.ext
  change sourceRadialVector y x = -sourceRadialVector x y
  simp only [sourceRadialVector,ite_eq_right hxy,ite_eq_right hxy.symm]
  rw [← neg_sub y x,norm_neg,smul_neg]

theorem outerEndpointMask_radial_swap (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (c : ℕ) (z x y : Plane) :
    outerEndpointMask Q ρ m N lam sig kap c z (sourceRadialUnit y x) =
      outerEndpointMask Q ρ m N lam sig kap c z (sourceRadialUnit x y) := by
  by_cases hxy : x = y
  · subst y; rfl
  · rw [sourceRadialUnit_swap hxy]
    exact descriptorListMask_antipodal _ _ _ _ _ _ _ _ _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_TwoRootClassMixture
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem twoRootClassMeasure_mask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    (a : List ℕ × List ℕ) :
    twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a =
      (((actualClassMeasure Q₀ μ N B₀ a.1).prod (actualClassMeasure Q₁ ν N B₁ a.2)).withDensity
        (fun z => distanceWeight z * twoRootPairMask Q₀ Q₁ (actualClassMeasure Q₀ μ N B₀ a.1)
          (actualClassMeasure Q₁ ν N B₁ a.2) (m₀ a.1) (m₁ a.2) N lam sig kap β z)).map
            (fun z => dist z.1 z.2) := by
  unfold twoRootClassMeasure
  rw [RootShellData.ofOuter_measure]
  congr 2
  funext z
  simp only [twoRootPairMask,distanceWeight,outerEndpointMask_radial_swap]
  simp only [neg_div]
  exact ENNReal.ofReal_mul (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist z.1 z.2) _)

theorem twoRootClassCoefficient_prod (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N B₀ B₁ : ℕ) (a : List ℕ × List ℕ) :
    twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
      (actualClassMeasure Q₀ μ N B₀ a.1).prod (actualClassMeasure Q₁ ν N B₁ a.2) =
        (μ.prod ν).restrict (actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2) := by
  rw [← Measure.prod_restrict,← actualClassMass_smul_measure Q₀ μ N B₀ a.1,
    ← actualClassMass_smul_measure Q₁ ν N B₁ a.2,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  rfl

theorem twoRootClassCoefficient_measure (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
    (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) (a : List ℕ × List ℕ) :
    twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
      twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a =
        ((μ.prod ν).withDensity (fun z => distanceWeight z *
          twoRootRetainedMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a z)).map
            (fun z => dist z.1 z.2) := by
  rw [twoRootClassMeasure_mask,
    ← Measure.map_smul]
  congr 1
  rw [ENNReal.smul_def,← withDensity_smul_measure,← ENNReal.smul_def,twoRootClassCoefficient_prod]
  rw [← withDensity_indicator ((measurableSet_actualClassDomain ..).prod (measurableSet_actualClassDomain ..))]
  congr 1
  funext z
  classical
  unfold twoRootRetainedMask
  by_cases h : z ∈ actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h,mul_zero]

theorem restoredTwoRootCandidate_eq_sum_oai (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
    (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) :
    restoredTwoRootCandidate Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β =
      ∑ a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam,
        twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
          twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a := by
  simp_rw [twoRootClassCoefficient_measure]
  unfold restoredTwoRootCandidate restoredTwoRootMask
  simp_rw [Finset.mul_sum]
  rw [← Measure.map_finset_sum (by fun_prop)]
  congr 1
  ext S hS
  simp only [withDensity_apply _ hS,Measure.finsetSum_apply]
  exact lintegral_finsetSum _ (fun a _ =>
    (show Measurable distanceWeight by unfold distanceWeight; fun_prop).mul
      (measurable_twoRootRetainedMask ..))

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.restoredTwoRootCandidate_eq_sum_oai := @OAI.PlanarFalconer.restoredTwoRootCandidate_eq_sum_oai
