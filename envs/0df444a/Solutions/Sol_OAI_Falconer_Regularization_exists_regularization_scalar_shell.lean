-- Prove2me | solution 1 for OAI.Falconer.Regularization.exists_regularization_scalar_shell
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:55:07.575455+00:00
-- url     : https://prove2.me/submissions/98b4545c-45bf-42c8-a3ac-07656c36cf8d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_exists_regular_class_shell

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ProductFilterIntegral
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original-law splitting over the finite coarse product filter

No approximation of the spatial indicators is needed. Each filter piece
is a product of Borel sets, so its integral uses the two restricted original
marginals. The number of summands is the already proved partition bound.
-/
namespace Falconer
open Set MeasureTheory
open scoped BigOperators
variable {d : ℕ}

theorem finite_product_restriction {ι : Type*} [Fintype ι]
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A B : ι → Set (Space d))
    (hm : ∀ i, MeasurableSet (A i) ∧ MeasurableSet (B i))
    (hd : Pairwise fun i j => Disjoint (A i ×ˢ B i) (A j ×ˢ B j)) :
    (μ.prod ν).restrict (⋃ i, A i ×ˢ B i) =
      ∑ i, (μ.restrict (A i)).prod (ν.restrict (B i)) := by
  rw [Measure.restrict_iUnion hd (fun i => (hm i).1.prod (hm i).2),
    Measure.sum_fintype]
  simp only [Measure.prod_restrict]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationClasses
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regularization classes on the original all-dimensional dyadic tree

Classes are literal disjoint unions of half-open leaves. The measure
identities and the discarded mass bounds hold for the original law.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem leafUnion_measurable (Q : DyadicCube d) (L : Finset (CellPath d)) :
    MeasurableSet (leafUnion Q L) :=
  Finset.measurableSet_biUnion _ (fun p _ => (Q.descendant p).measurable)

theorem leafUnion_subset (Q : DyadicCube d) (_hQ : 0 < Q.side)
    (L : Finset (CellPath d)) : leafUnion Q L ⊆ Q.carrier := by
  intro z hz
  obtain ⟨p,_,hp⟩ := mem_iUnion₂.mp hz
  exact Q.descendant_subset p hp

theorem leafUnion_disjoint (Q : DyadicCube d) (_hQ : 0 < Q.side) {N : ℕ}
    {L T : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (hT : T ⊆ cubePaths d N) (h : Disjoint L T) :
    Disjoint (leafUnion Q L) (leafUnion Q T) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨p,hp,hzp⟩ := mem_iUnion₂.mp hz
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz'
  have hne : p ≠ q := by
    intro he; subst q; exact Finset.disjoint_left.mp h hp hq
  exact Set.disjoint_left.mp (Q.descendants_disjoint
    ((mem_cubePaths _ _ _).mp (hL hp) |>.trans ((mem_cubePaths _ _ _).mp (hT hq)).symm)
    hne) hzp hzq

theorem classLeaves_disjoint (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) {T U : List ℕ} (h : T ≠ U) :
    Disjoint (classLeaves L f T) (classLeaves L f U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact h ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

theorem leafUnion_classes (Q : DyadicCube d) (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) :
    (⋃ T ∈ L.image f, leafUnion Q (classLeaves L f T)) = leafUnion Q L := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨T,_,hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨p,(Finset.mem_filter.mp hp).1,hz⟩
  · intro hz
    obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨f p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      mem_iUnion₂.mpr ⟨p,by simp [classLeaves,hp],hz⟩⟩

theorem class_mass_sum (Q : DyadicCube d) (hQ : 0 < Q.side) (μ : Measure (Space d))
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) :
    (∑ T ∈ L.image f, classMeasure Q μ L f T univ) = μ (leafUnion Q L) := by
  classical
  simp only [classMeasure, Measure.restrict_apply_univ]
  rw [← leafUnion_classes Q L f]
  symm
  apply measure_biUnion_finset
  · intro T _ U _ hne
    exact leafUnion_disjoint Q hQ (fun _ hp => hL (Finset.mem_filter.mp hp).1)
      (fun _ hp => hL (Finset.mem_filter.mp hp).1) (classLeaves_disjoint L f hne)
  · intro T _; exact leafUnion_measurable Q _

theorem normalizedClass_probability (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) (T : List ℕ)
    (h : classMeasure Q μ L f T univ ≠ 0) :
    IsProbabilityMeasure (normalizedClass Q μ L f T) := by
  constructor
  simp only [normalizedClass, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel h
  simp only [classMeasure, Measure.restrict_apply_univ]
  exact measure_ne_top _ _

theorem normalizedClass_apply (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ)
    (S : Set (Space d)) :
    normalizedClass Q μ L f T S =
      (μ (leafUnion Q (classLeaves L f T)))⁻¹ *
        μ (S ∩ leafUnion Q (classLeaves L f T)) := by
  simp only [normalizedClass, classMeasure, univ_inter,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (leafUnion_measurable Q _)]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationSelection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting the regular classes with their original masses

Classes are disjoint unions of original leaves. Discarding small leaves
costs 2^(-2N), and discarding small classes costs their number times the
class threshold. No lower density of the original law is required.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularizationSet_measurable (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (T : List ℕ) : MeasurableSet (regularizationSet Q μ N B T) :=
  leafUnion_measurable Q _

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ClassSupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original support and occupied anchors of the normalized classes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

namespace Regularization

 theorem normalizedClass_absolutelyContinuous (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    normalizedClass Q μ L f T ≪ μ :=
  Measure.smul_absolutelyContinuous.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

 theorem sourceClass_absolutelyContinuous (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) : sourceClass Q μ N B p ≪ μ :=
  normalizedClass_absolutelyContinuous Q μ _ _ _

 theorem normalizedClass_parent (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    normalizedClass Q μ L f T Q.carrierᶜ = 0 := by
  rw [normalizedClass_apply]
  have he : Q.carrierᶜ ∩ leafUnion Q (classLeaves L f T) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (leafUnion_subset Q hQ _ hx.2)
  rw [he,measure_empty,mul_zero]

 theorem sourceClass_parent (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) (p : CellPath d) :
    sourceClass Q μ N B p Q.carrierᶜ = 0 :=
  normalizedClass_parent Q hQ μ _ _ _

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ClassRecombination
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact recombination with the original class masses -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem classMeasure_eq_mass_smul (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ)
    (hT : classMeasure Q μ L f T univ ≠ 0) :
    classMeasure Q μ L f T =
      classMeasure Q μ L f T univ • normalizedClass Q μ L f T := by
  let : IsFiniteMeasure (classMeasure Q μ L f T) := by unfold classMeasure; infer_instance
  rw [normalizedClass,smul_smul,ENNReal.mul_inv_cancel hT (measure_ne_top _ _),one_smul]

 theorem retained_class_mass_sum_le_one (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) (F : Finset (List ℕ)) (hF : F ⊆ L.image f) :
    (∑ T ∈ F, classMeasure Q μ L f T univ) ≤ 1 := by
  apply (Finset.sum_le_sum_of_subset hF).trans
  rw [class_mass_sum Q hQ μ hL f]
  exact prob_le_one

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ClassPairWeights
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original class-pair weights have total mass at most one -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal NNReal
variable {d : ℕ}

theorem retained_class_real_mass_sum_le_one (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) (F : Finset (List ℕ)) (hF : F ⊆ L.image f) :
    (∑ T ∈ F, (classMeasure Q μ L f T univ).toReal) ≤ 1 := by
  have hfinite (T : List ℕ) : classMeasure Q μ L f T univ ≠ ∞ := by
    change μ.restrict _ univ ≠ ∞
    exact measure_ne_top _ _
  rw [← ENNReal.toReal_sum (fun T _ => hfinite T)]
  exact (ENNReal.toReal_mono (by simp) (retained_class_mass_sum_le_one Q hQ μ hL f F hF)).trans_eq (by simp)

theorem retained_class_pair_real_mass_sum_le_one
    (Q₁ Q₂ : DyadicCube d) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N : ℕ} {L₁ L₂ : Finset (CellPath d)}
    (hL₁ : L₁ ⊆ cubePaths d N) (hL₂ : L₂ ⊆ cubePaths d N)
    (f₁ f₂ : CellPath d → List ℕ) (F G : Finset (List ℕ))
    (hF : F ⊆ L₁.image f₁) (hG : G ⊆ L₂.image f₂) :
    (∑ i ∈ F.product G,
      (classMeasure Q₁ μ L₁ f₁ i.1 univ * classMeasure Q₂ ν L₂ f₂ i.2 univ).toReal) ≤ 1 := by
  classical
  have he := Finset.sum_product F G (fun i : List ℕ × List ℕ =>
    (classMeasure Q₁ μ L₁ f₁ i.1 univ * classMeasure Q₂ ν L₂ f₂ i.2 univ).toReal)
  rw [Finset.product_eq_sprod,he]
  simp only [ENNReal.toReal_mul]
  rw [← Finset.sum_mul_sum]
  have h₁ := retained_class_real_mass_sum_le_one Q₁ hQ₁ μ hL₁ f₁ F hF
  have h₂ := retained_class_real_mass_sum_le_one Q₂ hQ₂ ν hL₂ f₂ G hG
  exact (mul_le_mul h₁ h₂ (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)) zero_le_one).trans_eq (one_mul 1)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorAmbient
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth ambient extensions of the actual spatially anchored masks

At each spatial point there is at most one active anchor cell. Consequently
the ambient derivative bound has no factor counting anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem descriptorAmbientMask_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) :
    Measurable (Function.uncurry (descriptorAmbientMask Q ρ m N σ J i b S)) := by
  apply Finset.measurable_sum
  intro p _
  exact ((capCutoffAmbient_contDiff (descriptorMaskRadius_pos N σ b) S _).continuous.measurable.comp
    measurable_snd).ite ((Q.descendant p).measurable.preimage measurable_fst) measurable_const

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_AmbientProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient products preserve every original descriptor support -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
variable {d : ℕ}

 theorem descriptorAmbientProduct_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) :
    Measurable (Function.uncurry (descriptorAmbientProduct Q ρ m N σ J i B S)) :=
  Finset.measurable_prod B (fun b _ => descriptorAmbientMask_measurable Q ρ m N σ J i b (S b))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_Shells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set ComplexConjugate
open scoped ENNReal

theorem fourier_energy_even (μ : Measure ℝ) (r : ℝ) :
    ‖charFun μ (-r)‖^2 = ‖charFun μ r‖^2 := by
  rw [charFun_neg]
  simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_EndpointWeightedDistance
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted distance law for two different endpoint profiles

Both original marginal laws and their separate normalizations are retained.
The endpoint factors may be the actual descriptor products of different
regularized classes. No common probability law is introduced.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem endpointDistanceWeight_bound {d : ℕ} (hd : 1 ≤ d) {s δ : ℝ} (hδ : 0 < δ)
    (B C : Space d → Space d → ℝ)
    (hB : ∀ x w, B x w ∈ Icc (0:ℝ) 1) (hC : ∀ x w, C x w ∈ Icc (0:ℝ) 1)
    (z : Space d × Space d) (hz : δ ≤ dist z.1 z.2/s) :
    endpointDistanceWeight s B C z ≤ δ^(-(((d:ℝ)-1)/2)) := by
  have hr : 0 ≤ (dist z.1 z.2/s)^(-(((d:ℝ)-1)/2)) := Real.rpow_nonneg (hδ.trans_le hz).le _
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  apply (mul_le_of_le_one_right (mul_nonneg hr (hB _ _).1) (hC _ _).2).trans
  exact (mul_le_of_le_one_right hr (hB _ _).2).trans
    (Real.rpow_le_rpow_of_nonpos hδ hz (by linarith))

 theorem endpointWeightedDistance_finite {d : ℕ} (hd : 1 ≤ d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P s δ : ℝ} (hM : 0 < M) (hP : 0 < P) (hδ : 0 < δ)
    (B C : Space d → Space d → ℝ)
    (hB : ∀ x w, B x w ∈ Icc (0:ℝ) 1) (hC : ∀ x w, C x w ∈ Icc (0:ℝ) 1)
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) :
    IsFiniteMeasure (endpointWeightedDistance μ ν M P s B C) := by
  have hbound : ∀ᵐ z ∂μ.prod ν,
      ENNReal.ofReal ((M⁻¹*P⁻¹)*endpointDistanceWeight s B C z) ≤
        ENNReal.ofReal ((M⁻¹*P⁻¹)*δ^(-(((d:ℝ)-1)/2))) := by
    filter_upwards [hsep] with z hz
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (endpointDistanceWeight_bound hd hδ B C hB hC z hz) (by positivity))
  let := finite_withDensity_of_bounded (μ.prod ν) _ ENNReal.ofReal_lt_top hbound
  unfold endpointWeightedDistance
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularOuterMask
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual outer mask, with both oriented restoration identities -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularOuterMask_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (profile : ℝ → ℝ) (N : ℕ) (σ κ : ℝ) (c : ℕ) :
    Measurable (Function.uncurry (regularOuterMask Q ρ profile N σ κ c)) :=
  descriptorAmbientProduct_measurable ..

theorem regularOuterMask_bounds (Q : DyadicCube d) (ρ : Measure (Space d))
    (profile : ℝ → ℝ) (N : ℕ) (σ κ : ℝ) (c : ℕ) (x w : Space d) :
    regularOuterMask Q ρ profile N σ κ c x w ∈ Icc (0:ℝ) 1 := by
  unfold regularOuterMask descriptorAmbientProduct
  constructor
  · exact Finset.prod_nonneg (fun b _ => (descriptorAmbientMask_global_bounds Q ρ _ N σ _ 0 b _ x w).1)
  · exact Finset.prod_le_one
      (fun b _ => (descriptorAmbientMask_global_bounds Q ρ _ N σ _ 0 b _ x w).1)
      (fun b _ => (descriptorAmbientMask_global_bounds Q ρ _ N σ _ 0 b _ x w).2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationTestBad
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining the actual class test failures on the original product law -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_eq_normalized (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) (T : List ℕ) (hp : regularizationLabel Q μ N B p = T) :
    sourceClass Q μ N B p =
      normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T := by
  unfold sourceClass
  rw [hp]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_PartitionMaskedMeasure
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact weighted law of a mask assembled on finitely many regions -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [MeasurableSpace X]

theorem withDensity_finset_sum (π : Measure X) (F : Finset ι) (f : ι → X → ℝ≥0∞)
    (hf : ∀ i ∈ F, Measurable (f i)) :
    π.withDensity (fun x => ∑ i ∈ F, f i x) = ∑ i ∈ F, π.withDensity (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    have he : (fun x => ∑ i ∈ insert a F, f i x) =
        f a + (fun x => ∑ i ∈ F, f i x) := by ext x; simp [ha]
    rw [he,withDensity_add_left (hf a (Finset.mem_insert_self a F)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)),Finset.sum_insert ha]

theorem finitePartitionMask_weighted_measure (π : Measure X) (F : Finset ι)
    (C : ι → Set X) (w : X → ℝ) (v : ι → X → ℝ)
    (hC : ∀ i ∈ F, MeasurableSet (C i)) (hw : Measurable w)
    (hv : ∀ i ∈ F, Measurable (v i))
    (hw0 : ∀ x, 0 ≤ w x) (hv0 : ∀ i ∈ F, ∀ x, 0 ≤ v i x) :
    π.withDensity (fun x => ENNReal.ofReal (w x * finitePartitionMask F C v x)) =
      ∑ i ∈ F, (π.restrict (C i)).withDensity (fun x => ENNReal.ofReal (w x*v i x)) := by
  classical
  have he : (fun x => ENNReal.ofReal (w x * finitePartitionMask F C v x)) =
      (fun x => ∑ i ∈ F, (C i).indicator (fun y => ENNReal.ofReal (w y*v i y)) x) := by
    funext x
    rw [finitePartitionMask,Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hx : x ∈ C i <;> simp [hx]
    · intro i hi
      exact mul_nonneg (hw0 x) (indicator_nonneg (fun y _ => hv0 i hi y) x)
  rw [he,withDensity_finset_sum π F
    (fun i x => (C i).indicator (fun y => ENNReal.ofReal (w y*v i y)) x)
    (fun i hi => ((hw.mul (hv i hi)).ennreal_ofReal.indicator (hC i hi)))]
  apply Finset.sum_congr rfl
  intro i hi
  exact withDensity_indicator (hC i hi) _

theorem finitePartitionMask_weighted_map (π : Measure X) (F : Finset ι)
    (C : ι → Set X) (w : X → ℝ) (v : ι → X → ℝ) (f : X → ℝ)
    (hC : ∀ i ∈ F, MeasurableSet (C i)) (hw : Measurable w)
    (hv : ∀ i ∈ F, Measurable (v i)) (hf : Measurable f)
    (hw0 : ∀ x, 0 ≤ w x) (hv0 : ∀ i ∈ F, ∀ x, 0 ≤ v i x) :
    (π.withDensity (fun x => ENNReal.ofReal (w x * finitePartitionMask F C v x))).map f =
      ∑ i ∈ F, ((π.restrict (C i)).withDensity (fun x => ENNReal.ofReal (w x*v i x))).map f := by
  rw [finitePartitionMask_weighted_measure π F C w v hC hw hv hw0 hv0,
    ← Measure.sum_coe_finset,Measure.map_sum hf.aemeasurable]
  exact Measure.sum_coe_finset F
    (fun i => ((π.restrict (C i)).withDensity (fun x => ENNReal.ofReal (w x*v i x))).map f)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FilteredEndpointDistance
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact masked distance decomposition over a Borel product filter -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem filteredEndpointDistance_product_sum {ι : Type*} [Fintype ι]
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A D : ι → Set (Space d))
    (hm : ∀ i, MeasurableSet (A i) ∧ MeasurableSet (D i))
    (hd : Pairwise fun i j => Disjoint (A i ×ˢ D i) (A j ×ˢ D j))
    (B C : Space d → Space d → ℝ) :
    filteredEndpointDistance μ ν (⋃ i, A i ×ˢ D i) B C =
      ∑ i, endpointWeightedDistance (μ.restrict (A i)) (ν.restrict (D i)) 1 1 1 B C := by
  classical
  unfold filteredEndpointDistance endpointWeightedDistance
  simp only [inv_one,one_mul]
  rw [finite_product_restriction μ ν A D hm hd,← Measure.sum_fintype,
    withDensity_sum,Measure.map_sum (by fun_prop),Measure.sum_fintype]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PartitionEndpointDistance
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact distance law for class-dependent endpoint masks -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem endpointPairMask_measurable (B C : Space d → Space d → ℝ)
    (hB : Measurable (Function.uncurry B)) (hC : Measurable (Function.uncurry C)) :
    Measurable (endpointPairMask B C) := by
  have hn : Measurable (fun z : Space d × Space d => NormedSpace.normalize (z.1-z.2)) := by
    unfold NormedSpace.normalize
    fun_prop
  exact (hB.comp (measurable_fst.prodMk hn)).mul (hC.comp (measurable_snd.prodMk hn))

theorem partitionEndpointDistance_eq_sum (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Γ : Set (Space d × Space d)) (_hΓ : MeasurableSet Γ)
    (F : Finset ι) (S T : ι → Set (Space d))
    (B C : ι → Space d → Space d → ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hT : ∀ i ∈ F, MeasurableSet (T i))
    (hB : ∀ i ∈ F, Measurable (Function.uncurry (B i)))
    (hC : ∀ i ∈ F, Measurable (Function.uncurry (C i)))
    (hB0 : ∀ i ∈ F, ∀ x w, 0 ≤ B i x w) (hC0 : ∀ i ∈ F, ∀ x w, 0 ≤ C i x w) :
    partitionEndpointDistance μ ν Γ F S T B C =
      ∑ i ∈ F, filteredEndpointDistance (μ.restrict (S i)) (ν.restrict (T i)) Γ (B i) (C i) := by
  unfold partitionEndpointDistance
  rw [finitePartitionMask_weighted_map _ F _ _ _ _
    (fun i hi => (hS i hi).prod (hT i hi))
    ((measurable_fst.dist measurable_snd).pow_const _)
    (fun i hi => endpointPairMask_measurable _ _ (hB i hi) (hC i hi))
    (by fun_prop) (fun _ => Real.rpow_nonneg dist_nonneg _)
    (fun i hi z => mul_nonneg (hB0 i hi _ _) (hC0 i hi _ _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.restrict_comm ((hS i hi).prod (hT i hi)),← Measure.prod_restrict]
  simp only [filteredEndpointDistance,endpointDistanceWeight,div_one,endpointPairMask,mul_assoc]

theorem partitionEndpointDistance_product_sum {κ : Type*} [Fintype κ]
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A D : κ → Set (Space d))
    (hm : ∀ j, MeasurableSet (A j) ∧ MeasurableSet (D j))
    (hd : Pairwise fun j k => Disjoint (A j ×ˢ D j) (A k ×ˢ D k))
    (F : Finset ι) (S T : ι → Set (Space d))
    (B C : ι → Space d → Space d → ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hT : ∀ i ∈ F, MeasurableSet (T i))
    (hB : ∀ i ∈ F, Measurable (Function.uncurry (B i)))
    (hC : ∀ i ∈ F, Measurable (Function.uncurry (C i)))
    (hB0 : ∀ i ∈ F, ∀ x w, 0 ≤ B i x w) (hC0 : ∀ i ∈ F, ∀ x w, 0 ≤ C i x w) :
    partitionEndpointDistance μ ν (⋃ j, A j ×ˢ D j) F S T B C =
      ∑ i ∈ F, ∑ j, endpointWeightedDistance (μ.restrict (A j ∩ S i))
        (ν.restrict (D j ∩ T i)) 1 1 1 (B i) (C i) := by
  rw [partitionEndpointDistance_eq_sum μ ν _
    (MeasurableSet.iUnion (fun j => (hm j).1.prod (hm j).2)) F S T B C hS hT hB hC hB0 hC0]
  apply Finset.sum_congr rfl
  intro i _
  rw [filteredEndpointDistance_product_sum _ _ A D hm hd]
  simp only [Measure.restrict_restrict (hm _).1,Measure.restrict_restrict (hm _).2]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_OriginalClassDistance
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact distance-law weights of restrictions to original classes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem endpointWeightedDistance_smul (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν]
    (a b : ℝ≥0∞) (M P s : ℝ) (B C : Space d → Space d → ℝ) :
    endpointWeightedDistance (a • μ) (b • ν) M P s B C =
      (a*b) • endpointWeightedDistance μ ν M P s B C := by
  unfold endpointWeightedDistance
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
    withDensity_smul_measure,Measure.map_smul]

namespace Regularization

theorem normalizedClass_finite (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    IsFiniteMeasure (normalizedClass Q μ L f T) := by
  by_cases hT : classMeasure Q μ L f T univ = 0
  · have hz : classMeasure Q μ L f T = 0 := Measure.measure_univ_eq_zero.mp hT
    simp only [normalizedClass,hz,smul_zero]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  · let : IsProbabilityMeasure (normalizedClass Q μ L f T) := normalizedClass_probability Q μ L f T hT
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem sourceClass_finite (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (N B : ℕ) (p : CellPath d) : IsFiniteMeasure (sourceClass Q μ N B p) :=
  normalizedClass_finite Q μ _ _ _

theorem restrict_class_eq_mass_smul (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (T : List ℕ) (hT : classMeasure Q μ L f T univ ≠ 0)
    (A : Set (Space d)) (hA : MeasurableSet A) :
    μ.restrict (A ∩ leafUnion Q (classLeaves L f T)) =
      classMeasure Q μ L f T univ • (normalizedClass Q μ L f T).restrict A := by
  rw [← Measure.restrict_restrict hA]
  change (classMeasure Q μ L f T).restrict A = _
  conv_lhs => rw [classMeasure_eq_mass_smul Q μ L f T hT,Measure.restrict_smul]

theorem original_class_endpoint_distance
    (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (L₁ L₂ : Finset (CellPath d)) (f₁ f₂ : CellPath d → List ℕ) (T U : List ℕ)
    (hT : classMeasure Q₁ μ L₁ f₁ T univ ≠ 0)
    (hU : classMeasure Q₂ ν L₂ f₂ U univ ≠ 0)
    (A D : Set (Space d)) (hA : MeasurableSet A) (hD : MeasurableSet D)
    (B C : Space d → Space d → ℝ) :
    endpointWeightedDistance
      (μ.restrict (A ∩ leafUnion Q₁ (classLeaves L₁ f₁ T)))
      (ν.restrict (D ∩ leafUnion Q₂ (classLeaves L₂ f₂ U))) 1 1 1 B C =
      (classMeasure Q₁ μ L₁ f₁ T univ * classMeasure Q₂ ν L₂ f₂ U univ) •
        endpointWeightedDistance ((normalizedClass Q₁ μ L₁ f₁ T).restrict A)
          ((normalizedClass Q₂ ν L₂ f₂ U).restrict D) 1 1 1 B C := by
  let : IsProbabilityMeasure (normalizedClass Q₁ μ L₁ f₁ T) :=
    normalizedClass_probability Q₁ μ L₁ f₁ T hT
  let : IsProbabilityMeasure (normalizedClass Q₂ ν L₂ f₂ U) :=
    normalizedClass_probability Q₂ ν L₂ f₂ U hU
  rw [restrict_class_eq_mass_smul Q₁ μ L₁ f₁ T hT A hA,
    restrict_class_eq_mass_smul Q₂ ν L₂ f₂ U hU D hD,
    endpointWeightedDistance_smul]

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ClassPairDistance
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original-mass mixture for the two-class distance law -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal NNReal
variable {d : ℕ}

theorem classPairWeight_sum_le_one (Q₁ Q₂ : DyadicCube d)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) :
    (∑ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂),
      (classPairWeight Q₁ Q₂ μ ν N B₁ B₂ i : ℝ)) ≤ 1 :=
  retained_class_pair_real_mass_sum_le_one Q₁ Q₂ hQ₁ hQ₂ μ ν
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) _ _ _ _
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem classPairWeight_coe (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N B₁ B₂ : ℕ) (i : List ℕ × List ℕ) :
    (classPairWeight Q₁ Q₂ μ ν N B₁ B₂ i : ℝ≥0∞) =
      classMeasure Q₁ μ (regularizationLeaves Q₁ μ N) (regularizationLabel Q₁ μ N B₁) i.1 univ *
      classMeasure Q₂ ν (regularizationLeaves Q₂ ν N) (regularizationLabel Q₂ ν N B₂) i.2 univ := by
  apply ENNReal.coe_toNNReal
  apply ENNReal.mul_ne_top
  · change μ.restrict _ univ ≠ ∞
    exact measure_ne_top _ _
  · change ν.restrict _ univ ≠ ∞
    exact measure_ne_top _ _

theorem regularizationPairDistance_eq_mixture {k : ℕ}
    (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d)
    (he₁ : ∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T)
    (he₂ : ∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T)
    (c : List ℕ × List ℕ → ℕ) (A D : Fin k → Set (Space d))
    (hm : ∀ j, MeasurableSet (A j) ∧ MeasurableSet (D j))
    (hd : Pairwise fun j l => Disjoint (A j ×ˢ D j) (A l ×ˢ D l)) :
    regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c (⋃ j, A j ×ˢ D j) =
      ∑ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂),
        classPairWeight Q₁ Q₂ μ ν N B₁ B₂ i •
          ∑ j, endpointWeightedDistance ((sourceClass Q₁ μ N B₁ (p₁ i.1)).restrict (A j))
            ((sourceClass Q₂ ν N B₂ (p₂ i.2)).restrict (D j)) 1 1 1
              (sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) (c i))
              (sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) (c i)) := by
  unfold regularizationPairDistance
  rw [partitionEndpointDistance_product_sum μ ν A D hm hd]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi₁ := (Finset.mem_product.mp hi).1
    have hi₂ := (Finset.mem_product.mp hi).2
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [regularizationSet]
    rw [original_class_endpoint_distance Q₁ Q₂ μ ν _ _ _ _ i.1 i.2
      (ht₁.trans_le (Finset.mem_filter.mp hi₁).2).ne'
      (ht₂.trans_le (Finset.mem_filter.mp hi₂).2).ne' (A j) (D j) (hm j).1 (hm j).2]
    rw [← sourceClass_eq_normalized Q₁ μ N B₁ (p₁ i.1) i.1 (he₁ i.1 hi₁),
      ← sourceClass_eq_normalized Q₂ ν N B₂ (p₂ i.2) i.2 (he₂ i.2 hi₂)]
    rw [← classPairWeight_coe Q₁ Q₂ μ ν N B₁ B₂ i]
    rfl
  · exact fun _ _ => regularizationSet_measurable _ _ _ _ _
  · exact fun _ _ => regularizationSet_measurable _ _ _ _ _
  · exact fun _ _ => regularOuterMask_measurable _ _ _ _ _ _ _
  · exact fun _ _ => regularOuterMask_measurable _ _ _ _ _ _ _
  · exact fun _ _ _ _ => (regularOuterMask_bounds _ _ _ _ _ _ _ _ _).1
  · exact fun _ _ _ _ => (regularOuterMask_bounds _ _ _ _ _ _ _ _ _).1

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FiniteWeightedShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem finite_weighted_shell_square {ι : Type*} (s : Finset ι)
    (μ : Measure ℝ) (F : ι → ℝ → ℂ) (w : ι → ℝ) {B : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hi : ∀ i ∈ s, Integrable (fun r => ‖F i r‖^2) μ)
    (hm : ∀ i ∈ s, AEStronglyMeasurable (F i) μ)
    (hB : ∀ i ∈ s, (∫ r, ‖F i r‖^2 ∂μ) ≤ (w i)^2*B) :
    (∫ r, ‖∑ i ∈ s, F i r‖^2 ∂μ) ≤ (∑ i ∈ s, w i)^2*B := by
  classical
  have hz (i : ι) (his : i ∈ s) (hwi : w i = 0) :
      ∀ᵐ r ∂μ, F i r = 0 := by
    have he : (∫ r, ‖F i r‖^2 ∂μ) = 0 :=
      le_antisymm (by simpa [hwi] using hB i his)
        (integral_nonneg (fun _ => sq_nonneg _))
    have hh := (integral_eq_zero_iff_of_nonneg (fun r => sq_nonneg (‖F i r‖)) (hi i his)).mp he
    filter_upwards [hh] with r hr
    simpa using hr
  have hae : ∀ᵐ r ∂μ, ∀ i ∈ s, w i = 0 → F i r = 0 := by
    exact (eventually_all_finset s).mpr (fun i his =>
      (ae_all_iff).mpr (fun hwi => hz i his hwi))
  let G : ℝ → ℝ := fun r => ∑ i ∈ s, ‖F i r‖^2 / w i
  let W : ℝ := ∑ i ∈ s, w i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  have hgi : Integrable G μ := integrable_finsetSum s
    (fun i his => (hi i his).div_const (w i))
  have hpoint : ∀ᵐ r ∂μ, ‖∑ i ∈ s, F i r‖^2 ≤ W*G r := by
    filter_upwards [hae] with r hr
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s _) 2).trans
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
      (fun i his => div_nonneg (sq_nonneg _) (hw i his))
    intro i his
    by_cases hwi : w i = 0
    · simp [hwi,hr i his hwi]
    · rw [mul_div_cancel₀ _ hwi]
  have hsi : Integrable (fun r => ‖∑ i ∈ s, F i r‖^2) μ := by
    have hsm : AEStronglyMeasurable (fun r => ∑ i ∈ s, F i r) μ := by
      convert Finset.aestronglyMeasurable_sum s hm using 1
      all_goals try with_reducible_and_instances rfl
      ext r
      simp
    apply (hgi.const_mul W).mono' (hsm.norm.pow 2)
    filter_upwards [hpoint] with r hr
    change ‖‖∑ i ∈ s, F i r‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hr
  have hBi (i : ι) (his : i ∈ s) :
      (∫ r, ‖F i r‖^2 ∂μ) / w i ≤ w i*B := by
    by_cases hwi : w i = 0
    · simp [hwi]
    · apply (div_le_iff₀ (lt_of_le_of_ne (hw i his) (Ne.symm hwi))).mpr
      nlinarith [hB i his]
  calc
    _ ≤ ∫ r, W*G r ∂μ := integral_mono_ae hsi (hgi.const_mul W) hpoint
    _ = W * ∑ i ∈ s, (∫ r, ‖F i r‖^2 ∂μ) / w i := by
      rw [integral_const_mul,integral_finsetSum s (fun i his => (hi i his).div_const (w i))]
      simp only [integral_div]
    _ ≤ W * ∑ i ∈ s, w i*B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hBi) hW
    _ = _ := by rw [← Finset.sum_mul]; dsimp [W]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ShellMixtures
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem norm_weighted_sum_sq_le {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0) (z : ι → ℂ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) :
    ‖∑ i ∈ s, (c i : ℝ) • z i‖^2 ≤ ∑ i ∈ s, (c i : ℝ) * ‖z i‖^2 := by
  have hn : ‖∑ i ∈ s, (c i : ℝ) • z i‖ ≤ ∑ i ∈ s, (c i : ℝ)*‖z i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using
      norm_sum_le s (fun i => (c i : ℝ) • z i)
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun i => (c i : ℝ)) (g := fun i => (c i : ℝ)*‖z i‖^2)
    (r := fun i => (c i : ℝ)*‖z i‖)
    (fun _ _ => NNReal.coe_nonneg _) (fun _ _ => by positivity)
    (fun _ _ => by nlinarith)
  have hg : 0 ≤ ∑ i ∈ s, (c i : ℝ)*‖z i‖^2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hsq : ‖∑ i ∈ s, (c i : ℝ) • z i‖^2 ≤ (∑ i ∈ s, (c i : ℝ)*‖z i‖)^2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hsq.trans (hs.trans (by nlinarith))

theorem charFun_weighted_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (r : ℝ) :
    charFun (∑ i ∈ s, c i • τ i) r = ∑ i ∈ s, (c i : ℝ) • charFun (τ i) r := by
  simp only [charFun_eq_integral_innerProbChar]
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_smul_nnreal_measure _ _
  · intro i hi
    exact (BoundedContinuousFunction.innerProbChar r).integrable _

theorem shellEnergy_weighted_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (N : ℕ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) :
    shellEnergy (∑ i ∈ s, c i • τ i) N ≤ ∑ i ∈ s, (c i : ℝ)*shellEnergy (τ i) N := by
  have hi : IntegrableOn (fun r => ∑ i ∈ s, (c i : ℝ)*‖charFun (τ i) r‖^2) (dyadicShell N) volume :=
    integrable_finsetSum s (fun i _ => (shell_energy_integrable (τ i) N).const_mul _)
  have hpoint (r : ℝ) : ‖charFun (∑ i ∈ s, c i • τ i) r‖^2 ≤
      ∑ i ∈ s, (c i : ℝ)*‖charFun (τ i) r‖^2 := by
    rw [charFun_weighted_sum]
    exact norm_weighted_sum_sq_le s c _ hc
  unfold shellEnergy
  calc
    _ ≤ ∫ r in dyadicShell N, ∑ i ∈ s, (c i : ℝ)*‖charFun (τ i) r‖^2 :=
      integral_mono (shell_energy_integrable _ N) hi hpoint
    _ = _ := by
      rw [integral_finsetSum s (fun i _ => (shell_energy_integrable (τ i) N).const_mul _)]
      simp_rw [integral_const_mul]

theorem shellEnergy_weighted_sum_uniform {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (N : ℕ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hτ : ∀ i ∈ s, shellEnergy (τ i) N ≤ C) :
    shellEnergy (∑ i ∈ s, c i • τ i) N ≤ C := by
  apply (shellEnergy_weighted_sum_le s c τ N hc).trans
  calc
    _ ≤ ∑ i ∈ s, (c i : ℝ)*C := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hτ i hi) (NNReal.coe_nonneg _))
    _ = (∑ i ∈ s, (c i : ℝ))*C := (Finset.sum_mul ..).symm
    _ ≤ C := by nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_TwoSidedShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem shellEnergy_eq_twice_positive (μ : Measure ℝ) [IsFiniteMeasure μ] (N : ℕ) :
    shellEnergy μ N = 2 *
      ∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun μ r‖^2 := by
  let a := (2:ℝ)^((N:ℝ)-1)
  let b := (2:ℝ)^((N:ℝ)+1)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hsets : dyadicShell N = Icc a b ∪ Icc (-b) (-a) := by
    ext r
    change (a ≤ |r| ∧ |r| ≤ b) ↔ (a ≤ r ∧ r ≤ b) ∨ (-b ≤ r ∧ r ≤ -a)
    rcases le_total 0 r with h | h
    · rw [abs_of_nonneg h]
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · exfalso; linarith
    · rw [abs_of_nonpos h]
      constructor
      · intro h; right; constructor <;> linarith
      · rintro (h | h)
        · exfalso; linarith
        · constructor <;> linarith
  have hdis : Disjoint (Icc a b) (Icc (-b) (-a)) := by
    apply Set.disjoint_left.mpr
    intro r h₀ h₁
    have := h₀.1
    have := h₁.2
    linarith
  have hi (c d : ℝ) : IntegrableOn (fun r => ‖charFun μ r‖^2) (Icc c d) :=
    (continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hneg : (∫ r in Icc (-b) (-a), ‖charFun μ r‖^2) =
      ∫ r in Icc a b, ‖charFun μ r‖^2 := by
    have hemb : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    have h := hemb.setIntegral_map
      (μ := (volume : Measure ℝ)) (fun r => ‖charFun μ r‖^2) (Icc (-b) (-a))
    rw [Measure.map_neg_eq_self] at h
    have hp : (fun x : ℝ => -x) ⁻¹' Icc (-b) (-a) = Icc a b := by
      ext x
      simp only [mem_preimage,mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith
    simpa only [hp,fourier_energy_even] using h
  rw [shellEnergy,hsets,setIntegral_union hdis measurableSet_Icc (hi a b) (hi (-b) (-a)),hneg]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FilteredClassShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Class mixtures cost only the square of the product-filter count -/

namespace Falconer
open Set MeasureTheory
open scoped NNReal

theorem positive_shell_finite_sum {ι : Type*} (F : Finset ι)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (N : ℕ) {E : ℝ}
    (hτ : ∀ i ∈ F,
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun (τ i) r‖^2) ≤ E) :
    (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)),
      ‖charFun (∑ i ∈ F, τ i) r‖^2) ≤ (F.card:ℝ)^2*E := by
  have he (r : ℝ) : charFun (∑ i ∈ F, τ i) r = ∑ i ∈ F, charFun (τ i) r := by
    simpa using PlanarFalconer.charFun_weighted_sum F (fun _ => (1:ℝ≥0)) τ r
  simp_rw [he]
  have hi (i : ι) : IntegrableOn (fun r => ‖charFun (τ i) r‖^2)
      (Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1))) :=
    (continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hb := PlanarFalconer.finite_weighted_shell_square F
    (volume.restrict (Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1))))
    (fun i r => charFun (τ i) r) (fun _ => (1:ℝ))
    (fun _ _ => zero_le_one) (fun i _ => hi i)
    (fun _ _ => continuous_charFun.aestronglyMeasurable)
    (fun i hi => by simpa using hτ i hi)
  simpa using hb

theorem shellEnergy_filter_mixture {ι : Type*} (F : Finset ι)
    (c : ι → ℝ≥0) (n N : ℕ) (τ : ι → Fin n → Measure ℝ)
    [∀ i j, IsFiniteMeasure (τ i j)] (hc : (∑ i ∈ F, (c i:ℝ)) ≤ 1)
    {E : ℝ} (hE : 0 ≤ E)
    (hτ : ∀ i ∈ F, ∀ j,
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun (τ i j) r‖^2) ≤ E) :
    PlanarFalconer.shellEnergy (∑ i ∈ F, c i • ∑ j, τ i j) N ≤ 2*(n:ℝ)^2*E := by
  apply PlanarFalconer.shellEnergy_weighted_sum_uniform F c (fun i => ∑ j, τ i j) N hc
    (by positivity)
  intro i hi
  rw [PlanarFalconer.shellEnergy_eq_twice_positive]
  have hh := positive_shell_finite_sum Finset.univ (τ i) N (fun j _ => hτ i hi j)
  simpa only [Finset.card_univ,Fintype.card_fin,mul_assoc] using
    mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ClassPairShell
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The assembled class law inherits the local shell bound -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal NNReal
variable {d : ℕ}

theorem regularizationPairDistance_shell_le {k : ℕ} (hdim : 1 ≤ d)
    (Q₁ Q₂ : DyadicCube d) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d)
    (he₁ : ∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T)
    (he₂ : ∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T)
    (c : List ℕ × List ℕ → ℕ) (A D : Fin k → Set (Space d))
    (hm : ∀ j, MeasurableSet (A j) ∧ MeasurableSet (D j))
    (hd : Pairwise fun j l => Disjoint (A j ×ˢ D j) (A l ×ˢ D l))
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2)
    {E : ℝ} (hE : 0 ≤ E)
    (hlocal : ∀ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂),
      ∀ j : Fin k,
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)),
        ‖charFun (endpointWeightedDistance ((sourceClass Q₁ μ N B₁ (p₁ i.1)).restrict (A j))
          ((sourceClass Q₂ ν N B₂ (p₂ i.2)).restrict (D j)) 1 1 1
          (sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) (c i))
          (sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) (c i))) r‖^2) ≤ E) :
    PlanarFalconer.shellEnergy
      (regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c (⋃ j, A j ×ˢ D j)) N ≤
        2*(k:ℝ)^2*E := by
  let : ∀ T, IsFiniteMeasure (sourceClass Q₁ μ N B₁ (p₁ T)) := fun _ => sourceClass_finite ..
  let : ∀ T, IsFiniteMeasure (sourceClass Q₂ ν N B₂ (p₂ T)) := fun _ => sourceClass_finite ..
  let τ := fun (i : List ℕ × List ℕ) (j : Fin k) =>
    endpointWeightedDistance ((sourceClass Q₁ μ N B₁ (p₁ i.1)).restrict (A j))
      ((sourceClass Q₂ ν N B₂ (p₂ i.2)).restrict (D j)) 1 1 1
      (sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) (c i))
      (sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) (c i))
  let : ∀ i j, IsFiniteMeasure (τ i j) := by
    intro i j
    apply endpointWeightedDistance_finite hdim _ _ zero_lt_one zero_lt_one hδ
      _ _ (fun x w => regularOuterMask_bounds _ _ _ _ _ _ _ x w)
      (fun x w => regularOuterMask_bounds _ _ _ _ _ _ _ x w)
    have hμ : (sourceClass Q₁ μ N B₁ (p₁ i.1)).restrict (A j) ≪ μ :=
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans (sourceClass_absolutelyContinuous ..)
    have hν : (sourceClass Q₂ ν N B₂ (p₂ i.2)).restrict (D j) ≪ ν :=
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans (sourceClass_absolutelyContinuous ..)
    filter_upwards [(hμ.prod hν).ae_le hsep] with z hz
    simpa only [div_one] using hz
  rw [regularizationPairDistance_eq_mixture Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ ht₁ ht₂ σ κ p₁ p₂ he₁ he₂ c A D hm hd]
  exact shellEnergy_filter_mixture _ (classPairWeight Q₁ Q₂ μ ν N B₁ B₂) k N τ
    (classPairWeight_sum_le_one Q₁ Q₂ hQ₁ hQ₂ μ ν N B₁ B₂ t₁ t₂) hE hlocal

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RegularizationScalarShell
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar shell decay after summing the actual regularized class pairs -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal SchwartzMap ContDiff

theorem exists_regularization_scalar_shell_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {χ : ℝ} (hχ : 0 < χ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
    ∃ lam σ κ β : ℝ, 0 < lam ∧ 0 < σ ∧ lam ≤ σ ∧ 0 < κ ∧ 0 < β ∧
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q₁ Q₂ : DyadicCube (m+3)), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (μ ν : Measure (Space (m+3))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞), 0 < t₁ → 0 < t₂ →
      ∀ p₁ p₂ : List ℕ → CellPath (m+3),
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T) →
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁,
        RegularizedProfileData Q₁ (sourceClass Q₁ μ N B₁ (p₁ T)) N ((m+3:ℕ)/2+χ) lam
          (sourceUnitProfile Q₁ μ N B₁ (p₁ T))) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂,
        RegularizedProfileData Q₂ (sourceClass Q₂ ν N B₂ (p₂ T)) N ((m+3:ℕ)/2+χ) lam
          (sourceUnitProfile Q₂ ν N B₂ (p₂ T))) →
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂μ.prod ν,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      ∃ c : List ℕ × List ℕ → ℕ,
        (∀ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂), c i ≤ N) ∧
        ∀ (k : ℕ) (A D : Fin k → Set (Space (m+3))),
          (∀ j, MeasurableSet (A j) ∧ MeasurableSet (D j)) →
          (Pairwise fun j l => Disjoint (A j ×ˢ D j) (A l ×ˢ D l)) →
          PlanarFalconer.shellEnergy
            (regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c (⋃ j, A j ×ˢ D j)) N ≤
              2*(k:ℝ)^2*((2:ℝ)^N)^(-β/16) := by
  classical
  obtain ⟨lam,σ,κ,β,hlam,hσ,hlamσ,hκ,hβ,N₀,hN₀,hmain⟩ :=
    exists_regular_class_shell hgnomonic hquadratic m hχ φ Ψ hφ hΨ hsmooth
      hpos hzero hone hV hΨV hsupp δ W hδ hW
  refine ⟨lam,σ,κ,β,hlam,hσ,hlamσ,hκ,hβ,N₀,hN₀,?_⟩
  intro N hN Q₁ Q₂ hQ₁ hQ₂ μ ν _ _ B₁ B₂ t₁ t₂ ht₁ ht₂ p₁ p₂ he₁ he₂ hreg₁ hreg₂ hsep hnear
  let I := (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂)
  have hside₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hside₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  have hex (i : List ℕ × List ℕ) (hi : i ∈ I) :
      ∃ c : ℕ, c ≤ N ∧ ∀ A D : Set (Space (m+3)), MeasurableSet A → MeasurableSet D →
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)),
        ‖charFun (endpointWeightedDistance ((sourceClass Q₁ μ N B₁ (p₁ i.1)).restrict A)
          ((sourceClass Q₂ ν N B₂ (p₂ i.2)).restrict D) 1 1 1
          (sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) c)
          (sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) c)) r‖^2) ≤ ((2:ℝ)^N)^(-β/16) := by
    have hi₁ := (Finset.mem_product.mp hi).1
    have hi₂ := (Finset.mem_product.mp hi).2
    let : IsProbabilityMeasure (sourceClass Q₁ μ N B₁ (p₁ i.1)) := (hreg₁ i.1 hi₁).probability
    let : IsProbabilityMeasure (sourceClass Q₂ ν N B₂ (p₂ i.2)) := (hreg₂ i.2 hi₂).probability
    have hac := (sourceClass_absolutelyContinuous Q₁ μ N B₁ (p₁ i.1)).prod
      (sourceClass_absolutelyContinuous Q₂ ν N B₂ (p₂ i.2))
    obtain ⟨c,hc,_hw,_hclo,hb⟩ := hmain N hN Q₁ Q₂ hQ₁ hQ₂ _ _ _ _
      (hreg₁ i.1 hi₁) (hreg₂ i.2 hi₂)
      (sourceClass_parent Q₁ hside₁ μ N B₁ (p₁ i.1))
      (sourceClass_parent Q₂ hside₂ ν N B₂ (p₂ i.2)) (hac.ae_le hsep) (hac.ae_le hnear)
    exact ⟨c,by omega,hb⟩
  let c : List ℕ × List ℕ → ℕ := fun i => if hi : i ∈ I then (hex i hi).choose else 0
  have hc (i : List ℕ × List ℕ) (hi : i ∈ I) : c i ≤ N := by
    simpa only [c,dite_eq_left hi] using (hex i hi).choose_spec.1
  refine ⟨c,hc,?_⟩
  intro k A D hm hd
  apply regularizationPairDistance_shell_le (by omega) Q₁ Q₂ hside₁ hside₂ μ ν N B₁ B₂
    t₁ t₂ ht₁ ht₂ σ κ p₁ p₂ he₁ he₂ c A D hm hd hδ (hsep.mono fun _ h => h.1) (by positivity)
  intro i hi j
  have hb := (hex i hi).choose_spec.2 (A j) (D j) (hm j).1 (hm j).2
  simpa only [c,I,dite_eq_left hi] using hb

end Falconer.Regularization

end OAI
end

theorem solution : type_of% @OAI.Falconer.Regularization.exists_regularization_scalar_shell_oai := @OAI.Falconer.Regularization.exists_regularization_scalar_shell_oai
