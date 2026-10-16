-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.mixedCoveredJet_normalized_complex_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:15:59.563162+00:00
-- url     : https://prove2.me/submissions/6ec59c13-2c70-4a53-a6df-c8bb147ea92a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1376

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set


end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem restrictedChartDensity_indicator (q : X → Y) (S : Set X) (c : ℝ) (f : X → ℝ) :
    restrictedChartDensity q S c (S.indicator f) = restrictedChartDensity q S c f := by
  unfold restrictedChartDensity
  congr 1
  funext x
  exact indicator_of_mem x.property f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators


end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredJetReference
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

namespace VectorPolynomial

variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem coveredJetChart_density_law (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
    (f : CoveredJetChartSource U O B n d → ℝ)
    (hf : ∀ x ∉ coveredJetSourceRegion U b d Ω, f x = 0) :
    (realDensityMeasure (coveredJetReference U d) f).map (coveredJetChart U b hb bW d) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
      (restrictedChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1 f) := by
  apply restrictedChartDensity_law _ (coveredJetChart_continuous U b hb bW d).measurable
    (coveredJetSourceRegion_measurable U b d Ω hΩm)
    (coveredJetChart_embedding U b hb bW d Ω hΩm hΩ) _ _ zero_le_one _ f hf
  simpa only [ENNReal.ofReal_one, one_smul] using
    coveredJetChart_reference_map U b hb bW d ν Ω hΩm hΩ

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedCoveredRowReindex
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators ENNReal



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}

theorem coveredJetArrayReference_density (d : ℕ) [NeZero d]
    (f : ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) → ℝ) :
    realDensityMeasure (coveredJetArrayReference U d)
      (fun x => f x / coveredJetArrayScale (O := O) U) =
    realDensityMeasure
      ((Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
        (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure) f := by
  rw [coveredJetArrayReference_eq_real_smul,
    realDensityMeasure_smul_real _ _ (coveredJetArrayScale_pos U).le]
  congr 1
  funext x
  field_simp [(coveredJetArrayScale_pos (O := O) U).ne']

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical ENNReal

namespace VectorPolynomial


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set
open scoped Classical BigOperators





end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedCoveredDensityMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem coveredJetArray_density_law (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
    (f : ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) → ℝ)
    (hf : ∀ p, mixedCoveredJetCoordinates U o d p ∉ coveredJetSourceRegion U b d Ω → f p = 0) :
    (realDensityMeasure (coveredJetArrayReference U d) f).map
      (fun p => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d p)) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))
      (restrictedChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1
        (fun x => f ((mixedCoveredJetEquiv U o d).symm x))) := by
  let e := mixedCoveredJetEquiv (O := O) (B := B) (n := n) U o d
  have he : MeasurePreserving e (coveredJetArrayReference U d) (coveredJetReference U d) :=
    mixedCoveredJetEquiv_measurePreserving U o d
  have hq := (coveredJetChart_continuous (O := O) U b hb bW d).measurable
  change (realDensityMeasure (coveredJetArrayReference U d) f).map
    (coveredJetChart U b hb bW d ∘ e) = _
  rw [← Measure.map_map hq e.measurable, realDensityMeasure_map_equiv, he.map_eq]
  apply coveredJetChart_density_law U b hb bW d ν Ω hΩm hΩ
  intro x hx
  apply hf
  change e (e.symm x) ∉ coveredJetSourceRegion U b d Ω
  simpa only [e.apply_symm_apply] using hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d

include hΩm hΩ

theorem mixedCoveredJet_density_law (f : MixedCoveredJetSource I O E n d → ℝ)
    (hf : ∀ z ∉ region, f z = 0) :
    Measure.map chart (realDensityMeasure (coveredJetArrayReference U d) f) =
      realDensityMeasure haar (restrictedChartDensity chart region 1 f) := by
  have h := coveredJetArray_density_law U o b hb bW d ν Ω hΩm hΩ f hf
  have he : restrictedChartDensity (coveredJetChart U b hb bW d)
      (coveredJetSourceRegion U b d Ω) 1 (fun z => f ((mixedCoveredJetEquiv U o d).symm z)) =
      restrictedChartDensity chart region 1 f := by
    apply restrictedChartDensity_eq_of_values chart region
      (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
    · intro z hz
      rw [mixedCoveredJetChart, restrictedChartDensity_apply _ _ _ _
        (coveredJetChart_injOn U b hb bW d Ω hΩ) hz, one_mul]
      exact congrArg f ((mixedCoveredJetEquiv U o d).symm_apply_apply z)
    · intro y hy
      apply restrictedChartDensity_zero
      rwa [← mixedCoveredJetChart_image U o b hb bW d Ω]
  rw [he] at h
  exact h

theorem mixedCoveredJet_normalized_density_law (f : MixedCoveredJetSource I O E n d → ℝ) :
    Measure.map chart (realDensityMeasure raw (Set.indicator region f)) =
      realDensityMeasure haar (restrictedChartDensity chart region 1
        (fun z => f z / coveredJetArrayScale (O := O) U)) := by
  have he : (fun z => Set.indicator region f z / coveredJetArrayScale (O := O) U) =
      Set.indicator region (fun z => f z / coveredJetArrayScale (O := O) U) := by
    funext z
    by_cases hz : z ∈ region
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, zero_div]
  unfold mixedCoveredJetRawReference
  rw [← coveredJetArrayReference_density U d (Set.indicator region f)]
  rw [he, mixedCoveredJet_density_law U o b hb bW d ν Ω hΩm hΩ _
    (fun z hz => Set.indicator_of_notMem hz _), restrictedChartDensity_indicator]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical




end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d

include hΩm hΩ in
theorem mixedCoveredJet_normalized_complex_integral_oai
    (f : MixedCoveredJetSource I O E n d → ℝ) (hfm : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) (hfs : ∀ z ∉ region, f z = 0)
    (φ : EuclideanJetLayers U O → ℂ) (hφ : Measurable φ) :
    (∫ z, (f z : ℂ) * φ (chart z) ∂raw) =
      ∫ y, (restrictedChartDensity chart region 1
        (fun z => f z / coveredJetArrayScale (O := O) U) y : ℂ) * φ y ∂haar := by
  let ρ := restrictedChartDensity chart region 1
    (fun z => f z / coveredJetArrayScale (O := O) U)
  have hρm : Measurable ρ :=
    mixedCoveredJet_restrictedDensity_measurable U o b hb bW d Ω hΩm hΩ _ (hfm.div_const _)
  have hρ0 : ∀ y, 0 ≤ ρ y := by
    intro y
    by_cases hy : y ∈ chart '' region
    · obtain ⟨z, hz, rfl⟩ := hy
      dsimp only [ρ]
      rw [restrictedChartDensity_apply _ _ _ _
        (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) hz, one_mul]
      exact div_nonneg (hf0 z) (coveredJetArrayScale_pos U).le
    · exact (restrictedChartDensity_zero chart region 1 _ hy).ge
  have hi : Set.indicator region f = f := by
    funext z
    by_cases hz : z ∈ region
    · exact Set.indicator_of_mem hz f
    · rw [Set.indicator_of_notMem hz, hfs z hz]
  have hlaw := mixedCoveredJet_normalized_density_law U o b hb bW d ν Ω hΩm hΩ f
  rw [hi] at hlaw
  have hchart : Measurable chart :=
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d)
  rw [← realDensityMeasure_integral_complex raw f hfm hf0,
    ← integral_map hchart.aemeasurable hφ.aestronglyMeasurable, hlaw]
  exact realDensityMeasure_integral_complex haar ρ hρm hρ0 φ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory _root_.Set _root_.OAI.Set
open scoped Classical

namespace VectorPolynomial

open Module Submodule




end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators








end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators






end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators






end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal




end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.mixedCoveredJet_normalized_complex_integral_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.mixedCoveredJet_normalized_complex_integral_oai.{u_1, u_2, u_3, u_4}
