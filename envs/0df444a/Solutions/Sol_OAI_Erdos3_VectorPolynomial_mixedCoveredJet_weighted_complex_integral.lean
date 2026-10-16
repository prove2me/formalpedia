-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.mixedCoveredJet_weighted_complex_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:16:29.129984+00:00
-- url     : https://prove2.me/submissions/6769cc3f-dd82-4d8e-927d-959a60dfd5ea

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1376

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



end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory _root_.Set _root_.OAI.Set
open scoped Classical

theorem restrictedComplexChartDensity_weighted_integral_of_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : X → Y) (hq : Measurable q) (S : Set X) (hS : MeasurableSet S)
    (hinj : Set.InjOn q S) (himage : MeasurableSet (q '' S))
    (μ : Measure X) (ν : Measure Y)
    (hmap : Measure.map q (μ.restrict S) = ν.restrict (q '' S))
    (f : X → ℂ) (test : Y → ℂ)
    (hm : Measurable (fun y => restrictedComplexChartDensity q S 1 f y * test y)) :
    (∫ y, restrictedComplexChartDensity q S 1 f y * test y ∂ν) =
      ∫ x in S, f x * test (q x) ∂μ := by
  let F := fun y => restrictedComplexChartDensity q S 1 f y * test y
  have hind : (q '' S).indicator F = F := by
    funext y
    by_cases hy : y ∈ q '' S
    · exact indicator_of_mem hy F
    · simp only [indicator_of_notMem hy, F,
        restrictedComplexChartDensity_zero q S 1 f hy, zero_mul]
  calc
    _ = ∫ y in q '' S, F y ∂ν := by rw [← integral_indicator himage, hind]
    _ = ∫ x in S, F (q x) ∂μ := by
      rw [← hmap, integral_map_of_stronglyMeasurable hq hm.stronglyMeasurable]
    _ = _ := by
      apply setIntegral_congr_fun hS
      intro x hx
      simp only [F, restrictedComplexChartDensity_apply q S 1 f hinj hx,
        Complex.ofReal_one, one_mul]

namespace VectorPolynomial

open Module Submodule

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

theorem mixedCoveredJet_reference_map :
    Measure.map chart ((coveredJetArrayReference U d).restrict region) =
      (haar).restrict (chart '' region) := by
  let e := mixedCoveredJetEquiv (O := O) (B := E) (n := n) U o d
  have hp := mixedCoveredJetEquiv_measurePreserving (O := O) (B := E) (n := n) U o d
  have he : Measure.map e ((coveredJetArrayReference U d).restrict region) =
      (coveredJetReference U d).restrict (coveredJetSourceRegion U b d Ω) := by
    rw [← hp.map_eq, e.restrict_map]
    rfl
  change Measure.map (coveredJetChart U b hb bW d ∘ e) _ = _
  rw [← Measure.map_map (coveredJetChart_continuous (O := O) U b hb bW d).measurable
    e.measurable, he, coveredJetChart_reference_map U b hb bW d ν Ω hΩm hΩ,
    mixedCoveredJetChart_image U o b hb bW d Ω]

theorem mixedCoveredJet_weighted_complex_integral_oai
    (f : MixedCoveredJetSource I O E n d → ℂ) (hf : Measurable f)
    (test : EuclideanJetLayers U O → ℂ) (htest : Measurable test) :
    (∫ y, restrictedComplexChartDensity chart region 1 f y * test y ∂haar) =
      (coveredJetArrayScale (O := O) U : ℂ) *
        ∫ z in region, f z * test (chart z) ∂raw := by
  have hq : Measurable chart :=
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d)
  have hS : MeasurableSet region :=
    (coveredJetSourceRegion_measurable U b d Ω hΩm).preimage
      (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d)
  have himage : MeasurableSet (chart '' region) := by
    rw [mixedCoveredJetChart_image U o b hb bW d Ω]
    have h := (coveredJetChart_embedding U b hb bW d Ω hΩm hΩ).measurableSet_range
    have he : Set.range (fun x : coveredJetSourceRegion U b d Ω =>
        coveredJetChart U b hb bW d x.val) =
        coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ω := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.val, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rwa [he] at h
  rw [restrictedComplexChartDensity_weighted_integral_of_map chart hq region hS
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) himage
    (coveredJetArrayReference U d) haar
    (mixedCoveredJet_reference_map U o b hb bW d ν Ω hΩm hΩ) f test
    ((mixedCoveredJet_restrictedComplexDensity_measurable U o b hb bW d Ω hΩ hΩm f hf).mul htest)]
  rw [coveredJetArrayReference_eq_real_smul, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (coveredJetArrayScale_pos (O := O) U).le]
  rfl

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

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.mixedCoveredJet_weighted_complex_integral_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.mixedCoveredJet_weighted_complex_integral_oai.{u_1, u_2, u_3, u_4}
