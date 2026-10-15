-- Prove2me | solution 1 for OAI.IndependentProducts.averaged_midpoint_from_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:43:10.522315+00:00
-- url     : https://prove2.me/submissions/a21217f6-78d6-4eca-840a-605a5ee1828f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/GaussianBounds.lean:L39-L64
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.averaged_midpoint_from_scalar. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients
import Theorems.Thm_OAI_IndependentProducts_FiniteHead_affine_finite_polynomials
import Theorems.Thm_OAI_IndependentProducts_FiniteHead_tailSpace_cofinite
import Theorems.Thm_OAI_IndependentProducts_averagedModulus_of_dense_affine
import Theorems.Thm_OAI_IndependentProducts_dense_pathVector_span
import Theorems.Thm_OAI_IndependentProducts_main_general

-- ---- from OAI.Analysis.ProductSpaces.MidpointModulus ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uX

namespace IndependentProducts
section MidpointGeometry
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma continuous_midpointGain (t : ℝ) (x : X) : Continuous (midpointGain t x : X → ℝ) := by
  unfold midpointGain
  fun_prop

lemma affine_on_closed_tail (F : Submodule ℝ X) {A B t : ℝ} (u : X)
    (h : ∀ y ∈ F, A * ‖y‖ - B * ‖u‖ ≤ midpointGain t u y) :
    ∀ y ∈ F.topologicalClosure, A * ‖y‖ - B * ‖u‖ ≤ midpointGain t u y := by
  have hc : IsClosed {y : X | A * ‖y‖ - B * ‖u‖ ≤ midpointGain t u y} :=
    isClosed_le (by fun_prop) (continuous_midpointGain t u)
  exact closure_minimal h hc

end MidpointGeometry
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.FiniteHeads ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uκ

namespace IndependentProducts
namespace FiniteHead
variable (T : FiniteHead)

lemma exit_prefix (v : Vertex) (hv : v ∉ T.vertices) : (T.exit v hv).val.val <+: v :=
  Classical.choose_spec (T.exists_boundary_prefix v hv)

lemma mem_containing (s : Finset Vertex) {v : Vertex} (hv : v ∈ s) :
    v ∈ (containing s).vertices := by
  simp only [containing, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_range]
  exact Or.inr ⟨v, hv, v.length, by omega, List.take_length⟩

end FiniteHead
end IndependentProducts

namespace IndependentProducts

section Selector
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end Selector
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.TailCoefficients ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι uκ

namespace IndependentProducts
section FiniteRepresentatives
variable (μ : Measure ℝ) [hμprob : IsProbabilityMeasure μ]
  (h₂ : MemLp (fun w : ℝ => w) 2 μ)

namespace FiniteHead
variable (T : FiniteHead)

lemma head_representative (x : productSpan μ) (hx : x ∈ T.headSpan μ h₂) :
    ∃ a : T.vertices → ℝ, x = ∑ v : T.vertices, a v • pathVector μ h₂ v := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_image_finset_iff_exists_fun ℝ).mp hx
  exact ⟨a, ha.symm⟩

lemma tail_representative (y : productSpan μ) (hy : y ∈ T.tailAlgebraic μ h₂) :
    ∃ s : Finset Vertex, (∀ v ∈ s, v ∉ T.vertices) ∧
      ∃ a : s → ℝ, y = ∑ v : s, a v • T.relativeVector μ h₂ v := by
  obtain ⟨s, hs, a, ha⟩ := (Submodule.mem_span_image_iff_exists_fun ℝ).mp hy
  exact ⟨s, fun v hv => hs hv, a, ha.symm⟩

end FiniteHead
end FiniteRepresentatives

namespace FiniteHead
section FiniteTailData
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ] [DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)

end FiniteTailData
end FiniteHead
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.GaussianBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts
namespace FiniteHead

lemma affine_algebraic_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₂ : MemLp (fun w : ℝ => w) 2 μ) (hmean : ∫ w : ℝ, w ∂μ = 1)
    (T : FiniteHead) (x : productSpan μ) (hx : x ∈ T.headSpan μ h₂)
    (t A D : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ (ι : Type) [Fintype ι], ∀ aa : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize aa - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, aa i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    ∀ y ∈ T.tailAlgebraic μ h₂,
      (A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))) * ‖y‖ - D * ‖x‖ ≤ midpointGain t x y := by
  classical
  obtain ⟨c, rfl⟩ := T.head_representative μ h₂ x hx
  intro y hy
  obtain ⟨s, hs, a, rfl⟩ := T.tail_representative μ h₂ y hy
  let b : s → T.Boundary := fun k => T.exit k (hs k k.property)
  let ι := Set.range b
  let : Fintype ι := Fintype.ofFinite _
  let e : ι → T.Boundary := Subtype.val
  let j : s → ι := fun k => ⟨b k, ⟨k, rfl⟩⟩
  have he : Function.Injective e := Subtype.val_injective
  have hv : ∀ k : s, (e (j k)).val.val <+: k.val := fun k => T.exit_prefix k (hs k k.property)
  exact T.affine_finite_polynomials μ h₂ hmean e he (fun k : s => k.val) j a hv c
    t A D ht hA hC (hscalar ι)

end FiniteHead

lemma averaged_midpoint_from_scalar (μ : Measure ℝ) (hμ : MultiplierHypotheses μ)
    (t A D : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ (ι : Type) [Fintype ι], ∀ aa : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize aa - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, aa i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ)) - D ≤
      averagedMidpointModulus (productSpan μ) (normSeminorm ℝ (productSpan μ)) t := by
  let := hμ.probability
  apply averagedModulus_of_dense_affine (main_general μ hμ).1 (dense_pathVector_span μ hμ.second_moment)
    _ D t (div_nonneg hA hC.le) hD
  intro u hu
  have hu' : u ∈ Submodule.span ℝ (pathVector μ hμ.second_moment '' (Set.univ : Set Vertex)) := by
    change u ∈ Submodule.span ℝ (Set.range (pathVector μ hμ.second_moment)) at hu
    simpa only [Set.image_univ] using hu
  obtain ⟨s, hs, a, ha⟩ := (Submodule.mem_span_image_iff_exists_fun ℝ).mp hu'
  let T := FiniteHead.containing s
  have hut : u ∈ T.headSpan μ hμ.second_moment := by
    rw [← ha]
    apply Submodule.sum_mem
    intro v hv
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨v.val, FiniteHead.mem_containing s v.property, rfl⟩
  refine ⟨T.tailSpace μ hμ.second_moment, T.tailSpace_cofinite μ hμ.second_moment, ?_⟩
  exact affine_on_closed_tail (T.tailAlgebraic μ hμ.second_moment) u
    (T.affine_algebraic_tail μ hμ.second_moment hμ.mean_one u hut t A D ht hA hC hscalar)

end IndependentProducts

namespace IndependentProducts

end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

theorem solution (μ : Measure ℝ) (hμ : MultiplierHypotheses μ)
    (t A D : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ (ι : Type) [Fintype ι], ∀ aa : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize aa - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, aa i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ)) - D ≤
      averagedMidpointModulus (productSpan μ) (normSeminorm ℝ (productSpan μ)) t := by
  first
    | exact OAI.IndependentProducts.averaged_midpoint_from_scalar μ hμ t A D ht hA hD hC hscalar
    | exact OAI.IndependentProducts.averaged_midpoint_from_scalar
    | (apply OAI.IndependentProducts.averaged_midpoint_from_scalar <;> assumption)
    | (intros; apply OAI.IndependentProducts.averaged_midpoint_from_scalar <;> assumption)
