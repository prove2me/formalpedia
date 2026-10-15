-- Prove2me | solution 1 for OAI.ProjectionCounterexample.product_facet_eq_affine_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:20:09.270786+00:00
-- url     : https://prove2.me/submissions/cfbf46dd-480a-4113-9543-9ef0c21c4c14

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductFacetCharts.lean:L57-L112
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.product_facet_eq_affine_image. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Definitions.Def_ProjectionCounterexample
import Definitions.Def_OAI_Geometry_ProjectionBody_GeometryDefinitions
import Definitions.Def_OAI_Geometry_ProjectionBody_ConvexGeometry
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCover
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCoordinates
import Definitions.Def_OAI_Geometry_ProjectionBody_GraphChart
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacetCharts
import Definitions.Def_OAI_Geometry_Zonotope_Decomposition
import Definitions.Def_OAI_Geometry_Zonotope_Support
import Definitions.Def_OAI_Geometry_Zonotope_Euclidean
import Definitions.Def_OAI_Geometry_Zonotope_Product
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetCharts
import Theorems.Thm_OAI_ProjectionCounterexample_coordinate_facet_eq_image
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_eq_halfspaceBody
import Theorems.Thm_OAI_ProjectionCounterexample_sum_facet_eq_image

-- ---- from OAI.Geometry.ProjectionBody.SimplexFacets ----
namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

theorem simplex_boundingFace_coordinate {d : ℕ} (i : Fin d) :
    boundingFace (simplexFunctional d) simplexLevel (some i) =
      {x ∈ simplex d | x i = 0} := by
  ext x
  simp [boundingFace, ← simplex_eq_halfspaceBody, simplexLevel]

theorem simplex_boundingFace_sum (d : ℕ) :
    boundingFace (simplexFunctional d) simplexLevel none =
      {x ∈ simplex d | ∑ i, x i = 1} := by
  ext x
  simp [boundingFace, ← simplex_eq_halfspaceBody, simplexLevel]

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.ProductFacets ----
namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

theorem productBody_eq_halfspaceBody :
    productBody = halfspaceBody productFunctional productLevel := by
  ext x
  change (firstBlock x ∈ simplex 10 ∧ secondBlock x ∈ simplex 10) ↔ _
  rw [simplex_eq_halfspaceBody]
  constructor
  · rintro ⟨hx, hy⟩ ⟨b, i⟩
    cases b
    · exact hx i
    · exact hy i
  · intro hx
    exact ⟨fun i => hx (false, i), fun i => hx (true, i)⟩

theorem product_boundingFace_first (i : Option (Fin 10)) :
    boundingFace productFunctional productLevel (false, i) =
      {x | firstBlock x ∈ boundingFace (simplexFunctional 10) simplexLevel i ∧
        secondBlock x ∈ simplex 10} := by
  ext x
  simp only [boundingFace, ← productBody_eq_halfspaceBody, productBody,
    mem_ofPred_eq, productFunctional_first, productLevel, simplex_eq_halfspaceBody]
  tauto

theorem product_boundingFace_second (i : Option (Fin 10)) :
    boundingFace productFunctional productLevel (true, i) =
      {x | firstBlock x ∈ simplex 10 ∧
        secondBlock x ∈ boundingFace (simplexFunctional 10) simplexLevel i} := by
  ext x
  simp only [boundingFace, ← productBody_eq_halfspaceBody, productBody,
    mem_ofPred_eq, productFunctional_second, productLevel, simplex_eq_halfspaceBody]
  tauto

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.SimplexFacetCharts ----
namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

theorem simplexFacetChart_none (n : ℕ) (x : E n) :
    simplexFacetCenter n none + simplexFacetLinear n none x = sumFacetMap n x := by
  ext j
  induction j using Fin.lastCases
  · simp [simplexFacetCenter, simplexFacetLinear, graphLinear, sub_eq_add_neg]
  · simp [simplexFacetCenter, simplexFacetLinear, graphLinear, insertZero,
      Fin.insertNth_last']

theorem simplex_facet_eq_affine_image (n : ℕ) (i : Option (Fin (n + 1))) :
    boundingFace (simplexFunctional (n + 1)) simplexLevel i =
      (fun x => simplexFacetCenter n i + simplexFacetLinear n i x) '' simplex n := by
  cases i with
  | none =>
    simp_rw [simplex_boundingFace_sum, simplexFacetChart_none]
    exact sum_facet_eq_image n
  | some i =>
    rw [simplex_boundingFace_coordinate, coordinate_facet_eq_image]
    simp [simplexFacetCenter, simplexFacetLinear]

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.ProductFacetCharts ----
namespace OAI

/-! Explicit nineteen-dimensional affine charts on the twenty-two product facets. -/
noncomputable section
open Set

namespace ProjectionCounterexample

lemma productFacetChart_first (i : Option (Fin 10)) (x : E 19) :
    (@EuclideanSpace.finAddEquivProd ℝ _ 10 10)
      (productFacetCenter (false, i) + productFacetLinear (false, i) x) =
      (simplexFacetCenter 9 i + simplexFacetLinear 9 i
        ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) x).1,
       ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) x).2) := by
  simp [productFacetCenter, productFacetLinear, map_add, LinearMap.prodMap_apply]
  rfl

lemma productFacetChart_second (i : Option (Fin 10)) (x : E 19) :
    (@EuclideanSpace.finAddEquivProd ℝ _ 10 10)
      (productFacetCenter (true, i) + productFacetLinear (true, i) x) =
      (((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) x).1,
       simplexFacetCenter 9 i + simplexFacetLinear 9 i
        ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) x).2) := by
  simp [productFacetCenter, productFacetLinear, map_add, LinearMap.prodMap_apply]
  rfl

/-- Each product facet is exactly the image of the appropriate product simplex. -/
theorem product_facet_eq_affine_image (i : Bool × Option (Fin 10)) :
    boundingFace productFunctional productLevel i =
      (fun x => productFacetCenter i + productFacetLinear i x) '' productFacetDomain i.1 := by
  rcases i with ⟨b, i⟩
  cases b
  · rw [product_boundingFace_first, simplex_facet_eq_affine_image]
    ext x
    constructor
    · rintro ⟨⟨a, ha, heq⟩, hb⟩
      let z : E 19 := (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (a, secondBlock x)
      refine ⟨z, ?_, ?_⟩
      · change (@EuclideanSpace.finAddEquivProd ℝ _ 9 10) z ∈ simplex 9 ×ˢ simplex 10
        simpa only [z, ContinuousLinearEquiv.apply_symm_apply, Set.mem_prod] using And.intro ha hb
      · apply (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).injective
        rw [productFacetChart_first]
        simp only [z, ContinuousLinearEquiv.apply_symm_apply]
        apply Prod.ext
        · exact heq
        · rfl
    · rintro ⟨z, hz, rfl⟩
      have heq := productFacetChart_first i z
      have hfirst := congrArg Prod.fst heq
      have hsecond := congrArg Prod.snd heq
      rw [firstBlock_finAdd] at hfirst
      rw [secondBlock_finAdd] at hsecond
      change ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) z).1 ∈ simplex 9 ∧
        ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) z).2 ∈ simplex 10 at hz
      refine ⟨⟨_, hz.1, hfirst.symm⟩, ?_⟩
      rw [hsecond]
      exact hz.2
  · rw [product_boundingFace_second, simplex_facet_eq_affine_image]
    ext x
    constructor
    · rintro ⟨ha, ⟨b, hb, heq⟩⟩
      let z : E 19 := (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (firstBlock x, b)
      refine ⟨z, ?_, ?_⟩
      · change (@EuclideanSpace.finAddEquivProd ℝ _ 10 9) z ∈ simplex 10 ×ˢ simplex 9
        simpa only [z, ContinuousLinearEquiv.apply_symm_apply, Set.mem_prod] using And.intro ha hb
      · apply (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).injective
        rw [productFacetChart_second]
        simp only [z, ContinuousLinearEquiv.apply_symm_apply]
        apply Prod.ext
        · rfl
        · exact heq
    · rintro ⟨z, hz, rfl⟩
      have heq := productFacetChart_second i z
      have hfirst := congrArg Prod.fst heq
      have hsecond := congrArg Prod.snd heq
      rw [firstBlock_finAdd] at hfirst
      rw [secondBlock_finAdd] at hsecond
      change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) z).1 ∈ simplex 10 ∧
        ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) z).2 ∈ simplex 9 at hz
      refine ⟨?_, ⟨_, hz.2, hsecond.symm⟩⟩
      rw [hfirst]
      exact hz.1

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set

theorem solution (i : Bool × Option (Fin 10)) :
    boundingFace productFunctional productLevel i =
      (fun x => productFacetCenter i + productFacetLinear i x) '' productFacetDomain i.1 := by
  first
    | exact OAI.ProjectionCounterexample.product_facet_eq_affine_image i
    | exact OAI.ProjectionCounterexample.product_facet_eq_affine_image
    | (apply OAI.ProjectionCounterexample.product_facet_eq_affine_image <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.product_facet_eq_affine_image <;> assumption)
