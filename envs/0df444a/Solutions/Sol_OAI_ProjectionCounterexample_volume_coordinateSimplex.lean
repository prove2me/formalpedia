-- Prove2me | solution 1 for OAI.ProjectionCounterexample.volume_coordinateSimplex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:30:44.286411+00:00
-- url     : https://prove2.me/submissions/8049a290-77d5-44e7-bbc9-3bf560f78c1f

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/SimplexVolume.lean:L63-L110
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.volume_coordinateSimplex. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetGraphs
import Definitions.Def_OAI_Geometry_ProjectionBody_HyperplaneJacobian
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexVolume

-- ---- from OAI.Geometry.ProjectionBody.SimplexVolume ----
namespace OAI

/-!
# Volumes of standard simplices and their products

The simplex-volume calculation below uses Tonelli's theorem and induction on the
dimension.  At first coordinate `t`, the remaining section is a simplex of radius
`r - t`; its volume is integrated over `0 ≤ t ≤ r`.  The Euclidean versions use
the measure-preserving equivalence between coordinate space and `EuclideanSpace`.
The product formula is proved using the product Lebesgue measure under the
canonical splitting of `Fin (p + q)`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ProjectionCounterexample

theorem coordinateSimplex_measurableSet (n : ℕ) (r : ℝ) :
    MeasurableSet (coordinateSimplex n r) := by
  unfold coordinateSimplex
  measurability

theorem integral_simplex_slice (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ t in Icc 0 r, ENNReal.ofReal ((r - t) ^ n / (n.factorial : ℝ))) =
      ENNReal.ofReal (r ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
  have hi : IntegrableOn (fun t : ℝ => (r - t) ^ n / (n.factorial : ℝ)) (Icc 0 r) :=
    ContinuousOn.integrableOn_Icc (by fun_prop)
  have hn : 0 ≤ᵐ[volume.restrict (Icc 0 r)]
      (fun t : ℝ => (r - t) ^ n / (n.factorial : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) n) (by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr,
    intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) r]
  simp only [sub_self, sub_zero, integral_pow,
    zero_pow (Nat.succ_ne_zero n), sub_zero]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_div]

theorem volume_coordinateSimplex (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume (coordinateSimplex n r) =
      ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by
  induction n generalizing r with
  | zero =>
    have h : coordinateSimplex 0 r = univ := by
      ext x
      simp [coordinateSimplex, hr]
    simp [h, Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have he (p : ℝ × (Fin n → ℝ)) : e.symm p = Fin.cons p.1 p.2 := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [e, MeasurableEquiv.piFinSuccAbove]
    have hslice (t : ℝ) :
        Prod.mk t ⁻¹' (e.symm ⁻¹' coordinateSimplex (n + 1) r) =
        if t ∈ Icc 0 r then coordinateSimplex n (r - t) else ∅ := by
      ext x
      simp only [mem_preimage, he, coordinateSimplex, mem_ofPred_eq,
        Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
      split_ifs with ht
      · simp only [mem_ofPred_eq]
        constructor
        · rintro ⟨⟨_, hx⟩, hs⟩
          exact ⟨hx, by linarith⟩
        · rintro ⟨hx, hs⟩
          exact ⟨⟨ht.1, hx⟩, by linarith⟩
      · simp only [mem_empty_iff_false, iff_false]
        rintro ⟨⟨ht0, hx⟩, hs⟩
        apply ht
        have hsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
        exact ⟨ht0, by linarith⟩
    rw [← (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).symm.measure_preimage_equiv]
    change volume (e.symm ⁻¹' coordinateSimplex (n + 1) r) = _
    rw [Measure.volume_eq_prod, Measure.prod_apply
      ((coordinateSimplex_measurableSet (n + 1) r).preimage e.symm.measurable)]
    simp_rw [hslice]
    have hfun : (fun t : ℝ => volume
        (if t ∈ Icc 0 r then coordinateSimplex n (r - t) else ∅)) =
        (Icc 0 r).indicator
          (fun t : ℝ => ENNReal.ofReal ((r - t) ^ n / (n.factorial : ℝ))) := by
      funext t
      by_cases ht : t ∈ Icc 0 r
      · simp [ht, ih (r - t) (sub_nonneg.mpr ht.2)]
      · simp [ht]
    rw [hfun, lintegral_indicator measurableSet_Icc]
    exact integral_simplex_slice n hr

end ProjectionCounterexample

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem solution (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume (coordinateSimplex n r) =
      ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by
  first
    | exact OAI.ProjectionCounterexample.volume_coordinateSimplex n r hr
    | exact OAI.ProjectionCounterexample.volume_coordinateSimplex
    | (apply OAI.ProjectionCounterexample.volume_coordinateSimplex <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.volume_coordinateSimplex <;> assumption)
