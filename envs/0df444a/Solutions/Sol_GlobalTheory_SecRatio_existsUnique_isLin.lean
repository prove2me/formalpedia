-- Prove2me | solution 1 for GlobalTheory.SecRatio.existsUnique_isLin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:11.195799+00:00
-- url     : https://prove2.me/submissions/75dd285e-9067-48fc-b6b0-4aaa871d5df7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
namespace GlobalTheory.SecRatio
private theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (e : U ≤ V) (a : R) : resG X e (constFn p V a) = constFn p U a := by
  unfold constFn
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  erw [Scheme.Hom.appLE_map]
variable {X : Scheme.{0}} {H : LB X}
end GlobalTheory.SecRatio
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.SecRatio
variable {X : Scheme.{0}} {H : LB X}
namespace GlobalTheory.SecRatio
theorem _root_.solution {k : Type} [CommRing k] (p : X ⟶ Sp k) {J : Type} [Fintype J]
    (s : J → H.Sec) (a : J → k) : ∃! φ : H.Sec, IsLin p s a φ := by
  refine ⟨⟨fun l => ∑ j, constFn p (H.U l) (a j) * (s j).f l, fun i j => ?_⟩, fun l => rfl, ?_⟩
  · change resG X inf_le_left _ = _ * resG X inf_le_right _
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_mul, res_const, res_const]
    have : resG X inf_le_left _ = _ * resG X inf_le_right _ := (s n).compat i j
    rw [this]; ring
  · rintro ⟨f, hf⟩ h
    have : f = _ := funext h
    subst this
    rfl
end GlobalTheory.SecRatio
