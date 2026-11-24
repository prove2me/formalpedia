-- Prove2me | solution 1 for GlobalTheory.SegreCoord.Loc.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:56:13.661902+00:00
-- url     : https://prove2.me/submissions/766871e1-b3ed-453f-9f99-e462d83423c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Theorems.Thm_GlobalTheory_SegreCoord_ev_ext
import Theorems.Thm_GlobalTheory_SegreCoord_isUnit_of_ev
import Theorems.Thm_GlobalTheory_SegreCoord_exists_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
namespace GlobalTheory.SegreCoord
namespace Loc
theorem _root_.solution (hM : M.IsLB) {x : Sp T ⟶ X} {v w : σ → T} (h : Loc M th x v) (h' : Loc M th x w)
    (hv : Ideal.span (Set.range v) = ⊤) : ∃ t : T, IsUnit t ∧ ∀ i, w i = t * v i := by
  obtain ⟨s, c, hc⟩ := exists_comb hv
  have key : ∀ y : Sp T, ∃ u : ((Sp T).presheaf.stalk y)ˣ, (∀ i, ev y (w i) = u * ev y (v i)) ∧
      ev y (∑ i ∈ s, c i * w i) = u := fun y => by
    obtain ⟨j, hj⟩ := exists_chart hM (x y)
    obtain ⟨u, hu⟩ := h y j hj
    obtain ⟨u', hu'⟩ := h' y j hj
    have e : ∀ i, ev y (w i) = (u * u'⁻¹ :).val * ev y (v i) := fun i => by
      rw [Units.val_mul, mul_comm, ← mul_assoc, ← hu, hu', Units.mul_inv_cancel_right]
    refine ⟨u * u'⁻¹, e, ?_⟩
    simp only [map_sum, map_mul, e, mul_left_comm _ (u * u'⁻¹ :).val]
    simp only [← map_mul, ← Finset.mul_sum, ← map_sum, hc, map_one, mul_one]
  refine ⟨∑ i ∈ s, c i * w i, isUnit_of_ev fun y => ?_, fun i => ev_ext fun y => ?_⟩
  · obtain ⟨u, -, e⟩ := key y
    rw [e]; exact u.isUnit
  · obtain ⟨u, e', e⟩ := key y
    rw [map_mul, e, e']
end Loc
end GlobalTheory.SegreCoord
