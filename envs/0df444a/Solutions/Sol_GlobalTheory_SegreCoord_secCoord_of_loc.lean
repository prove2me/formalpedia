-- Prove2me | solution 1 for GlobalTheory.SegreCoord.secCoord_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:55:01.334+00:00
-- url     : https://prove2.me/submissions/f1bf675e-8fe2-4e9a-9318-1372997d5223

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
import Theorems.Thm_GlobalTheory_SegreCoord_ev_eq
import Theorems.Thm_GlobalTheory_SegreCoord_gs_appLE
import Theorems.Thm_GlobalTheory_SegreCoord_secCoord_mk
import Theorems.Thm_GlobalTheory_SegreCoord_gs_sum
import Theorems.Thm_GlobalTheory_SegreCoord_exists_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
theorem _root_.solution {x : Sp T ⟶ X} {v : σ → T} (hv : Ideal.span (Set.range v) = ⊤) (h : Loc M th x v) :
    SecCoord M th x v := by
  obtain ⟨s, c, hc⟩ := exists_comb hv
  have key : ∀ y j, x y ∈ M.U j → ∀ u : ((Sp T).presheaf.stalk y)ˣ, (∀ i, gs x y _ ((th i).f j) = ev y (v i) * u) →
      ∑ i ∈ s, ev y (c i) * gs x y _ ((th i).f j) = u := fun y j _ u hu => by
    simp only [hu, ← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum, hc, map_one, one_mul]
  refine secCoord_mk (fun j => ∑ i ∈ s, resG (Sp T) le_top ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (c i)) *
    (x.appLE _ _ (fun z hz => mem_pull.1 hz)).hom ((th i).f (j PUnit.unit)))
    (fun y j => ∑ i ∈ s, ev y (c i) * gs x y _ ((th i).f j)) (fun j y hy => ?_) (fun y j hy => ?_)
    (fun y j j' hy hy' => ?_) (fun y j i hy => ?_)
  · refine (gs_sum _ y _ hy _ _).trans (Finset.sum_congr rfl fun i _ => (gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans (ev_eq y _).symm) (gs_appLE x y _ hy _)
  · obtain ⟨u, hu⟩ := h y j hy
    rw [key y j hy u hu]; exact u.isUnit
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [gs_sec (th i) x y hy hy', mul_left_comm]
  · obtain ⟨u, hu⟩ := h y j hy
    rw [key y j hy u hu, hu]
end GlobalTheory.SegreCoord
