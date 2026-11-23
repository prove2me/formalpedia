-- Prove2me | solution 1 for GlobalTheory.SegreCoord.exists_secCoord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:52.769919+00:00
-- url     : https://prove2.me/submissions/1b6cc83d-9992-4931-8bf3-755b36a42e82

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
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
theorem _root_.solution (hM : M.IsLB) {x : Sp T ⟶ X} {k : M.ι} (hk : ∀ y, x y ∈ M.U k) : ∃ v, SecCoord M th x v := by
  have le : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U k) := fun j y hy => ⟨mem_pull.1 hy, hk y⟩
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom ((x.appLE (M.U k) ⊤ (fun y _ => hk y)).hom ((th i).f k)),
    secCoord_mk (fun j => (x.appLE _ _ (le j)).hom (M.g (j PUnit.unit) k).val)
    (fun y j => gs x y _ (M.g j k).val) (fun j y hy => gs_appLE x y _ hy _) (fun y j hy => ?_)
    (fun y j j' hy hy' => ?_) (fun y j i hy => ?_)⟩
  · rw [gs_unit x y (M.U _ ⊓ M.U k) ⟨hy, hk y⟩]; exact Units.isUnit _
  · rw [gs_unit x y (M.U _ ⊓ M.U k) ⟨hy, hk y⟩, gs_unit x y (M.U _ ⊓ M.U k) ⟨hy', hk y⟩, ← Units.val_mul, gm_cocycle hM x y hy hy' (hk y)]
  · rw [gs_unit x y (M.U _ ⊓ M.U k) ⟨hy, hk y⟩, gs_sec (th i) x y hy (hk y), mul_comm, ev_eq]
    congr 1
    rw [← gs_appLE x y (V := ⊤) (fun y _ => hk y) trivial]
    congr 1
    simp
end GlobalTheory.SegreCoord
