-- Prove2me | solution 1 for GlobalTheory.SegreCoord.secCoord_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:26:44.968167+00:00
-- url     : https://prove2.me/submissions/da67c1d4-f2d3-44ea-a00f-31b7ee298615

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
theorem _root_.solution {x : Sp T ⟶ X} {v : σ → T} (t : ∀ j : PUnit → M.ι, Γ(Sp T, (M.pull x).U j))
    (c : ∀ (y : Sp T), M.ι → (Sp T).presheaf.stalk y)
    (ht : ∀ j y, y ∈ (M.pull x).U j → gs (𝟙 _) y _ (t j) = c y (j PUnit.unit))
    (hu : ∀ y j, x y ∈ M.U j → IsUnit (c y j))
    (hc : ∀ y j j', x y ∈ M.U j → x y ∈ M.U j' → c y j = (gm x y _ (M.g j j')).val * c y j')
    (hv : ∀ y j i, x y ∈ M.U j → gs x y _ ((th i).f j) = ev y (v i) * c y j) : SecCoord M th x v := by
  have hU : ∀ j, IsUnit (t j) := fun j => (Sp T).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
    (congrArg IsUnit ((gs_eq (𝟙 _) y _ hy _).symm.trans (ht j y hy))).mpr (hu y _ (mem_pull.1 hy))
  refine ⟨⟨fun j => (hU j).unit⟩, fun j j' => Units.ext (fn_ext fun y hy => ?_), fun i j h => fn_ext fun y hy => ?_⟩
  · refine ((gs_res (𝟙 _) y inf_le_left hy (t j)).trans (ht j y hy.1)).trans (Eq.trans ?_
      ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 _) y _ hy _).trans
        (congrArg Units.val (gm_pull_g M x (𝟙 _) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 _) y inf_le_right hy (t j')).trans (ht j' y hy.2)))).symm)
    rw [Category.id_comp]
    exact hc y _ _ (mem_pull.1 hy.1) (mem_pull.1 hy.2)
  · refine (gs_appLE x y _ hy _).trans ((hv y _ i (mem_pull.1 hy)).trans (Eq.symm ?_))
    exact (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans (ev_eq y _).symm) (ht j y hy))
end GlobalTheory.SegreCoord
