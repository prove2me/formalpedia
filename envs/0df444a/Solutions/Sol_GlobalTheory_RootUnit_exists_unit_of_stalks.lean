-- Prove2me | solution 1 for GlobalTheory.RootUnit.exists_unit_of_stalks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:18.907789+00:00
-- url     : https://prove2.me/submissions/73ae2b32-aa99-44d2-a57b-a04af761a98f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitOfStalks
import Theorems.Thm_GlobalTheory_RootUnit_gs_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RootUnit
open TopologicalSpace
namespace GlobalTheory.RootUnit
theorem _root_.solution {Y : Scheme.{0}} [IsIntegral Y] (W : Y.Opens) (a b : Γ(Y, W))
    (hb : ∀ y ∈ W, gs (𝟙 Y) y W b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y W a = v.val * gs (𝟙 Y) y W b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y W a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y W b := by
  have loc : ∀ y : W, ∃ (V : Y.Opens) (_ : y.1 ∈ V) (_ : V ≤ W) (c : Γ(Y, V)),
      ∀ z ∈ V, gs (𝟙 Y) z W a = gs (𝟙 Y) z V c * gs (𝟙 Y) z W b := by
    rintro ⟨y, hy⟩
    obtain ⟨v, hv⟩ := h y hy
    obtain ⟨U, hU, c, hc⟩ := Y.presheaf.germ_exist v.val
    have hm : y ∈ U ⊓ W := ⟨hU, hy⟩
    have e : gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_right).op).hom a) =
        gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_left).op).hom c *
          (Y.presheaf.map (homOfLE inf_le_right).op).hom b) := by
      rw [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, hv, gs_id y U hU]
      exact congrArg (· * _) hc.symm
    rw [gs_id y _ hm, gs_id y _ hm] at e
    have e' := germ_injective_of_isIntegral Y y hm e
    refine ⟨U ⊓ W, hm, inf_le_right, (Y.presheaf.map (homOfLE inf_le_left).op).hom c, fun z hz => ?_⟩
    have := congrArg (gs (𝟙 Y) z (U ⊓ W)) e'
    rwa [gs_mul _ z _ hz, gs_res _ z inf_le_right hz, gs_res _ z inf_le_right hz] at this
  choose V hV hle c hc using loc
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hle i))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV _⟩) c
    (fun i j => fn_ext (V := V i ⊓ V j) fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      exact mul_right_cancel₀ (hb y (hle i hy.1)) ((hc i y hy.1).symm.trans (hc j y hy.2)))
  have key : ∀ y ∈ W, gs (𝟙 Y) y W a = gs (𝟙 Y) y W s * gs (𝟙 Y) y W b := fun y hy => by
    rw [hc ⟨y, hy⟩ y (hV _), ← hs ⟨y, hy⟩]
    exact congrArg (· * _) (gs_res (𝟙 Y) y (hle ⟨y, hy⟩) (hV ⟨y, hy⟩) s)
  have hu : IsUnit (show Γ(Y, W) from s) := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨v, hv⟩ := h y hy
    have := mul_right_cancel₀ (hb y hy) ((key y hy).symm.trans hv)
    exact (congrArg IsUnit ((gs_id y W hy _).symm.trans this)).mpr v.isUnit
  refine ⟨hu.unit, fun y hy => ?_⟩
  rw [← gs_unit _ y W hy]
  exact key y hy
end GlobalTheory.RootUnit
