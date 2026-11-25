-- Prove2me | solution 1 for GlobalTheory.TorusCube.HasVal.exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:26.221413+00:00
-- url     : https://prove2.me/submissions/1fcecafb-8988-42e7-9dc2-b6c353272f24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SplitTorusGenCubical
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusCube
open Rosenlicht SplitTorusPoints Geo.Tor
variable {X Y : Scheme.{0}} (L : LB X)
variable {L}
namespace GlobalTheory.TorusCube
namespace HasVal
theorem _root_.solution (hL : L.IsLB) {F : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V} {f}
    (h : HasVal L F f) (hF : ∀ (V : Type) [CommGroup V] (k : (Y ⟶ X) → V), F V k = 1) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (f Z r z J).val = gs (𝟙 Z) z ⊤ (r.appTop.hom w.val) := by
  obtain ⟨K, _, φ, ε, u, hu, a, b⟩ := h
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun V _ k => (a V k).trans ((hF V k).trans (Fintype.prod_empty _).symm)) u hu
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← b Z r z J hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  refine (congrArg Units.val (gm_res r z le trivial _)).symm.trans
    ((gs_unit r z ⊤ trivial _).symm.trans ?_)
  refine Eq.trans ?_ (gs_pull (𝟙 Z) r z ⊤ trivial _).symm
  rw [Category.id_comp]
end HasVal
end GlobalTheory.TorusCube
