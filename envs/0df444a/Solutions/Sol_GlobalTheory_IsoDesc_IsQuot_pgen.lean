-- Prove2me | solution 1 for GlobalTheory.IsoDesc.IsQuot.pgen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:55:35.120133+00:00
-- url     : https://prove2.me/submissions/daf76b1d-54e4-47bb-ae0e-6625d0d8a2da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_IsoDesc_kap_gm
import Theorems.Thm_GlobalTheory_IsoDesc_kap_injective
import Theorems.Thm_GlobalTheory_IsoDesc_kap_gw
import Theorems.Thm_GlobalTheory_IsoDesc_IsQuot_trans
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {X Y Z : Scheme.{0}}
variable {G B' B : Scheme.{0}} {L : LB G} {M' : LB B'} {M : LB B} {q : G ⟶ B'} {β : B' ⟶ B}
namespace GlobalTheory.IsoDesc
namespace IsQuot
theorem _root_.solution [Flat q] [Surjective q] (hL : L.IsLB) {u : LB.Iso L (M'.pull q)}
    {w : LB.Iso L (M.pull (q ≫ β))} (hu : PGen u) (hw : PGen w) {s} (hs : IsQuot u w s)
    {v : LB.Iso M' (M.pull β)} (hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ G) (y : Y) j i, q (f y) ∈ dom M' M β j i →
      gw v (f ≫ q) y j i = gm f y _ (s j i)) : PGen v := by
  intro Y f y j j' i i' hj hj' hi hi'
  obtain ⟨z, rfl⟩ := (pullback.fst f q).surjective y
  have e : q (pullback.snd f q z) = f (pullback.fst f q z) :=
    congrArg (fun g => g z) (pullback.condition (f := f) (g := q)).symm
  apply kap_injective _ z
  have a := hs.trans hL hu hw (pullback.snd f q) z j j' i i' (e ▸ hj) (e ▸ hj') (e ▸ hi) (e ▸ hi')
  rw [← hv _ _ _ _ _ ⟨mem_pull.2 (e ▸ hj), e ▸ hi⟩, ← hv _ _ _ _ _ ⟨mem_pull.2 (e ▸ hj'), e ▸ hi'⟩,
    ← pullback.condition, Category.assoc] at a
  simp only [map_mul, map_inv, kap_gm, kap_gw]
  exact a
end IsQuot
end GlobalTheory.IsoDesc
