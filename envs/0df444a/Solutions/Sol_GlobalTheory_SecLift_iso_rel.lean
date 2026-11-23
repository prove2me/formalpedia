-- Prove2me | solution 1 for GlobalTheory.SecLift.iso_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:36.788223+00:00
-- url     : https://prove2.me/submissions/ca10ef39-f230-44ee-b7b5-f40dc6426c59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
variable {N : LB X} {N' : LB Y} {F : Y ⟶ X}
namespace GlobalTheory.SecLift
theorem _root_.solution {w : LB.Iso N' (N.pull F)} (hw : w.IsGen) (y : Y) {k l : N.ι} {k' l' : N'.ι}
    (hk : F y ∈ N.U k) (hl : F y ∈ N.U l) (hk' : y ∈ N'.U k') (hl' : y ∈ N'.U l') :
    (Geo.Tor.gw w (𝟙 Y) y k k').val * gr (𝟙 Y) y (N'.U k' ⊓ N'.U l') ⟨hk', hl'⟩ (N'.g k' l').val =
      gr (𝟙 Y ≫ F) y (N.U k ⊓ N.U l) ⟨hk, hl⟩ (N.g k l).val * (Geo.Tor.gw w (𝟙 Y) y l l').val := by
  have h := (isGen_iff w).1 hw _ (𝟙 Y) y k l k' l' hk hl hk' hl'
  have e₁ := gm_val (𝟙 Y) y (N'.U k' ⊓ N'.U l') ⟨hk', hl'⟩ (N'.g k' l')
  have e₂ := gm_val (𝟙 Y ≫ F) y (N.U k ⊓ N.U l) ⟨hk, hl⟩ (N.g k l)
  refine (congrArg _ e₁.symm).trans (Eq.trans ?_ (congrArg (· * _) e₂))
  rw [h, ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right]
end GlobalTheory.SecLift
