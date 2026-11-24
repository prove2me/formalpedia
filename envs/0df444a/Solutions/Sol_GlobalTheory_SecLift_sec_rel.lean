-- Prove2me | solution 1 for GlobalTheory.SecLift.sec_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:22.611747+00:00
-- url     : https://prove2.me/submissions/0349f8d5-d22f-47cf-aec6-2d7390069596

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


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
theorem _root_.solution (s : LB.Sec N) (x : X) {k l : N.ι} (hk : x ∈ N.U k) (hl : x ∈ N.U l) :
    gr (𝟙 X) x _ hk (s.f k) =
      gr (𝟙 X) x (N.U k ⊓ N.U l) ⟨hk, hl⟩ (N.g k l).val * gr (𝟙 X) x _ hl (s.f l) := by
  have := congrArg (gr (𝟙 X) x (N.U k ⊓ N.U l) ⟨hk, hl⟩) (s.compat k l)
  rwa [map_mul, gr_res, gr_res] at this
end GlobalTheory.SecLift
