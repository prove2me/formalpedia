-- Prove2me | solution 1 for GlobalTheory.SecLift.exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:57.518521+00:00
-- url     : https://prove2.me/submissions/2f940bfb-9ae6-49c4-aab2-b581874708f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val


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
theorem _root_.solution (w : LB.Iso N' (N.pull F)) (k : N.ι) (k' : N'.ι) {V : X.Opens}
    (h : V ≤ N.U k) (h' : F ⁻¹ᵁ V ≤ N'.U k') :
    ∃ ω : Γ(Y, F ⁻¹ᵁ V)ˣ, ∀ (y : Y) (hy : F y ∈ V),
      gr (𝟙 Y) y (F ⁻¹ᵁ V) hy ω.val = (Geo.Tor.gw w (𝟙 Y) y k k').val :=
  ⟨res (le_inf (pull_le N F k h) h') (w.s (fun _ => k, k')), fun y hy =>
    (gm_val (𝟙 Y) y (F ⁻¹ᵁ V) hy _).symm.trans (congrArg Units.val (gm_res (𝟙 Y) y _ hy _))⟩
end GlobalTheory.SecLift
