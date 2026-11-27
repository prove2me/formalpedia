-- Prove2me | solution 1 for GlobalTheory.UU.SecMod.one_ne_zero_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:07.735406+00:00
-- url     : https://prove2.me/submissions/6a6c5906-5c6e-4aec-a9ca-f08ebdec6eea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
import Theorems.Thm_GlobalTheory_UU_SecMod_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.UU
open GlobalTheory.UU.SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}
namespace GlobalTheory.UU.SecMod
theorem _root_.solution [Nontrivial F] :
    ofFun (𝟙 (Spec (CommRingCat.of F))) 1 ≠ 0 := by
  intro h
  have h1 : (1 : Γ(Spec (CommRingCat.of F), ⊤)) = 0 := (eq_zero_iff _).1 h PUnit.unit
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom h1
  rw [map_one, map_zero] at h2
  exact one_ne_zero h2
end GlobalTheory.UU.SecMod
