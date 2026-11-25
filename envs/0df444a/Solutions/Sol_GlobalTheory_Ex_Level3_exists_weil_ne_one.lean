-- Prove2me | solution 1 for GlobalTheory.Ex.Level3.exists_weil_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:20.718208+00:00
-- url     : https://prove2.me/submissions/9b9f0ae1-0c1b-405c-9a42-2be61a74f8a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Theorems.Thm_GlobalTheory_Ex_Level3_bun_nondeg
import Theorems.Thm_GlobalTheory_Ex_Level3_septicCharacter_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.Level3
namespace GlobalTheory.Ex.Level3
theorem _root_.solution : ∃ (N : NumD (ZMod 7)) (b b' : N.A), b ^ 3 = 1 ∧ b' ^ 3 = 1 ∧ N.weil 3 b b' ≠ 1 := by
  have t : ∀ b : A₃, b ^ 3 = 1 := by decide +kernel
  by_contra h
  have := bun_nondeg chi7 septicCharacter_injective (fun _ => 1) (Multiplicative.ofAdd (1, 0)) fun b' =>
    not_not.1 fun e => h ⟨dat chi7 (fun _ => 1) 1, _, b', t _, t _, e⟩
  revert this
  decide
end GlobalTheory.Ex.Level3
