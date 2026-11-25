-- Prove2me | solution 1 for GlobalTheory.KerPow.locGen_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:10:47.038366+00:00
-- url     : https://prove2.me/submissions/7e9f1752-8cb4-4c57-ade9-79b58637e0ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
import Theorems.Thm_GlobalTheory_KerPow_hasGen_of_trivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KerPow
variable {X Y Y' B B' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
namespace GlobalTheory.KerPow
theorem _root_.solution (hL : L.IsLB) {π : Y ⟶ B} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (e : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) : LocGen L π φ ε :=
  fun _ => ⟨⊤, trivial, hasGen_of_trivial hL fun U _ h => e U fun q => h ((π ⁻¹ᵁ ⊤).ι ≫ q)⟩
end GlobalTheory.KerPow
