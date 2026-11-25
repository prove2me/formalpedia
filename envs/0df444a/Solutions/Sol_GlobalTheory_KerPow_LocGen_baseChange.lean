-- Prove2me | solution 1 for GlobalTheory.KerPow.LocGen.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:16:38.319734+00:00
-- url     : https://prove2.me/submissions/587acb4d-7cbc-428e-8d80-f079054121c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
import Theorems.Thm_GlobalTheory_KerPow_HasGen_of_range

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
namespace LocGen
theorem _root_.solution {π : Y ⟶ B} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (H : LocGen L π φ ε) {π' : Y' ⟶ B'}
    (h : Y' ⟶ Y) (g : B' ⟶ B) (sq : h ≫ π = π' ≫ g) {φ' : K → (Y' ⟶ X)} (e : ∀ k, h ≫ φ k = φ' k) :
    LocGen L π' φ' ε := by
  intro p
  obtain ⟨V, hV, t⟩ := H (g p)
  refine ⟨g ⁻¹ᵁ V, hV, t.of_range ((π' ⁻¹ᵁ (g ⁻¹ᵁ V)).ι ≫ h) (fun y => ?_) (fun k => by rw [Category.assoc, e])⟩
  exact (congrArg (fun q : Y' ⟶ B => q y.1 ∈ V) sq).mpr y.2
end LocGen
end GlobalTheory.KerPow
