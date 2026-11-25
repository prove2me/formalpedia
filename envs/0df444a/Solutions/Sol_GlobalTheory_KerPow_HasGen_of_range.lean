-- Prove2me | solution 1 for GlobalTheory.KerPow.HasGen.of_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:55:04.194817+00:00
-- url     : https://prove2.me/submissions/fbd638b7-7cf8-4780-b6ac-d87140c76364

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial

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
namespace HasGen
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {W : Y.Opens} (H : HasGen L (fun k => W.ι ≫ φ k) ε)
    (h : Y' ⟶ Y) (hW : ∀ y, h y ∈ W) {φ' : K → (Y' ⟶ X)} (e : ∀ k, h ≫ φ k = φ' k) : HasGen L φ' ε :=
  H.pull (IsOpenImmersion.lift W.ι h (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hW y))
    (fun k => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ k) (IsOpenImmersion.lift_fac _ _ _)).trans (e k)))
end HasGen
end GlobalTheory.KerPow
