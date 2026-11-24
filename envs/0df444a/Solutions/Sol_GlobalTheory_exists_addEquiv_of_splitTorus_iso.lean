-- Prove2me | solution 1 for GlobalTheory.exists_addEquiv_of_splitTorus_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:51.442999+00:00
-- url     : https://prove2.me/submissions/665daeda-4ec6-44b7-9a26-8396c7da64bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsAddEquivOfSplitTorusIso
import Theorems.Thm_GlobalTheory_SplitTorusHom_appTop_comp
import Theorems.Thm_GlobalTheory_SplitTorusHom_appTop_id
import Theorems.Thm_GlobalTheory_SplitTorusHom_charUnit_injective
import Theorems.Thm_GlobalTheory_SplitTorusHom_exists_addMonoidHom

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
open SplitTorusHom
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) [ConnectedSpace S] (X X' : Type) [AddCommGroup X] [AddCommGroup X']
      (θ : splitTorus S X' ≅ splitTorus S X), IsMonHom θ.hom →
      ∃ xe : X' ≃+ X, ∀ x : X',
        θ.hom.left.appTop.hom (charUnit S X (xe x)).val = (charUnit S X' x).val := by
  intro S _ X X' _ _ θ hθ
  obtain ⟨φ, hφ⟩ := exists_addMonoidHom θ.hom
  obtain ⟨ψ, hψ⟩ := exists_addMonoidHom θ.inv
  have h1 (x : X') : φ (ψ x) = x := charUnit_injective (S := S) (by
    rw [← hφ, ← hψ, ← appTop_comp, Iso.hom_inv_id, appTop_id])
  have h2 (x : X) : ψ (φ x) = x := charUnit_injective (S := S) (by
    rw [← hψ, ← hφ, ← appTop_comp, Iso.inv_hom_id, appTop_id])
  refine ⟨{ ψ with invFun := φ, left_inv := h1, right_inv := h2 }, fun x => ?_⟩
  rw [hφ]
  exact congrArg (fun z => (charUnit S X' z).val) (h1 x)
end GlobalTheory
