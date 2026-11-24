-- Prove2me | solution 1 for GlobalTheory.SplitTorusHom.existsUnique_pullback_charUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:46:51.512648+00:00
-- url     : https://prove2.me/submissions/7b6b0a67-dca6-4337-b020-82e9fb197915

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsAddEquivOfSplitTorusIso
import Theorems.Thm_GlobalTheory_SplitTorusHom_appTop_comp
import Theorems.Thm_GlobalTheory_SplitTorusHom_appTop_id
import Theorems.Thm_GlobalTheory_SplitTorusHom_appTop_mul_charUnit
import Theorems.Thm_GlobalTheory_existsUnique_character_of_mul
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val


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
open GlobalTheory.SplitTorusHom
variable {S : Scheme.{0}}
variable {X X' : Type} [AddCommGroup X] [AddCommGroup X']
namespace GlobalTheory.SplitTorusHom
theorem _root_.solution [ConnectedSpace S]
    (f : splitTorus S X' ⟶ splitTorus S X) [IsMonHom f] (χ : X) :
    ∃! x : X', f.left.appTop.hom (charUnit S X χ).val = (charUnit S X' x).val := by
  haveI : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  obtain ⟨x, hx, hu⟩ := existsUnique_character_of_mul S X' (𝟙_ (Over S))
    (splitTorusPointsEquiv S X _ (fst (splitTorus S X') (𝟙_ (Over S)) ≫ f)
      (Multiplicative.ofAdd χ)) (fun Z t t' y => by
        rw [splitTorusPointsEquiv_val, ← appTop_comp, ← appTop_comp, ← appTop_comp,
          lift_fst_assoc, lift_fst_assoc, lift_fst_assoc, MonObj.mul_comp, appTop_mul_charUnit])
  refine ⟨x, ?_, fun x' hx' => hu x' ?_⟩
  · have := congrArg (lift (𝟙 (splitTorus S X')) (toUnit _)).left.appTop.hom hx
    rwa [splitTorusPointsEquiv_val, ← appTop_comp, ← appTop_comp, lift_fst_assoc, lift_fst,
      Category.id_comp, appTop_id] at this
  · beta_reduce at hx' ⊢
    rw [splitTorusPointsEquiv_val, appTop_comp, hx']
end GlobalTheory.SplitTorusHom
