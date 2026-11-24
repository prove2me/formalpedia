-- Prove2me | solution 1 for GlobalTheory.SecAff.glue_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:51.397401+00:00
-- url     : https://prove2.me/submissions/71a4d29b-457b-4ad4-8274-0f8f9c7b15f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}
namespace GlobalTheory.SecAff
theorem _root_.solution {κ : Type} {U : X.Opens} (W : κ → X.Opens) (hW : ∀ a, W a ≤ U)
    (hc : U ≤ ⨆ a, W a) (x : ∀ a, Γ(X, W a))
    (h : ∀ a b, rs (inf_le_left : W a ⊓ W b ≤ W a) (x a) = rs (inf_le_right : W a ⊓ W b ≤ W b) (x b)) :
    ∃ y : Γ(X, U), ∀ a, rs (hW a) y = x a := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W U (fun a => homOfLE (hW a)) hc x h
  exact ⟨s, hs⟩
end GlobalTheory.SecAff
