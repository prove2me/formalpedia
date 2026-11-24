-- Prove2me | solution 1 for GlobalTheory.WeightGen.HasGen.iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:11:51.981292+00:00
-- url     : https://prove2.me/submissions/84deba87-5093-4359-9c27-354959e86e71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_HasGen_of_local
import Theorems.Thm_GlobalTheory_WeightGen_gm_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)
variable {q a p}
namespace GlobalTheory.WeightGen
namespace HasGen
theorem _root_.solution (h : a ≫ q = p ≫ q) {L M : LB B} {c : GermFn P} (hL : HasGen q a p L c)
    (cov : ∀ x, ∃ k, x ∈ L.U k) (w : LB.Iso L M) (hw : w.IsGen) : HasGen q a p M c := by
  obtain ⟨s, s₁, s₂⟩ := hL
  refine HasGen.of_local h L.U cov
    (fun j k Z r z => gm r z _ (s k) * (gm (r ≫ q) z (M.U j ⊓ L.U k) (w.s (j, k)))⁻¹)
    (fun j k => ⟨res (V := q ⁻¹ᵁ M.U j ⊓ q ⁻¹ᵁ L.U k) inf_le_right (s k) *
      (res (U := q ⁻¹ᵁ (M.U j ⊓ L.U k)) (le_inf inf_le_left inf_le_right)
        (pullU q (M.U j ⊓ L.U k) (w.s (j, k))))⁻¹, fun Z r z h₁ h₂ => ?_⟩)
    (fun Z r z j j' k k' h₁ h₂ h₃ h₄ => ?_) (fun Z r z j k h₁ h₂ => ?_)
  · have hm : r z ∈ q ⁻¹ᵁ M.U j ⊓ q ⁻¹ᵁ L.U k := ⟨h₁, h₂⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
      ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z _ hm _).trans (gm_pull r q z (M.U j ⊓ L.U k) hm _)))))
  · rw [gm_iso hw (r ≫ q) z h₁ h₂ h₃ h₄, s₁ Z r z k k' h₃ h₄]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [s₂ Z r z k h₂, Category.assoc, Category.assoc, h, _root_.mul_assoc]
end HasGen
end GlobalTheory.WeightGen
