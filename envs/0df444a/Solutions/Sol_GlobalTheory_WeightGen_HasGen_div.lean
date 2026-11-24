-- Prove2me | solution 1 for GlobalTheory.WeightGen.HasGen.div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:12.966823+00:00
-- url     : https://prove2.me/submissions/8174191b-04da-4f31-9002-ca017742ecf3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_pt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq


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
theorem _root_.solution (h : a ≫ q = p ≫ q) {L M : LB B} {c c' : GermFn P} (hM : HasGen q a p M c)
    (hL : HasGen q a p L c') :
    HasGen q a p (LB.div M L) (fun Z r z => c Z r z * (c' Z r z)⁻¹) := by
  obtain ⟨s, s₁, s₂⟩ := hM
  obtain ⟨t, t₁, t₂⟩ := hL
  obtain ⟨u, hu⟩ : ∃ u : ∀ j : M.ι × L.ι, Γ(G, q ⁻¹ᵁ (M.U j.1 ⊓ L.U j.2))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) j, q (r z) ∈ M.U j.1 ⊓ L.U j.2 →
        gm r z _ (u j) = gm r z _ (s j.1) * (gm r z _ (t j.2))⁻¹ :=
    ⟨fun j => res (q.preimage_mono inf_le_left) (s j.1) * (res (q.preimage_mono inf_le_right) (t j.2))⁻¹,
      fun Z r z j hj => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hj _)
        ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hj _))))⟩
  refine ⟨u, fun Z r z j j' h₁ h₂ => ?_, fun Z r z j h₁ => ?_⟩
  · refine (hu Z r z j' h₂).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_div L M (r ≫ q) z j j' ⟨h₁, h₂⟩) (hu Z r z j h₁)).symm)
    rw [s₁ Z r z _ _ h₁.1 h₂.1, t₁ Z r z _ _ h₁.2 h₂.2, mul_inv, _root_.mul_mul_mul_comm]
  · refine (hu Z (r ≫ a) z j ((pt_eq h (r z)).symm ▸ h₁ : q (a (r z)) ∈ _)).trans
      (Eq.trans ?_ (congrArg _ (hu Z (r ≫ p) z j h₁)).symm)
    rw [s₂ Z r z _ h₁.1, t₂ Z r z _ h₁.2, mul_inv, _root_.mul_mul_mul_comm]
end HasGen
end GlobalTheory.WeightGen
