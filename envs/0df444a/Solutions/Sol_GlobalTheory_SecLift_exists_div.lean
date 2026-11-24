-- Prove2me | solution 1 for GlobalTheory.SecLift.exists_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:16.69179+00:00
-- url     : https://prove2.me/submissions/0904dd23-2ab6-45c0-af8f-3072aa7af6e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
import Theorems.Thm_GlobalTheory_SecLift_stalkMap_gr
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_app
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cst
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
namespace GlobalTheory.SecLift
theorem _root_.solution {f : X ⟶ Spec (CommRingCat.of A)} {j : Y ⟶ X} {a : A}
    (hS : ∀ (y : Y) (e : X.presheaf.stalk (j y)),
      cstS (𝟙 X ≫ f) (j y) a * e = 0 → (j.stalkMap y).hom e = 0)
    (W : X.Opens) (d : Γ(X, W))
    (hd : ∀ (V : X.Opens) (hle : V ≤ W), IsAffineOpen V → ∃ e, rs X hle d = cst f V a * e) :
    ∃ φ : Γ(Y, j ⁻¹ᵁ W), ∀ (y : Y) (h : j y ∈ W), ∃ e, gr (𝟙 X) (j y) W h d =
      cstS (𝟙 X ≫ f) (j y) a * e ∧ (j.stalkMap y).hom e = gr (𝟙 Y) y (j ⁻¹ᵁ W) h φ := by
  let I := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  choose e he using fun V : I => hd V.1 V.2.2 V.2.1
  have he' : ∀ (V : I) (x : X) (h : x ∈ V.1), gr (𝟙 X) x W (V.2.2 h) d =
      cstS (𝟙 X ≫ f) x a * gr (𝟙 X) x V.1 h (e V) := fun V x h => by
    rw [← gr_res (𝟙 X) x V.2.2 h, ← gr_cst (𝟙 X) f x V.1 h, ← map_mul, ← he]
  have cov : ∀ x ∈ W, ∃ V : I, x ∈ V.1 := fun x hx => by
    obtain ⟨V, hV, hxV, hl⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    exact ⟨⟨V, hV, hl⟩, hxV⟩
  obtain ⟨φ, hφ, -⟩ := Y.sheaf.existsUnique_gluing' (fun V : I => j ⁻¹ᵁ V.1) (j ⁻¹ᵁ W)
    (fun V => homOfLE (fun _ h => V.2.2 h)) (fun y hy => Opens.mem_iSup.2 (cov _ hy))
    (fun V => (j.app V.1).hom (e V))
    (fun V V' => gr_ext (V := j ⁻¹ᵁ V.1 ⊓ j ⁻¹ᵁ V'.1) fun y hy => by
      refine (gr_res _ y inf_le_left hy _).trans (Eq.trans ?_ (gr_res _ y inf_le_right hy _).symm)
      rw [gr_app, gr_app, ← stalkMap_gr, ← stalkMap_gr, ← sub_eq_zero, ← map_sub]
      refine hS y _ ?_
      rw [mul_sub, ← he' V (j y) hy.1, ← he' V' (j y) hy.2, sub_self])
  refine ⟨φ, fun y h => ?_⟩
  obtain ⟨V, hV⟩ := cov _ h
  refine ⟨_, he' V _ hV, ?_⟩
  rw [stalkMap_gr, ← gr_app (𝟙 Y) j y V.1 hV]
  exact (congrArg (gr (𝟙 Y) y _ hV) (hφ V)).symm.trans (gr_res (𝟙 Y) y _ hV φ)
end GlobalTheory.SecLift
