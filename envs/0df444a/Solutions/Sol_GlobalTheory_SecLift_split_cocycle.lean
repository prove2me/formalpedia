-- Prove2me | solution 1 for GlobalTheory.SecLift.split_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:23.587379+00:00
-- url     : https://prove2.me/submissions/715dcd5f-7fb1-4b2a-962b-c50236265a58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
import Theorems.Thm_GlobalTheory_SecLift_iso_rel
import Theorems.Thm_GlobalTheory_SecLift_exists_unit
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
variable {N : LB X} {N' : LB Y} {F : Y ⟶ X}
namespace GlobalTheory.SecLift
theorem _root_.solution {w : LB.Iso N' (N.pull F)} (hw : w.IsGen) (H : FirstCohomologyVanishes N') {I : Type}
    (V : I → X.Opens) (cov : ∀ x : X, ∃ a, x ∈ V a) (k : I → N.ι) (k' : I → N'.ι)
    (h : ∀ a, V a ≤ N.U (k a)) (h' : ∀ a, F ⁻¹ᵁ V a ≤ N'.U (k' a))
    (φ : ∀ a b, Γ(Y, F ⁻¹ᵁ (V a ⊓ V b)))
    (hφ : ∀ a b d (y : Y) (ha : F y ∈ V a) (hb : F y ∈ V b) (hd : F y ∈ V d),
      gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) ⟨ha, hb⟩ (φ a b) +
        gr (𝟙 Y ≫ F) y (N.U (k a) ⊓ N.U (k b)) ⟨h a ha, h b hb⟩ (N.g (k a) (k b)).val *
          gr (𝟙 Y) y (F ⁻¹ᵁ (V b ⊓ V d)) ⟨hb, hd⟩ (φ b d) =
        gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V d)) ⟨ha, hd⟩ (φ a d)) :
    ∃ ψ : ∀ a, Γ(Y, F ⁻¹ᵁ V a), ∀ a b (y : Y) (ha : F y ∈ V a) (hb : F y ∈ V b),
      gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) ⟨ha, hb⟩ (φ a b) = gr (𝟙 Y) y (F ⁻¹ᵁ V a) ha (ψ a) -
        gr (𝟙 Y ≫ F) y (N.U (k a) ⊓ N.U (k b)) ⟨h a ha, h b hb⟩ (N.g (k a) (k b)).val *
          gr (𝟙 Y) y (F ⁻¹ᵁ V b) hb (ψ b) := by
  choose ω hω using fun a => exists_unit w (k a) (k' a) (h a) (h' a)
  have hi : ∀ a (y : Y) (ha : F y ∈ V a), (Geo.Tor.gw w (𝟙 Y) y (k a) (k' a)).val *
      gr (𝟙 Y) y (F ⁻¹ᵁ V a) ha (ω a)⁻¹.val = 1 := fun a y ha => by
    rw [← hω a y ha, ← map_mul, Units.mul_inv, map_one]
  let χ : ∀ a b, Γ(Y, F ⁻¹ᵁ V a ⊓ F ⁻¹ᵁ V b) := fun a b => rs Y inf_le_left (ω a)⁻¹.val *
    rs Y (show F ⁻¹ᵁ V a ⊓ F ⁻¹ᵁ V b ≤ F ⁻¹ᵁ (V a ⊓ V b) from fun _ h => h) (φ a b)
  have hχ : ∀ a b (y : Y) (hy : y ∈ F ⁻¹ᵁ V a ⊓ F ⁻¹ᵁ V b), gr (𝟙 Y) y _ hy (χ a b) =
      gr (𝟙 Y) y (F ⁻¹ᵁ V a) hy.1 (ω a)⁻¹.val * gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) hy (φ a b) :=
    fun a b y hy => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gr_res _ y _ hy _) (gr_res _ y _ hy _))
  clear_value χ
  obtain ⟨ψ, hψ⟩ := H I (fun a => F ⁻¹ᵁ V a) k' h'
    (eq_top_iff.2 fun y _ => Opens.mem_iSup.2 (cov (F y))) χ (fun a b d => gr_ext fun y hy => by
      rw [map_add, gr_res, gr_res, map_mul, gr_res, gr_res, hχ, hχ, hχ]
      have e₁ := hφ a b d y hy.1.1 hy.1.2 hy.2
      have e₂ := iso_rel hw y (h a hy.1.1) (h b hy.1.2) (h' a hy.1.1) (h' b hy.1.2)
      have e₃ := hi a y hy.1.1
      have e₄ := hi b y hy.1.2
      refine (Units.isUnit (Geo.Tor.gw w (𝟙 Y) y (k a) (k' a))).mul_left_cancel ?_
      linear_combination e₁ + (gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) hy.1 (φ a b) -
        gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V d)) ⟨hy.1.1, hy.2⟩ (φ a d)) * e₃ +
        (gr (𝟙 Y) y (F ⁻¹ᵁ V b) hy.1.2 (ω b)⁻¹.val *
          gr (𝟙 Y) y (F ⁻¹ᵁ (V b ⊓ V d)) ⟨hy.1.2, hy.2⟩ (φ b d)) * e₂ +
        (gr (𝟙 Y ≫ F) y (N.U (k a) ⊓ N.U (k b)) ⟨h a hy.1.1, h b hy.1.2⟩ (N.g (k a) (k b)).val *
          gr (𝟙 Y) y (F ⁻¹ᵁ (V b ⊓ V d)) ⟨hy.1.2, hy.2⟩ (φ b d)) * e₄)
  refine ⟨fun a => (ω a).val * ψ a, fun a b y ha hb => ?_⟩
  have e₁ := congrArg (gr (𝟙 Y) y (F ⁻¹ᵁ V a ⊓ F ⁻¹ᵁ V b) ⟨ha, hb⟩) (hψ a b)
  rw [hχ, map_sub, map_mul, gr_res, gr_res, gr_res] at e₁
  have e₂ := iso_rel hw y (h a ha) (h b hb) (h' a ha) (h' b hb)
  have e₃ := hi a y ha
  rw [map_mul, map_mul, hω, hω]
  linear_combination (Geo.Tor.gw w (𝟙 Y) y (k a) (k' a)).val * e₁ -
    gr (𝟙 Y) y (F ⁻¹ᵁ (V a ⊓ V b)) ⟨ha, hb⟩ (φ a b) * e₃ - gr (𝟙 Y) y (F ⁻¹ᵁ V b) hb (ψ b) * e₂
end GlobalTheory.SecLift
