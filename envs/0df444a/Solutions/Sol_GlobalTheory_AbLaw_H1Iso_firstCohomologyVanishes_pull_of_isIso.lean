-- Prove2me | solution 1 for GlobalTheory.AbLaw.H1Iso.firstCohomologyVanishes_pull_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:24:28.955691+00:00
-- url     : https://prove2.me/submissions/fb5e1a2d-81e7-4393-bc54-29db0418656b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_rs_pb
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_pb_rs
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_pb_pb
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_pull_g

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
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory.AbLaw.H1Iso
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLaw.H1Iso
theorem _root_.solution (e : Y ⟶ X) [IsIso e] (M : LB X) (hM : FirstCohomologyVanishes M) : FirstCohomologyVanishes (M.pull e) := by
  intro I V c hV hc φ hφ
  have h1 : inv e ≫ e = 𝟙 X := IsIso.inv_hom_id e
  have h2 : e ≫ inv e = 𝟙 Y := IsIso.hom_inv_id e
  have hV' : ∀ a, inv e ⁻¹ᵁ V a ≤ M.U (c a PUnit.unit) := fun a =>
    le_of_comp_id h1 le_rfl ((hV a).trans (pull_U_le M e (c a)))
  have hb : ∀ a, V a ≤ e ⁻¹ᵁ (inv e ⁻¹ᵁ V a) := fun a => by
    have : V a ≤ (e ≫ inv e) ⁻¹ᵁ V a := by rw [h2]; exact le_rfl
    exact this
  have hc' : ⨆ a, inv e ⁻¹ᵁ V a = ⊤ := by
    apply top_unique
    intro x _
    have hx : (inv e).base x ∈ ⨆ a, V a := by rw [hc]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩
  obtain ⟨ψ, hψ⟩ := hM I (fun a => inv e ⁻¹ᵁ V a) (fun a => c a PUnit.unit) hV' hc'
    (fun a b => pb (inv e) (le_pre_inf _ inf_le_left inf_le_right : inv e ⁻¹ᵁ V a ⊓ inv e ⁻¹ᵁ V b ≤ inv e ⁻¹ᵁ (V a ⊓ V b)) (φ a b))
    (fun a b d => by
      have h := congrArg (pb (inv e) (le_pre_inf _ (le_pre_inf _ (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right)) inf_le_right : inv e ⁻¹ᵁ V a ⊓ inv e ⁻¹ᵁ V b ⊓ inv e ⁻¹ᵁ V d ≤
        inv e ⁻¹ᵁ (V a ⊓ V b ⊓ V d))) (hφ a b d)
      simp only [map_add, map_mul, pull_g, rs_pb, pb_rs, pb_pb h1] at h
      simp only [rs_pb]
      exact h)
  refine ⟨fun a => pb e (hb a) (ψ a), fun a b => ?_⟩
  have h := congrArg (pb e (le_pre_inf e (inf_le_left.trans (hb a)) (inf_le_right.trans (hb b)) :
    V a ⊓ V b ≤ e ⁻¹ᵁ (inv e ⁻¹ᵁ V a ⊓ inv e ⁻¹ᵁ V b))) (hψ a b)
  simp only [map_sub, map_mul, pb_rs, pb_pb h2, rs_self] at h
  simp only [pull_g, rs_pb]
  exact h
end GlobalTheory.AbLaw.H1Iso
