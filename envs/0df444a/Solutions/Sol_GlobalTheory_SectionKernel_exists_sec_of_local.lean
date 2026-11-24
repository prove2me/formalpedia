-- Prove2me | solution 1 for GlobalTheory.SectionKernel.exists_sec_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:37:29.550731+00:00
-- url     : https://prove2.me/submissions/545b993d-e7ab-4f33-8b5f-fcd862a10c2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_glue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SectionKernel
variable {X Y : Scheme.{0}}
variable {A A₀ : Type} [CommRing A] [CommRing A₀] {g₀ : A →+* A₀} {a : A}
  {f : X ⟶ Spec (CommRingCat.of A)} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} {j : Y ⟶ X}
namespace GlobalTheory.SectionKernel
theorem _root_.solution {N : LB X} {N₀ : LB Y} (w : LB.Iso N₀ (N.pull j)) (hN₀ : N₀.IsLB)
    (hw : w.IsGen) {I : Type} (V : I → X.Opens) (c : I → N.ι) (hc : ∀ q, V q ≤ N.U (c q))
    (cov : ∀ z : Y, ∃ q, j z ∈ V q) (u : ∀ q, Γ(X, V q))
    (hu : ∀ q q' z, j z ∈ V q → j z ∈ V q' →
      gs j z _ (u q) = (gm j z _ (N.g (c q) (c q'))).val * gs j z _ (u q')) :
    ∃ τ₀ : LB.Sec N₀, ∀ q k' z, j z ∈ V q → z ∈ N₀.U k' →
      (gw w (𝟙 _) z (c q) k').val * gs (𝟙 _) z _ (τ₀.f k') = gs j z _ (u q) := by
  have tr : ∀ q q' k' l' z, j z ∈ V q → j z ∈ V q' → z ∈ N₀.U k' → z ∈ N₀.U l' →
      (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) =
        (gm (𝟙 _) z _ (N₀.g k' l')).val * ((gw w (𝟙 _) z (c q') l')⁻¹.val * gs j z _ (u q')) := by
    intro q q' k' l' z h h' hk hl
    have e := (isGen_iff w).1 hw _ (𝟙 Y) z (c q) (c q') k' l' (hc q h) (hc q' h') hk hl
    rw [Category.id_comp] at e
    rw [hu q q' z h h', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    congr 2
    generalize gm j z _ (N.g (c q) (c q')) = B
    generalize gm (𝟙 Y) z _ (N₀.g k' l') = C
    generalize gw w (𝟙 Y) z (c q') l' = D
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ k' : N₀.ι, ∃ s : Γ(Y, N₀.U k'), ∀ q z, j z ∈ V q → z ∈ N₀.U k' →
      gs (𝟙 _) z _ s = (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) := by
    intro k'
    let O : I → Y.Opens := fun q => j ⁻¹ᵁ V q ⊓ N₀.U k'
    have l₁ : ∀ q, O q ≤ (N.pull j).U (fun _ => c q) ⊓ N₀.U k' := fun q x hx =>
      ⟨mem_pull.2 (hc q hx.1), hx.2⟩
    obtain ⟨b, hb⟩ : ∃ b : ∀ q, Γ(Y, O q), ∀ q z, z ∈ O q →
        gs (𝟙 _) z (O q) (b q) = (gw w (𝟙 _) z (c q) k')⁻¹.val * gs j z _ (u q) :=
      ⟨fun q => rs Y (l₁ q) (w.s (fun _ => c q, k'))⁻¹.val *
          rs Y (inf_le_left : O q ≤ j ⁻¹ᵁ V q) ((j.app (V q)).hom (u q)), fun q z hz =>
        (gs_mul (𝟙 Y) z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_res (𝟙 Y) z _ hz _).trans ((gs_unit (𝟙 Y) z _ (l₁ q hz) _).trans
            (congrArg Units.val (map_inv _ _))))
          ((gs_res (𝟙 Y) z _ hz _).trans ((gs_pull (𝟙 Y) j z _ hz.1 _).trans
            (by rw [Category.id_comp]))))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' O (N₀.U k')
      (fun q => homOfLE inf_le_right) (fun z hz => by
        obtain ⟨q, hq⟩ := cov z
        exact Opens.mem_iSup.2 ⟨q, hq, hz⟩) b
      (fun q q' => fn_ext (V := O q ⊓ O q') fun z hz => by
        refine (gs_res (𝟙 Y) z inf_le_left hz _).trans
          (Eq.trans ?_ (gs_res (𝟙 Y) z inf_le_right hz _).symm)
        rw [hb q z hz.1, hb q' z hz.2, tr q q' k' k' z hz.1.1 hz.2.1 hz.1.2 hz.1.2,
          gm_self hN₀ (𝟙 Y) z hz.1.2, Units.val_one, _root_.one_mul])
    refine ⟨s, fun q z h₁ h₂ => ?_⟩
    have hz : z ∈ O q := ⟨h₁, h₂⟩
    exact (gs_res (𝟙 Y) z inf_le_right hz s).symm.trans
      ((congrArg (gs (𝟙 Y) z (O q)) (hs q)).trans (hb q z hz))
  choose s hs using glue
  refine ⟨⟨s, fun k' l' => fn_ext fun z hz => ?_⟩, fun q k' z h₁ h₂ => ?_⟩
  · obtain ⟨q, hq⟩ := cov z
    refine (gs_res (𝟙 Y) z _ hz _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 Y) z _ hz _) (gs_res (𝟙 Y) z _ hz _))).symm)
    rw [hs k' q z hq hz.1, hs l' q z hq hz.2]
    exact tr q q k' l' z hq hq hz.1 hz.2
  · change _ * gs (𝟙 Y) z _ (s k') = _
    rw [hs k' q z h₁ h₂, Units.mul_inv_cancel_left]
end GlobalTheory.SectionKernel
