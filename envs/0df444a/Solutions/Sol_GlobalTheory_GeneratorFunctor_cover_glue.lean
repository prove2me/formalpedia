-- Prove2me | solution 1 for GlobalTheory.GeneratorFunctor.cover_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:37.864266+00:00
-- url     : https://prove2.me/submissions/52bf1993-d8e2-4f9d-a820-f0e5d88df800

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
import Theorems.Thm_P2M_GlobalTheory_GeneratorFunctor_pb___injective_9545ad52f383

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
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GeneratorFunctor
theorem _root_.solution {Y : Scheme.{0}} (𝒰 : Y.OpenCover) (V : Y.Opens)
    (t : ∀ i, Γ(𝒰.X i, 𝒰.f i ⁻¹ᵁ V)ˣ)
    (ht : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ 𝒰.X i) (a' : Z ⟶ 𝒰.X j), a ≫ 𝒰.f i = a' ≫ 𝒰.f j →
      ∀ h h', pb a _ ⊤ h (t i) = pb a' _ ⊤ h' (t j)) :
    ∃ s : Γ(Y, V)ˣ, ∀ i, pb (𝒰.f i) V _ le_rfl s = t i := by
  let W : 𝒰.I₀ → Y.Opens := fun i => 𝒰.f i ''ᵁ (𝒰.f i ⁻¹ᵁ V)
  have hW : ∀ i, W i ≤ V := fun i => (𝒰.f i).image_preimage_le V
  have hW' : ∀ i, 𝒰.f i ⁻¹ᵁ V ≤ 𝒰.f i ⁻¹ᵁ W i := fun i =>
    ((𝒰.f i).preimage_image_eq _).ge
  have hc : V ≤ iSup W := fun y hy => by
    obtain ⟨i, z, rfl⟩ := 𝒰.exists_eq y
    exact Opens.mem_iSup.2 ⟨i, z, hy, rfl⟩
  have hu : ∀ i, ∃ u : Γ(Y, W i)ˣ, pb (𝒰.f i) _ _ (hW' i) u = t i := fun i => by
    refine ⟨Units.map ((𝒰.f i).appIso _).inv.hom.toMonoidHom (t i), ?_⟩
    ext
    rw [pb_val]
    change (((𝒰.f i).appIso _).inv ≫ (𝒰.f i).appLE _ _ _).hom _ = _
    rw [Scheme.Hom.appIso_inv_appLE]
    change ((𝒰.X i).presheaf.map (𝟙 _)).hom _ = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  choose u hu using hu
  have hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j) := by
    intro i j
    apply pb_ι_injective _ (by simp)
    let a := IsOpenImmersion.lift (𝒰.f i) (W i ⊓ W j).ι (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, -, hz⟩ := y.2.1
      exact ⟨z, hz⟩)
    let a' := IsOpenImmersion.lift (𝒰.f j) (W i ⊓ W j).ι (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, -, hz⟩ := y.2.2
      exact ⟨z, hz⟩)
    have ha : a ≫ 𝒰.f i = (W i ⊓ W j).ι := IsOpenImmersion.lift_fac _ _ _
    have ha' : a' ≫ 𝒰.f j = (W i ⊓ W j).ι := IsOpenImmersion.lift_fac _ _ _
    have h0 : ⊤ ≤ (W i ⊓ W j).ι ⁻¹ᵁ V := fun y _ => hW i y.2.1
    have := ht i j _ a a' (ha.trans ha'.symm) (by rw [← ha] at h0; exact h0)
      (by rw [← ha'] at h0; exact h0)
    rw [← hu i, ← hu j, pb_pb, pb_pb, pb_congr ha, pb_congr ha'] at this
    rw [res_eq_pb, res_eq_pb, pb_comp_id, pb_comp_id, this]
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (u i).val) (fun i j => congrArg Units.val (hh i j))
  obtain ⟨s', hs', -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i)⁻¹).val)
    (fun i j => congrArg Units.val
      (show res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ = res inf_le_right (u j)⁻¹ by
        rw [map_inv, map_inv, hh]))
  have e : (show Γ(Y, V) from s) * (show Γ(Y, V) from s') = 1 := by
    apply Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    change (Y.presheaf.map (homOfLE (hW i)).op).hom _ = (Y.presheaf.map (homOfLE (hW i)).op).hom _
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (hs i) (hs' i)).trans (u i).mul_inv
  refine ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, fun i => ?_⟩
  have : res (hW i) (⟨s, s', e, (mul_comm _ _).trans e⟩ : Γ(Y, V)ˣ) = u i := Units.ext (hs i)
  rw [← hu i, ← this, res_eq_pb, pb_comp_id]
end GlobalTheory.GeneratorFunctor
