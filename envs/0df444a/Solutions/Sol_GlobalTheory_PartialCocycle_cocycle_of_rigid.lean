-- Prove2me | solution 1 for GlobalTheory.PartialCocycle.cocycle_of_rigid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:26:13.188872+00:00
-- url     : https://prove2.me/submissions/95923c10-2a03-4514-b474-059b6a0a8d92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycle
import Theorems.Thm_GlobalTheory_PartialCocycle_gm_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.PartialCocycle
private theorem gm_res_eq_gm {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U)
    (hz : f z ∈ V) (u : Γ(X, U)ˣ) : gm f z V (res hle u) = gm f z U u := by
  have key : X.presheaf.map (homOfLE hle).op ≫ f.app V ≫ Z.presheaf.germ (f ⁻¹ᵁ V) z hz =
      f.app U ≫ Z.presheaf.germ (f ⁻¹ᵁ U) z (hle hz) := by
    rw [← Scheme.Hom.germ_stalkMap, ← Scheme.Hom.germ_stalkMap, ← Category.assoc, TopCat.Presheaf.germ_res]
  unfold gm
  rw [dif_pos hz, dif_pos (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map]
  unfold res pullU
  have h2 := congrArg (fun g => g.hom (u : Γ(X, U))) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2
private theorem algebraMap_OmS_eq_algebraMap_comp {G : Type*} [CommGroup G] (A B C s t u : G) :
    A * B⁻¹ * s * (B * C⁻¹ * t) * (A * C⁻¹ * u)⁻¹ = s * t * u⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
private theorem gm_val_eq_germ_app' {X Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) (U : X.Opens) (hz : g z ∈ U)
    (u : Γ(X, U)ˣ) : ((gm g z U u : Z.presheaf.stalk z)) = Z.presheaf.germ (g ⁻¹ᵁ U) z hz (g.app U u.val) := by
  unfold gm
  rw [dif_pos hz]
  rfl
private theorem gm_id_val_eq_germ' {X : Scheme.{0}} (z : X) (U : X.Opens) (hz : z ∈ U)
    (u : Γ(X, U)ˣ) : ((gm (𝟙 X) z U u : X.presheaf.stalk z)) = X.presheaf.germ U z hz u.val := by
  exact gm_val_eq_germ_app' (𝟙 X) z U hz u
end GlobalTheory.PartialCocycle
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.PartialCocycle
namespace GlobalTheory.PartialCocycle
theorem _root_.solution : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V₁ V₂ V₃ : S.Opens) (M₁ M₂ M₃ : LB X) (w₁₂ : LB.Iso M₂ M₁) (w₂₃ : LB.Iso M₃ M₂) (w₁₃ : LB.Iso M₃ M₁), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → ⨆ a, M₁.U a = p ⁻¹ᵁ V₁ → ⨆ a, M₂.U a = p ⁻¹ᵁ V₂ → ⨆ a, M₃.U a = p ⁻¹ᵁ V₃ → w₁₂.IsGen → w₂₃.IsGen → w₁₃.IsGen → (∀ (x : S) a b c, e x ∈ M₁.U a → e x ∈ M₂.U b → e x ∈ M₃.U c → gm e x (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm e x (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm e x (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c))) → ∀ (y : X) a b c, y ∈ M₁.U a → y ∈ M₂.U b → y ∈ M₃.U c → gm (𝟙 X) y (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm (𝟙 X) y (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm (𝟙 X) y (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c)) := by
  intro X S p e V₁ V₂ V₃ M₁ M₂ M₃ w₁₂ w₂₃ w₁₃ hep hrig hU₁ hU₂ hU₃ hg₁₂ hg₂₃ hg₁₃ hcoc y a b c hya hyb hyc
  let T : M₁.ι × M₂.ι × M₃.ι → X.Opens := fun i => M₁.U i.1 ⊓ M₂.U i.2.1 ⊓ M₃.U i.2.2
  have l₁ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₂.U i.2.1 := fun i => inf_le_left
  have l₂ : ∀ i, T i ≤ M₂.U i.2.1 ⊓ M₃.U i.2.2 := fun i => le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₃.U i.2.2 := fun i => le_inf (inf_le_left.trans inf_le_left) inf_le_right
  let t : ∀ i, Γ(X, T i)ˣ := fun i => res (l₁ i) (w₁₂.s (i.1, i.2.1)) * res (l₂ i) (w₂₃.s (i.2.1, i.2.2)) *
    (res (l₃ i) (w₁₃.s (i.1, i.2.2)))⁻¹
  have hprod : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i (hz : g z ∈ T i), gm g z (T i) (t i) =
      gm g z (M₁.U i.1 ⊓ M₂.U i.2.1) (w₁₂.s (i.1, i.2.1)) * gm g z (M₂.U i.2.1 ⊓ M₃.U i.2.2) (w₂₃.s (i.2.1, i.2.2)) *
        (gm g z (M₁.U i.1 ⊓ M₃.U i.2.2) (w₁₃.s (i.1, i.2.2)))⁻¹ := by
    intro Z g z i hz
    simp only [t, map_mul, map_inv]
    exact congrArg₂ _ (congrArg₂ _ (gm_res_eq_gm g z (l₁ i) hz _) (gm_res_eq_gm g z (l₂ i) hz _))
      (congrArg _ (gm_res_eq_gm g z (l₃ i) hz _))
  have hindep : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i j (hi : g z ∈ T i) (hj : g z ∈ T j),
      gm g z (T i) (t i) = gm g z (T j) (t j) := by
    intro Z g z i j hi hj
    rw [hprod g z i hi, hprod g z j hj]
    obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
    obtain ⟨⟨hj1, hj2⟩, hj3⟩ := hj
    rw [gm_iso hg₁₂ g z i.1 j.1 i.2.1 j.2.1 hi1 hj1 hi2 hj2, gm_iso hg₂₃ g z i.2.1 j.2.1 i.2.2 j.2.2 hi2 hj2 hi3 hj3,
      gm_iso hg₁₃ g z i.1 j.1 i.2.2 j.2.2 hi1 hj1 hi3 hj3]
    exact algebraMap_OmS_eq_algebraMap_comp _ _ _ _ _ _
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 T (fun i => (t i).val) := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf
    intro z hz
    show X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLELeft (T i) (T j)).op (t i).val) =
      X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLERight (T i) (T j)).op (t j).val)
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [← gm_id_val_eq_germ' z (T i) _ (t i), ← gm_id_val_eq_germ' z (T j) _ (t j)]
    exact congrArg Units.val (hindep (𝟙 X) z i j hz.1 hz.2)
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing T (fun i => (t i).val) hcompat
  have hcov : p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) ≤ iSup T := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have m1 : x ∈ ⨆ a, M₁.U a := by rw [hU₁]; exact h1
    have m2 : x ∈ ⨆ a, M₂.U a := by rw [hU₂]; exact h2
    have m3 : x ∈ ⨆ a, M₃.U a := by rw [hU₃]; exact h3
    obtain ⟨a₁, ha₁⟩ := TopologicalSpace.Opens.mem_iSup.1 m1
    obtain ⟨a₂, ha₂⟩ := TopologicalSpace.Opens.mem_iSup.1 m2
    obtain ⟨a₃, ha₃⟩ := TopologicalSpace.Opens.mem_iSup.1 m3
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a₁, a₂, a₃), ⟨⟨ha₁, ha₂⟩, ha₃⟩⟩
  have hV : V₁ ⊓ V₂ ⊓ V₃ ≤ e ⁻¹ᵁ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) := by
    intro x hx
    show (e ≫ p) x ∈ V₁ ⊓ V₂ ⊓ V₃
    rw [hep]
    exact hx
  let u : Γ(X, p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) := X.presheaf.map (homOfLE hcov).op s
  have hsT : ∀ i (z : X) (hz : z ∈ T i) (hz' : z ∈ iSup T),
      X.presheaf.germ (iSup T) z hz' s = X.presheaf.germ (T i) z hz (t i).val := by
    intro i z hz hz'
    have h := hs i
    dsimp only at h
    rw [← h]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (TopologicalSpace.Opens.leSupr T i) z hz s).symm
  have hu1 : (e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u = 1 := by
    apply TopCat.Presheaf.section_ext S.sheaf
    intro x hx
    have hex : e x ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) := hV hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov hex)
    show S.presheaf.germ _ x hx ((e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u) = S.presheaf.germ _ x hx 1
    rw [map_one]
    have k1 : e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV ≫ S.presheaf.germ _ x hx =
        X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (e x) hex ≫ e.stalkMap x := by
      rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    have k2 := congrArg (fun g => g.hom u) k1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k2
    rw [k2]
    have hg1 : gm e x (T i) (t i) = 1 := by
      rw [hprod e x i hi]
      obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
      rw [hcoc x i.1 i.2.1 i.2.2 hi1 hi2 hi3, mul_inv_cancel]
    rw [← Units.val_one, ← hg1, gm_val_eq_germ_app' e x (T i) hi]
    simp only [u]
    erw [TopCat.Presheaf.germ_res_apply, hsT i (e x) hi, Scheme.Hom.germ_stalkMap_apply]
  have hu : u = 1 := hrig _ u hV hu1
  have hyT : y ∈ T (a, b, c) := ⟨⟨hya, hyb⟩, hyc⟩
  have hyS : y ∈ iSup T := TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b, c), hyT⟩
  have fin : gm (𝟙 X) y (T (a, b, c)) (t (a, b, c)) = 1 := by
    apply Units.ext
    rw [gm_id_val_eq_germ' y _ hyT, Units.val_one, ← hsT (a, b, c) y hyT hyS]
    have hyV : y ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := (le_iSup M₁.U a) hya
        rw [hU₁] at this
        exact this
      · have := (le_iSup M₂.U b) hyb
        rw [hU₂] at this
        exact this
      · have := (le_iSup M₃.U c) hyc
        rw [hU₃] at this
        exact this
    have k3 := congrArg (X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) y hyV) hu
    simp only [u, map_one] at k3
    erw [TopCat.Presheaf.germ_res_apply] at k3
    exact k3
  rw [hprod (𝟙 X) y (a, b, c) hyT] at fin
  exact mul_inv_eq_one.1 fin
end GlobalTheory.PartialCocycle
