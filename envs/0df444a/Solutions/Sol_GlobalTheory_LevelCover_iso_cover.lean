-- Prove2me | solution 1 for GlobalTheory.LevelCover.iso_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:40:28.495656+00:00
-- url     : https://prove2.me/submissions/46637347-a518-4609-a050-025955701fdd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective
import Theorems.Thm_GlobalTheory_LevelCover_sab_comp
import Theorems.Thm_GlobalTheory_LevelCover_sab_cancel
import Theorems.Thm_GlobalTheory_LevelCover_sec_cancel
import Theorems.Thm_GlobalTheory_LevelCover_sec_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevelCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l l₂ : Level H}
namespace GlobalTheory.LevelCover
theorem _root_.solution (hC : ObjCompSt) {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} (k k' : ℕ)
    {X X₂ Y : Scheme.{0}} {s : X ⟶ Sp B} {r : X₂ ⟶ X} {π : Y ⟶ X} (o : Obj D l b s) (o₂ : Obj D l₂ b₂ (r ≫ s))
    (oc : Obj D l₂ b₂ (π ≫ s)) (o₁ : Obj D l b (π ≫ s)) (n : ObjMap o₁ o π)
    (m : SABMap o₂.t o.t r) (mc : SABMap oc.t o.t π)
    (hm : (∀ a, (o₂.eta a ^ k).left ≫ m.φ = r ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ k').left ≫ m.φ = r ≫ (o.etaA a).left))
    (hmc : (∀ a, (oc.eta a ^ k).left ≫ mc.φ = π ≫ (o.eta a).left) ∧
      (∀ a, (oc.etaA a ^ k').left ≫ mc.φ = π ≫ (o.etaA a).left))
    (hX : Represents o) (hX₂ : Represents o₂) (rX₂ : IsReduced X₂) (rY : IsReduced Y)
    (rig : ∀ m m' : SABMap o₁.t o.t π, (∀ a, ∃ σ, (o₁.eta a).left ≫ m.φ = σ ∧ (o₁.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (univ : ∀ (T : Scheme.{0}) (f : T ⟶ X) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f),
      (∀ a, (o'.eta a ^ k).left ≫ m'.φ = f ≫ (o.eta a).left) ∧
        (∀ a, (o'.etaA a ^ k').left ≫ m'.φ = f ≫ (o.etaA a).left) →
      ∃! h : T ⟶ Y, h ≫ π = f ∧ ∃ u : ObjMap o' oc h, u.toSABMap.φ ≫ mc.φ = m'.φ) :
    ∃ h : X₂ ⟶ Y, IsIso h ∧ h ≫ π = r := by
  obtain ⟨h, ⟨hh, u, hu⟩, -⟩ := univ X₂ r o₂ m hm
  obtain ⟨g, ⟨hg, ⟨w⟩⟩, -⟩ := hX₂ Y (π ≫ s) oc rY
  obtain ⟨v, hv⟩ := sab_cancel mc n.toSABMap (𝟙 Y) (Category.id_comp _)
  have v₁ : ∀ a, (o₁.eta a).left ≫ v.φ = (oc.eta a ^ k).left := fun a =>
    (sec_cancel v mc _ _ (by rw [hv, hmc.1, Category.id_comp]; exact n.eta a)).trans (Category.id_comp _)
  have v₂ : ∀ a, (o₁.etaA a).left ≫ v.φ = (oc.etaA a ^ k').left := fun a =>
    (sec_cancel v mc _ _ (by rw [hv, hmc.2, Category.id_comp]; exact n.etaA a)).trans (Category.id_comp _)
  obtain ⟨vw, hvw⟩ := sab_comp v w.toSABMap (Category.id_comp g)
  have key : ∀ (e : Y ⟶ X) (he : g ≫ r = e), ∃ z : ObjMap o₁ o e, z.toSABMap.φ = v.φ ≫ w.toSABMap.φ ≫ m.φ := by
    intro e he
    obtain ⟨z, hz⟩ := sab_comp vw m he
    rw [hvw, Category.assoc] at hz
    refine ⟨⟨z, fun a => ?_, fun a => ?_⟩, hz⟩
    · show _ ≫ z.φ = _
      rw [hz, ← Category.assoc, v₁, ← Category.assoc, sec_pow w.toSABMap _ _ (w.eta a), Category.assoc, hm.1,
        ← Category.assoc, he]
    · show _ ≫ z.φ = _
      rw [hz, ← Category.assoc, v₂, ← Category.assoc, sec_pow w.toSABMap _ _ (w.etaA a), Category.assoc, hm.2,
        ← Category.assoc, he]
  have hgr : g ≫ r = π := by
    obtain ⟨z, -⟩ := key _ rfl
    exact (hX Y (π ≫ s) o₁ rY).unique ⟨by rw [Category.assoc, hg], ⟨z⟩⟩ ⟨rfl, ⟨n⟩⟩
  obtain ⟨z, hz⟩ := key _ hgr
  have hzn : z.toSABMap.φ = n.toSABMap.φ := rig _ _ fun a => ⟨_, z.eta a, n.eta a⟩
  have : IsIso v.φ := v.cart.1.isIso_fst_of_isIso
  have hwm : w.toSABMap.φ ≫ m.φ = mc.φ := by
    rw [← cancel_epi v.φ, ← hz, hzn, hv]
  refine ⟨h, ⟨g, ?_, ?_⟩, hh⟩
  · obtain ⟨x, -⟩ := ((hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ o₂ oc o₂).2 g h w).1 u
    obtain ⟨y, -⟩ := (hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ o₂ o₂ o₂).1
    exact (hX₂ X₂ (r ≫ s) o₂ rX₂).unique
      ⟨by rw [Category.assoc, hg, ← Category.assoc, hh], ⟨x⟩⟩ ⟨Category.id_comp _, ⟨y⟩⟩
  · obtain ⟨x, hx⟩ := ((hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ oc o₂ oc).2 h g u).1 w
    obtain ⟨y, hy⟩ := (hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ oc oc oc).1
    exact (univ Y π oc mc hmc).unique
      ⟨by rw [Category.assoc, hh, hgr], x, by rw [hx, Category.assoc, hu, hwm]⟩
      ⟨Category.id_comp _, y, by rw [hy, Category.id_comp]⟩
end GlobalTheory.LevelCover
