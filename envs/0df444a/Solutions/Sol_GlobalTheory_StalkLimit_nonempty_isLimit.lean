-- Prove2me | solution 1 for GlobalTheory.StalkLimit.nonempty_isLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:56:01.721207+00:00
-- url     : https://prove2.me/submissions/9f34ddb0-76d9-4522-9224-795a3179f344

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_StalkLimit_exists_lift_fromSpecStalk
import Theorems.Thm_P2M_GlobalTheory_StalkLimit_cone___fst_b63b7be6912f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.StalkLimit
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
variable {S X : Scheme.{u}} (x : S) (p : X ⟶ S)
variable {x p} {X' : Scheme.{u}} {φ : X' ⟶ X} {p' : X' ⟶ Spec (S.presheaf.stalk x)}
namespace GlobalTheory.StalkLimit
theorem _root_.solution (h : IsPullback φ p' p (S.fromSpecStalk x)) : Nonempty (IsLimit (cone h)) := by
  obtain ⟨V0⟩ : Nonempty (AffNhd x) := IsCofiltered.nonempty
  have hfst : ∀ (s : Cone (diagram x p)) (V W : AffNhd x),
      s.π.app V ≫ pullback.fst p V.1.ι = s.π.app W ≫ pullback.fst p W.1.ι := by
    intro s V W
    rw [← s.w (IsCofiltered.minToLeft V W), ← s.w (IsCofiltered.minToRight V W), Category.assoc,
      Category.assoc, diagram_map_fst, diagram_map_fst]
  have hin : ∀ (s : Cone (diagram x p)) (W : S.Opens), x ∈ W →
      ⊤ ≤ (s.π.app V0 ≫ pullback.fst p V0.1.ι ≫ p) ⁻¹ᵁ W := by
    intro s W hxW z _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
    have e : s.π.app V0 ≫ pullback.fst p V0.1.ι ≫ p =
        (s.π.app ⟨V, hxV, hV⟩ ≫ pullback.snd p (Scheme.Opens.ι V)) ≫ Scheme.Opens.ι V := by
      rw [← Category.assoc, hfst s V0 ⟨V, hxV, hV⟩, Category.assoc, Category.assoc,
        pullback.condition]
    change (s.π.app V0 ≫ pullback.fst p V0.1.ι ≫ p) z ∈ W
    rw [e, Scheme.Hom.comp_apply]
    exact hVW (Scheme.Opens.range_ι V ▸ Set.mem_range_self _)
  let L : ∀ s : Cone (diagram x p), s.pt ⟶ X' := fun s =>
    h.lift (s.π.app V0 ≫ pullback.fst p V0.1.ι) (exists_lift_fromSpecStalk x _ (hin s)).choose
      (by rw [(exists_lift_fromSpecStalk x _ (hin s)).choose_spec, Category.assoc])
  refine ⟨⟨L, fun s V => ?_, fun s m hm => ?_⟩⟩
  · dsimp only [L]
    apply pullback.hom_ext
    · rw [Category.assoc, cone_π_fst, h.lift_fst]
      exact hfst s V0 V
    · rw [← cancel_mono V.1.ι]
      simp only [Category.assoc, cone, pullback.lift_snd_assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
        h.lift_snd_assoc, (exists_lift_fromSpecStalk x _ (hin s)).choose_spec]
      rw [← pullback.condition]
      simp only [← Category.assoc, hfst s V0 V]
  · have e1 : m ≫ φ = s.π.app V0 ≫ pullback.fst p V0.1.ι := by
      rw [← hm V0, Category.assoc, cone_π_fst]
    dsimp only [L]
    apply h.hom_ext
    · rw [e1, h.lift_fst]
    · rw [← cancel_mono (S.fromSpecStalk x)]
      simp only [Category.assoc, ← h.w, reassoc_of% e1, h.lift_fst_assoc]
end GlobalTheory.StalkLimit
