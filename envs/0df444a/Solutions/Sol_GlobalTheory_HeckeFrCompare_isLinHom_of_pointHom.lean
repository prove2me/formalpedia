-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.isLinHom_of_pointHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:18:18.98433+00:00
-- url     : https://prove2.me/submissions/56465526-c5ba-4c5b-932d-586a25d147e2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_HeckeFrCompare_ext_of_points
import Theorems.Thm_GlobalTheory_HeckeFrCompare_gx_ext
import Theorems.Thm_GlobalTheory_HeckeFrCompare_sends_unique
import Theorems.Thm_GlobalTheory_HeckeFrCompare_push_hom
import Theorems.Thm_GlobalTheory_HeckeFrCompare_push_res
import Theorems.Thm_P2M_GlobalTheory_HeckeFrCompare_sends_sec__iff_a2b331f1cbb6
import Theorems.Thm_GlobalTheory_HeckeFrCompare_lift_act
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isReduced
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution
    (h0 : ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)) (hf : ∀ a, Sends ψ a (ψp a))
    (ha : ∀ r a, ψp (a ≫ Xo.univ.t.act.act r) = ψp a ≫ Xo.univ.t.act.act r) : IsLinHom ψ := by
  have := Xo.univ.t.semi.smooth
  have := Xo.univ.t.semi.separated
  refine ⟨h0, fun T t a₁ a₂ b₁ b₂ h₁ h₂ => ?_, fun r => ?_⟩
  · let G := Xo.univ.t.G
    let t₀ : (Over.mk x ⊗ (G ⊗ G)).left ⟶ Sp Ω := (fst (Over.mk x) (G ⊗ G)).left
    have : Smooth (G ⊗ G).hom := by
      show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
      infer_instance
    have : Smooth t₀ := by
      show Smooth (pullback.fst x (G ⊗ G).hom)
      infer_instance
    have : IsReduced (Over.mk x ⊗ (G ⊗ G)).left := GlobalTheory.isReduced_of_smooth_of_isReduced t₀
    let s₀ : (Over.mk (t₀ ≫ x) : Over Xo.X) ⟶ G ⊗ G :=
      Over.homMk (snd (Over.mk x) (G ⊗ G)).left
        ((Over.w (snd (Over.mk x) (G ⊗ G))).trans (Over.w (fst (Over.mk x) (G ⊗ G))).symm)
    let v : (Over.mk (t₀ ≫ x) ⟶ G) → (Over.mk (t₀ ≫ x') ⟶ G) := fun u =>
      Over.homMk (push ψ t₀ u) (push_hom h0 t₀ u)
    have key : ∀ u₁ u₂, (v u₁ * v u₂).left = push ψ t₀ (u₁ * u₂) := fun u₁ u₂ => by
      refine ext_of_points t₀ G.hom ((Over.w _).trans (push_hom h0 _ _).symm) fun q hq => ?_
      have e : ∀ u, sec' x' q hq ≫ v u = ψp (sec' x q hq ≫ u) := fun u =>
        sends_unique ((sends_sec'_iff h0 q hq u _).2 rfl) (hf _)
      rw [(sends_sec'_iff h0 q hq _ _).1 (hf _), MonObj.comp_mul, map_mul, ← e, ← e, ← MonObj.comp_mul]
      rfl
    let q : T ⟶ (Over.mk x ⊗ (G ⊗ G)).left :=
      (lift (Over.homMk t rfl : Over.mk (t ≫ x) ⟶ Over.mk x) (lift a₁ a₂)).left
    have hq : q ≫ t₀ = t := lift_l_fst _ _
    have hs : res x q hq ≫ s₀ = lift a₁ a₂ := Over.OverMorphism.ext (lift_l_snd _ _)
    have e₁ : a₁ = res x q hq ≫ s₀ ≫ fst G G := by rw [reassoc_of% hs, lift_fst]
    have e₂ : a₂ = res x q hq ≫ s₀ ≫ snd G G := by rw [reassoc_of% hs, lift_snd]
    have f₁ : b₁ = res x' q hq ≫ v (s₀ ≫ fst G G) :=
      Over.OverMorphism.ext (h₁.trans (by rw [e₁, push_res]; rfl))
    have f₂ : b₂ = res x' q hq ≫ v (s₀ ≫ snd G G) :=
      Over.OverMorphism.ext (h₂.trans (by rw [e₂, push_res]; rfl))
    rw [e₁, e₂, f₁, f₂, ← MonObj.comp_mul, ← MonObj.comp_mul, push_res, ← key]
    rfl
  · have : Smooth (fst (Over.mk x) Xo.univ.t.G).left := by
      show Smooth (pullback.fst x Xo.univ.t.G.hom)
      infer_instance
    have : IsSeparated (fst (Over.mk x') Xo.univ.t.G).left := by
      show IsSeparated (pullback.fst x' Xo.univ.t.G.hom)
      infer_instance
    have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Sp Ω))
    have : IsReduced (Gx x) := GlobalTheory.isReduced_of_smooth_of_isReduced (fst (Over.mk x) Xo.univ.t.G).left
    have hw : ∀ z : Sp Ω ⟶ Xo.X, (Over.mk z ◁ Xo.univ.t.act.act r).left ≫ (fst (Over.mk z) Xo.univ.t.G).left =
        (fst (Over.mk z) Xo.univ.t.G).left := fun z => by rw [← Over.comp_left, whiskerLeft_fst]
    refine ext_of_points (fst (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x') Xo.univ.t.G).left
      (by rw [Category.assoc, Category.assoc, h0, hw, hw, h0]) fun q hq => ?_
    let a : Over.mk x ⟶ Xo.univ.t.G := Over.homMk (q ≫ (snd (Over.mk x) Xo.univ.t.G).left) (by
      rw [Category.assoc, snd_hom, reassoc_of% hq]; rfl)
    have e : q = (lift (𝟙 (Over.mk x)) a).left := by
      refine gx_ext ?_ ?_
      · rw [hq, lift_l_fst]; rfl
      · rw [lift_l_snd]; rfl
    have s₁ := hf (a ≫ Xo.univ.t.act.act r)
    rw [ha, Sends, lift_act, lift_act, ← show _ ≫ ψ = _ from hf a] at s₁
    rw [e]
    simpa only [Category.assoc] using s₁
end GlobalTheory.HeckeFrCompare
