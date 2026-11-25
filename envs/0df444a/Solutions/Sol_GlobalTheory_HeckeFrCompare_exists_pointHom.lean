-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.exists_pointHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:59:26.121232+00:00
-- url     : https://prove2.me/submissions/5e73dc3b-08b7-4b57-96eb-c00ae4dce1a1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_HeckeFrCompare_sends_unique
import Theorems.Thm_GlobalTheory_HeckeFrCompare_sends_iff
import Theorems.Thm_P2M_GlobalTheory_HeckeFrCompare_sends_sec__iff_a2b331f1cbb6
import Theorems.Thm_GlobalTheory_HeckeFrCompare_lift_act
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
variable {Ω : Type} [CommRing Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution (h : IsLinHom ψ) :
    ∃ ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G), (∀ a, Sends ψ a (ψp a)) ∧
      ∀ r a, ψp (a ≫ Xo.univ.t.act.act r) = ψp a ≫ Xo.univ.t.act.act r := by
  obtain ⟨h0, hm, ha⟩ := h
  let f : (Over.mk x ⟶ Xo.univ.t.G) → (Over.mk x' ⟶ Xo.univ.t.G) := fun a =>
    Over.homMk ((lift (𝟙 (Over.mk x)) a).left ≫ ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left) (by
      simp only [Category.assoc]
      rw [snd_hom, reassoc_of% h0, lift_l_fst_assoc]
      exact Category.id_comp _)
  have hf : ∀ a, Sends ψ a (f a) := fun a => (sends_iff h0 _ _).2 rfl
  let k : ∀ z : Sp Ω ⟶ Xo.X, (Over.mk (𝟙 _ ≫ z) : Over Xo.X) ⟶ Over.mk z := fun z => Over.homMk (𝟙 _) rfl
  have hk : ∀ a : Over.mk x ⟶ Xo.univ.t.G, sec' x (𝟙 _) (Category.id_comp _) ≫ k x ≫ a = a := fun a =>
    Over.OverMorphism.ext ((Category.id_comp _).trans (Category.id_comp _))
  have hs : ∀ a b, Sends ψ a b ↔ (k x' ≫ b).left = push ψ (𝟙 _) (k x ≫ a) := fun a b => by
    have := sends_sec'_iff h0 (𝟙 _) (Category.id_comp (𝟙 _)) (k x ≫ a) b
    rw [hk, Category.id_comp] at this
    rw [this, eq_comm]
    exact Iff.of_eq (congrArg (· = _) (Category.id_comp _).symm)
  refine ⟨MonoidHom.mk' f fun a b => sends_unique (hf _) ?_, hf, fun r a => sends_unique (hf _) ?_⟩
  · rw [hs, MonObj.comp_mul, MonObj.comp_mul]
    exact hm _ _ _ _ _ _ ((hs _ _).1 (hf a)) ((hs _ _).1 (hf b))
  · show Sends ψ _ (f a ≫ _)
    rw [Sends, lift_act, lift_act, Category.assoc, ha, ← Category.assoc, show _ ≫ ψ = _ from hf a]
end GlobalTheory.HeckeFrCompare
