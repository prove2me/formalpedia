-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.exists_framed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:20.094619+00:00
-- url     : https://prove2.me/submissions/fa973b13-669b-4dea-8ed9-daae292592a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_FramedFlatCoordinates
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FramedFlatCoordinates_lieMult_iff
import Theorems.Thm_GlobalTheory_LiePull_lieMult_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates
theorem _root_.solution (Y : Model Xo c β) (Xc : (Xo.XF c).Opens) (τ : E →+* ℂ)
    (hτ : τ (H.rt : E) = H.rt0) (k : Type) [Field k] [IsAlgClosed k] (j : c.F →+* k)
    (y : Sp k ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap j)
    (hm : Set.range y ⊆ (Xc : Set (Xo.XF c))) :
    ∃ a : Framed Y Xc τ k j, a.x = y ≫ Y.jQ := by
  obtain ⟨hd, -⟩ := Y.oF.geom k y (j.comp (IntermediateField.inclusion c.le).toRingHom) (by
    rw [pullback.condition, ← Category.assoc, hy]
    exact (Spec.map_comp _ _).symm)
  have h1 : chr c τ j H.rt = (j.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ :=
    congrArg j (Subtype.ext hτ)
  have h2 : chr c (conjEmb τ) j H.rt ≠
      (j.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ := fun h => by
    have h3 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := congrArg Subtype.val (j.injective h)
    rw [hτ] at h3
    have h4 := H.sqrt_neg_disc_sq
    have h5 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h3
    have h6 := congrArg Complex.re h4
    have h7 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
    simp [pow_two, h5] at h6
    nlinarith [mul_self_nonneg H.rt0.re]
  have hv := (LiePull.lieMult_pull _ _ _ _ _ _ _ Y.t.act Y.oF.t.act Y.m.cart Y.m.act _ y _ _).1
    ((hd _).1 h1)
  have hw := (LiePull.lieMult_pull _ _ _ _ _ _ _ Y.t.act Y.oF.t.act Y.m.cart Y.m.act _ y _ _).1
    ((hd _).2 h2)
  rw [← Category.assoc, lieMult_iff] at hv hw
  obtain ⟨v, hv⟩ := hv
  obtain ⟨w, hw⟩ := hw
  refine ⟨⟨y ≫ Y.jQ, by rw [Category.assoc, Y.jQ_over, hy], ?_, v, w, hv, hw⟩, rfl⟩
  rintro _ ⟨z, rfl⟩
  exact subset_closure ⟨y z, hm ⟨z, rfl⟩, by simp⟩
end GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates
