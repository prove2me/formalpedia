-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction.LevAct.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:00:17.691836+00:00
-- url     : https://prove2.me/submissions/8ea0307d-5fce-48d5-89c7-c51af4196ee2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelPairAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction
namespace LevAct
theorem _root_.solution {gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La} (hM : CongM l gM' gM) (hA : CongN l.A gA' gA)
    {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : LevAct gM gA y y') : LevAct gM' gA' y y' := by
  obtain ⟨r, ν, w, ⟨h0, h1, h2⟩, h3⟩ := h
  refine ⟨r, ν, w, ⟨h0, fun a => ?_, fun a => ?_⟩, h3⟩
  · have e : Xo.univ.eta (gM' a) = Xo.univ.eta (gM a) := by
      rw [show gM' a = (gM' a - gM a) + gM a by abel, Xo.univ.eta_add, Xo.univ.eta_ker _ (hM a), _root_.one_mul]
    rw [e]; exact h1 a
  · obtain ⟨b, hb⟩ := hA a
    have e : Xo.univ.etaA (gA' a) = Xo.univ.etaA (gA a) := by
      rw [show gA' a = (gA' a - gA a) + gA a by abel, Xo.univ.etaA_add, hb, Xo.univ.etaA_ker, _root_.one_mul]
    rw [e]; exact h2 a
end LevAct
end GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction
