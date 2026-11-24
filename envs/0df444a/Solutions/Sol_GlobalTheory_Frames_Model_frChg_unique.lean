-- Prove2me | solution 1 for GlobalTheory.Frames.Model.frChg_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:16:59.081796+00:00
-- url     : https://prove2.me/submissions/d73926ef-5cc9-46af-8d24-d897f018e665

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
import Theorems.Thm_GlobalTheory_Frames_Model_secBC_id_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
section Ring
variable {K : Type} [Field K] {J : Type} (m : J → ℕ) (R : Type) [CommRing R] [Algebra K R]
variable {m R}
end Ring
section Geo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
private theorem secBC_unique_of_secGen {S : Type} [CommRing S] (x x' : Sp S ⟶ Xo.X) (hx : x' = x) {a b : S}
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (ha : SecBC (RingHom.id S) a x x' s s')
    (hb : SecBC (RingHom.id S) b x x' s s') (hgen : SecGen x s) : a = b := by
  subst x'
  rw [secBC_id_iff] at ha hb
  exact (hgen s').unique ha hb
end Geo
end GlobalTheory.Frames.Model
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.Frames.Model
theorem _root_.solution {S : Type} [CommRing S] [Algebra c.F S]
    {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a a' : S} {y y' : FrPt Xo c S}
    (h : FrChg g a y y') (h' : FrChg g' a' y y') : g = g' ∧ a = a' := by
  unfold FrChg at h h'
  obtain ⟨hx, hu, hs⟩ := h
  obtain ⟨-, hu', hs'⟩ := h'
  refine ⟨funext fun τ => Matrix.ext fun i j => congrFun ((y.basis τ _ (by rw [← hx]; exact y'.tan τ i)
    (y'.eig τ i)).unique (hu τ i) (hu' τ i)) j, secBC_unique_of_secGen y.x y'.x hx y.s y'.s hs hs' y.gen⟩
end GlobalTheory.Frames.Model
