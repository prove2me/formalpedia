-- Prove2me | solution 1 for GlobalTheory.Frames.Model.exists_frChg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:58.185542+00:00
-- url     : https://prove2.me/submissions/c002b0e8-cfe4-4566-b1a8-3a5809b8ab44

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
private theorem exists_secBC_of_secGen {S : Type} [CommRing S] (x x' : Sp S ⟶ Xo.X) (hx : x' = x)
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (hgen : SecGen x s) :
    ∃ a, SecBC (RingHom.id S) a x x' s s' := by
  subst x'
  obtain ⟨a, ha, -⟩ := hgen s'
  exact ⟨a, (secBC_id_iff x a s s').2 ha⟩
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
theorem _root_.solution {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (h : y'.x = y.x) :
    ∃ g a, FrChg g a y y' := by
  choose g hg using fun τ i => (y.basis τ (y'.u τ i) (by rw [← h]; exact y'.tan τ i) (y'.eig τ i)).exists
  obtain ⟨a, ha⟩ := exists_secBC_of_secGen y.x y'.x h y.s y'.s y.gen
  refine ⟨fun τ => Matrix.of (g τ), a, ?_⟩
  unfold FrChg
  exact ⟨h, fun τ i => hg τ i, ha⟩
end GlobalTheory.Frames.Model
