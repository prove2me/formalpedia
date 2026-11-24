-- Prove2me | solution 1 for GlobalTheory.Frames.Model.FrChg.isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:17:04.931077+00:00
-- url     : https://prove2.me/submissions/dc0d3672-ef91-486e-b07d-a69e958614e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
import Theorems.Thm_GlobalTheory_Frames_Model_scal_one
import Theorems.Thm_GlobalTheory_Frames_Model_secBC_id_iff
import Theorems.Thm_GlobalTheory_Frames_Model_scal_mul
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
private theorem isUnit_of_secBC_of_secGen {S : Type} [CommRing S] (x x' : Sp S ⟶ Xo.X) (hx : x' = x) {a : S}
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (hs : SecBC (RingHom.id S) a x x' s s')
    (hgen : SecGen x s) (hgen' : SecGen x' s') : IsUnit a := by
  subst x'
  rw [secBC_id_iff] at hs
  obtain ⟨b, hb, -⟩ := hgen' s
  have h₁ : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
    calc s.f i = scal x b i * s'.f i := hb i
      _ = scal x b i * (scal x a i * s.f i) := by rw [hs i]
      _ = scal x (b * a) i * s.f i := by rw [scal_mul, _root_.mul_assoc]
  have h₂ : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one, _root_.one_mul]
  exact IsUnit.of_mul_eq_one_right b ((hgen s).unique h₁ h₂)
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
namespace FrChg
theorem _root_.solution {S : Type} [CommRing S] [Algebra c.F S]
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a : S} {y y' : FrPt Xo c S}
    (h : FrChg g a y y') : IsUnit a := by
  unfold FrChg at h
  exact isUnit_of_secBC_of_secGen y.x y'.x h.1 y.s y'.s h.2.2 y.gen y'.gen
end FrChg
end GlobalTheory.Frames.Model
