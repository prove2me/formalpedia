-- Prove2me | solution 1 for GlobalTheory.Frames.Model.OpenChart.eq_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:51:30.845139+00:00
-- url     : https://prove2.me/submissions/07c887a5-8879-41ae-957b-4c63c3d81ccf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.Frames.Model
namespace OpenChart
theorem _root_.solution {R : Type} [CommRing R] [Algebra c.F R] {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R}
    (h : OpenChart j y₀) :
    j = pullback.lift y₀.x (spMap (algebraMap c.F R)) (by rw [y₀.x_over, sOf]; simp [spMap]) := by
  obtain ⟨-, h₁, h₂⟩ := h
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact h₁
  · rw [pullback.lift_snd]
    exact h₂
end OpenChart
end GlobalTheory.Frames.Model
