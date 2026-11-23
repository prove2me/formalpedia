-- Prove2me | solution 1 for GlobalTheory.Frames.Model.frBor_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:26.140567+00:00
-- url     : https://prove2.me/submissions/6d806d19-d6d0-4e74-b78c-8f07a7794876

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
import Theorems.Thm_GlobalTheory_Frames_Model_spMap_id

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
theorem _root_.solution {S : Type} [CommRing S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) :
    FrBor t y y' ↔ ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S,
      (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ (∀ τ i j, i < j → g τ i j = 0) ∧ FrChg g (t none : S) y y' := by
  unfold FrBor FrChg SecBC
  simp only [spMap_id]
  constructor
  · rintro ⟨hx, hu, hs⟩
    choose cf hcf using hu
    exact ⟨fun τ => Matrix.of (cf τ), fun τ i => (hcf τ i).1, fun τ i j hij => (hcf τ i).2.1 j hij, hx,
      fun τ i => (hcf τ i).2.2, hs⟩
  · rintro ⟨g, hd, hl, hx, hu, hs⟩
    exact ⟨hx, fun τ i => ⟨g τ i, hd τ i, fun j hij => hl τ i j hij, hu τ i⟩, hs⟩
end GlobalTheory.Frames.Model
