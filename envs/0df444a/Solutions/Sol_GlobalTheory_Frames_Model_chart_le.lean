-- Prove2me | solution 1 for GlobalTheory.Frames.Model.chart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:52:12.769209+00:00
-- url     : https://prove2.me/submissions/a27d16c1-a392-426a-8faf-341557754ddd

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
theorem _root_.solution {S T : Type} [CommRing S] [CommRing T] (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (pm : Gx x' ⟶ Gx x)
    (h : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : p ∈ ⋂ k, ⇑(snd (Over.mk x') Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) := hp
  have e : ∀ q, (snd (Over.mk x) Xo.univ.t.G).left (pm q) = (snd (Over.mk x') Xo.univ.t.G).left q := fun q => by
    rw [← h]
    rfl
  show pm p ∈ ⋂ k, ⇑(snd (Over.mk x) Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  rw [Set.mem_preimage, e]
  exact Set.mem_iInter.1 hp' k
end GlobalTheory.Frames.Model
