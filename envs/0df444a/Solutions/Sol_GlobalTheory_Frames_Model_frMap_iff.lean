-- Prove2me | solution 1 for GlobalTheory.Frames.Model.frMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:43:43.523198+00:00
-- url     : https://prove2.me/submissions/e643b652-23d3-4e53-ab18-fbcf3856e180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
import Theorems.Thm_GlobalTheory_Frames_Model_scal_one

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
theorem _root_.solution {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) : FrMap φ y z ↔ z.x = spMap φ.toRingHom ≫ y.x ∧
      (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧ SecBC φ.toRingHom 1 y.x z.x y.s z.s := by
  unfold FrMap SecBC
  refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun pm => and_congr_right fun _ =>
    and_congr_right fun _ => forall_congr' fun i => forall_congr' fun h => ?_
  rw [scal_one y.x i, _root_.one_mul]
end GlobalTheory.Frames.Model
