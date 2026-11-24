-- Prove2me | solution 1 for GlobalTheory.FormalMulN.ev_add_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:59:52.82291+00:00
-- url     : https://prove2.me/submissions/fbd4f49c-61c7-41fb-9d7e-a596ae54d185

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_ev_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalMulN
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ} (G : FGLaw R d)
namespace GlobalTheory.FormalMulN
theorem _root_.solution {x y : Pt R m d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) {b : Fin m → Pt R n d}
    (hb : ∀ j i, constantCoeff (b j i) = 0) :
    (fun i => ev b (G.add x y i)) = G.add (fun i => ev b (x i)) (fun i => ev b (y i)) := by
  funext i
  exact ev_ev_two hx hy hb (G.F i)
end GlobalTheory.FormalMulN
