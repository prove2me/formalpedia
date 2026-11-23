-- Prove2me | solution 1 for GlobalTheory.FormalLog.CZ.cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:24.886122+00:00
-- url     : https://prove2.me/submissions/e6e23f80-52ea-4f71-83b8-e0ecc2063192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.FormalLog
namespace CZ
theorem _root_.solution {m n : ℕ} {p : Pt k n d} {a : Fin m → Pt k n d} (hp : ∀ i, constantCoeff (p i) = 0) (ha : CZ a) :
    CZ (Matrix.vecCons p a) := by
  intro j i
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa using hp i
  · simpa using ha j i
end CZ
end GlobalTheory.FormalLog
