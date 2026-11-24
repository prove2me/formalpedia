-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.chE_chR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:48.872388+00:00
-- url     : https://prove2.me/submissions/df6c3eb6-f213-444b-a3b4-028810995349

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] {n d : ℕ}
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) (hy : y.1.1 0 ≠ 0) : chE (chR y) = y := by
  obtain ⟨⟨x, u⟩, W⟩ := y
  simp only at hy
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [chR, chE]
  · ext j; simp [chR, chE, hy]
  · ext i j; simp [chR, chE, hy]
end GlobalTheory.ThK.Dbl.LD
