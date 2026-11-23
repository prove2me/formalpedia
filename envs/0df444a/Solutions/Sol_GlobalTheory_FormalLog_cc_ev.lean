-- Prove2me | solution 1 for GlobalTheory.FormalLog.cc_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:29.294353+00:00
-- url     : https://prove2.me/submissions/066d5c6c-af05-4e79-bd5c-827592f53e38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_ev_ev
import Theorems.Thm_GlobalTheory_FormalLog_ev_zeroFam


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
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have hz : CZ (fun (_ : Fin n) (_ : Fin d) => (0 : PS k n d)) := fun _ _ => map_zero _
  have h1 := ev_zeroFam (n := n) (ev a f)
  rw [ev_ev hz ha] at h1
  have e : (fun j i => ev (fun (_ : Fin n) (_ : Fin d) => (0 : PS k n d)) (a j i)) =
      fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d) := by
    funext j i; rw [ev_zeroFam, ha j i, map_zero]
  rw [e, ev_zeroFam] at h1
  simpa using (congrArg constantCoeff h1).symm
end GlobalTheory.FormalLog
