-- Prove2me | solution 1 for GlobalTheory.FormalLog.formalGroupLaw_ev_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:56.763797+00:00
-- url     : https://prove2.me/submissions/9296106b-d541-42f1-9fee-e0bd08ccf453

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Theorems.Thm_GlobalTheory_FormalLog_cc_pt
import Theorems.Thm_GlobalTheory_FormalLog_cc_zero
import Theorems.Thm_GlobalTheory_FormalLog_CZ_nil
import Theorems.Thm_GlobalTheory_FormalLog_CZ_cons
import Theorems.Thm_GlobalTheory_FormalLog_pt_apply
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_ev_X
import Theorems.Thm_GlobalTheory_FormalLog_ev_ev


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
variable (G : FGLaw k d)
namespace GlobalTheory.FormalLog
theorem _root_.solution (i : Fin d) : ev (n := 1) ![pt k d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have hz : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt 0) (CZ.cons cc_zero CZ.nil)
  have hs : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)
  have h := congrArg (ev (n := 1) ![pt k d 0, 0]) (G.comm i)
  rw [ev_ev hz hs] at h
  have e : (fun j c => ev (n := 1) ![pt k d 0, 0] ((![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) j c)) =
      (![0, pt k (n := 1) d 0] : Fin 2 → Pt k 1 d) := by
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X hz]
  rw [e, G.unit] at h
  exact h.symm
end GlobalTheory.FormalLog
