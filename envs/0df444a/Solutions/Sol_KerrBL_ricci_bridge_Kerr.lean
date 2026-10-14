-- Prove2me | solution 1 for KerrBL.ricci_bridge_Kerr
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T10:10:02.647295+00:00
-- url     : https://prove2.me/submissions/98902183-69ec-4aa0-a627-a28b28cea3f2

import Definitions.Def_KerrBL_Kerr_ClosedForms
import Definitions.Def_KerrBL_Kerr_Metric
import Definitions.Def_KerrBL_CoordGeometry
import Theorems.Thm_KerrBL_chrKerr_all
import Theorems.Thm_KerrBL_pdchrKerr_all
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Constructions
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open KerrBL Filter Topology

/- Layer II bridge: the generic derivative-based Ricci tensor of the Kerr metric equals the
explicit closed-form expression, on the regular domain. -/
theorem solution (M a : ℝ) (x : Pt) (hx : RegKerr M a x) (b d : Fin 4) :
    ricciOf (gKerr M a) (giKerr M a) b d x = RicciKerr M a b d (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) := by
  have h1 := pdchrKerr_all M a x hx
  have h2 := chrKerr_all M a x hx
  unfold ricciOf ricci RicciKerr
  simp only [h1, h2, GammaKerrpt]
