-- Prove2me | solution 1 for KerrBL.pdchrKerr_all
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T10:09:19.189901+00:00
-- url     : https://prove2.me/submissions/c0c1bdd0-1421-4725-a554-609f8a9dcf66

import Definitions.Def_KerrBL_Kerr_ClosedForms
import Definitions.Def_KerrBL_Kerr_Metric
import Definitions.Def_KerrBL_CoordGeometry
import Theorems.Thm_KerrBL_hdchrKerr_all
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

namespace KerrBL

/-- `pd` from a `HasDerivAt` witness on the slice. -/
theorem pd_eq_of_hasDerivAt {f : Pt → ℝ} {x : Pt} {i : Fin 4} {d : ℝ}
    (h : HasDerivAt (fun u : ℝ => f (Function.update x i u)) d (x i)) : pd i f x = d :=
  h.deriv

end KerrBL

theorem solution (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    ∀ l i j k : Fin 4, pd l (christoffel (gKerr M a) (giKerr M a) i j k) x = dGammaKerr M a l i j k (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) :=
  fun l i j k => pd_eq_of_hasDerivAt (hdchrKerr_all M a x hx l i j k)
