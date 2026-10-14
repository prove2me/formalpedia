-- Prove2me | solution 1 for KerrBL.pdgKerr_all
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T10:01:16.422755+00:00
-- url     : https://prove2.me/submissions/54fa12a7-9e2a-4d92-a2a5-3e26d1a70035

import Definitions.Def_KerrBL_Kerr_ClosedForms
import Definitions.Def_KerrBL_Kerr_Metric
import Definitions.Def_KerrBL_CoordGeometry
import Theorems.Thm_KerrBL_hdgKerr_all
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

/- All metric partial derivatives at once. -/
theorem solution (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    ∀ l i j : Fin 4, pd l (gKerr M a i j) x = dgKerr M a l i j (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) :=
  fun l i j => pd_eq_of_hasDerivAt (hdgKerr_all M a x hx l i j)
