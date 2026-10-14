-- Prove2me | solution 1 for KerrBL.vacuum_Kerr
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T10:11:39.004178+00:00
-- url     : https://prove2.me/submissions/2c9a61a3-2199-4d94-8df8-8c1e600513ab

import Definitions.Def_KerrBL_Kerr_ClosedForms
import Definitions.Def_KerrBL_Kerr_Metric
import Definitions.Def_KerrBL_CoordGeometry
import Theorems.Thm_KerrBL_ginv_mul_g_Kerr
import Theorems.Thm_KerrBL_hdchrKerr_all
import Theorems.Thm_KerrBL_hdgKerr_all
import Theorems.Thm_KerrBL_ricci_flat_Kerr
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

/- HEADLINE (self-contained): on the regular domain, (i) the candidate inverse is a left inverse,
(ii) every coordinate slice of the metric and of the generic Christoffel symbols is differentiable,
(iii) all 16 components of the generic coordinate Ricci tensor vanish. -/
theorem solution (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∀ i j : Fin 4, (∑ k : Fin 4, giKerr M a i k x * gKerr M a k j x) = (if i = j then 1 else 0)) ∧
    (∀ l i j : Fin 4, DifferentiableAt ℝ (fun u => gKerr M a i j (Function.update x l u)) (x l)) ∧
    (∀ l i j k : Fin 4, DifferentiableAt ℝ (fun u => christoffel (gKerr M a) (giKerr M a) i j k (Function.update x l u)) (x l)) ∧
    (∀ b d : Fin 4, ricciOf (gKerr M a) (giKerr M a) b d x = 0) :=
  ⟨ginv_mul_g_Kerr M a x hx, fun l i j => (hdgKerr_all M a x hx l i j).differentiableAt,
   fun l i j k => (hdchrKerr_all M a x hx l i j k).differentiableAt, ricci_flat_Kerr M a x hx⟩
