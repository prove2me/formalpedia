-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.meromorphicAt_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:56.34458+00:00
-- url     : https://prove2.me/submissions/e5c44733-685a-4cb2-97a7-fe8404b69230

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {g : ℂ → ℂ} {x : ℂ} (hg : MeromorphicAt g x) (P : ℂ[X]) :
    MeromorphicAt (fun z ↦ P.eval (g z)) x := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval_add]; fun_prop
  | monomial n a => simp only [eval_monomial]; fun_prop
end GroundTheory.Global.Elliptic
