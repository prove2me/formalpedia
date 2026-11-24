-- Prove2me | solution 1 for GlobalTheory.CycSpanFin.commute_aeval_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:12.158819+00:00
-- url     : https://prove2.me/submissions/12f595af-bc90-4e8a-a565-13b4d6bbd45d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CycSpanFin
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CycSpanFin
theorem _root_.solution {x y : Module.End ℂ V} (h : Commute x y) (p : ℂ[X]) : Commute (aeval x p) y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n a => rw [aeval_monomial]; exact (Algebra.commute_algebraMap_left a y).mul_left (h.pow_left n)
end GlobalTheory.CycSpanFin
