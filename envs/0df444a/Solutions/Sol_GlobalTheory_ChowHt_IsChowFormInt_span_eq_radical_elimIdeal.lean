-- Prove2me | solution 1 for GlobalTheory.ChowHt.IsChowFormInt.span_eq_radical_elimIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:12:11.748802+00:00
-- url     : https://prove2.me/submissions/d236cb2c-316f-4379-a03e-6daed6890d30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_Chow_forall_aeval_eq_zero_iff


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
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}
open GlobalTheory.ChowHt.IsChowFormInt
variable {I : Ideal (MvPolynomial (Fin N) k)} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}
namespace GlobalTheory.ChowHt.IsChowFormInt
theorem _root_.solution (h : IsChowFormInt I e dl f)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    Ideal.span {f} = (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure k)]
  refine le_antisymm ?_ fun p hp => ?_
  · rw [Ideal.span_singleton_le_iff_mem]
    exact fun u hu => (h.zero_iff u).2 ((GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u).1 hu)
  · rw [Ideal.mem_span_singleton]
    exact h.dvd_of_forall_aeval_eq_zero fun u hu =>
      hp u ((GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u).2 ((h.zero_iff u).1 hu))
end GlobalTheory.ChowHt.IsChowFormInt
