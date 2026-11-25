-- Prove2me | solution 1 for GlobalTheory.ChowHt.IsChowFormInt.span_eq_elimIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:47.817617+00:00
-- url     : https://prove2.me/submissions/30469c5c-9b00-460d-b2ed-89f3474bd28c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_ChowHt_IsChowFormInt_span_eq_radical_elimIdeal
import Theorems.Thm_GlobalTheory_Chow_isPrime_elimIdeal
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



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
theorem _root_.solution (h : IsChowFormInt I e dl f) (hp : I.IsPrime)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    Ideal.span {f} = GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I := by
  obtain ⟨y, hy, hyI⟩ := h.exists_point
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have : (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).IsPrime :=
    GlobalTheory.Chow.isPrime_elimIdeal ⟨j, fun hX => hj (by simpa using hyI _ hX)⟩
  rw [h.span_eq_radical_elimIdeal hI, this.radical]
end GlobalTheory.ChowHt.IsChowFormInt
