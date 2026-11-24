-- Prove2me | solution 1 for GlobalTheory.ChowHt.IsChowFormInt.zero_iff_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:28:00.025567+00:00
-- url     : https://prove2.me/submissions/6b18517b-31e6-4641-8d34-0fd8ecf1f5d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_ChowHt_IsChowFormInt_span_eq_radical_elimIdeal
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
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k))
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] (u : Fin (e + 1) × Fin N → Ω) :
    MvPolynomial.aeval u f = 0 ↔
      ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
        ∀ i, ∑ j, u (i, j) * y j = 0 := by
  rw [← GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u]
  have hs := h.span_eq_radical_elimIdeal hI
  refine ⟨fun hu p hp => ?_, fun hu => ?_⟩
  · have : p ∈ Ideal.span {f} := hs ▸ Ideal.le_radical hp
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 this
    rw [map_mul, hu, mul_zero]
  · have : f ∈ (GlobalTheory.Chow.elimIdeal (Fin (e + 1)) I).radical := hs ▸ Ideal.subset_span rfl
    obtain ⟨n, hn⟩ := this
    have := hu _ hn
    rw [map_pow] at this
    exact eq_zero_of_pow_eq_zero this
end GlobalTheory.ChowHt.IsChowFormInt
