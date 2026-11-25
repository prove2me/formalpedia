-- Prove2me | solution 1 for GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:37.483201+00:00
-- url     : https://prove2.me/submissions/280f09f8-efee-4af3-8082-155ea5c5fb52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPolynomialFinrankHomogeneousSubmodule
import Theorems.Thm_GlobalTheory_natCard_degree_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
private lemma finite_setOf_finsupp_degree_eq (σ : Type) [Finite σ] [Nonempty σ] (e : ℕ) :
    Finite ↑{d : σ →₀ ℕ | d.degree = e} := by
  have := Fintype.ofFinite σ
  have h : Nat.card {d : σ →₀ ℕ // d.degree = e} ≠ 0 := by
    rw [_root_.GlobalTheory.natCard_degree_eq]
    have := Fintype.card_pos (α := σ)
    exact (Nat.choose_pos (by omega)).ne'
  exact Nat.finite_of_card_ne_zero h
private lemma finrank_homogeneousSubmodule_eq_choose (σ : Type) [Fintype σ] [Nonempty σ] (K : Type)
    [Field K] (e : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K e) =
      (e + Fintype.card σ - 1).choose e := by
  have := finite_setOf_finsupp_degree_eq σ e
  have := Fintype.ofFinite ↑{d : σ →₀ ℕ | d.degree = e}
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
      {d : σ →₀ ℕ | d.degree = e}).finrank_eq,
    ← _root_.GlobalTheory.natCard_degree_eq σ e, Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
  rfl
private lemma cast_choose_eq_eval_descPochhammer (m e : ℕ) (hm : 1 ≤ m) :
    (((e + m - 1).choose e : ℕ) : ℚ) = (Polynomial.C (1 / ((m - 1).factorial : ℚ)) *
      (descPochhammer ℚ (m - 1)).comp (Polynomial.X + Polynomial.C ((m - 1 : ℕ) : ℚ))).eval
        (e : ℚ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  have h1 : (e : ℚ) + ((m - 1 : ℕ) : ℚ) = ((e + (m - 1) : ℕ) : ℚ) := by push_cast; ring
  rw [h1, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    show e + m - 1 = e + (m - 1) by omega, Nat.choose_symm_add]
  have : ((m - 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (σ : Type) [Finite σ] [Nonempty σ], ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (e : ℕ),
      ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) : ℕ) : ℚ) =
        Q.eval (e : ℚ) := by
  intro σ _ _
  have := Fintype.ofFinite σ
  refine ⟨Polynomial.C (1 / ((Fintype.card σ - 1).factorial : ℚ)) *
    (descPochhammer ℚ (Fintype.card σ - 1)).comp
      (Polynomial.X + Polynomial.C ((Fintype.card σ - 1 : ℕ) : ℚ)), fun K _ e => ?_⟩
  rw [finrank_homogeneousSubmodule_eq_choose σ K e]
  exact cast_choose_eq_eval_descPochhammer _ e Fintype.card_pos
end _root_.GlobalTheory
end GlobalTheory
