-- Prove2me | solution 1 for GlobalTheory.ChowHt.not_isChowForm_sq_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:04.656809+00:00
-- url     : https://prove2.me/submissions/3e208dc0-32b0-4522-8a4e-21c371196f1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_ChowHt_IsChowForm_isChowFormInt
import Theorems.Thm_GlobalTheory_Chow_IsBlockHomogeneous_unique
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
namespace GlobalTheory.ChowHt
theorem _root_.solution (δ : ℕ) (f : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ) :
    ¬ IsChowForm (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}) 0 δ f := by
  intro h
  obtain ⟨-, c, hc, rfl⟩ := isChowFormInt_sq_add_sq.unique h.isChowFormInt
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) two_pos
  have hz' : (C z : MvPolynomial (Fin (0 + 1) × Fin 2) (AlgebraicClosure ℚ)) ^ 2 = -1 := by
    rw [← map_pow, hz, map_neg, map_one]
  obtain ⟨φ, hi⟩ : ∃ φ : ℚ →+* AlgebraicClosure ℚ, Irreducible (MvPolynomial.map φ
      (C c * (X (0, 0) ^ 2 + X (0, 1) ^ 2) : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ)) := ⟨_, h.irred⟩
  have := hi.isUnit_or_isUnit
    (a := C (φ c) * (X (0, 0) + C z * X (0, 1))) (b := X (0, 0) - C z * X (0, 1)) (by
      simp only [map_mul, map_C, map_add, map_pow, map_X]
      linear_combination (C (φ c) * X (0, 1) ^ 2) * hz')
  rcases this with h1 | h1 <;> simpa using h1.map constantCoeff
end GlobalTheory.ChowHt
