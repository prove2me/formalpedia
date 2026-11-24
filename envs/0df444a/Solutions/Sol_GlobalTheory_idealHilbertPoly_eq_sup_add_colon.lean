-- Prove2me | solution 1 for GlobalTheory.idealHilbertPoly_eq_sup_add_colon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:29.385173+00:00
-- url     : https://prove2.me/submissions/22286a3b-2f7e-4db6-873e-56cba78c6139

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_isHomogeneous_sup_span_singleton
import Theorems.Thm_GlobalTheory_isHomogeneous_colon_singleton
import Theorems.Thm_GlobalTheory_finrank_quotPiece_sup_add_colon
import Theorems.Thm_GlobalTheory_eventually_finrank_quotPiece
import Theorems.Thm_GlobalTheory_polynomial_eq_of_eventually_eval_nat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
variable [Finite ι]
namespace GlobalTheory
theorem _root_.solution {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    idealHilbertPoly I = idealHilbertPoly (I ⊔ Ideal.span {f}) +
      (idealHilbertPoly (Submodule.colon I {f})).comp (Polynomial.X - Polynomial.C (d : ℚ)) := by
  apply polynomial_eq_of_eventually_eval_nat
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_finrank_quotPiece (isHomogeneous_colon_singleton hI hf))
  filter_upwards [eventually_finrank_quotPiece hI,
    eventually_finrank_quotPiece (isHomogeneous_sup_span_singleton hI hf),
    eventually_ge_atTop (N + d)] with n h1 h2 h3
  obtain ⟨n, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
  rw [Polynomial.eval_add, ← h1, ← h2, ← finrank_quotPiece_sup_add_colon hI hf n, Nat.cast_add,
    hN n (by omega)]
  simp
end GlobalTheory
