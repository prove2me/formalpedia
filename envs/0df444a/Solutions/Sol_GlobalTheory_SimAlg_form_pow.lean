-- Prove2me | solution 1 for GlobalTheory.SimAlg.form_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:02.970925+00:00
-- url     : https://prove2.me/submissions/9b79c952-f8cd-4b5c-abdf-fc3b6655001a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg
namespace GlobalTheory.SimAlg
theorem _root_.solution (g : ℕ → ℕ → ℤ) (i j : ℕ) : form g (X ^ i) (X ^ j) = g i j := by
  have h : ∀ k, (X ^ k : ℂ[X]) = basisMonomials ℂ k := fun k => by
    simp [monomial_one_right_eq_X_pow]
  rw [form, h, h, Module.Basis.constr_basis, Module.Basis.constr_basis]
end GlobalTheory.SimAlg
