-- Prove2me | solution 1 for GlobalTheory.SimAlg.form_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:34.959679+00:00
-- url     : https://prove2.me/submissions/1a86791b-0a83-42f5-b4c2-021aab9be105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
import Theorems.Thm_GlobalTheory_SimAlg_form_pow

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
theorem _root_.solution (g : ℕ → ℕ → ℤ) (d : ℕ) (f h : ℂ[X]) (hf : f.natDegree < d) (hh : h.natDegree < d) :
    form g f h = ∑ i : Fin d, ∑ j : Fin d, f.coeff i * h.coeff j * (g i j : ℂ) := by
  conv_lhs => rw [f.as_sum_range' d hf, h.as_sum_range' d hh]
  simp only [Finset.sum_range, ← smul_X_eq_monomial, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, form_pow, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.SimAlg
