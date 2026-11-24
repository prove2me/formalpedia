-- Prove2me | solution 1 for GlobalTheory.PolyNorm.ev_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:10.195744+00:00
-- url     : https://prove2.me/submissions/3707db1a-c689-4a63-a6f7-dcfbd0436f0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
namespace GlobalTheory.PolyNorm
theorem _root_.solution {r m : ℕ} {Φ : MvPolynomial (Fin r) ℚ} (h : Φ.IsHomogeneous m)
    {K : Type} [CommRing K] [Algebra ℚ K] (c : K) (F : K[X]) :
    ev Φ (C c * F) = c ^ m * ev Φ F := by
  unfold ev
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : ∑ i, d i = m := by
    have := h.degree_eq_sum_deg_support hd
    rw [this]
    exact (Finset.sum_subset (Finset.subset_univ _) (by simp)).symm
  simp only [coeff_C_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd']
  ring
end GlobalTheory.PolyNorm
