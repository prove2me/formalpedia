-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermSmooth.hasDerivAt_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:23:16.365825+00:00
-- url     : https://prove2.me/submissions/0c7b0776-85fc-4c4f-9da0-3ed2a7408c44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_u_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth
namespace GlobalTheory.HeckeTwo.TermSmooth
theorem _root_.solution (σ : ℂ) (ν : ℝ) (a b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (fun y => term σ ν a b m y t)
      (-(a : ℂ) * I * term σ ν (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * term σ ν a (b + 1) (m + 1) y t
        + (m : ℂ) * term σ ν a b (m - 1) y t) y := by
  have hu := u_ne hy t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => (t : ℂ) + (y : ℂ) * I) I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (t : ℂ)
  have h2 : HasDerivAt (fun y : ℝ => ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a)
      ((a : ℂ) * ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ (a - 1) * (-(((t : ℂ) + (y : ℂ) * I) ^ 2)⁻¹ * I)) y :=
    (((hasDerivAt_inv hu).comp y h1).pow a)
  have h3 : HasDerivAt (fun y : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))) ((2 * y : ℝ) : ℂ) y := by
    have : HasDerivAt (fun y : ℝ => t ^ 2 + y ^ 2) (2 * y) y := by
      simpa using ((hasDerivAt_pow 2 y).const_add (t ^ 2))
    exact this.ofReal_comp
  have h4 := (Complex.hasStrictDerivAt_cpow_const (c := -σ - (b : ℂ))
      (Complex.ofReal_mem_slitPlane.2 hQ)).hasDerivAt.comp y h3
  have h5 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ m) ((m : ℂ) * (y : ℂ) ^ (m - 1)) y :=
    (hasDerivAt_pow m (y : ℂ)).comp_ofReal
  have h := ((h2.mul h4).mul h5).mul_const (Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))))
  refine h.congr_deriv ?_
  simp only [term, Function.comp_def, Pi.mul_apply, ← inv_pow]
  generalize ((t : ℂ) + (y : ℂ) * I)⁻¹ = v
  rw [show -σ - ((b + 1 : ℕ) : ℂ) = -σ - (b : ℂ) - 1 by push_cast; ring]
  rcases a with _ | a <;> rcases m with _ | m <;>
    simp only [Nat.add_sub_cancel, Nat.zero_sub, pow_zero, Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add,
      neg_zero, Complex.ofReal_mul, Complex.ofReal_ofNat] <;> push_cast <;> ring
end GlobalTheory.HeckeTwo.TermSmooth
