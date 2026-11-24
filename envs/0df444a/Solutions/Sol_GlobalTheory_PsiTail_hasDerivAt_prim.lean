-- Prove2me | solution 1 for GlobalTheory.PsiTail.hasDerivAt_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:12.557807+00:00
-- url     : https://prove2.me/submissions/9c3fbf96-3c7c-4af2-a103-4c6dd009b145

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2Integrality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.PsiTail
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory.PsiTail
theorem _root_.solution (Q E u : ℝ) (hQ : 0 < Q) (hu : 1 < u) :
    HasDerivAt (fun t : ℝ => -(t ^ (-(1 : ℝ) / 400) *
        (400 * Real.log (t * Q) ^ 2 + 320000 * Real.log (t * Q) + 128000000) + E / Real.log t))
      ((u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) / u) u := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos hu
  have h1 : HasDerivAt (fun t : ℝ => t ^ (-(1 : ℝ) / 400)) ((-(1 : ℝ) / 400) * (u ^ (-(1 : ℝ) / 400) / u)) u := by
    have := Real.hasDerivAt_rpow_const (x := u) (p := -(1 : ℝ) / 400) (Or.inl hu0.ne')
    rwa [Real.rpow_sub_one hu0.ne'] at this
  have h2 : HasDerivAt (fun t : ℝ => Real.log (t * Q)) (1 / u) u := by
    have := ((hasDerivAt_id' u).mul_const Q).log (by positivity)
    refine this.congr_deriv ?_
    field_simp
  have h3 : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hu0.ne'
  have h4 := ((h1.fun_mul ((((h2.fun_pow 2).const_mul 400).fun_add (h2.const_mul 320000)).add_const 128000000)).fun_add
    ((hasDerivAt_const u E).fun_div h3 hlu.ne')).fun_neg
  refine h4.congr_deriv ?_
  have := hlu.ne'
  have := hu0.ne'
  generalize u ^ (-(1 : ℝ) / 400) = w
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  ring
end GlobalTheory.PsiTail
