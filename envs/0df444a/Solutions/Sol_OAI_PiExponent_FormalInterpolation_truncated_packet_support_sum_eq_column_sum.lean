-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_support_sum_eq_column_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:03:15.287496+00:00
-- url     : https://prove2.me/submissions/03fac389-0b04-4391-b24d-0597c70d9aec

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_sum_eq_sum_over_finite_embedding

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hcols : ∀ e ∈ P.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = e)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
      ∑ e ∈ P.support,
        P.coeff e * InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (e 0) (fun i => e i.succ) =
      ∑ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.entry
          r (fun i => InterpolationMatrix.truncatedLog (T i))
          rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
          (c.1 0) (fun i => c.1 i.succ) *
        P.coeff (InterpolationMatrix.exponentVector c.1) := by
  classical
  let f : InterpolationMatrix.Column w0 w H → (Fin (m + 1) →₀ Nat) :=
    fun c => InterpolationMatrix.exponentVector c.1
  let a : (Fin (m + 1) →₀ Nat) → Complex := P.coeff
  let g : (Fin (m + 1) →₀ Nat) → Complex := fun e =>
    InterpolationMatrix.entry
      r (fun i => InterpolationMatrix.truncatedLog (T i))
      rho.1.val (rho.2.1 0) (fun i => rho.2.1 i.succ)
      (e 0) (fun i => e i.succ)
  have hf : Function.Injective f := by
    intro c d h
    have h' := congrArg Finsupp.equivFunOnFinite h
    apply Subtype.ext
    simpa [f, InterpolationMatrix.exponentVector] using h'
  have hz : ∀ e, e ∉ P.support → a e = 0 := by
    intro e he
    exact MvPolynomial.notMem_support_iff.mp he
  have hsum := OAI.PiExponent.FormalInterpolation.sum_eq_sum_over_finite_embedding
    (S := P.support) (f := f) (a := a) (g := g) hf hcols hz
  simpa [f, a, g, InterpolationMatrix.exponentVector, mul_comm] using hsum