-- Prove2me | solution 1 for Hintz2026.Dm_div_sqrtDel
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:53:08.730974+00:00
-- url     : https://prove2.me/submissions/2fce90ea-69ae-4c1a-b5f6-49fca0cac2e3

import Definitions.Def_Hintz2026_Chiral

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (f : (Fin 2 -> ℝ) -> ℂ) (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) : Dm p (fun z => f z / ↑(Real.sqrt (Del p (z 0)))) x = Dm p f x / ↑(Real.sqrt (Del p (x 0))) - f x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0))) :=
  by
    have hD := Del_pos p hx.1
    have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
    have hDc : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
    have e : (fun z => f z / ↑(Real.sqrt (Del p (z 0)))) = fun z => f z * (↑(Real.sqrt (Del p (z 0))) : ℂ)⁻¹ := by
      funext z; rw [div_eq_mul_inv]
    rw [e, Dm_mul p f _ x (hf 0) (diff_inv_sqrtDel_slice p hx 0) (hf 1) (diff_inv_sqrtDel_slice p hx 1)]
    unfold Dm
    rw [cpd0_inv_sqrtDel p hx, cpd1_inv_sqrtDel]
    rw [Del'_eq]
    field_simp
    push_cast
    ring_nf
    rw [← hsq]
    field_simp
    ring

end
