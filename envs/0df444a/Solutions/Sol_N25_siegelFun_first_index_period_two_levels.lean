-- Prove2me | solution 1 for N25.siegelFun_first_index_period_two_levels
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:48.066489+00:00
-- url     : https://prove2.me/submissions/14547bb3-014e-421f-bf72-ff617e0071b1

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_SiegelUnit_siegelFun_add_level

set_option autoImplicit false

namespace N25

/-- At second index zero, two level shifts in the first index have trivial
multiplier; the resulting period holds for every signed integer multiple. -/
theorem _root_.solution
    (N : ℕ) (r k : ℤ) (τ : UpperHalfPlane) :
    ModularCurve.siegelFun N (r + 2*k*(N : ℤ)) 0 (τ : ℂ) =
      ModularCurve.siegelFun N r 0 (τ : ℂ) := by
  have hshift (t : ℤ) : ModularCurve.siegelFun N (t + N) 0 (τ : ℂ) =
      -ModularCurve.siegelFun N t 0 (τ : ℂ) := by
    simpa using (ModularCurve.SiegelUnit.siegelFun_add_level N t 0).2 τ
  have htwo (t : ℤ) : ModularCurve.siegelFun N (t + 2*N) 0 (τ : ℂ) =
      ModularCurve.siegelFun N t 0 (τ : ℂ) := by
    rw [show t + 2*N = (t + N) + N by ring, hshift, hshift, neg_neg]
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show r + 2*((n : ℤ)+1)*N = (r + 2*(n : ℤ)*N) + 2*N by ring, htwo, ih]
  | pred n ih =>
    have h := htwo (r + 2*(-(n : ℤ)-1)*N)
    rw [show r + 2*(-(n : ℤ)-1)*N + 2*N = r + 2*(-(n : ℤ))*N by ring] at h
    exact h.symm.trans ih

end N25
