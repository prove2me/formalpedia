-- Prove2me | solution 1 for ModularCurve.linearIndependent_coeffEmb_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e8d3e0a3-cce8-5e5d-925b-cb90d87e4958

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent

set_option autoImplicit false

open ModularCurve

universe u v

theorem solution
    (L : Type u) [Field L] [CharZero L]
    {ι : Type v} {v : ι → LaurentSeries ℚ} (hv : LinearIndependent ℚ v) :
    LinearIndependent L (fun i => coeffEmb L (v i)) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  let b := Module.Free.chooseBasis ℚ L

  have hcoeff : ∀ (k) (n : ℤ), ∑ j ∈ s, b.repr (g j) k * (v j).coeff n = 0 := by
    intro k n
    have h := congrArg (fun x : LaurentSeries L => b.repr (x.coeff n) k) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, coeffEmb_coeff, HahnSeries.coeff_zero,
      map_zero, Finsupp.zero_apply, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

  have hrepr : ∀ k, b.repr (g i) k = 0 := by
    intro k
    refine hv s (fun j => b.repr (g j) k) ?_ i hi
    ext n
    rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
    simp only [HahnSeries.coeff_smul, smul_eq_mul]
    exact hcoeff k n
  exact b.repr.map_eq_zero_iff.mp (Finsupp.ext fun k => hrepr k)

end S_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent
end P2MW
export P2MW.S_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent (solution)
