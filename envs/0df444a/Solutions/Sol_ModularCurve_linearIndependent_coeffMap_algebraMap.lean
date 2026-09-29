-- Prove2me | solution 1 for ModularCurve.linearIndependent_coeffMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/cdee74cd-311e-5e82-b16f-cbd39becd6f3

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_linearIndependent_coeffMap_algebraMap

set_option autoImplicit false
set_option Elab.async false

open ModularCurve

set_option maxHeartbeats 1600000 in
theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    {ι : Type*} (v : ι → LaurentSeries K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => coeffMap (algebraMap K L) (v i)) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  let B := Module.Free.chooseBasis K L

  have key : ∀ j, ∑ i ∈ s, (B.repr (g i) j) • v i = 0 := by
    intro j
    ext n
    have hn : (∑ i ∈ s, g i • coeffMap (algebraMap K L) (v i)).coeff n = 0 := by
      rw [hg]; rfl
    rw [HahnSeries.coeff_sum] at hn ⊢
    simp_rw [HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul] at hn ⊢

    have h2 := congrArg (fun x : L => B.repr x j) hn
    simp only [map_sum, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum, Finset.sum_apply] at h2
    rw [show (0 : LaurentSeries K).coeff n = 0 from rfl, ← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (g i) _, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

  have hcoord : ∀ j, B.repr (g i) j = 0 := fun j => hv s (fun i => B.repr (g i) j) (key j) i hi
  have : B.repr (g i) = 0 := Finsupp.ext fun j => hcoord j
  exact B.repr.map_eq_zero_iff.mp this

end S_ModularCurve_linearIndependent_coeffMap_algebraMap
end P2MW
export P2MW.S_ModularCurve_linearIndependent_coeffMap_algebraMap (solution)
