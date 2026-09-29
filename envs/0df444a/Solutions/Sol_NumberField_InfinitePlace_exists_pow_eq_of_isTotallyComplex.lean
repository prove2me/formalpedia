-- Prove2me | solution 1 for NumberField.InfinitePlace.exists_pow_eq_of_isTotallyComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a9927a3d-1eb2-518c-a5a5-d7be15191dbf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfinitePlace_exists_pow_eq_of_isTotallyComplex

set_option autoImplicit false

open NumberField

open NumberField in

theorem solution
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (w : InfinitePlace K) (u : (w.Completion)ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ v : (w.Completion)ˣ, v ^ n = u := by

  let e : w.Completion ≃+* ℂ :=
    InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)

  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (u : w.Completion)) hn
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hz
    exact (e.map_ne_zero_iff.2 u.ne_zero) hz.symm
  have hv0 : e.symm z ≠ 0 := fun h => hz0 (by simpa using congrArg e h)
  refine ⟨Units.mk0 (e.symm z) hv0, Units.ext ?_⟩
  change (e.symm z) ^ n = (u : w.Completion)
  apply e.injective
  rw [map_pow, e.apply_symm_apply, hz]

end S_NumberField_InfinitePlace_exists_pow_eq_of_isTotallyComplex
end P2MW
export P2MW.S_NumberField_InfinitePlace_exists_pow_eq_of_isTotallyComplex (solution)
