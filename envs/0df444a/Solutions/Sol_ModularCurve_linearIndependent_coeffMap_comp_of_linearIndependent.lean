-- Prove2me | solution 1 for ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6fc6c8a8-0246-5512-8800-5477b1612b61

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent

set_option autoImplicit false

open ModularCurve

theorem solution
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    {n : ℕ} (f : Fin n → LaurentSeries κ) (hf : LinearIndependent κ f) :
    LinearIndependent k (⇑(coeffMap (algebraMap κ k)) ∘ f) := by
  classical
  set g : κ →+* k := algebraMap κ k with hg
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc i₀

  let B := Module.Basis.ofVectorSpace κ k

  have hcomb : ∀ j, ∑ i, (B.repr (c i) j) • f i = 0 := by
    intro j
    ext m

    have hm : ∑ i, ((f i).coeff m) • c i = 0 := by
      have h0 := congrArg (fun x : LaurentSeries k => x.coeff m) hc
      simp only [HahnSeries.coeff_zero, HahnSeries.coeff_sum, Function.comp_apply, HahnSeries.coeff_smul, coeffMap_coeff,
        smul_eq_mul] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, mul_comm]

    have hj := congrArg (fun x : k => B.repr x j) hm
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hj
    rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
    simp only [HahnSeries.coeff_smul, smul_eq_mul]
    rw [← hj]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hzero : ∀ j, B.repr (c i₀) j = 0 := fun j => hf _ (hcomb j) i₀
  have hrepr : B.repr (c i₀) = 0 := Finsupp.ext hzero
  simpa using congrArg B.repr.symm hrepr

#print axioms solution

end S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent
end P2MW
export P2MW.S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent (solution)
