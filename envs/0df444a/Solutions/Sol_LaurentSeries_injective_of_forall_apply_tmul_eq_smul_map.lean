-- Prove2me | solution 1 for LaurentSeries.injective_of_forall_apply_tmul_eq_smul_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/11067155-c626-59a0-87cd-196bf41846f6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_injective_of_forall_apply_tmul_eq_smul_map

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct

universe u v

theorem solution
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (Φ : K ⊗[k] LaurentSeries k →ₗ[k] LaurentSeries K)
    (hΦ : ∀ (a : K) (f : LaurentSeries k), Φ (a ⊗ₜ[k] f) = a • f.map (algebraMap k K)) :
    Function.Injective Φ := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  let b := Module.Free.chooseBasis k K

  let e : K ⊗[k] LaurentSeries k ≃ₗ[k] (Module.Free.ChooseBasisIndex k K →₀ LaurentSeries k) :=
    (b.repr.rTensor (LaurentSeries k)) ≪≫ₗ TensorProduct.finsuppScalarLeft k (LaurentSeries k) _
  have he_symm : ∀ (i : Module.Free.ChooseBasisIndex k K) (f : LaurentSeries k),
      e.symm (Finsupp.single i f) = b i ⊗ₜ[k] f := by
    intro i f
    change (b.repr.rTensor (LaurentSeries k)).symm
      ((TensorProduct.finsuppScalarLeft k (LaurentSeries k) _).symm (Finsupp.single i f)) = _
    rw [TensorProduct.finsuppScalarLeft_symm_apply_single, LinearEquiv.rTensor_symm_tmul,
      Module.Basis.repr_symm_single_one]

  set g := e x with hg
  have hxsum : x = g.sum fun i f => b i ⊗ₜ[k] f := by
    have h1 : x = e.symm g := by rw [hg, LinearEquiv.symm_apply_apply]
    conv_lhs => rw [h1, ← Finsupp.sum_single g]
    rw [map_finsuppSum]
    exact Finsupp.sum_congr fun i _ => he_symm i (g i)

  have hcoeff : ∀ n : ℤ, (Φ x).coeff n = g.sum fun i f => (f.coeff n) • b i := by
    intro n
    rw [hxsum, map_finsuppSum]
    simp only [Finsupp.sum, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΦ, HahnSeries.coeff_smul, HahnSeries.map_coeff, smul_eq_mul, mul_comm, ← Algebra.smul_def]

  have hzero : ∀ i ∈ g.support, ∀ n : ℤ, (g i).coeff n = 0 := by
    intro i hi n
    have hli := (linearIndependent_iff'.mp b.linearIndependent) g.support (fun j => (g j).coeff n) ?_ i hi
    · exact hli
    · have h0 : (Φ x).coeff n = 0 := by rw [hx]; rfl
      rw [hcoeff n] at h0
      exact h0
  have hg0 : g = 0 := by
    ext i n
    by_cases hi : i ∈ g.support
    · rw [hzero i hi n]; rfl
    · rw [Finsupp.notMem_support_iff.mp hi]; rfl
  rw [hxsum, hg0, Finsupp.sum_zero_index]

end S_LaurentSeries_injective_of_forall_apply_tmul_eq_smul_map
end P2MW
export P2MW.S_LaurentSeries_injective_of_forall_apply_tmul_eq_smul_map (solution)
