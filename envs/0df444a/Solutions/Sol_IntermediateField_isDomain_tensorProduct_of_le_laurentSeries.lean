-- Prove2me | solution 1 for IntermediateField.isDomain_tensorProduct_of_le_laurentSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ddbeba72-3811-59c1-8512-42a8f4a5e720

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_isDomain_tensorProduct_of_le_laurentSeries

set_option autoImplicit false

open scoped TensorProduct

namespace RegExt

variable (κ k : Type*) [Field κ] [Field k] [Algebra κ k]

theorem algebraMap_laurent (c : κ) :
    algebraMap κ (LaurentSeries k) c = HahnSeries.C (algebraMap κ k c) := by
  have h1 : algebraMap κ (PowerSeries k) c = PowerSeries.C (algebraMap κ k c) := PowerSeries.algebraMap_apply
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

noncomputable def coeffAlgHom : LaurentSeries κ →ₐ[κ] LaurentSeries k :=
  { ModularCurve.coeffMap (algebraMap κ k) with
    commutes' := fun c => by
      show ModularCurve.coeffMap (algebraMap κ k) (algebraMap κ (LaurentSeries κ) c) = algebraMap κ (LaurentSeries k) c
      rw [algebraMap_laurent κ κ c, algebraMap_laurent κ k c, Algebra.algebraMap_self, RingHom.id_apply,
        HahnSeries.C_apply, HahnSeries.C_apply, ModularCurve.coeffMap_single] }

theorem coeffAlgHom_coeff (x : LaurentSeries κ) (n : ℤ) :
    (coeffAlgHom κ k x).coeff n = algebraMap κ k (x.coeff n) := rfl

noncomputable def constAlgHom : k →ₐ[κ] LaurentSeries k :=
  { (HahnSeries.C : k →+* LaurentSeries k) with
    commutes' := fun c => by
      show HahnSeries.C (algebraMap κ k c) = algebraMap κ (LaurentSeries k) c
      rw [algebraMap_laurent] }

theorem constAlgHom_apply (b : k) : constAlgHom κ k b = HahnSeries.C b := rfl

theorem linearDisjoint_range :
    (coeffAlgHom κ k).range.LinearDisjoint (constAlgHom κ k).range := by
  classical

  let b := Module.Basis.ofVectorSpace κ k

  let e : k ≃ₐ[κ] (constAlgHom κ k).range := AlgEquiv.ofInjective (constAlgHom κ k) (RingHom.injective _)
  let b' : Module.Basis _ κ (constAlgHom κ k).range := b.map e.toLinearEquiv
  refine Subalgebra.LinearDisjoint.of_basis_right _ _ b' ?_
  rw [linearIndependent_iff']
  intro s g hsum i hi

  have hx : ∀ j, ∃ x : LaurentSeries κ, coeffAlgHom κ k x = ((g j : (coeffAlgHom κ k).range) : LaurentSeries k) :=
    fun j => (AlgHom.mem_range _).mp (g j).2
  choose x hxg using hx

  have hval : ∀ j, ((constAlgHom κ k).range.val (b' j) : LaurentSeries k) = HahnSeries.C (b j) := by
    intro j
    show (((b.map e.toLinearEquiv) j : (constAlgHom κ k).range) : LaurentSeries k) = HahnSeries.C (b j)
    rw [Module.Basis.map_apply]
    show ((e (b j) : (constAlgHom κ k).range) : LaurentSeries k) = _
    rw [AlgEquiv.ofInjective_apply]
    rfl

  have hcoef : ∀ n : ℤ, ∑ j ∈ s, (x j).coeff n • b j = 0 := by
    intro n
    have h := congrArg (fun z : LaurentSeries k => z.coeff n) hsum
    simp only [Function.comp_apply, HahnSeries.coeff_zero] at h
    rw [HahnSeries.coeff_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, hval j, smul_eq_mul, mul_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      ← hxg j, coeffAlgHom_coeff, smul_eq_mul, Algebra.smul_def, mul_comm]
  have hzero : ∀ n : ℤ, (x i).coeff n = 0 := fun n =>
    linearIndependent_iff'.mp b.linearIndependent s (fun j => (x j).coeff n) (hcoef n) i hi
  have hxi : x i = 0 := HahnSeries.ext (funext hzero)
  apply Subtype.ext
  show ((g i : (coeffAlgHom κ k).range) : LaurentSeries k) = 0
  rw [← hxg i, hxi, map_zero]

end RegExt

namespace RegExt

theorem isDomain (κ k : Type*) [Field κ] [Field k] [Algebra κ k] (R : IntermediateField κ (LaurentSeries κ)) :
    IsDomain (↥R ⊗[κ] k) := by
  let fa : ↥R →ₐ[κ] LaurentSeries k := (coeffAlgHom κ k).comp R.val
  let fb : k →ₐ[κ] LaurentSeries k := constAlgHom κ k
  have hle : fa.range ≤ (coeffAlgHom κ k).range := by
    rintro _ ⟨r, rfl⟩
    exact ⟨(r : LaurentSeries κ), rfl⟩
  have H : fa.range.LinearDisjoint fb.range := (linearDisjoint_range κ k).of_le_left_of_flat hle
  exact H.isDomain_of_injective fa.injective fb.injective

end RegExt

theorem solution
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    (R : IntermediateField κ (LaurentSeries κ)) :
    IsDomain (↥R ⊗[κ] k) :=
  RegExt.isDomain κ k R

end S_IntermediateField_isDomain_tensorProduct_of_le_laurentSeries
end P2MW
export P2MW.S_IntermediateField_isDomain_tensorProduct_of_le_laurentSeries (solution)
