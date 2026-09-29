-- Prove2me | solution 1 for Module.free_quotient_range_of_ker_baseChange_residueField_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/35151749-0027-5036-b9c4-0b8f860856df

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace P2mKcTorCrit

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem rangeRestrict_comp_ker_subtype (f : M →ₗ[R] N) :
    f.rangeRestrict.comp (LinearMap.ker f).subtype = 0 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  change f x = 0
  exact x.2

theorem subtype_comp_rangeRestrict (f : M →ₗ[R] N) :
    (LinearMap.range f).subtype.comp f.rangeRestrict = f :=
  LinearMap.ext fun _ => rfl

theorem lTensor_subtype_range_injective (A : Type*) [CommRing A] [Algebra R A] (f : M →ₗ[R] N)
    (h : LinearMap.ker (f.baseChange A) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange A)) :
    Function.Injective ((LinearMap.range f).subtype.lTensor A) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hsurj : Function.Surjective (f.rangeRestrict.lTensor A) :=
    LinearMap.lTensor_surjective A (LinearMap.surjective_rangeRestrict f)
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : y ∈ LinearMap.ker (f.baseChange A) := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, subtype_comp_rangeRestrict] at hx
    exact hx
  obtain ⟨z, hz⟩ := h hy
  rw [Submodule.mem_bot, ← hz]
  change f.rangeRestrict.lTensor A ((LinearMap.ker f).subtype.lTensor A z) = 0
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, rangeRestrict_comp_ker_subtype,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

theorem free_quotient_range [IsLocalRing R] [Module.Finite R M] [Module.Finite R N]
    [Module.Free R N] (f : M →ₗ[R] N)
    (h : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (N ⧸ LinearMap.range f) :=
  Module.free_of_lTensor_residueField_injective (LinearMap.range f).subtype
    (LinearMap.range f).mkQ (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    (lTensor_subtype_range_injective (IsLocalRing.ResidueField R) f h)

end P2mKcTorCrit

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (N ⧸ LinearMap.range f) :=
  P2mKcTorCrit.free_quotient_range f h

end S_Module_free_quotient_range_of_ker_baseChange_residueField_le
end P2MW
export P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le (solution)
