-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_of_mem_adjoin_restrictSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:55.173797+00:00
-- url     : https://prove2.me/submissions/3ede8157-4600-4e81-bb5d-8aeb1e725141

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable [FiniteDimensional ℂ M]
omit [FiniteDimensional ℂ M]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {T : Set (End ℂ M)} {N : Submodule ℂ M}
    (hN : IsStable T N) {b : End ℂ N} (hb : b ∈ Algebra.adjoin ℂ (restrictSet T N hN)) :
    ∃ a ∈ Algebra.adjoin ℂ T, ∀ x : N, (b x : M) = a x := by
  let S : Subalgebra ℂ (End ℂ N) :=
    { carrier := {b | ∃ a ∈ Algebra.adjoin ℂ T, ∀ x : N, (b x : M) = a x}
      mul_mem' := by
        rintro b₁ b₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        exact ⟨a₁ * a₂, Subalgebra.mul_mem _ ha₁ ha₂, fun x => by
          rw [Module.End.mul_apply, h₁, Module.End.mul_apply, h₂]⟩
      add_mem' := by
        rintro b₁ b₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        exact ⟨a₁ + a₂, Subalgebra.add_mem _ ha₁ ha₂, fun x => by
          rw [LinearMap.add_apply, Submodule.coe_add, h₁, h₂, LinearMap.add_apply]⟩
      algebraMap_mem' := fun c => ⟨algebraMap ℂ (End ℂ M) c, Subalgebra.algebraMap_mem _ c,
        fun x => by simp [Algebra.algebraMap_eq_smul_one]⟩ }
  have : Algebra.adjoin ℂ (restrictSet T N hN) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨t, Algebra.subset_adjoin t.2, fun x => rfl⟩
  exact this hb
end GroundTheory.Automorphic.RestrictedTensor
