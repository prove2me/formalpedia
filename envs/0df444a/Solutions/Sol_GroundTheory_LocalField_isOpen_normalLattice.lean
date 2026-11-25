-- Prove2me | solution 1 for GroundTheory.LocalField.isOpen_normalLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:29.527566+00:00
-- url     : https://prove2.me/submissions/38596129-427f-48a7-900b-89ff018ee614

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_integer_smul_eq
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_pow_smul_mem_normalLattice
import Theorems.Thm_GroundTheory_LocalField_exists_pow_smul_mem_normalLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
section
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
section Lattice
variable (π : 𝒪[K]) (θ : L)
end Lattice
section Integral
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [ValuativeExtension K L]
variable (π : 𝒪[K]) (θ : L)
variable [IsGalois K L]
end Integral
section Product
variable (π : 𝒪[K]) (θ : L)
end Product
section Complete
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (π : 𝒪[K]) (θ : L)
variable {π θ}
end Complete
section Existence
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
variable [IsGalois K L]
end Existence
section Open
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L] [IsGalois K L]
  [ValuativeExtension K L] in
private theorem t2Space_isNonarchimedeanLocalField_singleBlock : T2Space L := by
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  infer_instance
variable (π : 𝒪[K]) (θ : L)
end Open
end GroundTheory.LocalField
end
end

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]
variable (π : 𝒪[K]) (θ : L)
namespace GroundTheory.LocalField
theorem _root_.solution (hπ : Irreducible π) (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ)
    (s : ℕ) : IsOpen (normalLattice π θ s : Set L) := by
  have := t2Space_isNonarchimedeanLocalField_singleBlock (L := L)
  have hπ0 : algebraMap K L (π : K) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  have hcont : Continuous fun c : Gal(L/K) → 𝒪[K] => π ^ s • ∑ σ, c σ • σ θ := by
    simp_rw [integer_smul_eq, Finset.mul_sum]
    refine continuous_finsetSum _ fun σ _ => ?_
    simp_rw [← Algebra.smul_def, smul_smul]
    refine Continuous.smul ?_ continuous_const
    exact continuous_const.mul (continuous_subtype_val.comp (continuous_apply σ))
  have hcpt : IsCompact (normalLattice π θ s : Set L) := by
    have : (normalLattice π θ s : Set L) = Set.range fun c : Gal(L/K) → 𝒪[K] =>
        π ^ s • ∑ σ, c σ • σ θ := by
      ext x
      exact (mem_normalLattice_iff π θ).trans (by simp)
    rw [this]
    exact isCompact_range hcont
  let A : ℕ → Set L := fun n => (fun y => algebraMap K L (π : K) ^ n * y) ⁻¹' normalLattice π θ s
  have hA : ∀ n, IsClosed (A n) := fun n =>
    hcpt.isClosed.preimage (continuous_const.mul continuous_id)
  have hU : ⋃ n, A n = Set.univ := by
    refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ?_
    obtain ⟨n, hn⟩ := exists_pow_smul_mem_normalLattice π θ hπ hθ y
    have h := pow_smul_mem_normalLattice π θ (u := s) (hn n le_rfl)
    rw [zero_add, ← mul_smul, ← pow_add, add_comm, integer_smul_eq] at h
    exact ⟨n + s, by simpa [A] using h⟩
  obtain ⟨n, y₀, hy₀⟩ := nonempty_interior_of_iUnion_of_closed hA hU
  let h : L ≃ₜ L := Homeomorph.mulLeft₀ (algebraMap K L (π : K) ^ n) (pow_ne_zero n hπ0)
  have hsub : h '' interior (A n) ⊆ normalLattice π θ s := by
    rintro _ ⟨y, hy, rfl⟩
    exact (interior_subset hy : y ∈ A n)
  exact AddSubgroup.isOpen_of_mem_nhds (normalLattice π θ s).toAddSubgroup
    (Filter.mem_of_superset ((h.isOpenMap _ isOpen_interior).mem_nhds ⟨y₀, hy₀, rfl⟩) hsub)
end GroundTheory.LocalField
