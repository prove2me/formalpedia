-- Prove2me | solution 1 for GroundTheory.LocalField.eq_zero_of_forall_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:51.684798+00:00
-- url     : https://prove2.me/submissions/b1246d2c-a776-4a81-8ae2-10132bef1f6a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_smodEq_iff_pow_dvd
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
omit [FiniteDimensional K L] in

private theorem isAdicComplete_maximalIdeal : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
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
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
omit [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {π : 𝒪[K]} (hπ : Irreducible π) {x : 𝒪[K]}
    (h : ∀ N, π ^ N ∣ x) : x = 0 :=
  IsHausdorff.haus (isAdicComplete_maximalIdeal (K := K)).toIsHausdorff x fun N => by
    rw [smodEq_iff_pow_dvd hπ, sub_zero]
    exact h N
end GroundTheory.LocalField
