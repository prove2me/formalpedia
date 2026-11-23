-- Prove2me | solution 1 for GroundTheory.LocalField.normalLattice_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:27.512236+00:00
-- url     : https://prove2.me/submissions/29fea371-8679-40bf-bf23-2258e61f8a1c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable (π : 𝒪[K]) (θ : L)
omit [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution : Antitone (normalLattice π θ) := by
  refine antitone_nat_of_succ_le fun s => Submodule.span_le.mpr ?_
  rintro _ ⟨σ, rfl⟩
  simp only [SetLike.mem_coe, pow_succ', mul_smul]
  exact Submodule.smul_mem _ π (Submodule.subset_span ⟨σ, rfl⟩)
end GroundTheory.LocalField
