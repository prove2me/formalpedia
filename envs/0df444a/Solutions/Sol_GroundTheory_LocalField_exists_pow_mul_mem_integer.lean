-- Prove2me | solution 1 for GroundTheory.LocalField.exists_pow_mul_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:37.575542+00:00
-- url     : https://prove2.me/submissions/8fff1638-a01d-434c-8777-c908b3651a86

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_exists_pow_mul_mem_integer_of_lt_one

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
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [ValuativeExtension K L]
variable (π : 𝒪[K]) (θ : L)
omit [ValuativeRel L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (hπ : Irreducible π) (a : K) :
    ∃ n, ∀ m ≥ n, (π : K) ^ m * a ∈ 𝒪[K] :=
  exists_pow_mul_mem_integer_of_lt_one
    (valuation_lt_one_of_mem_maximalIdeal ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)) a
end GroundTheory.LocalField
