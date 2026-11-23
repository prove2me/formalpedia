-- Prove2me | solution 1 for GroundTheory.LocalField.smodEq_iff_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:41.166174+00:00
-- url     : https://prove2.me/submissions/86e25986-d45c-4ce1-87bc-197d634e87a5

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
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
omit [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} {x y : 𝒪[K]} :
    x ≡ y [SMOD (𝓂[K] ^ n • ⊤ : Submodule 𝒪[K] 𝒪[K])] ↔ π ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_maximalIdeal_pow_iff hπ]
end GroundTheory.LocalField
