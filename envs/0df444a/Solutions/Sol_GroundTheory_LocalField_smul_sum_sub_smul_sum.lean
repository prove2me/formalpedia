-- Prove2me | solution 1 for GroundTheory.LocalField.smul_sum_sub_smul_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:28.033414+00:00
-- url     : https://prove2.me/submissions/aba31a08-3a9c-4b79-b417-01f1e55c214a

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
variable (π : 𝒪[K]) (θ : L)
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution (s : ℕ) (c d : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ - π ^ s • ∑ σ, d σ • σ θ = π ^ s • ∑ σ, (c σ - d σ) • σ θ := by
  simp only [sub_smul, sum_sub_distrib, smul_sub]
end GroundTheory.LocalField
