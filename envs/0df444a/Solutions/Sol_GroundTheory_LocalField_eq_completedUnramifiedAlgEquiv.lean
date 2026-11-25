-- Prove2me | solution 1 for GroundTheory.LocalField.eq_completedUnramifiedAlgEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:12.585939+00:00
-- url     : https://prove2.me/submissions/e6a70528-ce76-4e0f-b505-ec00b7b881e8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
import Theorems.Thm_GroundTheory_LocalField_eq_adicCompletionAlgEquiv

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
open IsLocalRing ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
local notation "𝔹" => CompletedUnramifiedIntegers K Ω
variable {K Ω}
namespace GroundTheory.LocalField
theorem _root_.solution (ρ : 𝔼 ≃ₐ[K] 𝔼) {τ : 𝔹 →+* 𝔹}
    (hτ : ∀ x : 𝒪[𝔼], τ (algebraMap 𝒪[𝔼] 𝔹 x) =
      algebraMap 𝒪[𝔼] 𝔹 (integerAlgEquivOfIsAlgebraic K 𝔼 ρ x)) :
    τ = (completedUnramifiedAlgEquiv K Ω ρ : 𝔹 →+* 𝔹) :=
  eq_adicCompletionAlgEquiv _ hτ
end GroundTheory.LocalField
