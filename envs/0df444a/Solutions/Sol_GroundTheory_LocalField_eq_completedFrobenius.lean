-- Prove2me | solution 1 for GroundTheory.LocalField.eq_completedFrobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:49:29.362159+00:00
-- url     : https://prove2.me/submissions/699e9745-e0f1-403c-a662-8cd2aed635cf

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
import Theorems.Thm_GroundTheory_LocalField_eq_completedUnramifiedAlgEquiv

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
variable [IsGalois K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution {τ : 𝔹 →+* 𝔹}
    (hτ : ∀ x : 𝒪[𝔼], τ (algebraMap 𝒪[𝔼] 𝔹 x) = algebraMap 𝒪[𝔼] 𝔹
      (integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x)) :
    τ = (completedFrobenius K Ω : 𝔹 →+* 𝔹) :=
  eq_completedUnramifiedAlgEquiv _ hτ
end GroundTheory.LocalField
