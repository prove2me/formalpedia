-- Prove2me | solution 1 for GroundTheory.LocalField.card_quotient_differentIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:17.809662+00:00
-- url     : https://prove2.me/submissions/9aa03d02-6f9e-4c83-a997-fc83f7385734

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
import Theorems.Thm_GroundTheory_LocalField_differentIdeal_eq_maximalIdeal_pow


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
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
namespace GroundTheory.LocalField
theorem _root_.solution :
    Nat.card (𝒪[L] ⧸ differentIdeal 𝒪[K] 𝒪[L]) = residueCard L ^ differentExponent K L := by
  rw [differentIdeal_eq_maximalIdeal_pow, ← Submodule.cardQuot_apply,
    cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field 𝒪[L]),
    Submodule.cardQuot_apply]
  rfl
end GroundTheory.LocalField
