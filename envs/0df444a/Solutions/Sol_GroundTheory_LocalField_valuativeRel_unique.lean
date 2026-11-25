-- Prove2me | solution 1 for GroundTheory.LocalField.valuativeRel_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:04.153487+00:00
-- url     : https://prove2.me/submissions/dc3299c8-2f0e-4b1e-93a8-cdd45da3b36b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Theorems.Thm_GroundTheory_LocalField_topologicalSpace_unique

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
open ValuativeRel Topology Filter
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {v₁ v₂ : ValuativeRel L} {t₁ t₂ : TopologicalSpace L}
    (h₁ : @IsNonarchimedeanLocalField L _ v₁ t₁) (h₂ : @IsNonarchimedeanLocalField L _ v₂ t₂)
    (e₁ : @ValuativeExtension K L _ _ _ v₁ _) (e₂ : @ValuativeExtension K L _ _ _ v₂ _) :
    v₁ = v₂ := by
  have ht := topologicalSpace_unique K h₁ h₂ e₁ e₂
  subst ht
  have hlt (z : L) : @valuation L _ v₂ z < 1 ↔ @valuation L _ v₁ z < 1 := by
    rw [← @tendsto_pow_atTop_nhds_zero_iff L _ v₁ t₁ h₁,
      ← @tendsto_pow_atTop_nhds_zero_iff L _ v₂ t₁ h₂]
  ext x y
  exact (@vle_map_iff_of_valuation_lt_one_iff L _ v₁ L _ v₂ (RingHom.id L) hlt x y).symm
end GroundTheory.LocalField
