-- Prove2me | solution 1 for GroundTheory.LocalField.natCard_tateZero_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:36:59.793282+00:00
-- url     : https://prove2.me/submissions/bc5e6517-0d92-4568-b87c-163055242118

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Theorems.Thm_GroundTheory_LocalField_cycHerbrand_units_eq_finrank
import Theorems.Thm_GroundTheory_LocalField_natCard_tateNegOne_units
import Theorems.Thm_GroundTheory_LocalField_cycHerbrand_ofMulDistribMulAction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsGalois K L] {σ : L ≃ₐ[K] L}
variable [IsCyclic (L ≃ₐ[K] L)]
namespace GroundTheory.LocalField
theorem _root_.solution :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Module.finrank K L := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have h := (cycHerbrand_units_eq_finrank hτ).2
  rw [cycHerbrand_ofMulDistribMulAction hτ, natCard_tateNegOne_units, Nat.cast_one, div_one] at h
  exact_mod_cast h
end GroundTheory.LocalField
