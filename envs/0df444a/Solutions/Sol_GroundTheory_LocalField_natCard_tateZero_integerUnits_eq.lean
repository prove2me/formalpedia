-- Prove2me | solution 1 for GroundTheory.LocalField.natCard_tateZero_integerUnits_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:56.721095+00:00
-- url     : https://prove2.me/submissions/b95d26e5-aab8-42f1-9038-38d9985d9433

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Theorems.Thm_GroundTheory_LocalField_cycHerbrand_integerUnits_eq_one
import Theorems.Thm_GroundTheory_LocalField_cycHerbrand_ofMulDistribMulAction
import Theorems.Thm_GroundTheory_LocalField_hasHerbrandQuotient_iff


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
    Finite (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) ∧ Finite (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) ∧
      Nat.card (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) = Nat.card (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  obtain ⟨hA, h1⟩ := cycHerbrand_integerUnits_eq_one hτ
  obtain ⟨f0, f1⟩ := (hasHerbrandQuotient_iff hτ).mp hA
  refine ⟨f0, f1, ?_⟩
  rw [cycHerbrand_ofMulDistribMulAction hτ] at h1
  have h0 : (Nat.card (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  exact_mod_cast (div_eq_one_iff_eq h0).mp h1
end GroundTheory.LocalField
