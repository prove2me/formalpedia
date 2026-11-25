-- Prove2me | solution 1 for GroundTheory.LocalField.unramifiedCoord_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:22.517934+00:00
-- url     : https://prove2.me/submissions/401b25e3-6b68-4b42-9f1d-0926a8cecd0c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Theorems.Thm_GroundTheory_LocalField_pow_sub_one_dvd_pow_sub_one
import Theorems.Thm_GroundTheory_LocalField_card_residueField_eq_pow_residueDegree

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
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
namespace GroundTheory.LocalField
theorem _root_.solution (σ : L.fixingSubgroup) (n : ℕ+) :
    unramifiedCoord K (σ : Ω ≃ₐ[K] Ω) n =
      (residueDegree K L : ZMod n) * unramifiedCoord L (fixingSubgroupEquiv L σ) n := by
  have hQ := card_residueField_eq_pow_residueDegree K L
  have key : ((residueDegree K L * (unramifiedCoord L (fixingSubgroupEquiv L σ) n).val : ℕ) :
      ZMod n) = unramifiedCoord K (σ : Ω ≃ₐ[K] Ω) n := by
    rw [natCast_eq_unramifiedCoord_iff_forall]
    intro ξ hξ
    have hξ' : ξ ^ (Nat.card 𝓀[L] ^ (n : ℕ) - 1) = 1 := by
      rw [hQ, ← pow_mul]
      obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K])
        (dvd_mul_left (n : ℕ) (residueDegree K L))
      rw [hc, pow_mul, hξ, one_pow]
    have h := (natCast_eq_unramifiedCoord_iff_forall (K := L) (fixingSubgroupEquiv L σ) n
      (unramifiedCoord L (fixingSubgroupEquiv L σ) n).val).1 (ZMod.natCast_zmod_val _) ξ hξ'
    rw [hQ, ← pow_mul] at h
    exact h
  rw [← key, Nat.cast_mul, ZMod.natCast_zmod_val]
end GroundTheory.LocalField
