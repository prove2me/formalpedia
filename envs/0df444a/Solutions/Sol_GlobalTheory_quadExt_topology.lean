-- Prove2me | solution 1 for GlobalTheory.quadExt_topology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:34.588399+00:00
-- url     : https://prove2.me/submissions/a3fb76ea-c24d-4a88-94d4-4404b1b277d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactOpenSubgroupExhaustionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopology
import Theorems.Thm_GlobalTheory_T_isSelfDualCompactOpenGroup_of_finiteDimensional
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_algebraMap_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ), FiniteDimensional F E ∧ IsTopologicalRing E ∧ ContinuousInv₀ E ∧ T2Space E ∧ Continuous c ∧ Continuous (Algebra.norm F : E → F) ∧ Continuous (Algebra.trace F E) ∧ ∀ (α ν : Type) [Fintype α] [Fintype ν], IsModuleTopology F (Matrix α ν E) ∧ Good (Matrix α ν E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE
  obtain ⟨b, -, -⟩ := hE.basis
  haveI hfd : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing F E
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
  have htr : Continuous (Algebra.trace F E) := IsModuleTopology.continuous_of_linearMap (Algebra.trace F E)
  have hN : ∀ z : E, Algebra.norm F z = (2 : F)⁻¹ * Algebra.trace F E (z * c z) := by
    intro z
    rw [← hE.algebraMap_norm z, Algebra.trace_algebraMap, Module.finrank_eq_card_basis b, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hNc : Continuous (Algebra.norm F : E → F) := by
    have : (Algebra.norm F : E → F) = fun z => (2 : F)⁻¹ * Algebra.trace F E (z * c z) := funext hN
    rw [this]
    exact continuous_const.mul (htr.comp (continuous_id.mul hc))
  have hT2 : T2Space E := (GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F E).t2
  have hinv : ∀ z : E, z⁻¹ = (Algebra.norm F z)⁻¹ • c z := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hn : Algebra.norm F z ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hz
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [Algebra.smul_def, mul_assoc, mul_comm (c z) z, ← hE.algebraMap_norm z, ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hI : ContinuousInv₀ E := by
    refine ⟨fun z hz => ?_⟩
    have : (Inv.inv : E → E) = fun z => (Algebra.norm F z)⁻¹ • c z := funext hinv
    rw [this]
    have hn : Algebra.norm F z ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hz
    exact ((continuousAt_inv₀ hn).comp hNc.continuousAt).smul hc.continuousAt
  refine ⟨hfd, inferInstance, hI, hT2, hc, hNc, htr, fun α ν _ _ => ?_⟩
  haveI hM : IsModuleTopology F (Matrix α ν E) := inferInstanceAs (IsModuleTopology F (α → ν → E))
  exact ⟨hM, GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F (Matrix α ν E)⟩
end GlobalTheory
