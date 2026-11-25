-- Prove2me | solution 1 for GlobalTheory.DenseCompl.continuous_of_valued_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:44:45.628673+00:00
-- url     : https://prove2.me/submissions/2f9dce2d-2040-4047-8d73-2e59498c84d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousOfValuationEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqZeroOfForallLeExp
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain
open WithZero
open GlobalTheory GlobalTheory.DenseCompl
namespace GlobalTheory.DenseCompl
theorem _root_.solution {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx
end GlobalTheory.DenseCompl
