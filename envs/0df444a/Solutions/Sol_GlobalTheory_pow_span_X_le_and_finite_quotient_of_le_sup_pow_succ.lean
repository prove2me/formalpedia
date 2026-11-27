-- Prove2me | solution 1 for GlobalTheory.pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:53.854843+00:00
-- url     : https://prove2.me/submissions/f3957560-faf4-4c7c-a77a-b840910720bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PowSpanXLeAndFiniteQuotientOfLeSupPowSucc
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_quotient_of_pow_le
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (I : Ideal (MvPowerSeries σ k)) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ (M + 1) → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ I ∧ Module.Finite k (MvPowerSeries σ k ⧸ I) := by
  intro k _ σ _ I M h
  set m : Ideal (MvPowerSeries σ k) := Ideal.span (Set.range MvPowerSeries.X) with hm
  have hfg : m.FG := Submodule.fg_span (Set.finite_range _)
  have hjac : m ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hm, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hle : m ^ M ≤ I := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (N' := m ^ M) (N := I) (I := m)
      (Ideal.FG.pow hfg) hjac ?_
    rw [pow_succ'] at h
    exact h
  exact ⟨hle, FormalIsogeny.finite_quotient_of_pow_le (N := M) hle⟩
end GlobalTheory
