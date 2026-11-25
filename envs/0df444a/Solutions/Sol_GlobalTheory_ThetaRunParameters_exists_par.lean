-- Prove2me | solution 1 for GlobalTheory.ThetaRunParameters.exists_par
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:27.595268+00:00
-- url     : https://prove2.me/submissions/fe03d828-0f5c-4cf4-af8b-27d1fa17eeb0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorus
import Theorems.Thm_GlobalTheory_ThetaRunParameters_exists_large_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaRunParameters
namespace GlobalTheory.ThetaRunParameters
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ),
    2 ≤ PT.f E * r → 1 ≤ m → m ^ 4 ≤ PT.f E → (PT.f E : ℝ) ≤ PT.rd E →
    (PT.f E : ℝ) ^ 2 ≤ PT.rd E → 16 ≤ PT.rd E →
    ∃ (q : ℕ) (R0 : ℝ), 0 < th (E := E) q R0 ∧ ∀ X : PT E, X.r = r → (∃ τ, X.dim τ ≤ m) →
      ∃ P : Par X 1, P.q = q ∧ P.R0 = R0 ∧ P.m = m := by
  intro E _ _ _ r m hfr hm1 hmf hfrd hf2 hrd
  have hf : 0 < PT.f E := by
    rcases Nat.eq_zero_or_pos (PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hfR : (0 : ℝ) < PT.f E := by exact_mod_cast hf
  have hrd0 : 0 < PT.rd E := by linarith
  have hRR : 0 < RR (E := E) := by unfold RR; positivity
  set S : ℝ := 270 + 90 * (((PT.f E * r : ℕ) : ℝ) + 1) with hS
  have hS0 : 0 < S := by positivity
  have hsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0.le
  have hB : 0 < Real.sqrt S ^ 2 * RR (E := E) ^ 4 := by rw [hsq]; positivity
  have hA : 0 < PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3 := by rw [hsq]; positivity
  obtain ⟨q, hq1, hc1, hc2, hb, h5, h6⟩ := exists_large_nat (Real.sqrt S ^ 2 * RR (E := E) ^ 4)
    ((dstar (E := E) m : ℝ) ^ 2 * omStar (E := E) * (PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3))
    (M1 (E := E) m) (dstar (E := E) m)
    (((PT.f E * r : ℕ) : ℝ) * Real.log 2 + 2 * dstar (E := E) m + 3 +
      (1 + 1) * (r * Real.log r + 3 * r + 3)) hB (Nat.cast_nonneg _)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  refine ⟨q, Real.sqrt S, Real.sqrt_pos.mpr (div_pos hA hq0), ?_⟩
  intro X hX hdim
  subst hX
  refine ⟨⟨q, Real.sqrt S, m, hq1, le_rfl, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, hb, hc2,
    hq1, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [hsq, hS]
    unfold PT.gA
    have : (0 : ℝ) ≤ ((PT.f E * X.r : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor
    · linarith
    · rw [Nat.cast_one]; linarith
  · unfold th
    rw [Real.sq_sqrt (div_pos hA hq0).le, ← mul_div_assoc, div_lt_one hq0]
    exact hc1
  · unfold t0 b0
    rw [Nat.cast_one, mul_one, mul_one]
    exact h5
  · unfold t0 b0 PT.gA
    rw [Nat.cast_one]
    exact h6
end GlobalTheory.ThetaRunParameters
