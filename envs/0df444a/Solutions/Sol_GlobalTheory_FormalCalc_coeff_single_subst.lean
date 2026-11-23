-- Prove2me | solution 1 for GlobalTheory.FormalCalc.coeff_single_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:03.178534+00:00
-- url     : https://prove2.me/submissions/bdf7e25d-662c-45a9-b1f5-1d2393121c68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_C__c5547c7a475b
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalCalc
namespace GlobalTheory.FormalCalc
theorem _root_.solution {σ τ R : Type*} [CommRing R] [Fintype σ]
    {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ R) (j : τ) :
    coeff (Finsupp.single j 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single j 1) (a s) := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have hsplit : f = C (constantCoeff f) + ∑ s, C (coeff (Finsupp.single s 1) f) * X s +
      (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s) := by ring
  have hlow : ∀ e : σ →₀ ℕ, Finsupp.degree e < 2 →
      coeff e (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s) = 0 := by
    intro e he
    have hle : Finsupp.degree e ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain rfl : e = 0 := (Finsupp.degree_eq_zero_iff e).mp h0
      simp [coeff_zero_X, coeff_zero_eq_constantCoeff_apply]
    · have hr : e ∈ Set.range (fun t : σ => Finsupp.single t 1) := by
        rw [Finsupp.range_single_one]; exact h1
      obtain ⟨t, rfl⟩ := hr
      simp [coeff_X, coeff_C, Finsupp.single_eq_single_iff]
  have hord : coeff (Finsupp.single j 1)
      (subst a (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s)) = 0 := by
    apply coeff_of_lt_order
    have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
      le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.mpr (ha0 i)
    have h2 : (2 : ℕ∞) ≤
        (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s).order :=
      le_order fun e he => hlow e (by exact_mod_cast he)
    calc ((Finsupp.degree (Finsupp.single j 1) : ℕ) : ℕ∞) < 2 := by
          rw [Finsupp.degree_single]; norm_num
      _ = 1 * 2 := by norm_num
      _ ≤ _ := mul_le_mul' h1 h2
      _ ≤ _ := le_order_subst ha _
  have hexp : subst a f = subst a (C (constantCoeff f)) +
      subst a (∑ s, C (coeff (Finsupp.single s 1) f) * X s) +
      subst a (f - C (constantCoeff f) - ∑ s, C (coeff (Finsupp.single s 1) f) * X s) := by
    conv_lhs => rw [hsplit]
    rw [subst_add ha, subst_add ha]
  rw [hexp, map_add, map_add, hord, add_zero, subst_C' ha, subst_sum' ha, map_sum]
  simp [subst_mul ha, subst_C' ha, subst_X ha, coeff_C_mul, coeff_C]
end GlobalTheory.FormalCalc
