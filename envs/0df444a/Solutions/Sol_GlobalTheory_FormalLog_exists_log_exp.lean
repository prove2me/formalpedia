-- Prove2me | solution 1 for GlobalTheory.FormalLog.exists_log_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:55.388819+00:00
-- url     : https://prove2.me/submissions/4fea2247-152e-424c-978b-f175c28f7ffd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalCompApplyEqMvPowerSeriesSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOrSingleOfDegreeLeOne
import Theorems.Thm_GlobalTheory_FormalLog_eq_zero_or_single_of_degree_le_one
import Theorems.Thm_GlobalTheory_ChartInv_exists_isInvPair
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inr
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_logSt_and_logDerivSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inl
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inr



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog
namespace GlobalTheory.FormalLog
theorem _root_.solution :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d), ∃ lg ex : Pt k 1 d, (∀ i (μ : Fin 1 × Fin d →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS k 1 d)) ∧ (∀ i, ev (n := 2) ![addOf G.F (pt k d 0) (pt k d 1)] (lg i) = ev (n := 2) ![pt k d 0] (lg i) + ev (n := 2) ![pt k d 1] (lg i)) ∧ (∀ i, MvPowerSeries.constantCoeff (ex i) = 0) ∧ comp1 lg ex = pt k d 0 ∧ comp1 ex lg = pt k d 0 := by
  intro k _ _ d G
  obtain ⟨lg, h0, h1, hadd⟩ := logSt_and_logDerivSt.1 k d G
  obtain ⟨ex, -, he, ha, hb⟩ := GlobalTheory.ChartInv.exists_isInvPair k d lg h0 (by rw [h1]; simp)
  refine ⟨lg, ex, ?_, fun i => congrFun hadd i, he, ha, hb⟩
  intro i μ hμ
  rcases eq_zero_or_single_of_degree_le_one μ hμ with rfl | ⟨⟨a, j⟩, rfl⟩
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0, MvPowerSeries.coeff_zero_X]
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    have hc := congrFun (congrFun h1 i) j
    simp only [dLin] at hc
    rw [hc, MvPowerSeries.coeff_X, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · have : Finsupp.single ((0 : Fin 1), j) 1 ≠ Finsupp.single ((0 : Fin 1), i) 1 := by
        intro h
        have := Finsupp.single_left_injective (one_ne_zero (α := ℕ)) h
        exact hij (Prod.mk.inj this).2.symm
      rw [if_neg hij, if_neg this]
end GlobalTheory.FormalLog
