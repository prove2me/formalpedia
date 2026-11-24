-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cvalR_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:36.244798+00:00
-- url     : https://prove2.me/submissions/b0d52193-976a-4798-ba9f-4fadda3a4401

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_CasOfCapelliVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rho_eq_rhoC_add_rhoN


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Inh GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Polynomial
namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) :
    ((Formalism.REAL.cvalR ε lam : ℝ) : ℂ)
      = ∑ l, (lam l : ℂ) ^ 2 - ∑ l : Fin n, (((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ)) ^ 2 := by
  have h : Formalism.REAL.rhoC ε + Formalism.REAL.rhoN ε = ReciprocityTheory.ChartRestriction.DS.rho n :=
    (ReciprocityTheory.ChartRestriction.DS.rho_eq_rhoC_add_rhoN ε).symm
  rw [Formalism.REAL.cvalR, h]
  simp only [Formalism.REAL.nsq, Formalism.REAL.dot, ReciprocityTheory.ChartRestriction.DS.rho]
  push_cast
  congr 1 <;> refine sum_congr rfl fun l _ => ?_ <;> ring
end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
