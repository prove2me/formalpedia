-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CapelliCasimir.sum_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:40.131388+00:00
-- url     : https://prove2.me/submissions/aa9f35c1-2c00-426a-9e6c-70aed1b8cb8e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_CasOfCapelliVec

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
theorem _root_.solution {A : Type} [AddCommGroup A] [Module ℂ A] {n : ℕ} (x : Fin n → A) :
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (x i - x j)
      = ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • x i := by
  simp only [sum_sub_distrib]
  have : ∑ i, ∑ j ∈ univ.filter (fun j => i < j), x j
      = ∑ j, ∑ i ∈ univ.filter (fun i => i < j), x j := by
    simp only [sum_filter]; exact sum_comm
  rw [this, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_const, sum_const, filter_lt_eq_Ioi, filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
  congr 1
  have := i.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring
end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
