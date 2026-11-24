-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CapelliCasimir.rev_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:37.332913+00:00
-- url     : https://prove2.me/submissions/ce7d1370-b4ec-489f-9d05-19bd8a3c1134

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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    (rev s f).coeff 0 = 1 ∧ (rev s f).coeff 1 = ∑ l ∈ s, f l ∧
      2 * (rev s f).coeff 2 = (∑ l ∈ s, f l) ^ 2 - ∑ l ∈ s, f l ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rev, coeff_one]
  | insert a s ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have c1 : ∀ p : ℂ[X], (X * p).coeff 1 = p.coeff 0 := fun p => coeff_X_mul p 0
    have c2 : ∀ p : ℂ[X], (X * p).coeff 2 = p.coeff 1 := fun p => coeff_X_mul p 1
    have : rev (insert a s) f = rev s f + C (f a) * (X * rev s f) := by
      simp only [rev, prod_insert ha]; ring
    rw [this, sum_insert ha, sum_insert ha]
    simp only [coeff_add, coeff_C_mul]
    refine ⟨?_, ?_, ?_⟩
    · simp [h0]
    · rw [c1, h0, h1]; ring
    · rw [c2, h1]
      linear_combination h2
end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
