-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CapelliCasimir.sq_sub_cas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:48.224854+00:00
-- url     : https://prove2.me/submissions/d0451deb-618f-4aef-be68-5b5416879918

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_CasOfCapelliVec
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CapelliCasimir_sum_sq_split
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CapelliCasimir_sum_diff

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
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) :
    (∑ i, E i i) * (∑ i, E i i) - Formalism.REAL.Cas E
      = (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i := by
  rw [← sum_diff, Formalism.REAL.Cas, sum_mul_sum, ← sum_sub_distrib]
  simp only [← sum_sub_distrib]
  rw [sum_sq_split]
  simp only [sub_self, sum_const_zero, zero_add, smul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := (mem_filter.1 hj).2.ne
  have h1 := hE i j j i
  have h2 := hE i i j j
  simp only [if_true, hij, hij.symm, if_false, sub_zero] at h1 h2
  rw [two_smul, ← h1, ← sub_eq_zero.1 h2]
  abel
end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
