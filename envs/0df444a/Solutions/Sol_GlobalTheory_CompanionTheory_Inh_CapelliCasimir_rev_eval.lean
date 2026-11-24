-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CapelliCasimir.rev_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:38.782793+00:00
-- url     : https://prove2.me/submissions/0ac9ca76-f3b3-4759-be67-52dddfef338b

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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → ℂ) (t : ℂ) (ht : t ≠ 0) :
    (rev s f).eval t = t ^ s.card * ∏ l ∈ s, (t⁻¹ + f l) := by
  rw [rev, eval_prod, ← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  simp; field_simp
end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
