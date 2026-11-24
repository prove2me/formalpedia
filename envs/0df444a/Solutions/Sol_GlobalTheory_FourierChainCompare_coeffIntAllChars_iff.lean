-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.coeffIntAllChars_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:10:15.82654+00:00
-- url     : https://prove2.me/submissions/0b253a2c-f77e-4d7b-a512-cdb6b6dfcd9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_manyChars_of_perfect
import Theorems.Thm_GlobalTheory_FourierChainCompare_manyChars_iff_exists
import Theorems.Thm_GlobalTheory_FourierChainCompare_denominators_iff
import Theorems.Thm_GlobalTheory_FourierChainCompare_values_iff
import Theorems.Thm_GlobalTheory_FourierChainCompare_addChar_mem_valuationSubring
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one
attribute [local simp] GlobalTheory.FormalSeries.jacobian_X
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
open GlobalTheory GlobalTheory.FourierChainCompare
variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K] [Fintype A] [Fintype B]
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution : CoeffIntAllChars ↔ FourierDenominators := by
  constructor
  · intro H A B K _ _ _ _ _ e he φ
    have h1 : ∀ O : Subring K, (∀ a, φ a ∈ O) → (∀ a t, ((e a t : Kˣ) : K) ∈ O) →
        ∀ t, ((Fintype.card B : ℕ) : K) * IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t ∈ O := fun O hφ hO t =>
      (denominators_iff he O φ t).mp
        (H A K O φ (manyChars_of_perfect he) hφ ((values_iff he O).mpr hO) (chr he t))
    refine ⟨h1, fun O hφ => ?_⟩
    have h2 : ∀ t, ((Fintype.card B : ℕ) : K) * IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t ∈ O :=
      h1 O.toSubring hφ fun a t => addChar_mem_valuationSubring O (chr he t) a
    refine ⟨h2, fun hu t => ?_⟩
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have h3 : (v : K) * ((Fintype.card B : ℕ) : K) = 1 := by
      simpa using congrArg (fun x : O => (x : K)) hv
    have h4 := O.mul_mem _ _ v.2 (h2 t)
    rwa [← mul_assoc, h3, one_mul] at h4
  · intro H A _ _ K _ O φ hm hφ hχ χ
    obtain ⟨B, _, _, e, he⟩ := (manyChars_iff_exists A K).mp hm
    obtain ⟨t, rfl⟩ := (chrEquiv he).surjective χ
    exact (denominators_iff he O φ t).mpr
      ((H A B K e he φ).1 O hφ ((values_iff he O).mp hχ) t)
end GlobalTheory.FourierChainCompare
