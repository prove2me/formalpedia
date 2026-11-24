-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.fourierInv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:25:59.823716+00:00
-- url     : https://prove2.me/submissions/40dc11fa-5ebb-4c45-a9cb-3937f8200b3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_manyChars_of_perfect
import Theorems.Thm_GlobalTheory_FourierChainCompare_manyChars_iff_exists
import Theorems.Thm_GlobalTheory_FourierChainCompare_inversion_iff
import Theorems.Thm_GlobalTheory_FourierChainCompare_coeff_chr_of_inversion
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
theorem _root_.solution : FourierInvSt ↔ FourierInversion := by
  classical
  constructor
  · intro H A B K _ _ _ _ _ e he
    haveI := finite_addChar A K
    letI := Fintype.ofFinite (AddChar A K)
    have hm := manyChars_of_perfect he
    have hinv : ∀ (φ : A → K) (a : A),
        φ a = ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t * ((e a t : Kˣ) : K) := fun φ a =>
      (inversion_iff he φ a).mp (H A K hm.1 (by rw [← Nat.card_eq_fintype_card, hm.2]) φ a)
    have hc := fun t₀ : B => coeff_chr_of_inversion he t₀ (hinv _)
    refine ⟨card_eq_of_perfect he, card_eq_of_perfect he ▸ hm.1, hinv,
      fun t₀ => ⟨by rw [hc, if_pos rfl], fun t ht => by rw [hc, if_neg ht]⟩, fun V _ _ θ t₀ => ?_⟩
    simp [onDatum, hc]
  · intro H A _ _ K _ _ h1 h2 φ a
    obtain ⟨B, _, _, e, he⟩ :=
      (manyChars_iff_exists A K).mp ⟨h1, by rw [Nat.card_eq_fintype_card, h2]⟩
    exact (inversion_iff he φ a).mpr ((H A B K e he).2.2.1 φ a)
end GlobalTheory.FourierChainCompare
