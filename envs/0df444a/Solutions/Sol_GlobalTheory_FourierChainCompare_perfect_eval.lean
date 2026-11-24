-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.perfect_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:09.385807+00:00
-- url     : https://prove2.me/submissions/67cecb81-db01-49b0-bc79-0e659bbc0841

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
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
variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]
variable [Fintype A] [Fintype B]
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution (h : Nat.card (AddChar A K) = Fintype.card A) :
    IsPerfectPairing (evalPairing A K) := by
  classical
  refine ⟨fun a a' t => ?_, fun a t t' => ?_, fun a ha => ?_, fun t ht => ?_⟩
  · simp [evalPairing]
  · simp [evalPairing]
  · haveI := finite_addChar A K
    letI := Fintype.ofFinite (AddChar A K)
    have hs := (linearIndependent_addChar A K).span_eq_top_of_card_eq_finrank
      (by rw [← Nat.card_eq_fintype_card, h]; simp)
    have key : ∀ f : A → K, f a = f 0 := by
      intro f
      have hf : f ∈ Submodule.span K (Set.range fun χ : AddChar A K => (χ : A → K)) := by
        rw [hs]; trivial
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨χ, rfl⟩ := hx
        have := congrArg Units.val (ha (Additive.ofMul χ.toMonoidHom.toHomUnits))
        simpa [evalPairing] using this
      | zero => rfl
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
    by_contra hne
    have := key (fun b => if b = 0 then 1 else 0)
    simp [hne] at this
  · ext a
    exact congrArg Units.val (ht (Multiplicative.toAdd a))
end GlobalTheory.FourierChainCompare
