-- Prove2me | solution 1 for GlobalTheory.PeriodLift.hermC_emb_inv_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:49.406924+00:00
-- url     : https://prove2.me/submissions/90f613a2-16ac-4f1f-bdee-dc445c190a45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PeriodCoordinatesFramesLiftTendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix
open GlobalTheory GlobalTheory.PeriodLift
namespace GlobalTheory.PeriodLift
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (u : Fin r → ℂ) (k : Fin r) :
    hermC τ G u (Data.emb τ fun b => cc (G⁻¹ b k)) = u k := by
  have e : ∀ a, ∑ b, u a * τ (G a b) * (starRingEnd ℂ) (τ (cc (G⁻¹ b k))) =
      u a * τ ((G * G⁻¹) a k) := by
    intro a
    rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cc, IsCMField.complexEmbedding_complexConj, Complex.conj_conj, map_mul, mul_assoc]
  simp only [hermC, Data.emb, e]
  rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hG)]
  simp [Matrix.one_apply, apply_ite τ]
end GlobalTheory.PeriodLift
