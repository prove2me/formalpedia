-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_size_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:29:59.70368+00:00
-- url     : https://prove2.me/submissions/715ab5e9-d046-46d1-8b30-f599312bfa9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_exists_sq_le_be

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ μ, A.size μ ^ 2 ≤ C * A.be μ μ := by
  choose c hc0 hc using fun i => A.exists_sq_le_be ((Module.Free.chooseBasis ℤ A.X).coord i)
  have h0 : 0 ≤ (Fintype.card (Module.Free.ChooseBasisIndex ℤ A.X) : ℝ) * ∑ i, (c i : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => by exact_mod_cast hc0 i)
  refine ⟨(Fintype.card (Module.Free.ChooseBasisIndex ℤ A.X) : ℝ) * ∑ i, (c i : ℝ) + 1, by linarith, fun μ => ?_⟩
  have hb : (0 : ℝ) ≤ A.be μ μ := by exact_mod_cast A.be_self_nonneg μ
  refine sq_sum_le_card_mul_sum_sq.trans ?_
  rw [add_mul, mul_assoc, Finset.sum_mul, Finset.card_univ]
  refine le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _))
    (by linarith)
  rw [sq_abs]
  exact_mod_cast hc i μ
end GlobalTheory.AnArc
