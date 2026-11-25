-- Prove2me | solution 1 for GlobalTheory.MainToRows.rows_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:28:32.629164+00:00
-- url     : https://prove2.me/submissions/d1cbe5f6-6374-47ad-8ba3-be79f5cf44c0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open scoped BigOperators
open Classical MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open GlobalTheory GlobalTheory.MainToRows
variable {C : Type} [Field C]
namespace GlobalTheory.MainToRows
theorem _root_.solution (V : VF C) (i n0 : ℕ) :
    ∑ ρ : Fin n0, rename (rowE ρ) (mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0)) =
      -((V.l : C) ^ (expE V.l i))⁻¹ • (∑ b : Fin n0, ∑ c : Fin n0,
        (X (Sum.inl (b, c)) ^ (V.l ^ i) * X (Sum.inr (b, c)) : MvPowerSeries (PVar n0) C)) := by
  unfold mainM
  refine Eq.trans (Finset.sum_congr rfl fun ρ _ => ?_) (Finset.smul_sum).symm
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_smul, map_sum,
    map_mul, map_pow, rename_X, neg_smul, one_smul, map_neg, Finset.sum_neg_distrib, smul_neg]
  rfl
end GlobalTheory.MainToRows
