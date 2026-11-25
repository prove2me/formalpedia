-- Prove2me | solution 1 for GlobalTheory.HL.encard_eq_tsum_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:17.095471+00:00
-- url     : https://prove2.me/submissions/40ba42f8-286f-4fe2-9566-d296d6d1ce78

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {X Z : Type*} (q : X → Z) (Q : X → Prop) :
    (({x | Q x} : Set X).encard : ℝ≥0∞)
      = ∑' z : Z, (({x | q x = z ∧ Q x} : Set X).encard : ℝ≥0∞) := by
  have e : ∀ S : Set X, (S.encard : ℝ≥0∞) = ∑' x, S.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro S
    rw [← ENNReal.tsum_set_one, tsum_subtype S (fun _ => (1 : ℝ≥0∞))]
  simp only [e]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [tsum_eq_single (q x)]
  · simp [Set.indicator]
  · intro z hz
    have : ¬ q x = z := fun h => hz h.symm
    simp [Set.indicator, this]
end GlobalTheory.HL
