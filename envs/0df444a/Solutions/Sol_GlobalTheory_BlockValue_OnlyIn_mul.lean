-- Prove2me | solution 1 for GlobalTheory.BlockValue.OnlyIn.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:54:21.811942+00:00
-- url     : https://prove2.me/submissions/dcd12af3-ea50-4e7d-96f7-a2f6714d3dee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
open GlobalTheory GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.BlockValue
namespace OnlyIn
theorem _root_.solution {S : σ → Prop} {f g : MvPowerSeries σ C} (hf : OnlyIn S f) (hg : OnlyIn S g) :
    OnlyIn S (f * g) := by
  classical
  intro m hm x hx
  rw [MvPowerSeries.coeff_mul] at hm
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp] at hx
  rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h
  · exact hf _ (left_ne_zero_of_mul hne) x h
  · exact hg _ (right_ne_zero_of_mul hne) x h
end OnlyIn
end GlobalTheory.BlockValue
