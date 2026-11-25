-- Prove2me | solution 1 for GlobalTheory.BlockValue.Lead.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:15:32.755595+00:00
-- url     : https://prove2.me/submissions/e6a22844-66f6-400b-a427-b617f33add24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_mul
import Theorems.Thm_GlobalTheory_BlockValue_Lead_of_coeff_zero
import Theorems.Thm_GlobalTheory_BlockValue_Lead_mul

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
namespace Lead
theorem _root_.solution {π : σ → κ} {ι : Type} (s : Finset ι) {d : ι → σ →₀ ℕ}
    {f : ι → MvPowerSeries σ C} (hf : ∀ i ∈ s, Lead π (d i) (f i)) :
    Lead π (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lead.of_coeff_zero π (by simp)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
end Lead
end GlobalTheory.BlockValue
