-- Prove2me | solution 1 for GlobalTheory.MinorGerm.low_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:16:18.338896+00:00
-- url     : https://prove2.me/submissions/71b52126-a452-4766-8f41-d9ff764f0a37

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_low_one
import Theorems.Thm_GlobalTheory_MinorGerm_Low_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}
namespace GlobalTheory.MinorGerm
theorem _root_.solution {ι : Type} (s : Finset ι) (α : ι → σ →₀ ℕ) (g : ι → MvPowerSeries σ C)
    (h : ∀ i ∈ s, Low (α i) (g i)) : Low (∑ i ∈ s, α i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (low_one : Low (0 : σ →₀ ℕ) (1 : MvPowerSeries σ C))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
end GlobalTheory.MinorGerm
