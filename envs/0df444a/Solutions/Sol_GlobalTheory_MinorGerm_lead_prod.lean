-- Prove2me | solution 1 for GlobalTheory.MinorGerm.lead_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:43.891075+00:00
-- url     : https://prove2.me/submissions/b13d4879-d46d-4945-b185-542d2a57d25c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_Low_mul
import Theorems.Thm_GlobalTheory_MinorGerm_lead_one
import Theorems.Thm_GlobalTheory_MinorGerm_Lead_mul

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
variable {p : σ → Prop} [DecidablePred p]
namespace GlobalTheory.MinorGerm
theorem _root_.solution {ι : Type} (s : Finset ι) (α : ι → σ →₀ ℕ) (P : ι → MvPolynomial σ C)
    (h : ∀ i ∈ s, Lead p (α i) (P i)) : Lead p (∑ i ∈ s, α i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (lead_one (p := p) : Lead p (0 : σ →₀ ℕ) (1 : MvPolynomial σ C))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
end GlobalTheory.MinorGerm
