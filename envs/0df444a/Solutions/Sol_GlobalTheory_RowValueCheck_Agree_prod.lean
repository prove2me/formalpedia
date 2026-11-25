-- Prove2me | solution 1 for GlobalTheory.RowValueCheck.Agree.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:29:34.356284+00:00
-- url     : https://prove2.me/submissions/d3979761-eac0-4427-950c-4d36a7eaf775

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep
import Theorems.Thm_GlobalTheory_RowValueCheck_Agree_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GlobalTheory GlobalTheory.RowValueCheck
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
namespace GlobalTheory.RowValueCheck
namespace Agree
theorem _root_.solution {σ α : Type} {S : Set σ} (s : Finset α) {F F' : α → MvPowerSeries σ C}
    (h : ∀ i, Agree S (F i) (F' i)) : Agree S (∏ i ∈ s, F i) (∏ i ∈ s, F' i) := by
  induction s using Finset.induction_on with
  | empty => intro μ _; simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha]; exact (h a).mul ih
end Agree
end GlobalTheory.RowValueCheck
