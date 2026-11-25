-- Prove2me | solution 1 for GlobalTheory.RowValueCheck.Agree.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:29:29.792151+00:00
-- url     : https://prove2.me/submissions/971e6a9b-7596-4f92-882d-fae56722f1dd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep
import Theorems.Thm_GlobalTheory_RowValueCheck_Agree_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


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
theorem _root_.solution {σ : Type} {S : Set σ} {F F' : MvPowerSeries σ C} (h : Agree S F F') (k : ℕ) :
    Agree S (F ^ k) (F' ^ k) := by
  induction k with
  | zero => intro μ _; simp
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h
end Agree
end GlobalTheory.RowValueCheck
