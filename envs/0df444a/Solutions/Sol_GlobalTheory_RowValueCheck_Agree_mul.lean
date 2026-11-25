-- Prove2me | solution 1 for GlobalTheory.RowValueCheck.Agree.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:23.634825+00:00
-- url     : https://prove2.me/submissions/d2f6699a-503f-47f7-843e-0381076e0b8a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep

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
theorem _root_.solution {σ : Type} {S : Set σ} {F F' K K' : MvPowerSeries σ C} (h : Agree S F F')
    (h' : Agree S K K') : Agree S (F * K) (F' * K') := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have e : p.1 + p.2 = μ := by simpa using hp
  rw [h p.1 fun x hx => hμ x (by rw [← e]; simp; omega),
    h' p.2 fun x hx => hμ x (by rw [← e]; simp; omega)]
end Agree
end GlobalTheory.RowValueCheck
