-- Prove2me | solution 1 for GlobalTheory.MinorGerm.Low.term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:50:06.618049+00:00
-- url     : https://prove2.me/submissions/8982872d-e5c8-4043-b168-91ac69a20736

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag

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
namespace Low
theorem _root_.solution {α β : σ →₀ ℕ} {g h : MvPowerSeries σ C} (hg : Low α g) (hh : Low β h)
    (a b : σ →₀ ℕ) (hd : a.degree + b.degree ≤ α.degree + β.degree) (hne : (a, b) ≠ (α, β)) :
    MvPowerSeries.coeff a g * MvPowerSeries.coeff b h = 0 := by
  classical
  by_cases ha : a.degree ≤ α.degree ∧ a ≠ α
  · rw [hg.2 a ha.1 ha.2, zero_mul]
  by_cases hb : b.degree ≤ β.degree ∧ b ≠ β
  · rw [hh.2 b hb.1 hb.2, mul_zero]
  exfalso
  push_neg at ha hb
  by_cases ha' : a = α
  · by_cases hb' : b = β
    · exact hne (by rw [ha', hb'])
    · have : ¬ b.degree ≤ β.degree := fun h => hb' (hb h)
      rw [ha'] at hd
      omega
  · have : ¬ a.degree ≤ α.degree := fun h => ha' (ha h)
    by_cases hb' : b = β
    · rw [hb'] at hd
      omega
    · have : ¬ b.degree ≤ β.degree := fun h => hb' (hb h)
      omega
end Low
end GlobalTheory.MinorGerm
