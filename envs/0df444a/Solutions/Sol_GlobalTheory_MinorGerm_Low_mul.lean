-- Prove2me | solution 1 for GlobalTheory.MinorGerm.Low.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:59:44.731302+00:00
-- url     : https://prove2.me/submissions/84baaa9b-24af-46ed-882a-38e3b11c0c74

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_Low_term

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
theorem _root_.solution {α β : σ →₀ ℕ} {g h : MvPowerSeries σ C} (hg : Low α g) (hh : Low β h) :
    Low (α + β) (g * h) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (α, β)]
    · rw [hg.1, hh.1, mul_one]
    · intro q hq hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
      apply hg.term hh
      · have h := congrArg Finsupp.degree hq
        rw [map_add, map_add] at h
        omega
      · exact hne
    · intro h
      exact (h (Finset.HasAntidiagonal.mem_antidiagonal.2 rfl)).elim
  · intro m hm hne
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    apply hg.term hh
    · have h := congrArg Finsupp.degree hq
      rw [map_add] at h hm
      omega
    · intro h
      apply hne
      rw [Prod.mk.injEq] at h
      rw [← hq, h.1, h.2]
end Low
end GlobalTheory.MinorGerm
