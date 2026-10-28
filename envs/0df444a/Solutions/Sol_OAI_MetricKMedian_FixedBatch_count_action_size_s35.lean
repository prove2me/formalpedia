-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.count_action_size_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:00:29.301996+00:00
-- url     : https://prove2.me/submissions/16b68977-9083-4a59-9f84-50817f6d4e8f

import Mathlib
import Definitions.Def_OAIQ035K021

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

theorem mass_mono {g : ℝ} {S T : Finset I} (hg : 0 ≤ g) (hST : S ⊆ T) :
    mass g S ≤ mass g T := by
  apply mul_le_mul_of_nonneg_left _ hg
  exact_mod_cast Finset.card_le_card hST

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_UnbalancedActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

omit [Fintype I] [Fintype E] in
 theorem countErase_subset (D : Actions I E) (Δ : ℕ) (e : E) : countErase D Δ e ⊆ D.erase e := by
  unfold countErase
  split_ifs
  · exact empty_subset _
  · exact Subset.rfl

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

omit [Fintype I] [Fintype E] in
theorem countOpening_le_one (D : Actions I E) (Δ : ℕ) (e : E) : countOpening D Δ e ≤ 1 := by
  unfold countOpening
  split_ifs <;> norm_num

 theorem heavy_action_mass_le (G : I → Finset I) (H : Finset I) {g B : ℝ}
    (hgB : g ≤ B) (hB : ∀ h, h ∉ H → mass g ((graphActions G).erase h) ≤ B)
    (e : HeavyAction (graphActions G) H) : mass g ((heavyActions (graphActions G) H).erase e) ≤ B := by
  cases e with
  | inl e => exact hB e e.property
  | inr e => simpa only [heavyActions,Sum.elim_inr,mass,card_singleton,Nat.cast_one,mul_one] using hgB

 theorem count_action_size_s35_oai (G : I → Finset I) (H : Finset I) {Δ : ℕ} {g B : ℝ}
    (hg : 0 ≤ g) (hgB : g ≤ B) (hB : ∀ h, h ∉ H → mass g ((graphActions G).erase h) ≤ B)
    (e : HeavyAction (graphActions G) H) :
    countOpening (heavyActions (graphActions G) H) Δ e+
      mass g (countErase (heavyActions (graphActions G) H) Δ e) ≤ B+2 := by
  have hm := (mass_mono hg (countErase_subset (heavyActions (graphActions G) H) Δ e)).trans
    (heavy_action_mass_le G H hgB hB e)
  have ha := countOpening_le_one (heavyActions (graphActions G) H) Δ e
  linarith only [ha,hm]

end MetricKMedian.FixedBatch
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.FixedBatch.count_action_size_s35_oai.{u_1} := @OAI.MetricKMedian.FixedBatch.count_action_size_s35_oai.{u_1}
