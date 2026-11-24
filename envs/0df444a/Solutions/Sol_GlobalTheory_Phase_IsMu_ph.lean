-- Prove2me | solution 1 for GlobalTheory.Phase.IsMu.ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:26:03.702835+00:00
-- url     : https://prove2.me/submissions/8f72ecbf-fdf9-40ba-851a-3133e01ff425

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Theorems.Thm_GlobalTheory_Phase_IsMu_norm_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open GlobalTheory.SW
open GlobalTheory GlobalTheory.Phase
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
variable {n g : ℕ}
namespace GlobalTheory.Phase
namespace IsMu
theorem _root_.solution {a : ℂ} (ha : IsMu a) : Ph a := by
  obtain ⟨m, hm, h⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [IsMu.norm_eq_one ⟨m, hm, h⟩, Complex.ofReal_one, one_pow, h]
end IsMu
end GlobalTheory.Phase
