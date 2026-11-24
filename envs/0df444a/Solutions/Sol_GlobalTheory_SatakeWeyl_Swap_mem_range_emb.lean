-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Swap.mem_range_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:31:05.782828+00:00
-- url     : https://prove2.me/submissions/bf66c287-74d0-462b-8975-889056b1ae4f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffAdjacentSwapOfLeviReduction
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Swap
namespace GlobalTheory.SatakeWeyl.Swap
theorem _root_.solution {n i : ℕ} (h : 2 * i + 4 ≤ n) (a : Fin n) :
    a ∈ Set.range (emb n i h) ↔ a.val = i ∨ a.val = i + 1 ∨ a.val = n - 2 - i ∨ a.val = n - 1 - i := by
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [emb]
  · rintro (h1 | h1 | h1 | h1)
    exacts [⟨0, Fin.ext h1.symm⟩, ⟨1, Fin.ext h1.symm⟩, ⟨2, Fin.ext h1.symm⟩, ⟨3, Fin.ext h1.symm⟩]
end GlobalTheory.SatakeWeyl.Swap
