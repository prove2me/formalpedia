-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Heis.mem_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:49:57.664095+00:00
-- url     : https://prove2.me/submissions/ab66a6e9-45b1-48a3-9817-495c66bbcabe

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
import Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_mem_root_iff
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mem_KU_iff
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
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.Heis
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ 3) :
    g ∈ KU σ 3 ⊓ rootU σ ![0, 0, 0] ↔
      ∃ x ∈ intL L, ∃ y ∈ intL L, y + σ y + x * σ x = 0 ∧ mat g = Heisenberg₂ σ x y := by
  rw [Subgroup.mem_inf, mem_root_iff hσ, mem_KU_iff hv]
  constructor
  · rintro ⟨h, x, y, hr, e⟩
    refine ⟨x, ?_, y, ?_, hr, e⟩
    · simpa [e, Heisenberg₂] using h 0 1
    · simpa [e, Heisenberg₂] using h 0 2
  · rintro ⟨x, hx, y, hy, hr, e⟩
    refine ⟨fun i j => ?_, x, y, hr, e⟩
    have hx' : σ x ∈ intL L := by
      show Valued.v (σ x) ≤ 1
      rw [hv]; exact hx
    rw [e]
    fin_cases i <;> fin_cases j <;> simp [Heisenberg₂, hx, hy, hx', one_mem, zero_mem]
end GlobalTheory.SatakeWeyl.Heis
