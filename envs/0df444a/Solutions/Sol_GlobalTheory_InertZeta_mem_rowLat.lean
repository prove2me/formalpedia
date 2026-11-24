-- Prove2me | solution 1 for GlobalTheory.InertZeta.mem_rowLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:29:29.193812+00:00
-- url     : https://prove2.me/submissions/d3702e93-61a8-436a-9961-3a5278286c8c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution {ι : Type} [Fintype ι] {M : Matrix ι (Fin n) L} {w : Fin n → L} :
    w ∈ rowLat M ↔ ∃ ρ : ι → L, (∀ i, ρ i ∈ intL L) ∧ w = ρ ᵥ* M := by
  rw [rowLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (c i).2, by rw [Matrix.vecMul_eq_sum]; rfl⟩
  · rintro ⟨ρ, h, rfl⟩
    exact ⟨fun i => ⟨ρ i, h i⟩, by rw [Matrix.vecMul_eq_sum]; rfl⟩
end GlobalTheory.InertZeta
