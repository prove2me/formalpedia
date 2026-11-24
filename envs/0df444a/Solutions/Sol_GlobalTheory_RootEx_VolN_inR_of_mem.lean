-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.inR_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:03:16.066041+00:00
-- url     : https://prove2.me/submissions/eca691fc-7839-4521-a946-e65e67d23276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_val_embX
import Theorems.Thm_GlobalTheory_RootEx_VolN_exists_of_mem_R

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ R k n c p) : InR p g := by
  obtain ⟨x, u, hu, rfl⟩ := exists_of_mem_R hg
  rw [mem_N_iff] at hu
  rintro (r | r) (s | s) h h'
  · simp at h'
  · have : ∀ t, u.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
      simpa using hu (Sum.inl t) (Sum.inr s) h
    simp [val_embX, Matrix.mul_apply, this]
  · rw [← hu _ _ h]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]
  · rw [← hu _ _ h]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]
end GlobalTheory.RootEx.VolN
