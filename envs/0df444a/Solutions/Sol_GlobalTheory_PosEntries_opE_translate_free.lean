-- Prove2me | solution 1 for GlobalTheory.PosEntries.opE_translate_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:36:50.324378+00:00
-- url     : https://prove2.me/submissions/6cbeb4ea-a3ea-49af-ace8-ffbef5156722

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditions
import Theorems.Thm_GlobalTheory_PosEntries_ch_add
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.PosEntries
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.PosEntries
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (p : ℕ)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k}
    (hz : ∀ r s, ¬ Free p (r, s) → z r s = 0) (hΨ : ∀ x, Ψ (x + z) = Ψ x) (x₀ : Matrix n n' k) :
    opE ψ ν p Ψ x₀ = (ψ (-ch z) : ℂ) * opE ψ ν p Ψ x₀ := by
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ez : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k := fun rs => z rs.1.1 rs.1.2
  have hpt : ∀ e, affPt p x₀ (e + ez) = affPt p x₀ e + z := by
    intro e; ext r s
    simp only [affPt, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
    split_ifs with h
    · simp only [ez]; ring
    · simp [hz r s h]
  unfold opE
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_add_right_eq_self _ ez]
  congr 1; ext e
  rw [hpt, hΨ, ch_add, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring
end GlobalTheory.PosEntries
