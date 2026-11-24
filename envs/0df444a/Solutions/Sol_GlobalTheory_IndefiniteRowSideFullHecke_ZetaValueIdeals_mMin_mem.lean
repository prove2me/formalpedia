-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.mMin_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:39.422016+00:00
-- url     : https://prove2.me/submissions/365a3600-6a4e-4a96-b694-ae5c0b4ecfa7

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ZetaValueIdeals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
theorem _root_.solution {l : ℕ} (hl : 1 ≤ l) (n : ℕ) : ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ mMin l n = padicValNat l (a ^ n - 1) :=
  Nat.sInf_mem (s := {m | ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ m = padicValNat l (a ^ n - 1)})
    ⟨_, l + 1, by omega, by simp, rfl⟩
end GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
