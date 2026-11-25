-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.tateModule_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:50:40.926065+00:00
-- url     : https://prove2.me/submissions/fc03905c-b9c0-4f62-a7d3-8eff610f1840

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FormalGroupTorsionCharts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing TensorProduct ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
universe u v
variable {R₀ : Type u} [CommRing R₀]
variable {k : LAlg R₀}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
theorem _root_.solution (B : BX R₀) (p : ℕ) (O : LAlg R₀) (τ : ℕ → B.G O)
    (hτ : τ ∈ tateModule B p O) : τ 0 = 0 ↔ ∃ τ' ∈ tateModule B p O, τ = p • τ' := by
  constructor
  · intro h0
    have key : ∀ n, p ^ n • τ n = τ 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, mul_smul, ← hτ.2 n, ih]
    exact ⟨fun n => τ (n + 1), ⟨fun n => by rw [key, h0], fun n => hτ.2 (n + 1)⟩,
      funext fun n => hτ.2 n⟩
  · rintro ⟨τ', h', rfl⟩
    simpa using h'.1 0
end GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
