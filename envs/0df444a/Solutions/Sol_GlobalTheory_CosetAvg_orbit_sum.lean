-- Prove2me | solution 1 for GlobalTheory.CosetAvg.orbit_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:58:40.357293+00:00
-- url     : https://prove2.me/submissions/57c475c0-fb42-4868-9691-6fc6b3904cbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTranslatesEqDoubleCosetAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.CosetAvg
open MulAction
namespace GlobalTheory.CosetAvg
theorem _root_.solution {H X M : Type*} [Group H] [Fintype H] [MulAction H X] [AddCommGroup M]
    [Module ℂ M] (y : X) [Fintype (orbit H y)] (F : X → M) :
    (Fintype.card (orbit H y) : ℂ) • ∑ h : H, F (h • y) =
      (Fintype.card H : ℂ) • ∑ z : orbit H y, F z := by
  have h1 : ∀ z : orbit H y, ∑ h : H, F (h • (z : X)) = ∑ h : H, F (h • y) := by
    rintro ⟨z, g, rfl⟩
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => by simp [mul_smul])
  have h2 : ∀ h : H, ∑ z : orbit H y, F (h • (z : X)) = ∑ z : orbit H y, F z := by
    intro h
    exact Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun z => rfl)
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.card_univ,
    ← Finset.sum_const, ← Finset.sum_const]
  calc ∑ _z : orbit H y, ∑ h : H, F (h • y) = ∑ z : orbit H y, ∑ h : H, F (h • (z : X)) :=
        Finset.sum_congr rfl (fun z _ => (h1 z).symm)
    _ = ∑ h : H, ∑ z : orbit H y, F (h • (z : X)) := Finset.sum_comm
    _ = ∑ _h : H, ∑ z : orbit H y, F z := Finset.sum_congr rfl (fun h _ => h2 h)
end GlobalTheory.CosetAvg
