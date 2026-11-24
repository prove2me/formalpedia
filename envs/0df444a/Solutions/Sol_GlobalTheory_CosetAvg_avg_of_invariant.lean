-- Prove2me | solution 1 for GlobalTheory.CosetAvg.avg_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:43.033858+00:00
-- url     : https://prove2.me/submissions/ae7b4489-84d2-4d1e-bd49-ca76c27ea06e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTranslatesEqDoubleCosetAverage
import Theorems.Thm_GlobalTheory_CosetAvg_orbit_sum

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
theorem _root_.solution {H X M ι : Type*} [Group H] [Fintype H] [MulAction H X]
    [AddCommGroup M] [Module ℂ M] (s : Finset ι) (y : ι → X) [∀ i, Fintype (orbit H (y i))]
    (F : ι → X → M) (hinv : ∀ h : H, ∑ i ∈ s, F i (h • y i) = ∑ i ∈ s, F i (y i)) :
    ∑ i ∈ s, F i (y i) =
      ∑ i ∈ s, ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hO : ∀ i, (Fintype.card (orbit H (y i)) : ℂ) ≠ 0 := fun i => by
    haveI : Nonempty (orbit H (y i)) := ⟨⟨y i, mem_orbit_self _⟩⟩
    exact_mod_cast Fintype.card_ne_zero
  have key : ∀ i, ∑ h : H, F i (h • y i) = (Fintype.card H : ℂ) •
      ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by
    intro i
    rw [smul_comm (Fintype.card H : ℂ), ← orbit_sum, smul_smul, inv_mul_cancel₀ (hO i), one_smul]
  apply smul_right_injective M hH
  simp only
  calc (Fintype.card H : ℂ) • ∑ i ∈ s, F i (y i) = ∑ _h : H, ∑ i ∈ s, F i (y i) := by
        rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    _ = ∑ h : H, ∑ i ∈ s, F i (h • y i) := Finset.sum_congr rfl (fun h _ => (hinv h).symm)
    _ = ∑ i ∈ s, ∑ h : H, F i (h • y i) := Finset.sum_comm
    _ = _ := by rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _ => key i)
end GlobalTheory.CosetAvg
