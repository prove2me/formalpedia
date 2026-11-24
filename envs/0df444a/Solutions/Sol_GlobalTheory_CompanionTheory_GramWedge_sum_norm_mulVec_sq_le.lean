-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GramWedge.sum_norm_mulVec_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:34.181062+00:00
-- url     : https://prove2.me/submissions/48857ac2-7618-4485-b5a0-bbd62c7bc900

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityInfinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_GramWedge_norm_entry_le_sz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GramWedge
namespace GlobalTheory.CompanionTheory.GramWedge
theorem _root_.solution {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (v : ι → ℂ) :
    ∑ a, ‖(g *ᵥ v) a‖ ^ 2 ≤
      (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
  have row : ∀ a, ‖(g *ᵥ v) a‖ ^ 2 ≤ (Fintype.card ι : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
    intro a
    have h1 : ‖(g *ᵥ v) a‖ ≤ sz g * ∑ b, ‖v b‖ := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_entry_le_sz g a b) (norm_nonneg _)
    have h2 : (∑ b, ‖v b‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ b, ‖v b‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun b => ‖v b‖)
    calc ‖(g *ᵥ v) a‖ ^ 2 ≤ (sz g * ∑ b, ‖v b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = sz g ^ 2 * (∑ b, ‖v b‖) ^ 2 := mul_pow _ _ _
      _ ≤ sz g ^ 2 * ((Fintype.card ι : ℝ) * ∑ b, ‖v b‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  calc ∑ a, ‖(g *ᵥ v) a‖ ^ 2
      ≤ ∑ _a : ι', (Fintype.card ι : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := Finset.sum_le_sum fun a _ => row a
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
end GlobalTheory.CompanionTheory.GramWedge
