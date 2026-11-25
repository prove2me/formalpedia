-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.val_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:13.789202+00:00
-- url     : https://prove2.me/submissions/c75cf650-e0c0-43fc-ab01-cecdf0af6e27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_add_of_lt__04023416b8fe
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_zero
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_add
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_firstIdx_spec
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_val_eq
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_exists_evalAt_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
variable {D n : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
  (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ))
variable {φ}
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution (hinj : ∀ u : A, (∀ j, φ j u = 0) → u = 0) (u v : A) (hu : u ≠ 0) (hv : v ≠ 0)
    (hlt : val φ u < val φ v) : u + v ≠ 0 ∧ val φ (u + v) = val φ u := by
  obtain ⟨hu1, hu2⟩ := firstIdx_spec φ (exists_evalAt_ne_zero hinj hu)
  obtain ⟨hv1, hv2⟩ := firstIdx_spec φ (exists_evalAt_ne_zero hinj hv)
  unfold val at hlt
  rw [Prod.Lex.toLex_lt_toLex] at hlt
  rcases hlt with hlt | ⟨heq, hlt⟩
  · dsimp only at hlt
    have e1 : evalAt φ (firstIdx φ u) (u + v) = evalAt φ (firstIdx φ u) u := by
      rw [evalAt_add, hv2 _ hlt, add_zero]
    have e2 : ∀ i < firstIdx φ u, evalAt φ i (u + v) = 0 := fun i hi => by
      rw [evalAt_add, hu2 i hi, hv2 i (hi.trans hlt), add_zero]
    refine ⟨fun h0 => hu1 (by rw [← e1, h0, evalAt_zero]), ?_⟩
    rw [val_eq φ (by rw [e1]; exact hu1) e2, e1]; rfl
  · dsimp only at heq hlt
    rw [← heq] at hlt
    have e1 : lexOrder (evalAt φ (firstIdx φ u) (u + v)) = lexOrder (evalAt φ (firstIdx φ u) u) := by
      rw [evalAt_add, lexOrder_add_of_lt' hlt]
    have hne : evalAt φ (firstIdx φ u) (u + v) ≠ 0 := by
      rw [ne_eq, ← lexOrder_eq_top_iff_eq_zero, e1, lexOrder_eq_top_iff_eq_zero]; exact hu1
    have e2 : ∀ i < firstIdx φ u, evalAt φ i (u + v) = 0 := fun i hi => by
      rw [evalAt_add, hu2 i hi, hv2 i (heq ▸ hi), add_zero]
    refine ⟨fun h0 => hne (by rw [h0, evalAt_zero]), ?_⟩
    rw [val_eq φ hne e2, e1]; rfl
end GlobalTheory.HilbertSamuelPS
