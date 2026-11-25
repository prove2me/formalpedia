-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.val_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:32.676663+00:00
-- url     : https://prove2.me/submissions/820e26ac-842e-4158-ae3a-7b47d90f3d99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_sub_smul__a846a0077eea
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_sub
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_smul
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
    (heq : val φ u = val φ v) : ∃ c : ℂ, u - c • v = 0 ∨ val φ u < val φ (u - c • v) := by
  obtain ⟨hu1, hu2⟩ := firstIdx_spec φ (exists_evalAt_ne_zero hinj hu)
  obtain ⟨hv1, hv2⟩ := firstIdx_spec φ (exists_evalAt_ne_zero hinj hv)
  unfold val at heq
  have hk : firstIdx φ u = firstIdx φ v := congrArg (fun p => (ofLex p).1) heq
  have hl : lexOrder (evalAt φ (firstIdx φ u) u) = lexOrder (evalAt φ (firstIdx φ u) v) := by
    have := congrArg (fun p => (ofLex p).2) heq
    simp only [ofLex_toLex] at this
    rw [this, hk]
  obtain ⟨c, hc⟩ := lexOrder_sub_smul' hu1 hl
  refine ⟨c, ?_⟩
  by_cases hw : u - c • v = 0
  · exact Or.inl hw
  right
  set k := firstIdx φ u with hkdef
  have e2 : ∀ i < k, evalAt φ i (u - c • v) = 0 := fun i hi => by
    rw [evalAt_sub, evalAt_smul, hu2 i hi, hv2 i (hk ▸ hi), smul_zero, sub_zero]
  have e1 : evalAt φ k (u - c • v) = evalAt φ k u - c • evalAt φ k v := by
    rw [evalAt_sub, evalAt_smul]
  obtain ⟨hw1, hw2⟩ := firstIdx_spec φ (exists_evalAt_ne_zero hinj hw)
  have hge : k ≤ firstIdx φ (u - c • v) := by
    by_contra hlt; push_neg at hlt
    exact hw1 (e2 _ hlt)
  by_cases hz : evalAt φ k (u - c • v) = 0
  · have hlt : k < firstIdx φ (u - c • v) := lt_of_le_of_ne hge (fun h => hw1 (h ▸ hz))
    unfold val
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl hlt
  · rw [val_eq φ hz e2]
    unfold val
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inr ⟨rfl, by rw [e1]; exact hc⟩
end GlobalTheory.HilbertSamuelPS
