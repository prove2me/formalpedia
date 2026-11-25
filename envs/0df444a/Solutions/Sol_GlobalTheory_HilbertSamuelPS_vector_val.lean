-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.vector_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:15.374812+00:00
-- url     : https://prove2.me/submissions/dc2aef8c-5a44-46ce-8dd3-03c6d69c279f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_pow__4340d25ca8f4
import Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_prod_X_pow__790a47b3fadf
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_of_lt
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_of_not_lt
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_zero
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_mul
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_pow
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_firstIdx_spec
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_val_eq

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
  {φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)} {x : Fin D → A} {c : Fin D → ℂ}
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution (hx : ∀ j i, φ j (x i) = MvPowerSeries.X i + MvPowerSeries.C (c i))
    {m : ℕ} (hm : m ≠ 0) {b : A} (hb : ∃ k, evalAt φ k b ≠ 0) {e : Fin D →₀ ℕ}
    (he : lexOrder (evalAt φ (firstIdx φ b) b) = ((toLex e : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))))
    (a : Fin D → ℕ) :
    b ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ a d ≠ 0 ∧
    val φ (b ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ a d) =
      toLex (firstIdx φ b, ((toLex (m • e + ∑ d, Finsupp.single d (a d)) : Lex (Fin D →₀ ℕ)) :
        WithTop (Lex (Fin D →₀ ℕ)))) := by
  obtain ⟨hb1, hb2⟩ := firstIdx_spec φ hb
  set k := firstIdx φ b
  have hkn : k < n := by
    by_contra h; exact hb1 (evalAt_of_not_lt φ h b)
  have hP : evalAt φ k (∏ d, (x d - algebraMap ℂ A (c d)) ^ a d) = ∏ d, (X d : MvPowerSeries (Fin D) ℂ) ^ a d := by
    rw [evalAt_of_lt φ hkn]
    simp [map_prod, hx, MvPowerSeries.algebraMap_apply]
  set w := b ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ a d with hw
  have hwk : evalAt φ k w = evalAt φ k b ^ m * ∏ d, (X d : MvPowerSeries (Fin D) ℂ) ^ a d := by
    rw [hw, evalAt_mul, evalAt_pow φ _ _ hm, hP]
  have hlex : lexOrder (evalAt φ k w) = ((toLex (m • e + ∑ d, Finsupp.single d (a d)) : Lex (Fin D →₀ ℕ)) :
        WithTop (Lex (Fin D →₀ ℕ))) := by
    rw [hwk, lexOrder_mul, lexOrder_pow' he, lexOrder_prod_X_pow', ← WithTop.coe_add, ← toLex_add]
  have hne : evalAt φ k w ≠ 0 := by
    rw [ne_eq, ← lexOrder_eq_top_iff_eq_zero, hlex]; exact WithTop.coe_ne_top
  have hlt : ∀ i < k, evalAt φ i w = 0 := by
    intro i hi
    rw [hw, evalAt_mul, evalAt_pow φ _ _ hm, hb2 i hi, zero_pow hm, zero_mul]
  refine ⟨fun h0 => hne (by rw [h0, evalAt_zero]), ?_⟩
  rw [val_eq φ hne hlt, hlex]
end GlobalTheory.HilbertSamuelPS
