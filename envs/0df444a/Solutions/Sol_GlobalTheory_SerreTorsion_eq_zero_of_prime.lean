-- Prove2me | solution 1 for GlobalTheory.SerreTorsion.eq_zero_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:28:41.001644+00:00
-- url     : https://prove2.me/submissions/f7874f0b-f23e-44ef-9308-46dac3d885d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
import Theorems.Thm_GlobalTheory_SerreTorsion_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.SerreTorsion
variable {E : Type} [Ring E]
namespace GlobalTheory.SerreTorsion
theorem _root_.solution (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c l : ℕ}
    (hq : q.Prime) (hsep : ∀ x : E, (∀ k : ℕ, ∃ y : E, x = q ^ k • y) → x = 0)
    (hl : l.Prime) (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (ψ : E)
    (h : (1 + c • ψ) ^ l = 1) : ψ = 0 := by
  apply hsep
  intro k
  induction k with
  | zero => exact ⟨ψ, by simp⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih
    have h' : (1 + (c * q ^ k) • y) ^ l = 1 := by rw [mul_smul, ← hy, h]
    obtain ⟨w, hw⟩ := step htf hq hl (mul_ne_zero hc0 (pow_ne_zero k hq.ne_zero))
      (hqc.mul_right _) (fun hq2 => (h2 hq2).mul_right _) y h'
    exact ⟨w, by rw [hy, hw, pow_succ, mul_smul]⟩
end GlobalTheory.SerreTorsion
