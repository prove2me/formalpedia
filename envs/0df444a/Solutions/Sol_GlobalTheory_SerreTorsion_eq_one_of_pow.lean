-- Prove2me | solution 1 for GlobalTheory.SerreTorsion.eq_one_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:44.256785+00:00
-- url     : https://prove2.me/submissions/2c61033c-2884-4b71-8623-1d17dd9f8a11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
import Theorems.Thm_GlobalTheory_SerreTorsion_one_add_smul_pow_expand
import Theorems.Thm_GlobalTheory_SerreTorsion_eq_zero_of_prime

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
theorem _root_.solution (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c : ℕ}
    (hq : q.Prime) (hsep : ∀ x : E, (∀ k : ℕ, ∃ y : E, x = q ^ k • y) → x = 0)
    (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (m : ℕ) :
    m ≠ 0 → ∀ ψ : E, (1 + c • ψ) ^ m = 1 → 1 + c • ψ = 1 := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ ψ h; simpa only [pow_one] using h
  | prime_mul l a hl ih =>
    intro hm ψ h
    have ha : a ≠ 0 := right_ne_zero_of_mul hm
    obtain ⟨z, hz⟩ := one_add_smul_pow_expand c ψ l
    rw [pow_mul, hz] at h
    have h1 := ih ha _ h
    rw [← hz] at h1
    rw [eq_zero_of_prime htf hq hsep hl hc0 hqc h2 ψ h1, smul_zero, add_zero]
end GlobalTheory.SerreTorsion
