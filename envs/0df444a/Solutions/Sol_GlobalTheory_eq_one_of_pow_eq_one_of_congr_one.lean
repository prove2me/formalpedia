-- Prove2me | solution 1 for GlobalTheory.eq_one_of_pow_eq_one_of_congr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:57.137842+00:00
-- url     : https://prove2.me/submissions/f1683ff5-1c97-4d96-b331-de10911c2a78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
import Theorems.Thm_GlobalTheory_SerreTorsion_eq_one_of_pow

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
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Ring E] (M : ℕ), 3 ≤ M → (∀ (n : ℕ) (x : E), n ≠ 0 → (n : E) * x = 0 → x = 0) → (∀ (q : ℕ) (x : E), 2 ≤ q → (∀ k : ℕ, ∃ y : E, x = (q : E) ^ k * y) → x = 0) → ∀ (σ φ : E) (m : ℕ), m ≠ 0 → σ = 1 + (M : E) * φ → σ ^ m = 1 → σ = 1 := by
  intro E _ M hM htf hsep σ φ m hm hσ h
  have hq : ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ (q = 2 → 4 ∣ M) := by
    rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (by omega : 2 < M) with
      h4 | ⟨p, hp, hpM, hodd⟩
    · exact ⟨2, Nat.prime_two, Dvd.dvd.trans (by norm_num) h4, fun _ => h4⟩
    · refine ⟨p, hp, hpM, fun h2 => ?_⟩
      subst h2
      exact absurd hodd (by decide)
  obtain ⟨q, hq, hqM, h2⟩ := hq
  rw [← nsmul_eq_mul] at hσ
  subst hσ
  refine SerreTorsion.eq_one_of_pow (fun n x hn hx => htf n x hn (by rwa [← nsmul_eq_mul])) hq
    (fun x hx => hsep q x hq.two_le fun k => ?_) (by omega) hqM h2 m hm φ h
  obtain ⟨y, hy⟩ := hx k
  exact ⟨y, by rw [hy, nsmul_eq_mul, Nat.cast_pow]⟩
end GlobalTheory
