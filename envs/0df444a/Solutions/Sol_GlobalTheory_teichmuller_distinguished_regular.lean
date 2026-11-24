-- Prove2me | solution 1 for GlobalTheory.teichmuller_distinguished_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:32.786441+00:00
-- url     : https://prove2.me/submissions/d0b8dc6c-0a6e-4605-812b-589ffcc4151f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TeichmullerDistinguishedRegularSequence
import Theorems.Thm_GlobalTheory_teichmuller_dvd_of_dvd_natCast_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l] (x : O) (e : ℕ) (w E' : WittVector l O), x ≠ 0 → 0 < e → IsUnit w → E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w → ∀ (k : ℕ) (a : WittVector l O), (WittVector.teichmuller l x ^ k ∣ E' * a → WittVector.teichmuller l x ^ k ∣ a) ∧ (E' ∣ WittVector.teichmuller l x ^ k * a → E' ∣ a) := by
  intro l _ O _ _ _ _ x e w E' hx he hw hE
  have hT : WittVector.teichmuller l x ≠ 0 := by
    intro h
    apply hx
    rw [← WittVector.teichmuller_coeff_zero l x, h]
    simp
  have h1 : ∀ a : WittVector l O, WittVector.teichmuller l x ∣ E' * a →
      WittVector.teichmuller l x ∣ a := by
    intro a h
    rw [hE, add_mul] at h
    have h2 : WittVector.teichmuller l x ∣ WittVector.teichmuller l x ^ e * a :=
      (dvd_pow_self _ he.ne').mul_right a
    have h3 := (dvd_add_right h2).mp h
    rw [mul_assoc] at h3
    exact hw.dvd_mul_left.mp (teichmuller_dvd_of_dvd_natCast_mul l O x hx _ h3)
  have hk : ∀ (k : ℕ) (a : WittVector l O), WittVector.teichmuller l x ^ k ∣ E' * a →
      WittVector.teichmuller l x ^ k ∣ a := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a h
      obtain ⟨c, rfl⟩ := h1 a ((dvd_pow_self _ k.succ_ne_zero).trans h)
      rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left hT] at h
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih c h)
  intro k a
  refine ⟨hk k a, ?_⟩
  rintro ⟨b, hb⟩
  obtain ⟨c, rfl⟩ := hk k b ⟨a, hb.symm⟩
  refine ⟨c, mul_left_cancel₀ (pow_ne_zero k hT) ?_⟩
  rw [hb]; ring
end GlobalTheory
