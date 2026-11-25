-- Prove2me | solution 1 for GlobalTheory.DI.divided_frob_logForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:20.65799+00:00
-- url     : https://prove2.me/submissions/73427164-0216-4181-9ef6-f1cc4d9407f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedFrobLogForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (s : Finset ι) (A : Subring K) (g : K), (∀ i, IsF p π (F i) (f i)) → (∀ i j, IsH p π (F i) (F j) (h i j)) → LogLift p π F s (A : Set K) g → (∀ i ∈ s, ∃ w ∈ A, g ≠ 0 → f i (g⁻¹ • KaehlerDifferential.D ℤ K g) = g⁻¹ • KaehlerDifferential.D ℤ K g + KaehlerDifferential.D ℤ K w) ∧ ∀ i ∈ s, ∀ j ∈ s, h i j (g⁻¹ • KaehlerDifferential.D ℤ K g) ∈ A := by
  intro K Kt _ _ p hp _ π ι F f h s A g hF hH hL
  obtain ⟨z, hz, hw⟩ := hL
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hDp : KaehlerDifferential.D ℤ K (g ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  have e2 : ∀ hg : g ≠ 0, g⁻¹ ^ p * g ^ p = 1 := fun hg => by
    rw [← mul_pow, inv_mul_cancel₀ hg, one_pow]
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨w, hwA, hFw⟩ := hw i hi
    refine ⟨π w, hwA, fun hg => ?_⟩
    have key := (hF i).2 z (z ^ p * w) (by rw [hFw]; ring)
    rw [map_mul, map_pow, hz] at key
    have e1 : g⁻¹ ^ p * g ^ (p - 1) = g⁻¹ := by
      obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm (g⁻¹ ^ n), mul_assoc, ← mul_pow, inv_mul_cancel₀ hg,
        one_pow, mul_one]
    rw [(hF i).1, key, Derivation.leibniz, hDp, smul_zero, add_zero, smul_add, smul_smul, smul_smul, e1,
      e2 hg, one_smul]
  · obtain ⟨wi, hwiA, hFi⟩ := hw i hi
    obtain ⟨wj, hwjA, hFj⟩ := hw j hj
    have key := (hH i j).2 z (z ^ p * (wj - wi)) (by rw [hFj, hFi]; ring)
    rw [map_mul, map_pow, map_sub, hz] at key
    rw [(hH i j).1, key]
    by_cases hg : g = 0
    · subst hg
      simp [hp0]
    · rw [← mul_assoc, e2 hg, one_mul]
      exact A.sub_mem hwjA hwiA
end GlobalTheory.DI
