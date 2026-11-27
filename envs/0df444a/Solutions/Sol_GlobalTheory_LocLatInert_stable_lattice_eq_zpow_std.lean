-- Prove2me | solution 1 for GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:10:30.965952+00:00
-- url     : https://prove2.me/submissions/6dd381c8-9b28-480d-8bf1-9b1aee29bee2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableLatticeEqZpowStdInertCompletion
import Theorems.Thm_GlobalTheory_LocLatInert_exists_unit_of_inert
import Theorems.Thm_GlobalTheory_LocLatInert_single_mem_of_mem
import Theorems.Thm_GlobalTheory_LocLatInert_single_mem_swap
import Theorems.Thm_GlobalTheory_LocLatInert_set_classify
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped Matrix
open GlobalTheory GlobalTheory.LocLatInert
namespace GlobalTheory.LocLatInert
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (σ : P.adicCompletion E →+* P.adicCompletion E), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) → ∀ (ϖ : P.adicCompletion E), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (n : ℕ) (L : AddSubgroup (Fin n → P.adicCompletion E)) (N : P.adicCompletion E), N ≠ 0 → (∀ a : P.adicCompletion E, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L) → (∀ w : Fin n → P.adicCompletion E, (∀ i, Valued.v (w i) ≤ 1) → N • w ∈ L) → (∀ w ∈ L, ∀ i, Valued.v (N * w i) ≤ 1) → (∀ U : GL (Fin n) (P.adicCompletion E), U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) → (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L) → ∃ k : ℤ, ∀ w, w ∈ L ↔ ∀ i, Valued.v (ϖ ^ k * w i) ≤ 1 := by
  intro E _ _ P σ hσ hv hx ϖ hϖ n L N hN hO hN' hb hU
  obtain ⟨u, hu, hu1, hu2, hu3, hu4⟩ := exists_unit_of_inert σ hσ hv hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    refine ⟨0, fun w => ⟨fun _ i => i.elim0, fun _ => ?_⟩⟩
    have hw : w = 0 := funext fun i => i.elim0
    rw [hw]
    exact L.zero_mem
  ·
    let i0 : Fin n := ⟨0, hn⟩
    let I : Set (P.adicCompletion E) := {t | Pi.single i0 t ∈ L}
    have hIall : ∀ (i : Fin n) t, Pi.single i t ∈ L ↔ t ∈ I := fun i t =>
      ⟨single_mem_swap σ L hU i i0 t, single_mem_swap σ L hU i0 i t⟩
    have hmul : ∀ a : P.adicCompletion E, Valued.v a ≤ 1 → ∀ t ∈ I, a * t ∈ I := by
      intro a ha t ht
      have e : Pi.single i0 (a * t) = a • (Pi.single i0 t : Fin n → P.adicCompletion E) := by
        funext j
        by_cases hj : j = i0
        · rw [hj, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
        · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]
      show Pi.single i0 (a * t) ∈ L
      rw [e]
      exact hO a ha _ ht
    have hNI : N ∈ I := by
      have h1 := hN' (Pi.single i0 1) fun i => by
        by_cases hi : i = i0
        · rw [hi, Pi.single_eq_same, map_one]
        · rw [Pi.single_eq_of_ne hi, map_zero]; exact zero_le
      have e : N • (Pi.single i0 1 : Fin n → P.adicCompletion E) = Pi.single i0 N := by
        funext j
        by_cases hj : j = i0
        · rw [hj, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul, mul_one]
        · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]
      show Pi.single i0 N ∈ L
      rw [← e]
      exact h1
    have hbI : ∀ t ∈ I, Valued.v (N * t) ≤ 1 := fun t ht => by
      have h1 := hb _ ht i0
      rwa [Pi.single_eq_same] at h1
    obtain ⟨M, hM⟩ := set_classify I hmul N hN hNI hbI

    have key : ∀ t : P.adicCompletion E, Valued.v (ϖ ^ M * t) ≤ 1 ↔ Valued.v t ≤ WithZero.exp M := by
      intro t
      rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]
      constructor
      · intro h
        calc Valued.v t = WithZero.exp M * (WithZero.exp (-M) * Valued.v t) := by
              rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
          _ ≤ WithZero.exp M * 1 := by gcongr
          _ = WithZero.exp M := mul_one _
      · intro h
        calc WithZero.exp (-M) * Valued.v t ≤ WithZero.exp (-M) * WithZero.exp M := by gcongr
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    refine ⟨M, fun w => ⟨fun hw i => ?_, fun hw => ?_⟩⟩
    · exact (key (w i)).2 ((hM (w i)).1
        ((hIall i (w i)).1 (single_mem_of_mem σ L hO hU u hu hu1 hu2 hu3 hu4 w hw i)))
    · rw [← Finset.univ_sum_single w]
      exact L.sum_mem fun i _ => (hIall i (w i)).2 ((hM (w i)).2 ((key (w i)).1 (hw i)))
end GlobalTheory.LocLatInert
