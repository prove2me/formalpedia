-- Prove2me | solution 1 for GlobalTheory.SS.weightedOrder_slope_comparison
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:41:06.038687+00:00
-- url     : https://prove2.me/submissions/08d68407-c67d-494d-9ccf-47b3df13f763

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightedOrderSlopeComparison
import Theorems.Thm_GlobalTheory_SS_Slope_weight_two
import Theorems.Thm_GlobalTheory_SS_Slope_exists_min
import Theorems.Thm_GlobalTheory_SS_Slope_lt_iff
import Theorems.Thm_GlobalTheory_SS_Slope_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
open MvPowerSeries Slope
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (k : Type) [Field k] (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → ∀ Q : ℕ → ℕ → Prop, (∀ m n, Q m n ↔ ∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ((∀ i, MvPowerSeries.X 1 ∣ h i) → ¬ MvPowerSeries.X 1 ∣ d → (∃ m n, 1 ≤ m ∧ m ≤ n ∧ ¬ Q m n) → ∃ m n, 1 ≤ m ∧ m ≤ n ∧ (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∃ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d = MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ (Q 1 1 → ∃ m₀, ∀ m, m₀ ≤ m → Q m (m + 1)) ∧ (∀ m n l, 1 ≤ l → (Q (l * m) (l * n) ↔ Q m n)) ∧ ((∀ n, 1 ≤ n → Q 1 n) → ∀ i, ∃ u v, ¬ MvPowerSeries.X 1 ∣ v ∧ h i * v = d * u) := by
  classical
  intro k _ r h d hd Q hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro hh hdX ⟨m, n, hm, hmn, hnQ⟩
    have hf : ∀ i (t : Fin 2 →₀ ℕ), coeff t (h i) ≠ 0 → 1 ≤ t 1 := by
      intro i t ht
      by_contra hc
      exact ht (X_dvd_iff.1 (hh i) t (by omega))
    obtain ⟨s₀, hs₀', hs₀⟩ : ∃ s : Fin 2 →₀ ℕ, s 1 = 0 ∧ coeff s d ≠ 0 := by
      rw [X_dvd_iff] at hdX
      push Not at hdX
      exact hdX
    by_contra hcon
    have key : ∀ m n, 1 ≤ m → m ≤ n → ¬ Q m n →
        ∃ p, n * (s₀ 0).factorial < m * p ∧ ¬ Q (s₀ 0).factorial p := by
      intro m n hm hmn hnQ
      by_cases hall : ∀ i, weightedOrder (![m, n] : Fin 2 → ℕ) d ≤
          weightedOrder (![m, n] : Fin 2 → ℕ) (h i)
      · exfalso
        apply hcon
        refine ⟨m, n, hm, hmn, hall, ?_⟩
        rw [hQ] at hnQ
        push Not at hnQ
        obtain ⟨i, hi⟩ := hnQ
        exact ⟨i, le_antisymm (hall i) hi⟩
      · push Not at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨p, hp, hp'⟩ := step (h i) d (hf i) s₀ hs₀ hs₀' m n hm hmn hi
        exact ⟨p, hp, fun hq => hp' ((hQ _ _).1 hq i)⟩
    set N := (s₀ 0).factorial with hN
    have hNpos : 0 < N := Nat.factorial_pos _
    have unb : ∀ j : ℕ, ∃ p, N + j ≤ p ∧ ¬ Q N p := by
      intro j
      induction j with
      | zero =>
        obtain ⟨p, hp, hp'⟩ := key m n hm hmn hnQ
        refine ⟨p, ?_, hp'⟩
        have : m * N < m * p := lt_of_le_of_lt (Nat.mul_le_mul_right _ hmn) hp
        have := lt_of_mul_lt_mul_left this (Nat.zero_le _)
        omega
      | succ j ih =>
        obtain ⟨q, hq, hq'⟩ := ih
        obtain ⟨p, hp, hp'⟩ := key N q hNpos (by omega) hq'
        refine ⟨p, ?_, hp'⟩
        rw [mul_comm] at hp
        have := lt_of_mul_lt_mul_left hp (Nat.zero_le _)
        omega
    obtain ⟨p, hp, hp'⟩ := unb (N * s₀ 0)
    apply hp'
    rw [hQ]
    intro i
    rw [lt_iff]
    refine ⟨s₀, hs₀, fun t ht => ?_⟩
    have := hf i t ht
    rw [hs₀']
    nlinarith [Nat.mul_le_mul_left p this, Nat.zero_le (N * t 0)]
  · intro h11
    obtain ⟨s, hs, hs'⟩ := exists_min ![1, 1] d hd
    refine ⟨s 1 + 1, fun m hm => ?_⟩
    rw [hQ]
    intro i
    rw [lt_iff]
    refine ⟨s, hs, fun t ht => ?_⟩
    have h1 := lt_of_lt_of_le (hs' ▸ (hQ _ _).1 h11 i) (weightedOrder_le ![1, 1] ht)
    rw [weight_two, weight_two] at h1
    have h2 : 1 * s 0 + 1 * s 1 < 1 * t 0 + 1 * t 1 := by exact_mod_cast h1
    have h3 : s 0 + s 1 + 1 ≤ t 0 + t 1 := by omega
    nlinarith [Nat.mul_le_mul_left m h3, Nat.zero_le (t 1)]
  · intro m n l hl
    rw [hQ, hQ]
    refine forall_congr' fun i => ?_
    rw [lt_iff, lt_iff]
    refine exists_congr fun s => and_congr_right fun _ => forall_congr' fun t =>
      imp_congr_right fun _ => ?_
    rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add]
    exact Nat.mul_lt_mul_left hl
  · intro hall i
    have hP : ∃ e, ∃ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 ∧ s 1 = e := by
      obtain ⟨s, hs, -⟩ := exists_min ![1, 1] d hd
      exact ⟨_, s, hs, rfl⟩
    obtain ⟨s₁, hs₁, he⟩ := Nat.find_spec hP
    set e := Nat.find hP with hedef
    have hmin : ∀ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 → e ≤ s 1 := fun s hs =>
      Nat.find_min' hP ⟨s, hs, rfl⟩
    have hdv : (X 1 : MvPowerSeries (Fin 2) k) ^ e ∣ d := by
      rw [X_pow_dvd_iff]
      intro s hs
      by_contra hc
      have := hmin s hc
      omega
    have hhu : (X 1 : MvPowerSeries (Fin 2) k) ^ e ∣ h i := by
      rw [X_pow_dvd_iff]
      intro t ht
      by_contra hc
      obtain ⟨s, hs, hs'⟩ := (lt_iff _ _ _ _).1 ((hQ _ _).1 (hall (t 0 + 1) (by omega)) i)
      have h1 := hs' t hc
      have h2 : t 1 + 1 ≤ s 1 := le_trans ht (hmin s hs)
      nlinarith [Nat.mul_le_mul_left (t 0 + 1) h2, Nat.zero_le (s 0)]
    obtain ⟨v, hv⟩ := hdv
    obtain ⟨u, hu⟩ := hhu
    refine ⟨u, v, ?_, by rw [hu, hv]; ring⟩
    rintro ⟨w, hw⟩
    have : (X 1 : MvPowerSeries (Fin 2) k) ^ (e + 1) ∣ d := ⟨w, by rw [hv, hw]; ring⟩
    exact hs₁ (X_pow_dvd_iff.1 this s₁ (by omega))
end GlobalTheory.SS
