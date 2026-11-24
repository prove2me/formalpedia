-- Prove2me | solution 1 for GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:58.959642+00:00
-- url     : https://prove2.me/submissions/daca970d-04e5-45d6-aa5e-1695326ca2c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLowCoeffNotDvdOfCongrMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
open PowerSeries
open scoped BigOperators
open PowerSeries
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (D g f : PowerSeries O) (m₀ v nT MT : ℕ), (∃ m ≤ m₀, IsUnit (PowerSeries.coeff m D)) → ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff 0 g → v + 1 ≤ nT → (v + 1) * m₀ ≤ MT → (∀ i ≤ MT, ϖ ^ nT ∣ PowerSeries.coeff i (f - D * g)) → ∃ i ≤ (v + 1) * m₀, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff i f := by
  intro O _ _ _ ϖ hϖ D g f m₀ v nT MT hD hg hv hM hf
  classical
  have hnu : ∀ x : O, ¬ IsUnit x → ϖ ∣ x := fun x hx => by
    have hmax : x ∈ IsLocalRing.maximalIdeal O := hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.mem_span_singleton] at hmax
    exact hmax
  by_contra hcon
  push_neg at hcon
  have hDg : ∀ i ≤ (v + 1) * m₀, ϖ ^ (v + 1) ∣ PowerSeries.coeff i (D * g) := by
    intro i hi
    have h1 := dvd_trans (pow_dvd_pow ϖ hv) (hf i (hi.trans hM))
    have h2 := hcon i hi
    have : PowerSeries.coeff i (D * g) = PowerSeries.coeff i f - PowerSeries.coeff i (f - D * g) := by
      simp
    rw [this]
    exact dvd_sub h2 h1
  have hD' : ∃ m, m ≤ m₀ ∧ IsUnit (PowerSeries.coeff m D) := hD
  set m₁ := Nat.find hD' with hm₁
  have hm₁le : m₁ ≤ m₀ := (Nat.find_spec hD').1
  have hm₁u : IsUnit (PowerSeries.coeff m₁ D) := (Nat.find_spec hD').2
  have hlow : ∀ a < m₁, ϖ ∣ PowerSeries.coeff a D := fun a ha =>
    hnu _ fun hu => Nat.find_min hD' ha ⟨(ha.trans_le hm₁le).le, hu⟩
  have claim : ∀ j ≤ v + 1, ∀ i, i + j * m₁ ≤ (v + 1) * m₀ → ϖ ^ j ∣ PowerSeries.coeff i g := by
    intro j
    induction j with
    | zero => intro _ i _; simp
    | succ j ihj =>
      intro hj i
      induction i using Nat.strong_induction_on with
      | _ i ihi =>
        intro hi
        have hsplit := (Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal (i + m₁))
          (fun p : ℕ × ℕ => PowerSeries.coeff p.1 D * PowerSeries.coeff p.2 g)
          (a := (m₁, i)) (by simp [add_comm])).symm
        rw [← PowerSeries.coeff_mul] at hsplit
        have hrest : ϖ ^ (j + 1) ∣ ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (i + m₁)).erase (m₁, i),
            PowerSeries.coeff p.1 D * PowerSeries.coeff p.2 g := by
          apply Finset.dvd_sum
          rintro ⟨a, b⟩ hp
          simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at hp
          obtain ⟨hne, hab⟩ := hp
          rcases lt_trichotomy a m₁ with h | h | h
          · rw [pow_succ, mul_comm (ϖ ^ j)]
            exact mul_dvd_mul (hlow a h) (ihj (by omega) b (by nlinarith))
          · exact absurd ⟨h, by omega⟩ hne
          · exact dvd_mul_of_dvd_right (ihi b (by omega) (by nlinarith)) _
        have htot : ϖ ^ (j + 1) ∣ PowerSeries.coeff (i + m₁) (D * g) :=
          dvd_trans (pow_dvd_pow ϖ hj) (hDg _ (by nlinarith))
        rw [hsplit] at htot
        have := (dvd_add_left hrest).1 htot
        exact (hm₁u.dvd_mul_left).1 this
  exact hg (by simpa using claim (v + 1) le_rfl 0 (by simpa using Nat.mul_le_mul_left (v + 1) hm₁le))
end _root_.GlobalTheory
end GlobalTheory
