-- Prove2me | solution 1 for MasulloRH.dyadic_twisted_prime_shell_absolute_mass
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T10:18:59.511283+00:00
-- url     : https://prove2.me/submissions/6e52d74e-4a06-4751-9353-3b3179b06d0f

import Mathlib
import Theorems.Thm_MasulloRH_critical_half_weight_prime_mass_exceeds_summably_damped_interior_jets
open Filter Finset
theorem solution (q : ℕ) [NeZero q] (B : ℕ) (f : ℝ → ℝ)
    (hplateau : ∀ t ∈ Set.Icc (1:ℝ) 8, f t = 1) (hcut : ∀ t : ℝ, B ≤ t → f t = 0) :
    ∀ᶠ n : ℕ in atTop,
    let X := (2:ℕ)^n
    let S := Nat.primesLE (8*X) \ Nat.primesLE X
    ∀ (χ : DirichletCharacter ℂ q) (J : ℕ → Finset ℕ), (∀ p ∈ S, 0 ∈ J p) →
      (Real.log 2 / (2*Real.sqrt 8)) * Real.sqrt X ≤
       ∑ p ∈ S, ‖∑ k ∈ J p,
        (χ (p : ZMod q))^(k+1) * ((Real.log p / (Real.sqrt p)^(k+1) *
          f ((p:ℝ)^(k+1)/X) : ℝ) : ℂ)‖ := by
  classical
  have hmass := MasulloRH.critical_half_weight_prime_mass_exceeds_summably_damped_interior_jets
    (fun _ => 0) (fun _ => 1) (fun _ => 0) (by simp) (by simp) (by simp)
  have hpow : Tendsto (fun n : ℕ => (2:ℕ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  filter_upwards [hmass,hpow.eventually_ge_atTop (max q B)] with n hn hN
  let X := (2:ℕ)^n
  let S := Nat.primesLE (8*X) \ Nat.primesLE X
  change max q B ≤ X at hN
  change ∀ χ : DirichletCharacter ℂ q, ∀ J : ℕ → Finset ℕ, _ → _
  intro χ J hJ
  have hX : (0:ℝ) < X := by dsimp [X]; positivity
  have hmass' : (Real.log 2 / (2*Real.sqrt 8)) * Real.sqrt X ≤
      ∑ p ∈ S, Real.log p / Real.sqrt p := by simpa [X,S] using hn
  apply hmass'.trans_eq
  apply Finset.sum_congr rfl
  intro p hp
  change p ∈ S at hp
  obtain ⟨hup,hlo⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hup
  have hlt : X < p := by
    by_contra! hx
    exact hlo (Nat.mem_primesLE.mpr ⟨hx,hprime⟩)
  have hqp : q < p := lt_of_le_of_lt ((le_max_left _ _).trans hN) hlt
  have hunit : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr
    (hprime.coprime_iff_not_dvd.mpr (fun h => (Nat.le_of_dvd (NeZero.pos q) h).not_gt hqp))
  have hnorm : ‖χ (p : ZMod q)‖ = 1 := χ.unit_norm_eq_one hunit.unit
  have hltr : (X:ℝ) < p := by exact_mod_cast hlt
  have hler : (p:ℝ) ≤ 8*X := by exact_mod_cast hle
  have h1 := hplateau ((p:ℝ)/X) ⟨(le_div_iff₀ hX).2 (by linarith),(div_le_iff₀ hX).2 hler⟩
  have hB : (B:ℝ) ≤ X := by exact_mod_cast ((le_max_right q B).trans hN)
  have hpo : (1:ℝ) ≤ p := by exact_mod_cast hprime.one_le
  have hvan (k : ℕ) (hk : k ≠ 0) : f ((p:ℝ)^(k+1)/X) = 0 := by
    apply hcut
    apply (le_div_iff₀ hX).2
    calc
      (B:ℝ)*X ≤ (p:ℝ)*p := mul_le_mul (by linarith) hltr.le (by positivity) (by positivity)
      _ = (p:ℝ)^2 := by ring
      _ ≤ (p:ℝ)^(k+1) := pow_le_pow_right₀ hpo (by omega)
  rw [Finset.sum_eq_single 0 (by intro k hk hk0; rw [hvan k hk0, mul_zero, Complex.ofReal_zero, mul_zero]) (by simp [hJ p hp])]
  have hnn : 0 ≤ Real.log p / Real.sqrt p := div_nonneg (Real.log_nonneg hpo) (Real.sqrt_nonneg _)
  simp only [zero_add, pow_one]
  rw [h1, mul_one, norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
