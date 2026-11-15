-- Prove2me | solution 1 for InfoLossLAR.WorstCase.theorem_9_9
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T23:06:01.197387+00:00
-- url     : https://prove2.me/submissions/a0b3bf57-12e7-46d5-a14d-1bdbaa712bfe

import Theorems.Thm_InfoLossLAR_WorstCase_Integration_fixedFamily_admitsGaussianAFT


set_option autoImplicit false

namespace Integration9_9.AFTToPlatformTheorem
open InfoLossLAR.WorstCase

/-- A fixed stronger accuracy absorbs the requested numerical budget once
security is at least two. No asymptotic uniformity in the accuracy is needed. -/
theorem stronger_accuracy_numerical_budget (lam e : ℕ) (hlam : 2 ≤ lam) :
    (lam : ℝ) ^ (-((2 * e + 6 : ℕ) : ℝ)) ≤
      (1 / 4 : ℝ) * (famL lam : ℝ) ^ (-((e : ℝ) + 2)) := by
  have hn : (2 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hnpos : (0 : ℝ) < lam := by linarith
  have hbase : (0 : ℝ) < (famL lam : ℝ) := by unfold famL; positivity
  have hbasele : (famL lam : ℝ) ≤ (lam : ℝ) ^ 2 := by
    simp only [famL, Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  have hp : (famL lam : ℝ) ^ (e+2) ≤ ((lam : ℝ) ^ 2) ^ (e+2) :=
    pow_le_pow_left₀ hbase.le hbasele _
  have hfour : (4 : ℝ) ≤ (lam : ℝ) ^ 2 := by nlinarith
  have hscale : 4 * (famL lam : ℝ) ^ (e+2) ≤ (lam : ℝ) ^ (2*e+6) := by
    calc
      _ ≤ 4 * ((lam : ℝ) ^ 2) ^ (e+2) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ ≤ (lam : ℝ) ^ 2 * ((lam : ℝ) ^ 2) ^ (e+2) :=
        mul_le_mul_of_nonneg_right hfour (by positivity)
      _ = (lam : ℝ) ^ (2*e+6) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
  have he : (e : ℝ) + 2 = ((e+2 : ℕ) : ℝ) := by push_cast; rfl
  rw [he, Real.rpow_neg hnpos.le, Real.rpow_natCast,
    Real.rpow_neg hbase.le, Real.rpow_natCast]
  calc
    ((lam : ℝ) ^ (2*e+6))⁻¹ ≤ (4 * (famL lam : ℝ) ^ (e+2))⁻¹ :=
      inv_anti₀ (by positivity) hscale
    _ = (1 / 4 : ℝ) * ((famL lam : ℝ) ^ (e+2))⁻¹ := by ring

/-- The exact platform Theorem 9.9 type follows from fixed-order AFT existence.
The platform type constrains the error bound, but does not constrain the
sampler's internal calibration order to equal its argument `R`. -/
theorem theorem_9_9_of_fixed_order_aft
    (hAFT : AdmitsFixedOrderGaussianAFT famInput famq famd (fun _ => 1)
      (fun lam => (famσ lam : ℝ)) famLabel) (R : ℕ) :
    ∃ C_R : ℝ, 0 < C_R ∧ ∃ negl_R : ℕ → ℝ, Negligible negl_R ∧
      ∀ c : ℕ, 1 ≤ c → 4 * c + 267 ≤ R → ∀ e : ℕ, c ≤ e →
        ∃ (m : Polynomial ℕ)
          (S : (lam : ℕ) → (Fin (m.eval lam) → Bool) →
            Matrix (Fin (famd lam)) (Fin (famd lam)) ℤ × (Fin (famd lam) → ℤ)),
          IsPPTAffineSampler famInput famd m S ∧
          (∀ (lam : ℕ) (ρ : Fin (m.eval lam) → Bool), IsUnit (matModq (famq lam) (S lam ρ).1).det) ∧
          (∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
            sdist (transportLaw (S lam) (chiG (famq lam) (famd lam) (famσ lam)))
                (unifZeroFiber (famLabel lam)) ≤
              C_R * (famq lam : ℝ) * (famL lam : ℝ) ^ (-((R : ℝ) + 1) / 4) +
                negl_R (famL lam) + (1 / 4) * (famL lam : ℝ) ^ (-((e : ℝ) + 2))) ∧
          (∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
            sdist (transportLaw (S lam) (chiG (famq lam) (famd lam) (famσ lam)))
                (unifZeroFiber (famLabel lam)) ≤ (lam : ℝ) ^ (-(c : ℝ))) := by
  refine ⟨1, by norm_num, fun _ => 0, ?_, ?_⟩
  · constructor
    · intro n; exact le_refl _
    · intro a ha
      refine ⟨0, ?_⟩
      intro n hn
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · intro c hc hR e hce
    obtain ⟨m, sampler, hPPT, hinvertible, cutoff, haccuracy⟩ :=
      hAFT (2*e+6) (by omega)
    refine ⟨m, sampler, hPPT, hinvertible, ?_, ?_⟩
    · refine ⟨max cutoff 2, ?_⟩
      intro lam hlam
      have hlcut : cutoff ≤ lam := (le_max_left _ _).trans hlam
      have hltwo : 2 ≤ lam := (le_max_right _ _).trans hlam
      calc
        _ ≤ (lam : ℝ) ^ (-((2*e+6 : ℕ) : ℝ)) := haccuracy lam hlcut
        _ ≤ (1/4 : ℝ) * (famL lam : ℝ) ^ (-((e : ℝ)+2)) :=
          stronger_accuracy_numerical_budget lam e hltwo
        _ ≤ 1 * (famq lam : ℝ) * (famL lam : ℝ) ^ (-((R : ℝ)+1)/4) +
            0 + (1/4 : ℝ) * (famL lam : ℝ) ^ (-((e : ℝ)+2)) := by
          have hf : 0 ≤ 1 * (famq lam : ℝ) * (famL lam : ℝ) ^ (-((R : ℝ)+1)/4) := by positivity
          linarith
    · refine ⟨max cutoff 1, ?_⟩
      intro lam hlam
      have hlcut : cutoff ≤ lam := (le_max_left _ _).trans hlam
      have hlone : 1 ≤ lam := (le_max_right _ _).trans hlam
      have ha : c ≤ 2*e+6 := by omega
      exact (haccuracy lam hlcut).trans
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hlone) (by exact_mod_cast neg_le_neg (show (c : ℝ) ≤ (2*e+6 : ℕ) by exact_mod_cast ha)))

end Integration9_9.AFTToPlatformTheorem



set_option autoImplicit false

open InfoLossLAR.WorstCase

theorem solution (R : ℕ) :
    ∃ C_R : ℝ, 0 < C_R ∧ ∃ negl_R : ℕ → ℝ, Negligible negl_R ∧
      ∀ c : ℕ, 1 ≤ c → 4 * c + 267 ≤ R → ∀ e : ℕ, c ≤ e →
        ∃ (m : Polynomial ℕ)
          (S : (lam : ℕ) → (Fin (m.eval lam) → Bool) →
            Matrix (Fin (famd lam)) (Fin (famd lam)) ℤ × (Fin (famd lam) → ℤ)),
          IsPPTAffineSampler famInput famd m S ∧
          (∀ (lam : ℕ) (ρ : Fin (m.eval lam) → Bool), IsUnit (matModq (famq lam) (S lam ρ).1).det) ∧
          (∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
            sdist (transportLaw (S lam) (chiG (famq lam) (famd lam) (famσ lam)))
                (unifZeroFiber (famLabel lam)) ≤
              C_R * (famq lam : ℝ) * (famL lam : ℝ) ^ (-((R : ℝ) + 1) / 4) +
                negl_R (famL lam) + (1 / 4) * (famL lam : ℝ) ^ (-((e : ℝ) + 2))) ∧
          (∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
            sdist (transportLaw (S lam) (chiG (famq lam) (famd lam) (famσ lam)))
                (unifZeroFiber (famLabel lam)) ≤ (lam : ℝ) ^ (-(c : ℝ))) := by
  exact Integration9_9.AFTToPlatformTheorem.theorem_9_9_of_fixed_order_aft
    Integration.fixedFamily_admitsGaussianAFT R
