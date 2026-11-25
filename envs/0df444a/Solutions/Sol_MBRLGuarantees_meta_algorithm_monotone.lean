-- Prove2me | solution 1 for MBRLGuarantees.meta_algorithm_monotone
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T09:48:55.084809+00:00
-- url     : https://prove2.me/submissions/641599b6-0ae2-45d9-a58a-9540baa4dc74

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
open MBRLGuarantees

theorem solution {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀]
    (Pol : Set (Kernel S A)) (hPol : ∀ pi ∈ Pol, IsMarkovKernel pi)
    (Mod : Set (Kernel (S × A) S)) (hMod : ∀ M ∈ Mod, IsMarkovKernel M)
    (Mstar : Kernel (S × A) S) (hMstar : Mstar ∈ Mod)
    (D : Kernel S A → Kernel (S × A) S → Kernel S A → ℝ) (hD0 : ∀ piref M pi, 0 ≤ D piref M pi)
    (d : Kernel S A → Kernel S A → ℝ≥0∞) (δ : ℝ≥0∞)
    (hR1 : ∀ (piref pi : Kernel S A) (Mhat : Kernel (S × A) S), IsMarkovKernel piref →
      IsMarkovKernel pi → IsMarkovKernel Mhat → d pi piref ≤ δ →
      value γ R μ₀ pi Mhat - D piref Mhat pi ≤ value γ R μ₀ pi Mstar)
    (hR2 : ∀ piref pi : Kernel S A, IsMarkovKernel piref → IsMarkovKernel pi →
      D piref Mstar pi = 0)
    (hdself : ∀ pi ∈ Pol, d pi pi = 0)
    (T : ℕ) (pol : ℕ → Kernel S A) (mod : ℕ → Kernel (S × A) S) (hpol0 : pol 0 ∈ Pol)
    (hstep : ∀ k < T, pol (k + 1) ∈ Pol ∧ mod (k + 1) ∈ Mod ∧ d (pol (k + 1)) (pol k) ≤ δ ∧
      ∀ pi ∈ Pol, ∀ M ∈ Mod, d pi (pol k) ≤ δ →
        value γ R μ₀ pi M - D (pol k) M pi ≤
          value γ R μ₀ (pol (k + 1)) (mod (k + 1)) - D (pol k) (mod (k + 1)) (pol (k + 1))) :
    ∀ i j, i ≤ j → j ≤ T → value γ R μ₀ (pol i) Mstar ≤ value γ R μ₀ (pol j) Mstar := by
  -- every iterate up to `T` lies in `Pol`
  have hmem : ∀ k, k ≤ T → pol k ∈ Pol := by
    intro k
    induction k with
    | zero => intro _; exact hpol0
    | succ k _ => intro hk; exact (hstep k (by omega)).1
  -- one-step improvement
  have hone : ∀ k < T, value γ R μ₀ (pol k) Mstar ≤ value γ R μ₀ (pol (k + 1)) Mstar := by
    intro k hk
    obtain ⟨hk1, hmod, hd, hopt⟩ := hstep k hk
    have hk0 := hmem k (by omega)
    have h1 := hopt (pol k) hk0 Mstar hMstar (by rw [hdself _ hk0]; exact zero_le)
    rw [hR2 _ _ (hPol _ hk0) (hPol _ hk0)] at h1
    have h2 := hR1 (pol k) (pol (k + 1)) (mod (k + 1)) (hPol _ hk0) (hPol _ hk1)
      (hMod _ hmod) hd
    linarith
  intro i j hij hjT
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hone j (by omega))
