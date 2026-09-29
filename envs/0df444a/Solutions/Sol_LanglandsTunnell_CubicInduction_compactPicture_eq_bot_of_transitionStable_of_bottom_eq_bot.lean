-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.compactPicture_eq_bot_of_transitionStable_of_bottom_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3337f55d-a26f-52e1-aec5-0ab659922d04

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Theorems.Thm_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two
import Theorems.Thm_LanglandsTunnell_CubicInduction_compactPicture_eq_zero_of_lowering_eq_zero_of_three_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_eq_bot_of_transitionStable_of_bottom_eq_bot

set_option autoImplicit false

namespace CompactPictureDescent

private theorem evenClass_eq_bot {L₂ L₁ M₂ : MvPolynomial (Fin 3) ℂ → MvPolynomial (Fin 3) ℂ}
    {T : Set (MvPolynomial (Fin 3) ℂ)}
    (hA : ∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} → S₂ ≤ Submodule.span ℂ T →
      (∀ p ∈ S₂, L₂ p ∈ S₀ ∧ M₂ p ∈ S₂) → (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀)
    (hC : ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous ℓ →
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 → L₂ p = 0 → L₁ p = 0 → p = 0)
    (S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ))
    (hhar : ∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
      p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0)
    (hS0 : S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)}) (hS1 : S 1 = ⊥) (hS2 : S 2 ≤ Submodule.span ℂ T)
    (htrans : ∀ ℓ, ∀ p ∈ S ℓ, L₂ p ∈ S (ℓ - 2) ∧ L₁ p ∈ S (ℓ - 1))
    (hsame : ∀ p ∈ S 2, M₂ p ∈ S 2) (hbot : S 0 = ⊥) (ℓ : ℕ) : S ℓ = ⊥ := by
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    rcases ℓ with _ | _ | _ | ℓ
    · exact hbot
    · exact hS1
    · by_contra h2
      have h1 : (1 : MvPolynomial (Fin 3) ℂ) ∈ S 0 :=
        hA (S 0) (S 2) hS0 hS2 (fun p hp => ⟨by simpa using (htrans 2 p hp).1, hsame p hp⟩) (Or.inr h2)
      rw [hbot, Submodule.mem_bot] at h1
      exact one_ne_zero h1
    · refine (Submodule.eq_bot_iff _).2 fun p hp => ?_
      have h₂ : L₂ p = 0 := by
        have h := (htrans _ p hp).1
        rwa [ih (ℓ + 1 + 1 + 1 - 2) (by omega), Submodule.mem_bot] at h
      have h₁ : L₁ p = 0 := by
        have h := (htrans _ p hp).2
        rwa [ih (ℓ + 1 + 1 + 1 - 1) (by omega), Submodule.mem_bot] at h
      exact hC _ (by omega) p (hhar _ p hp).1 (hhar _ p hp).2 h₂ h₁

private theorem oddClass_eq_bot {L₂ L₁ : MvPolynomial (Fin 3) ℂ → MvPolynomial (Fin 3) ℂ}
    {w q : MvPolynomial (Fin 3) ℂ}
    (hw : w ≠ 0)
    (hA : ∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {w} → S₂ ≤ Submodule.span ℂ {q} →
      (∀ p ∈ S₂, L₁ p ∈ S₁) → (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → w ∈ S₁)
    (hC : ∀ ℓ : ℕ, 3 ≤ ℓ → ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous ℓ →
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 → L₂ p = 0 → L₁ p = 0 → p = 0)
    (S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ))
    (hhar : ∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
      p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0)
    (hS0 : S 0 = ⊥) (hS1 : S 1 ≤ Submodule.span ℂ {w}) (hS2 : S 2 ≤ Submodule.span ℂ {q})
    (htrans : ∀ ℓ, ∀ p ∈ S ℓ, L₂ p ∈ S (ℓ - 2) ∧ L₁ p ∈ S (ℓ - 1))
    (hbot : S 1 = ⊥) (ℓ : ℕ) : S ℓ = ⊥ := by
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    rcases ℓ with _ | _ | _ | ℓ
    · exact hS0
    · exact hbot
    · by_contra h2
      have h1 : w ∈ S 1 :=
        hA (S 1) (S 2) hS1 hS2 (fun p hp => by simpa using (htrans 2 p hp).2) (Or.inr h2)
      rw [hbot, Submodule.mem_bot] at h1
      exact hw h1
    · refine (Submodule.eq_bot_iff _).2 fun p hp => ?_
      have h₂ : L₂ p = 0 := by
        have h := (htrans _ p hp).1
        rwa [ih (ℓ + 1 + 1 + 1 - 2) (by omega), Submodule.mem_bot] at h
      have h₁ : L₁ p = 0 := by
        have h := (htrans _ p hp).2
        rwa [ih (ℓ + 1 + 1 + 1 - 1) (by omega), Submodule.mem_bot] at h
      exact hC _ (by omega) p (hhar _ p hp).1 (hhar _ p hp).2 h₂ h₁

end CompactPictureDescent

theorem solution
    (τ τ₃ : ℝ) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    let ν₁₂ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, 1 / 2 + τ * Complex.I, τ₃ * Complex.I]
    let ν₁₃ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, τ₃ * Complex.I, 1 / 2 + τ * Complex.I]
    (∀ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
        p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) →
      S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} → S 1 = ⊥ →
      S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₂ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₂ p) ∈ S (ℓ - 1)) →
      (∀ p ∈ S 2, same₂ (Ξ ν₁₂ p) ∈ S 2) →
      S 0 = ⊥ → ∀ ℓ, S ℓ = ⊥) ∧
    (∀ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
        p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) →
      S 0 = ⊥ → S 1 ≤ Submodule.span ℂ {(MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      S 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₂ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₂ p) ∈ S (ℓ - 1)) →
      S 1 = ⊥ → ∀ ℓ, S ℓ = ⊥) ∧
    (∀ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
        p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) →
      S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} → S 1 = ⊥ →
      S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₃ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₃ p) ∈ S (ℓ - 1)) →
      (∀ p ∈ S 2, same₂ (Ξ ν₁₃ p) ∈ S 2) →
      S 0 = ⊥ → ∀ ℓ, S ℓ = ⊥) ∧
    (∀ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
        p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) →
      S 0 = ⊥ → S 1 ≤ Submodule.span ℂ {(MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      S 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₃ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₃ p) ∈ S (ℓ - 1)) →
      S 1 = ⊥ → ∀ ℓ, S ℓ = ⊥) := by
  intro Ξ lower₂ lower₁ same₂ ν₁₂ ν₁₃
  obtain ⟨hA₁, hA₂, hA₃, hA₄⟩ :=
    LanglandsTunnell.CubicInduction.compactPicture_bottom_mem_of_transitionStable_degree_le_two τ τ₃
  have hC := LanglandsTunnell.CubicInduction.compactPicture_eq_zero_of_lowering_eq_zero_of_three_le τ τ₃
  refine ⟨fun S hhar hS0 hS1 hS2 htrans hsame hbot => ?_, fun S hhar hS0 hS1 hS2 htrans hbot => ?_,
    fun S hhar hS0 hS1 hS2 htrans hsame hbot => ?_, fun S hhar hS0 hS1 hS2 htrans hbot => ?_⟩
  · exact CompactPictureDescent.evenClass_eq_bot hA₁
      (fun ℓ hℓ p hh hΔ => ((hC ℓ hℓ) p hh hΔ).1) S hhar hS0 hS1 hS2 htrans hsame hbot
  · exact CompactPictureDescent.oddClass_eq_bot (MvPolynomial.X_ne_zero 2) hA₂
      (fun ℓ hℓ p hh hΔ => ((hC ℓ hℓ) p hh hΔ).1) S hhar hS0 hS1 hS2 htrans hbot
  · exact CompactPictureDescent.evenClass_eq_bot hA₃
      (fun ℓ hℓ p hh hΔ => ((hC ℓ hℓ) p hh hΔ).2) S hhar hS0 hS1 hS2 htrans hsame hbot
  · exact CompactPictureDescent.oddClass_eq_bot (MvPolynomial.X_ne_zero 1) hA₄
      (fun ℓ hℓ p hh hΔ => ((hC ℓ hℓ) p hh hΔ).2) S hhar hS0 hS1 hS2 htrans hbot

end S_LanglandsTunnell_CubicInduction_compactPicture_eq_bot_of_transitionStable_of_bottom_eq_bot
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_eq_bot_of_transitionStable_of_bottom_eq_bot (solution)
