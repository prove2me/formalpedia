-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_transitionStable_family_read_of_actStable_signIsotypic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/bb8b7b7d-389d-5ad5-a8f0-7d67c358d93a

import Mathlib
import Theorems.Thm_LanglandsTunnell_CubicInduction_isHomogeneous_sub_two_and_sum_pderiv_pderiv_eq_zero_lowerTwo_xi
import Theorems.Thm_LanglandsTunnell_CubicInduction_isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi
import Theorems.Thm_LanglandsTunnell_CubicInduction_aeval_signTwist_eq_C_mul_of_read_polynomial_signIsotypic
import Theorems.Thm_LanglandsTunnell_CubicInduction_read_lowerTwo_xi_and_read_lowerOne_xi_of_read_polynomial_actStable
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_transitionStable_family_read_of_actStable_signIsotypic

set_option autoImplicit false

open LanglandsTunnell.CubicInduction

theorem solution
    (ν : Fin 3 → ℂ) (ε : Fin 3 → Fin 2) (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ)) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
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
    (∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W) →
    (∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P ∈ W) →
    (∀ P ∈ W, ∀ τ : Fin 3 → Fin 2, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => (((∑ c : Fin 3, (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) ij.1 c * o c ij.2) : ℝ) : ℂ)) P =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P) →
    ∃ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν p) ∈ S (ℓ - 1)) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
            (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
              MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p))) ∧
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous ℓ →
        (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 →
        (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
            (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
              MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) → p ∈ S ℓ) ∧
      ((∃ P ∈ W, ∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P ≠ 0) → ∃ ℓ, S ℓ ≠ ⊥)  := by
  intro act Ξ lower₂ lower₁ hact hr hiso
  classical

  let Rd : ℕ → MvPolynomial (Fin 3) ℂ → Prop := fun m q =>
    ∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
        (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((m + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q)
  have hRd_zero : ∀ m, Rd m 0 := fun m => ⟨0, W.zero_mem, fun o _ => by simp⟩
  have hRd_add : ∀ m q₁ q₂, Rd m q₁ → Rd m q₂ → Rd m (q₁ + q₂) := by
    rintro m q₁ q₂ ⟨Q₁, hQ₁, h₁⟩ ⟨Q₂, hQ₂, h₂⟩
    refine ⟨Q₁ + Q₂, W.add_mem hQ₁ hQ₂, fun o ho => ?_⟩
    rw [map_add, h₁ o ho, h₂ o ho, map_add, map_add]; ring
  have hRd_smul : ∀ m (c : ℂ) q, Rd m q → Rd m (c • q) := by
    rintro m c q ⟨Q, hQ, h⟩
    refine ⟨c • Q, W.smul_mem c hQ, fun o ho => ?_⟩
    rw [MvPolynomial.smul_eval, h o ho, map_smul, MvPolynomial.smul_eval]; ring

  let Δ : MvPolynomial (Fin 3) ℂ → MvPolynomial (Fin 3) ℂ := fun q => ∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i q)
  have hΔ_add : ∀ q₁ q₂, Δ (q₁ + q₂) = Δ q₁ + Δ q₂ := fun q₁ q₂ => by
    simp only [Δ, map_add, Finset.sum_add_distrib]
  have hΔ_smul : ∀ (c : ℂ) q, Δ (c • q) = c • Δ q := fun c q => by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
    simp only [Δ, MvPolynomial.pderiv_C_mul, Finset.mul_sum]

  let S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ) := fun ℓ =>
    { carrier := {p | p.IsHomogeneous ℓ ∧ Δ p = 0 ∧ Rd ℓ p}
      zero_mem' := ⟨MvPolynomial.isHomogeneous_zero _ _ _, by simp [Δ], hRd_zero ℓ⟩
      add_mem' := by
        rintro a b ⟨ha, ha', ha''⟩ ⟨hb, hb', hb''⟩
        exact ⟨ha.add hb, by rw [hΔ_add, ha', hb', add_zero], hRd_add ℓ a b ha'' hb''⟩
      smul_mem' := by
        rintro c a ⟨ha, ha', ha''⟩
        refine ⟨?_, by rw [hΔ_smul, ha', smul_zero], hRd_smul ℓ c a ha''⟩
        rw [MvPolynomial.smul_eq_C_mul]; exact ha.C_mul c }
  have hmem : ∀ ℓ p, p ∈ S ℓ ↔ p.IsHomogeneous ℓ ∧ Δ p = 0 ∧ Rd ℓ p := fun ℓ p => Iff.rfl
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro ℓ p hp; exact ⟨hp.1, hp.2.1⟩
  ·
    intro ℓ p hp σ
    exact aeval_signTwist_eq_C_mul_of_read_polynomial_signIsotypic ε W hiso ℓ p hp.1 hp.2.2 σ
  ·
    intro ℓ p hp
    have ht := read_lowerTwo_xi_and_read_lowerOne_xi_of_read_polynomial_actStable ν ε W ℓ p hp.1 hp.2.1 hact hr hp.2.2
    have h2 := isHomogeneous_sub_two_and_sum_pderiv_pderiv_eq_zero_lowerTwo_xi ν ℓ p hp.1 hp.2.1
    have h1 := isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi ν ℓ p hp.1 hp.2.1
    exact ⟨⟨h2.1, h2.2, ht.1⟩, ⟨h1.1, h1.2, ht.2⟩⟩
  ·
    intro ℓ p hp; exact hp.2.2
  ·
    intro ℓ p hp hh hread; exact ⟨hp, hh, hread⟩
  ·
    intro hne
    obtain ⟨ℓ, p, hp0, hp, hh, hread⟩ :=
      exists_ne_zero_isHomogeneous_harmonic_read_polynomial_of_signIsotypic_eval_ne_zero ε W hr hiso hne
    exact ⟨ℓ, (Submodule.ne_bot_iff _).2 ⟨p, ⟨hp, hh, hread⟩, hp0⟩⟩

end S_LanglandsTunnell_CubicInduction_exists_transitionStable_family_read_of_actStable_signIsotypic
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_transitionStable_family_read_of_actStable_signIsotypic (solution)
