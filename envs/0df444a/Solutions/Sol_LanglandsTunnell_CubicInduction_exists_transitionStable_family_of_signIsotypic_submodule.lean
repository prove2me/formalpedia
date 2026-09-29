-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_transitionStable_family_of_signIsotypic_submodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/48af2d57-4a33-51fb-9770-9c21705326a0

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_CubicInduction_aeval_signTwist_eq_smul_of_read_signIsotypic
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_read_lowerTwo_xi_of_read_signIsotypic
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_read_lowerOne_xi_of_read_signIsotypic
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_read_sameTwo_xi_of_read_signIsotypic
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_isHomogeneous_sub_two_and_sum_pderiv_pderiv_eq_zero_lowerTwo_xi
import Theorems.Thm_LanglandsTunnell_CubicInduction_isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi
import Theorems.Thm_LanglandsTunnell_CubicInduction_isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_transitionStable_family_of_signIsotypic_submodule

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

namespace FamEps

def fam (ε : Fin 3 → Fin 2) (Vε : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (ℓ : ℕ) :
    Submodule ℂ (MvPolynomial (Fin 3) ℂ) where
  carrier := {p | p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 ∧
    ∃ G ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
            (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) =
          G (WhittakerBlock.archRealLift3 o * k₁)}
  zero_mem' := by
    refine ⟨MvPolynomial.isHomogeneous_zero _ _ _, by simp, 0, Vε.zero_mem, fun o _ => by simp⟩
  add_mem' := by
    rintro p q ⟨hp1, hp2, G, hG, hp3⟩ ⟨hq1, hq2, G', hG', hq3⟩
    refine ⟨hp1.add hq1, by simp [map_add, Finset.sum_add_distrib, hp2, hq2], G + G', Vε.add_mem hG hG',
      fun o ho => ?_⟩
    rw [map_add, map_add, mul_add, hp3 o ho, hq3 o ho, Pi.add_apply]
  smul_mem' := by
    rintro z p ⟨hp1, hp2, G, hG, hp3⟩
    refine ⟨(MvPolynomial.mem_homogeneousSubmodule ℓ (z • p)).1
        ((MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ).smul_mem z
          ((MvPolynomial.mem_homogeneousSubmodule ℓ p).2 hp1)), ?_, z • G, Vε.smul_mem z hG, fun o ho => ?_⟩
    · simp [← Finset.smul_sum, hp2]
    · rw [map_smul, MvPolynomial.smul_eval, Pi.smul_apply, smul_eq_mul, ← hp3 o ho]
      ring

end FamEps

theorem solution
    (ν : Fin 3 → ℂ) (lam₁ lam₂ lam₃ : ℂ) (ε : Fin 3 → Fin 2) (V Vε : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (hVε : (∀ G ∈ Vε, Continuous G) ∧
      (∀ G ∈ Vε, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G) ∧
      (∀ G ∈ Vε, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g) ∧
      (∀ G ∈ Vε, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ Vε) ∧
      (∀ G ∈ Vε, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ G ∈ Vε, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ Vε, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0) ∧
      (∀ G ∈ Vε, ∀ σ : Fin 3 → Fin 2, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g) =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) * G g) ∧
      (∀ G ∈ Vε, ∃ F ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G g = (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g))) :
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
    ∃ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν p) ∈ S (ℓ - 1)) ∧
      (∀ p ∈ S 2, same₂ (Ξ ν p) ∈ S 2) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, ∃ G ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
            (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) =
          G (WhittakerBlock.archRealLift3 o * k₁)) ∧
      ((∃ G ∈ Vε, ∃ o : Fin 3 → Fin 3 → ℝ,
        (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ G (WhittakerBlock.archRealLift3 o * k₁) ≠ 0) → ∃ ℓ, S ℓ ≠ ⊥) := by
  intro Ξ lower₂ lower₁ same₂
  refine ⟨FamEps.fam ε Vε k₁, fun ℓ p hp => ⟨hp.1, hp.2.1⟩, ?_, ?_, ?_, fun ℓ p hp => hp.2.2, ?_⟩
  ·
    intro ℓ p hp σ
    obtain ⟨h1, h2, G, hG, hread⟩ := hp
    exact aeval_signTwist_eq_smul_of_read_signIsotypic ν lam₁ lam₂ lam₃ ε V Vε k₁ hk₁ hVε ℓ p h1 G hG hread σ
  ·
    intro ℓ p hp
    obtain ⟨h1, h2, G, hG, hread⟩ := hp
    obtain ⟨hA2, hB2⟩ := isHomogeneous_sub_two_and_sum_pderiv_pderiv_eq_zero_lowerTwo_xi ν ℓ p h1 h2
    obtain ⟨G2, hG2, hread2⟩ :=
      exists_read_lowerTwo_xi_of_read_signIsotypic ν lam₁ lam₂ lam₃ ε V Vε k₁ hk₁ hVε ℓ p h1 h2 G hG hread
    obtain ⟨hA1, hB1⟩ := isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi ν ℓ p h1 h2
    obtain ⟨G1, hG1, hread1⟩ :=
      exists_read_lowerOne_xi_of_read_signIsotypic ν lam₁ lam₂ lam₃ ε V Vε k₁ hk₁ hVε ℓ p h1 h2 G hG hread
    exact ⟨⟨hA2, hB2, G2, hG2, hread2⟩, ⟨hA1, hB1, G1, hG1, hread1⟩⟩
  ·
    intro p hp
    obtain ⟨h1, h2, G, hG, hread⟩ := hp
    obtain ⟨hAs, hBs⟩ := isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi ν p h1 h2
    obtain ⟨Gs, hGs, hreads⟩ :=
      exists_read_sameTwo_xi_of_read_signIsotypic ν lam₁ lam₂ lam₃ ε V Vε k₁ hk₁ hVε p h1 h2 G hG hread
    exact ⟨hAs, hBs, Gs, hGs, hreads⟩
  ·
    intro hne
    obtain ⟨ℓ, p, hp0, h1, h2, G', hG', hread⟩ :=
      exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero ν lam₁ lam₂ lam₃ ε V Vε k₁ hk₁ hVε hne
    exact ⟨ℓ, fun h => hp0 ((Submodule.eq_bot_iff _).1 h p ⟨h1, h2, G', hG', hread⟩)⟩

end S_LanglandsTunnell_CubicInduction_exists_transitionStable_family_of_signIsotypic_submodule
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_transitionStable_family_of_signIsotypic_submodule (solution)
