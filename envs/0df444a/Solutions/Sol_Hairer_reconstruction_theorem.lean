-- Prove2me | solution 1 for Hairer.reconstruction_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T06:38:53.780879+00:00
-- url     : https://prove2.me/submissions/372abddf-925a-47f6-bfcd-ac1238caa577
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Hairer_Model
import Theorems.Thm_Hairer_reconstruction_uniqueness
import Theorems.Thm_Hairer_reconstruction_operator

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

open Hairer

/-- **Theorem 3.10 (Reconstruction theorem), Hairer 2014**, in the case `γ > 0`. -/
theorem solution
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : IsLeast A α) (hαneg : α < 0)
    {γ : ℝ} (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∃ ξ : Distrib d,
      MemCalpha s α ξ ∧
      (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) ∧
      (∀ ζ : Distrib d,
        (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(ζ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) → ζ = ξ) := by
  obtain ⟨R, _, _, hR⟩ := Hairer.reconstruction_operator hs hT hmod hα hαneg γ
  obtain ⟨hmem, hbd⟩ := hR f hf
  refine ⟨R f, hmem, hbd, ?_⟩
  intro ζ hζ
  exact Hairer.reconstruction_uniqueness hs hT hmod hγ hf ζ (R f) hζ hbd
