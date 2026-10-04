-- Prove2me | solution 1 for Hairer.reconstruction_limit_bound_of_uniform_consistency
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:16:55.230716+00:00
-- url     : https://prove2.me/submissions/eab81575-35bd-4e6f-ac88-f8bea293db2f

import Mathlib
import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

open Hairer in
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
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (approx : (ψ : Pt d → ℝ) → ψ ∈ testFunctions d → ℕ → ℝ)
    (happrox : ∀ (ψ : Pt d → ℝ) (hψ : ψ ∈ testFunctions d) (n : ℕ),
      ∃ (m : ℕ) (x : Fin m → Pt d) (c : Fin m → ℝ) (η : Fin m → (Pt d → ℝ)),
        (∀ i, IsTestBall s r (η i)) ∧
        (∀ y, ψ y = ∑ i, c i * scaledTest s ((2 : ℝ) ^ (-(n : ℤ))) (x i) (η i) y) ∧
        approx ψ hψ n = ∑ i, c i * (Pi (x i) (f (x i))).eval
          (scaledTest s ((2 : ℝ) ^ (-(n : ℤ))) (x i) (η i)))
    (hcons : ∀ (φ : Pt d → ℝ) (hφ : φ ∈ testFunctions d),
      ∀ (K : Set (Pt d)) (M : ℝ), IsCompact K →
      ∃ C : ℝ,
      ∀ (δ δ' : ℝ) (p p' : ℕ)
        (x : Fin p → Pt d) (c : Fin p → ℝ) (η : Fin p → (Pt d → ℝ))
        (x' : Fin p' → Pt d) (c' : Fin p' → ℝ) (η' : Fin p' → (Pt d → ℝ)),
        0 < δ → δ ≤ 1 → 0 < δ' → δ' ≤ 1 →
        (∀ i, x i ∈ K) → (∀ i, x' i ∈ K) →
        (∑ i, |c i|) ≤ M → (∑ i, |c' i|) ≤ M →
        (∀ i, IsTestBall s r (η i)) → (∀ i, IsTestBall s r (η' i)) →
        (∀ y, φ y = ∑ i, c i * scaledTest s δ (x i) (η i) y) →
        (∀ y, φ y = ∑ i, c' i * scaledTest s δ' (x' i) (η' i) y) →
        |∑ i, c i * (Pi (x i) (f (x i))).eval (scaledTest s δ (x i) (η i))
         - ∑ i, c' i * (Pi (x' i) (f (x' i))).eval (scaledTest s δ' (x' i) (η' i))|
          ≤ C * (max δ δ') ^ γ)
    (huniform : ∀ (K : Set (Pt d)), IsCompact K → ∃ C : ℝ,
      ∀ (x : Pt d), x ∈ K → ∀ (δ : ℝ), ∀ hδ : 0 < δ, ∀ _ : δ ≤ 1,
      ∀ (η : Pt d → ℝ), ∀ hη : IsTestBall s r η, ∀ (n : ℕ),
        |approx (scaledTest s δ x η)
            (scaledTest_mem s hδ x ⟨hη.smooth, hη.compactSupport⟩) n
         - (Pi x (f x)).eval (scaledTest s δ x η)|
          ≤ C * (max ((2 : ℝ) ^ (-(n : ℤ))) δ) ^ γ)
    (limval : (ψ : Pt d → ℝ) → ψ ∈ testFunctions d → ℝ)
    (hlim : ∀ (ψ : Pt d → ℝ) (hψ : ψ ∈ testFunctions d),
      Filter.Tendsto (approx ψ hψ) Filter.atTop (nhds (limval ψ hψ))) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ (x : Pt d), x ∈ K →
      ∀ (δ : ℝ), ∀ hδ : 0 < δ, ∀ _ : δ ≤ 1, ∀ (η : Pt d → ℝ), ∀ hη : IsTestBall s r η,
        |limval (scaledTest s δ x η) (scaledTest_mem s hδ x ⟨hη.smooth, hη.compactSupport⟩)
          - (Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by
  intro K hK
  obtain ⟨C, hC⟩ := huniform K hK
  refine ⟨C, fun x hx δ hδ hδ1 η hη => ?_⟩
  have hψ : scaledTest s δ x η ∈ testFunctions d :=
    scaledTest_mem s hδ x ⟨hη.smooth, hη.compactSupport⟩
  have h3 := ((hlim _ hψ).sub_const ((Pi x (f x)).eval (scaledTest s δ x η))).abs
  apply le_of_tendsto h3
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have h2n : (2 : ℝ) ^ (-(n : ℤ)) ≤ δ := by
    have e : (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2 : ℝ) ^ n := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [e]
    exact le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) hN.le
  have := hC x hx δ hδ hδ1 η hη n
  rwa [max_eq_right h2n] at this

end
