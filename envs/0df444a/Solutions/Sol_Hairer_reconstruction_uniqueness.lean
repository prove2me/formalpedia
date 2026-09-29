-- Prove2me | solution 1 for Hairer.reconstruction_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T06:02:02.889033+00:00
-- url     : https://prove2.me/submissions/7046ea1e-0849-451b-99ce-62982c8e8d97

import Definitions.Def_Hairer_Model
import Theorems.Thm_Hairer_testFunction_decomposition_scaledTest

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

open Hairer Filter Topology

theorem solution
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {γ : ℝ} (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (ξ ζ : Distrib d)
    (hξ : ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ)
    (hζ : ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(ζ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) :
    ξ = ζ := by
  -- evaluation of a distribution at a genuine test function
  have heval : ∀ (ρ : Distrib d) (g : Pt d → ℝ) (hg : g ∈ testFunctions d),
      ρ.eval g = ρ ⟨g, hg⟩ := by
    intro ρ g hg
    simp [Distrib.eval, hg]
  ext p
  obtain ⟨φ, hφ⟩ := p
  obtain ⟨K, M, hK, hdec⟩ := testFunction_decomposition_scaledTest hs r hφ
  obtain ⟨C₁, h1⟩ := hξ K hK
  obtain ⟨C₂, h2⟩ := hζ K hK
  set B : ℝ := |C₁| + |C₂| with hB
  have hB0 : 0 ≤ B := by positivity
  have hM0 : 0 ≤ M := by
    obtain ⟨n, x, c, η, hx, hη, hc, hsum⟩ := hdec 1 one_pos le_rfl
    exact le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) hc
  -- the key quantitative bound, uniform in `δ`
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      |ξ ⟨φ, hφ⟩ - ζ ⟨φ, hφ⟩| ≤ M * B * δ ^ γ := by
    intro δ hδ0 hδ1
    obtain ⟨n, x, c, η, hx, hη, hc, hsum⟩ := hdec δ hδ0 hδ1
    have hmem : ∀ i : Fin n, scaledTest s δ (x i) (η i) ∈ testFunctions d := by
      intro i
      exact scaledTest_mem s hδ0 (x i) ⟨(hη i).smooth, (hη i).compactSupport⟩
    -- `φ` decomposes inside the submodule of test functions
    have hsub : (⟨φ, hφ⟩ : testFunctions d) =
        ∑ i : Fin n, c i • (⟨scaledTest s δ (x i) (η i), hmem i⟩ : testFunctions d) := by
      apply Subtype.ext
      push_cast
      funext y
      rw [Finset.sum_apply]
      simpa [smul_eq_mul] using hsum y
    -- pointwise bound on the difference of the two distributions
    have hpt : ∀ i : Fin n,
        |ξ ⟨scaledTest s δ (x i) (η i), hmem i⟩ - ζ ⟨scaledTest s δ (x i) (η i), hmem i⟩|
          ≤ B * δ ^ γ := by
      intro i
      have e1 := h1 (x i) (hx i) δ hδ0 hδ1 (η i) (hη i)
      have e2 := h2 (x i) (hx i) δ hδ0 hδ1 (η i) (hη i)
      have hsplit : ∀ ρ : Distrib d,
          (ρ - Pi (x i) (f (x i))).eval (scaledTest s δ (x i) (η i))
            = ρ ⟨scaledTest s δ (x i) (η i), hmem i⟩
              - (Pi (x i) (f (x i))) ⟨scaledTest s δ (x i) (η i), hmem i⟩ := by
        intro ρ
        simp [Distrib.eval, hmem i]
      rw [hsplit ξ] at e1
      rw [hsplit ζ] at e2
      have hδγ : (0:ℝ) ≤ δ ^ γ := Real.rpow_nonneg hδ0.le _
      have e1' : |ξ ⟨scaledTest s δ (x i) (η i), hmem i⟩
          - (Pi (x i) (f (x i))) ⟨scaledTest s δ (x i) (η i), hmem i⟩| ≤ |C₁| * δ ^ γ :=
        e1.trans (by nlinarith [le_abs_self C₁])
      have e2' : |ζ ⟨scaledTest s δ (x i) (η i), hmem i⟩
          - (Pi (x i) (f (x i))) ⟨scaledTest s δ (x i) (η i), hmem i⟩| ≤ |C₂| * δ ^ γ :=
        e2.trans (by nlinarith [le_abs_self C₂])
      calc |ξ ⟨scaledTest s δ (x i) (η i), hmem i⟩ - ζ ⟨scaledTest s δ (x i) (η i), hmem i⟩|
          = |(ξ ⟨scaledTest s δ (x i) (η i), hmem i⟩
              - (Pi (x i) (f (x i))) ⟨scaledTest s δ (x i) (η i), hmem i⟩)
            - (ζ ⟨scaledTest s δ (x i) (η i), hmem i⟩
              - (Pi (x i) (f (x i))) ⟨scaledTest s δ (x i) (η i), hmem i⟩)| := by ring_nf
        _ ≤ |ξ ⟨scaledTest s δ (x i) (η i), hmem i⟩
              - (Pi (x i) (f (x i))) ⟨scaledTest s δ (x i) (η i), hmem i⟩|
            + |ζ ⟨scaledTest s δ (x i) (η i), hmem i⟩
              - (Pi (x i) (f (x i))) ⟨scaledTest s δ (x i) (η i), hmem i⟩| := abs_sub _ _
        _ ≤ |C₁| * δ ^ γ + |C₂| * δ ^ γ := add_le_add e1' e2'
        _ = B * δ ^ γ := by rw [hB]; ring
    have hexp : ξ ⟨φ, hφ⟩ - ζ ⟨φ, hφ⟩
        = ∑ i : Fin n, c i * (ξ ⟨scaledTest s δ (x i) (η i), hmem i⟩
            - ζ ⟨scaledTest s δ (x i) (η i), hmem i⟩) := by
      rw [hsub, map_sum, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_smul, smul_eq_mul, mul_sub]
    have hδγ : (0:ℝ) ≤ δ ^ γ := Real.rpow_nonneg hδ0.le _
    calc |ξ ⟨φ, hφ⟩ - ζ ⟨φ, hφ⟩|
        = |∑ i : Fin n, c i * (ξ ⟨scaledTest s δ (x i) (η i), hmem i⟩
            - ζ ⟨scaledTest s δ (x i) (η i), hmem i⟩)| := by rw [hexp]
      _ ≤ ∑ i : Fin n, |c i * (ξ ⟨scaledTest s δ (x i) (η i), hmem i⟩
            - ζ ⟨scaledTest s δ (x i) (η i), hmem i⟩)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, |c i| * (B * δ ^ γ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hpt i) (abs_nonneg _)
      _ = (∑ i : Fin n, |c i|) * (B * δ ^ γ) := by rw [Finset.sum_mul]
      _ ≤ M * (B * δ ^ γ) := by
          exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ = M * B * δ ^ γ := by ring
  -- let `δ → 0`
  have hlim : Tendsto (fun δ : ℝ => M * B * δ ^ γ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun δ : ℝ => δ ^ γ) 0 :=
      Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)
    have h0 : Tendsto (fun δ : ℝ => δ ^ γ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have := hc.continuousWithinAt (s := Set.Ioi (0:ℝ))
      simpa [Real.zero_rpow hγ.ne'] using this.tendsto
    have := h0.const_mul (M * B)
    simpa using this
  have hle : |ξ ⟨φ, hφ⟩ - ζ ⟨φ, hφ⟩| ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with δ hδ0 hδ1
    exact key δ hδ0 hδ1.2
  have : ξ ⟨φ, hφ⟩ - ζ ⟨φ, hφ⟩ = 0 := by
    have := abs_nonneg (ξ ⟨φ, hφ⟩ - ζ ⟨φ, hφ⟩)
    have h : |ξ ⟨φ, hφ⟩ - ζ ⟨φ, hφ⟩| = 0 := le_antisymm hle this
    exact abs_eq_zero.mp h
  linarith [this]
