-- Prove2me | solution 1 for InterpOptStop.SAA.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:35:08.250891+00:00
-- url     : https://prove2.me/submissions/91f2d74d-ad7d-4c5e-b873-d08eec74b6d9

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
import Theorems.Thm_InterpOptStop_SAA_theorem_1
open MeasureTheory ProbabilityTheory Filter Topology

namespace InterpOptStop.SAA

/-- Supremum comparison: uniformly close bounded families have close suprema. -/
lemma abs_iSup_sub_iSup_le {ι : Type*} [Nonempty ι] (a b : ι → ℝ)
    (ha : BddAbove (Set.range a)) (hb : BddAbove (Set.range b)) (ε : ℝ)
    (h : ∀ q, |a q - b q| ≤ ε) : |(⨆ q, a q) - (⨆ q, b q)| ≤ ε := by
  rw [abs_sub_le_iff]
  constructor
  · have : (⨆ q, a q) ≤ (⨆ q, b q) + ε := by
      apply ciSup_le
      intro q
      have h1 := (abs_sub_le_iff.mp (h q)).1
      have h2 := le_ciSup hb q
      linarith
    linarith
  · have : (⨆ q, b q) ≤ (⨆ q, a q) + ε := by
      apply ciSup_le
      intro q
      have h1 := (abs_sub_le_iff.mp (h q)).2
      have h2 := le_ciSup ha q
      linarith
    linarith

/-- On a path lying in `𝒳`, the reward is bounded in absolute value by `G`. -/
lemma abs_reward_le {n T : ℕ} (X : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G)
    (π : (Fin n → ℝ) → Act) (x : Fin T → Fin n → ℝ) (hx : ∀ k, x k ∈ X) :
    |reward β g π x| ≤ G := by
  unfold reward
  split_ifs with h
  · set τ := (Finset.univ.filter fun k : Fin T => π (x k) = Act.stop).min' h
    have hp0 : 0 ≤ β ^ (τ : ℕ) := pow_nonneg hβ0 _
    have hp1 : β ^ (τ : ℕ) ≤ 1 := pow_le_one₀ hβ0 hβ1
    obtain ⟨hg0, hg1⟩ := hg τ (x τ) (hx τ)
    rw [abs_of_nonneg (mul_nonneg hp0 hg0)]
    nlinarith
  · simpa using hG

end InterpOptStop.SAA

open InterpOptStop.SAA in
theorem solution {n T : ℕ}
    (hT : 0 < T)
    (xbar : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (Xi : Fin n → Set ℝ) (hXprod : X = Set.univ.pi Xi)
    (hXtb : TotallyBounded X) (hXdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ 1)
    (μ : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hstart : ∀ᵐ x ∂μ, x ⟨0, hT⟩ = xbar)
    (hinX : ∀ᵐ x ∂μ, ∀ k, x k ∈ X)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ) (hgm : ∀ k, Measurable (g k))
    (G : ℝ) (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hfmono : StrictMonoOn f (Set.Ici 0))
    (hfcont : ContinuousOn f (Set.Ici 0))
    (hA3 : ∀ A : Set (Fin n → ℝ), MeasurableSet A → volume A ≠ ⊤ →
      ∀ k : Fin T, (k : ℕ) ≠ 0 → (μ {x | x k ∈ A}).toReal ≤ f (volume A).toReal)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Fin T → Fin n → ℝ) (hξm : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ P)
    (hlaw : ∀ k, P.map (ξ k) = μ) :
    ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∀ᵐ ω ∂P, ∃ Ω₀ : ℕ, ∀ m ≥ Ω₀,
      |(⨆ q : TreePol n d, J μ β g (policy q.1.1 q.1.2)) -
          (⨆ q : TreePol n d, Jhat (fun k => ξ k ω) m β g (policy q.1.1 q.1.2))| ≤ ε := by
  intro d ε hε
  -- `G ≥ 0`, since `𝒳` is nonempty
  obtain ⟨x0, hx0⟩ := hinX.exists
  have hG : 0 ≤ G := le_trans (hg ⟨0, hT⟩ _ (hx0 ⟨0, hT⟩)).1 (hg ⟨0, hT⟩ _ (hx0 ⟨0, hT⟩)).2
  -- `|J^π| ≤ G` for every policy
  have hJ : ∀ π : (Fin n → ℝ) → Act, |J μ β g π| ≤ G := by
    intro π
    have h := norm_integral_le_of_norm_le_const (μ := μ) (C := G)
      (f := fun x => reward β g π x)
      (hinX.mono fun x hx => by
        simpa [Real.norm_eq_abs] using abs_reward_le X β hβ0 hβ1 g G hG hg π x hx)
    simpa [J, Real.norm_eq_abs, measure_univ] using h
  filter_upwards [theorem_1 hT xbar X Xi hXprod hXtb hXdiam μ hstart hinX β hβ0 hβ1 g hgm G hg
    f hf0 hfmono hfcont hA3 P ξ hξm hind hlaw d ε hε] with ω hω
  obtain ⟨Ω₀, hΩ₀⟩ := hω
  refine ⟨Ω₀, fun m hm => ?_⟩
  have hclose : ∀ q : TreePol n d, |J μ β g (policy q.1.1 q.1.2) -
      Jhat (fun k => ξ k ω) m β g (policy q.1.1 q.1.2)| ≤ ε :=
    fun q => hΩ₀ m hm q.1.1 q.2 q.1.2
  apply abs_iSup_sub_iSup_le _ _ _ _ ε hclose
  · refine ⟨G, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact (abs_le.mp (hJ _)).2
  · refine ⟨G + ε, ?_⟩
    rintro _ ⟨q, rfl⟩
    have h1 := (abs_sub_le_iff.mp (hclose q)).2
    have h2 := (abs_le.mp (hJ (policy q.1.1 q.1.2))).2
    simp only
    linarith
