-- Prove2me | solution 1 for InterpOptStop.SAA.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:36:23.136155+00:00
-- url     : https://prove2.me/submissions/e01649ac-b132-4a79-9990-240ef652fa59

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
import Theorems.Thm_InterpOptStop_SAA_lemma_EC_1
open MeasureTheory ProbabilityTheory Filter Topology

namespace InterpOptStop.SAA

/-- There are finitely many skeletons of depth at most `d`. -/
lemma finite_depth_le (n d : ℕ) : {S : Tree n | S.depth ≤ d}.Finite := by
  induction d with
  | zero =>
    apply (({Tree.leaf Act.stop, Tree.leaf Act.go} : Set (Tree n)).toFinite).subset
    intro S hS
    cases S with
    | leaf a => cases a <;> simp
    | split i l r => simp [Tree.depth] at hS
  | succ d ih =>
    have hfin : (({Tree.leaf Act.stop, Tree.leaf Act.go} : Set (Tree n)) ∪
        (fun p : Fin n × Tree n × Tree n => Tree.split p.1 p.2.1 p.2.2) ''
          (Set.univ ×ˢ ({S : Tree n | S.depth ≤ d} ×ˢ {S : Tree n | S.depth ≤ d}))).Finite :=
      (Set.toFinite _).union ((Set.finite_univ.prod (ih.prod ih)).image _)
    apply hfin.subset
    intro S hS
    cases S with
    | leaf a => left; cases a <;> simp
    | split i l r =>
      right
      simp only [Set.mem_setOf_eq, Tree.depth] at hS
      refine ⟨(i, l, r), ?_, rfl⟩
      simp only [Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, true_and]
      omega

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
    ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∀ᵐ ω ∂P, ∃ Ω₀ : ℕ, ∀ m ≥ Ω₀, ∀ S : Tree n, S.depth ≤ d →
      ∀ θ : Thresholds,
        |J μ β g (policy S θ) - Jhat (fun k => ξ k ω) m β g (policy S θ)| ≤ ε := by
  intro d ε hε
  have hfin := finite_depth_le n d
  filter_upwards [(ae_ball_iff hfin.countable).2 (fun S _ => lemma_EC_1 hT xbar X Xi hXprod hXtb
    hXdiam μ hstart hinX β hβ0 hβ1 g hgm G hg f hf0 hfmono hfcont hA3 P ξ hξm hind hlaw S ε hε)]
    with ω hω
  choose! Ω₁ hΩ₁ using hω
  refine ⟨hfin.toFinset.sup Ω₁, fun m hm S hS θ => hΩ₁ S hS m ?_ θ⟩
  exact le_trans (Finset.le_sup (f := Ω₁) (by simpa using hS)) hm
