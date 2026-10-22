-- Prove2me | solution 1 for InterpOptStop.SAA.fixed_policy_slln
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:38:46.826596+00:00
-- url     : https://prove2.me/submissions/77e20fdd-b8dd-4bd2-bf89-0296da22138a

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
open MeasureTheory ProbabilityTheory Filter Topology

namespace InterpOptStop.SAA

/-- Rewards are bounded by `|G|` on paths lying in `𝒳`. -/
lemma abs_reward_le' {n T : ℕ} (X : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ) (G : ℝ)
    (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G)
    (π : (Fin n → ℝ) → Act) (x : Fin T → Fin n → ℝ) (hx : ∀ k, x k ∈ X) :
    |reward β g π x| ≤ |G| := by
  unfold reward
  split_ifs with h
  · set τ := (Finset.univ.filter fun k : Fin T => π (x k) = Act.stop).min' h
    have hp0 : 0 ≤ β ^ (τ : ℕ) := pow_nonneg hβ0 _
    have hp1 : β ^ (τ : ℕ) ≤ 1 := pow_le_one₀ hβ0 hβ1
    obtain ⟨hg0, hg1⟩ := hg τ (x τ) (hx τ)
    rw [abs_of_nonneg (mul_nonneg hp0 hg0)]
    have := le_abs_self G
    nlinarith
  · simp

/-- The stopping region of a (sub)tree policy is measurable. -/
lemma measurableSet_act_stop {n : ℕ} (S : Tree n) (θ : Thresholds) :
    ∀ p : List Bool, MeasurableSet {x : Fin n → ℝ | S.act θ p x = Act.stop} := by
  induction S with
  | leaf a =>
    intro p
    cases a
    · simp [Tree.act]
    · simp [Tree.act]
  | split i l r ihl ihr =>
    intro p
    have hle : MeasurableSet {x : Fin n → ℝ | x i ≤ θ p} :=
      measurableSet_le (measurable_pi_apply i) measurable_const
    have : {x : Fin n → ℝ | (Tree.split i l r).act θ p x = Act.stop} =
        ({x | x i ≤ θ p} ∩ {x | l.act θ (p ++ [true]) x = Act.stop}) ∪
        ({x | x i ≤ θ p}ᶜ ∩ {x | r.act θ (p ++ [false]) x = Act.stop}) := by
      ext x
      simp only [Tree.act, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      split_ifs with h <;> simp [h]
    rw [this]
    exact (hle.inter (ihl _)).union (hle.compl.inter (ihr _))

/-- The reward as a finite sum over the possible (first) stopping periods. -/
lemma reward_eq_sum {n T : ℕ} (β : ℝ) (g : Fin T → (Fin n → ℝ) → ℝ)
    (π : (Fin n → ℝ) → Act) (x : Fin T → Fin n → ℝ) :
    reward β g π x = ∑ k : Fin T,
      if (π (x k) = Act.stop ∧ ∀ j < k, π (x j) ≠ Act.stop) then β ^ (k : ℕ) * g k (x k)
      else 0 := by
  unfold reward
  split_ifs with h
  · set τ := (Finset.univ.filter fun k : Fin T => π (x k) = Act.stop).min' h with hτ
    have hτmem := Finset.min'_mem _ h
    rw [← hτ] at hτmem
    have hτs : π (x τ) = Act.stop := by simpa using hτmem
    have hmin : ∀ j < τ, π (x j) ≠ Act.stop := by
      intro j hj hjs
      have : τ ≤ j := Finset.min'_le _ _ (by simpa using hjs)
      exact absurd hj (not_lt.mpr this)
    rw [Finset.sum_eq_single τ]
    · rw [if_pos ⟨hτs, hmin⟩]
    · intro k _ hk
      rw [if_neg]
      rintro ⟨hks, hkmin⟩
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · have : τ ≤ k := Finset.min'_le _ _ (by simpa using hks)
        exact absurd hlt (not_lt.mpr this)
      · exact hkmin τ hgt hτs
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    rintro ⟨hks, -⟩
    exact h ⟨k, by simpa using hks⟩

/-- The reward of a tree policy is a measurable function of the path. -/
lemma measurable_reward {n T : ℕ} (β : ℝ) (g : Fin T → (Fin n → ℝ) → ℝ)
    (hgm : ∀ k, Measurable (g k)) (S : Tree n) (θ : Thresholds) :
    Measurable (fun x : Fin T → Fin n → ℝ => reward β g (policy S θ) x) := by
  simp_rw [reward_eq_sum]
  apply Finset.measurable_sum
  intro k _
  have hst : ∀ j : Fin T, MeasurableSet {x : Fin T → Fin n → ℝ | policy S θ (x j) = Act.stop} :=
    fun j => by
      have hj : Measurable (fun x : Fin T → Fin n → ℝ => x j) := measurable_pi_apply j
      have h := (measurableSet_act_stop S θ []).preimage hj
      exact h
  have hset : MeasurableSet {x : Fin T → Fin n → ℝ |
      policy S θ (x k) = Act.stop ∧ ∀ j < k, policy S θ (x j) ≠ Act.stop} := by
    have : {x : Fin T → Fin n → ℝ |
        policy S θ (x k) = Act.stop ∧ ∀ j < k, policy S θ (x j) ≠ Act.stop} =
        {x | policy S θ (x k) = Act.stop} ∩
          ⋂ j ∈ (Finset.univ.filter fun j : Fin T => j < k), {x | policy S θ (x j) = Act.stop}ᶜ := by
      ext x; simp
    rw [this]
    exact (hst k).inter (Finset.measurableSet_biInter _ fun j _ => (hst j).compl)
  exact Measurable.ite hset (measurable_const.mul ((hgm k).comp (measurable_pi_apply k)))
    measurable_const

/-- Strong law of large numbers for an integrable function of the i.i.d. paths. -/
lemma slln_comp {n T : ℕ} (μ : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Fin T → Fin n → ℝ) (hξm : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ P)
    (hlaw : ∀ k, P.map (ξ k) = μ) (h : (Fin T → Fin n → ℝ) → ℝ) (hm : Measurable h)
    (hi : Integrable h μ) :
    ∀ᵐ ω ∂P, Tendsto (fun m : ℕ => (∑ k ∈ Finset.range m, h (ξ k ω)) / m) atTop
      (𝓝 (∫ x, h x ∂μ)) := by
  have hint : Integrable (h ∘ ξ 0) P := by
    have : Integrable h (P.map (ξ 0)) := by rw [hlaw 0]; exact hi
    exact (integrable_map_measure hm.aestronglyMeasurable (hξm 0).aemeasurable).1 this
  have hindep : Pairwise (Function.onFun (fun a b => a ⟂ᵢ[P] b) (fun k => h ∘ ξ k)) := by
    intro i j hij
    exact (hind.comp (fun _ => h) (fun _ => hm)).indepFun hij
  have hident : ∀ i, IdentDistrib (h ∘ ξ i) (h ∘ ξ 0) P P := by
    intro i
    have : IdentDistrib (ξ i) (ξ 0) P P :=
      ⟨(hξm i).aemeasurable, (hξm 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩
    exact this.comp hm
  have key := strong_law_ae_real (fun k => h ∘ ξ k) hint hindep hident
  have hE : ∫ ω, (h ∘ ξ 0) ω ∂P = ∫ x, h x ∂μ := by
    rw [← hlaw 0, integral_map (hξm 0).aemeasurable hm.aestronglyMeasurable]
    rfl
  filter_upwards [key] with ω hω
  rw [← hE]
  simpa using hω

end InterpOptStop.SAA

open InterpOptStop.SAA in
theorem solution {n T : ℕ}
    (X : Set (Fin n → ℝ)) (Xi : Fin n → Set ℝ) (hXprod : X = Set.univ.pi Xi)
    (μ : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hinX : ∀ᵐ x ∂μ, ∀ k, x k ∈ X)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ) (hgm : ∀ k, Measurable (g k))
    (G : ℝ) (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Fin T → Fin n → ℝ) (hξm : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ P)
    (hlaw : ∀ k, P.map (ξ k) = μ) :
    ∀ (S : Tree n) (θ : Thresholds), ∀ᵐ ω ∂P,
      Tendsto (fun m : ℕ => Jhat (fun k => ξ k ω) m β g (policy S θ)) atTop
        (𝓝 (J μ β g (policy S θ))) := by
  intro S θ
  have hm := measurable_reward β g hgm S θ
  have hi : Integrable (fun x => reward β g (policy S θ) x) μ := by
    refine Integrable.mono' (integrable_const |G|) hm.aestronglyMeasurable ?_
    filter_upwards [hinX] with x hx
    simpa [Real.norm_eq_abs] using abs_reward_le' X β hβ0 hβ1 g G hg (policy S θ) x hx
  simpa [Jhat, J] using slln_comp μ P ξ hξm hind hlaw _ hm hi
