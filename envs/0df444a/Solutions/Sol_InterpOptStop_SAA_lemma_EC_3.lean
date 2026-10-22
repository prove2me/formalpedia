-- Prove2me | solution 1 for InterpOptStop.SAA.lemma_EC_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:44:34.301831+00:00
-- url     : https://prove2.me/submissions/4dfd70dd-4def-4900-9c85-332f7628308b

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

namespace InterpOptStop.SAA

/-- If two tree policies with the same skeleton disagree at `x`, then `x` falls, at some split
node, between the two split points. -/
lemma exists_split_of_act_ne {n : ℕ} (S : Tree n) (θ₁ θ₂ : Thresholds) (x : Fin n → ℝ) :
    ∀ p : List Bool, S.act θ₁ p x ≠ S.act θ₂ p x →
      ∃ s ∈ S.splitsAt p, x s.2 ∈ Set.uIcc (θ₁ s.1) (θ₂ s.1) := by
  induction S with
  | leaf a => intro p h; exact absurd rfl h
  | split i l r ihl ihr =>
    intro p h
    simp only [Tree.act] at h
    by_cases h1 : x i ≤ θ₁ p <;> by_cases h2 : x i ≤ θ₂ p
    · rw [if_pos h1, if_pos h2] at h
      obtain ⟨s, hs, hx⟩ := ihl _ h
      exact ⟨s, by simp [Tree.splitsAt, hs], hx⟩
    · refine ⟨(p, i), by simp [Tree.splitsAt], ?_⟩
      push_neg at h2
      exact Set.mem_uIcc.mpr (Or.inr ⟨h2.le, h1⟩)
    · refine ⟨(p, i), by simp [Tree.splitsAt], ?_⟩
      push_neg at h1
      exact Set.mem_uIcc.mpr (Or.inl ⟨h1.le, h2⟩)
    · rw [if_neg h1, if_neg h2] at h
      obtain ⟨s, hs, hx⟩ := ihr _ h
      exact ⟨s, by simp [Tree.splitsAt, hs], hx⟩

/-- Indicator form of `exists_split_of_act_ne`. -/
lemma one_le_sum_indicator {n : ℕ} (S : Tree n) (θ₁ θ₂ : Thresholds) (x : Fin n → ℝ)
    (h : policy S θ₁ x ≠ policy S θ₂ x) :
    1 ≤ ∑ s ∈ S.splits, (Set.uIcc (θ₁ s.1) (θ₂ s.1)).indicator (fun _ => (1 : ℝ)) (x s.2) := by
  obtain ⟨s, hs, hx⟩ := exists_split_of_act_ne S θ₁ θ₂ x [] h
  calc (1 : ℝ) = (Set.uIcc (θ₁ s.1) (θ₂ s.1)).indicator (fun _ => (1 : ℝ)) (x s.2) := by
        rw [Set.indicator_of_mem hx]
    _ ≤ _ := Finset.single_le_sum (f := fun s : List Bool × Fin n =>
          (Set.uIcc (θ₁ s.1) (θ₂ s.1)).indicator (fun _ => (1 : ℝ)) (x s.2))
          (fun s _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hs

lemma reward_nonneg_le {n T : ℕ} (X : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G)
    (π : (Fin n → ℝ) → Act) (x : Fin T → Fin n → ℝ) (hx : ∀ k, x k ∈ X) :
    0 ≤ reward β g π x ∧ reward β g π x ≤ G := by
  unfold reward
  split_ifs with h
  · set τ := (Finset.univ.filter fun k : Fin T => π (x k) = Act.stop).min' h
    have hp0 : 0 ≤ β ^ (τ : ℕ) := pow_nonneg hβ0 _
    have hp1 : β ^ (τ : ℕ) ≤ 1 := pow_le_one₀ hβ0 hβ1
    obtain ⟨hg0, hg1⟩ := hg τ (x τ) (hx τ)
    exact ⟨mul_nonneg hp0 hg0, by nlinarith⟩
  · exact ⟨le_rfl, hG⟩

lemma reward_congr {n T : ℕ} (β : ℝ) (g : Fin T → (Fin n → ℝ) → ℝ)
    (π₁ π₂ : (Fin n → ℝ) → Act) (x : Fin T → Fin n → ℝ) (h : ∀ j, π₁ (x j) = π₂ (x j)) :
    reward β g π₁ x = reward β g π₂ x := by
  simp only [reward_eq_sum, h]

/-- Pointwise form of Lemmas EC.2/EC.3: on a path in `𝒳` along which both policies continue at
the first period, the rewards differ by at most `G` times the number of (period, split) pairs at
which the state falls between the two split points. -/
lemma abs_reward_sub_le {n T : ℕ} (hT : 0 < T) (X : Set (Fin n → ℝ)) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (g : Fin T → (Fin n → ℝ) → ℝ) (G : ℝ)
    (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G)
    (S : Tree n) (θ₁ θ₂ : Thresholds) (x : Fin T → Fin n → ℝ) (hx : ∀ k, x k ∈ X)
    (h₁ : policy S θ₁ (x ⟨0, hT⟩) = Act.go) (h₂ : policy S θ₂ (x ⟨0, hT⟩) = Act.go) :
    |reward β g (policy S θ₁) x - reward β g (policy S θ₂) x| ≤
      G * ∑ j ∈ Finset.univ.filter (fun j : Fin T => (j : ℕ) ≠ 0),
        ∑ s ∈ S.splits, (Set.uIcc (θ₁ s.1) (θ₂ s.1)).indicator (fun _ => (1 : ℝ)) (x j s.2) := by
  have hG : 0 ≤ G := le_trans (hg ⟨0, hT⟩ _ (hx ⟨0, hT⟩)).1 (hg ⟨0, hT⟩ _ (hx ⟨0, hT⟩)).2
  have hnn : ∀ j : Fin T, 0 ≤ ∑ s ∈ S.splits,
      (Set.uIcc (θ₁ s.1) (θ₂ s.1)).indicator (fun _ => (1 : ℝ)) (x j s.2) :=
    fun j => Finset.sum_nonneg fun s _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases hall : ∀ j, policy S θ₁ (x j) = policy S θ₂ (x j)
  · rw [reward_congr β g _ _ x hall, sub_self, abs_zero]
    exact mul_nonneg hG (Finset.sum_nonneg fun j _ => hnn j)
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h0
      have : j = ⟨0, hT⟩ := Fin.ext h0
      rw [this, h₁, h₂] at hj
      exact hj rfl
    have hone := one_le_sum_indicator S θ₁ θ₂ (x j) hj
    have hsum : 1 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin T => (j : ℕ) ≠ 0),
        ∑ s ∈ S.splits, (Set.uIcc (θ₁ s.1) (θ₂ s.1)).indicator (fun _ => (1 : ℝ)) (x j s.2) :=
      le_trans hone (Finset.single_le_sum (f := fun j : Fin T => ∑ s ∈ S.splits,
        (Set.uIcc (θ₁ s.1) (θ₂ s.1)).indicator (fun _ => (1 : ℝ)) (x j s.2))
        (fun j _ => hnn j) (by simpa using hj0))
    obtain ⟨a0, a1⟩ := reward_nonneg_le X β hβ0 hβ1 g G hG hg (policy S θ₁) x hx
    obtain ⟨b0, b1⟩ := reward_nonneg_le X β hβ0 hβ1 g G hG hg (policy S θ₂) x hx
    rw [abs_le]
    constructor <;> nlinarith

end InterpOptStop.SAA

open InterpOptStop.SAA in
theorem solution {n T : ℕ}
    (hT : 0 < T)
    (xbar : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (Xi : Fin n → Set ℝ) (hXprod : X = Set.univ.pi Xi)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → (Fin n → ℝ) → ℝ)
    (G : ℝ) (hg : ∀ k, ∀ x ∈ X, 0 ≤ g k x ∧ g k x ≤ G) :
    ∀ (ys : ℕ → Fin T → Fin n → ℝ) (m : ℕ), (∀ k < m, ys k ⟨0, hT⟩ = xbar) →
      (∀ k < m, ∀ j, ys k j ∈ X) →
      ∀ (S : Tree n) (θ₁ θ₂ : Thresholds), policy S θ₁ xbar = Act.go →
      policy S θ₂ xbar = Act.go →
      |Jhat ys m β g (policy S θ₁) - Jhat ys m β g (policy S θ₂)| ≤
        G / m * ∑ k ∈ Finset.range m, ∑ j ∈ Finset.univ.filter (fun j : Fin T => (j : ℕ) ≠ 0),
          ∑ s ∈ S.splits, (Set.uIcc (θ₁ s.1) (θ₂ s.1)).indicator (fun _ => (1 : ℝ)) (ys k j s.2) := by
  intro ys m h0 hX S θ₁ θ₂ hgo₁ hgo₂
  have hpt : ∀ k ∈ Finset.range m, |reward β g (policy S θ₁) (ys k) -
      reward β g (policy S θ₂) (ys k)| ≤
      G * ∑ j ∈ Finset.univ.filter (fun j : Fin T => (j : ℕ) ≠ 0), ∑ s ∈ S.splits,
        (Set.uIcc (θ₁ s.1) (θ₂ s.1)).indicator (fun _ => (1 : ℝ)) (ys k j s.2) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    exact abs_reward_sub_le hT X β hβ0 hβ1 g G hg S θ₁ θ₂ (ys k) (hX k hk')
      (by rw [h0 k hk']; exact hgo₁) (by rw [h0 k hk']; exact hgo₂)
  unfold Jhat
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, Nat.abs_cast, div_eq_mul_inv,
    div_eq_mul_inv, mul_comm G, mul_assoc, Finset.mul_sum (s := Finset.range m) (a := G)]
  rw [mul_comm ((m : ℝ)⁻¹)]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg m))
  exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hpt)
