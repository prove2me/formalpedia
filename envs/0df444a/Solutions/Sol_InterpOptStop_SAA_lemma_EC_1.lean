-- Prove2me | solution 1 for InterpOptStop.SAA.lemma_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:52:51.945727+00:00
-- url     : https://prove2.me/submissions/bfc9a806-f248-4166-a3db-a862bdbe7f17

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
import Theorems.Thm_InterpOptStop_SAA_slab_bound
import Theorems.Thm_InterpOptStop_SAA_lemma_EC_2
import Theorems.Thm_InterpOptStop_SAA_lemma_EC_3
import Theorems.Thm_InterpOptStop_SAA_fixed_policy_slln
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

namespace InterpOptStop.SAA

/-- A tree policy reads its split points only at its split nodes. -/
lemma act_congr {n : ℕ} (S : Tree n) (θ θ' : Thresholds) (x : Fin n → ℝ) :
    ∀ p : List Bool, (∀ s ∈ S.splitsAt p, θ s.1 = θ' s.1) → S.act θ p x = S.act θ' p x := by
  induction S with
  | leaf a => intro p _; rfl
  | split i l r ihl ihr =>
    intro p h
    have hp : θ p = θ' p := h (p, i) (by simp [Tree.splitsAt])
    have hl : ∀ s ∈ l.splitsAt (p ++ [true]), θ s.1 = θ' s.1 :=
      fun s hs => h s (by simp [Tree.splitsAt, hs])
    have hr : ∀ s ∈ r.splitsAt (p ++ [false]), θ s.1 = θ' s.1 :=
      fun s hs => h s (by simp [Tree.splitsAt, hs])
    simp only [Tree.act, hp, ihl _ hl, ihr _ hr]

lemma le_clamp_iff (z t R : ℝ) (hz : |z| ≤ R) :
    z ≤ t ↔ z ≤ max (-(R + 1)) (min t (R + 1)) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hz
  rw [le_max_iff, le_min_iff]
  constructor
  · intro h; right; exact ⟨h, by linarith⟩
  · rintro (h | ⟨h, _⟩)
    · linarith
    · exact h

/-- On states with coordinates in `[-R, R]`, clamping the split points to `[-(R+1), R+1]`
does not change the action. -/
lemma act_clamp {n : ℕ} (S : Tree n) (θ : Thresholds) (R : ℝ) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ R) :
    ∀ p : List Bool, S.act θ p x = S.act (fun q => max (-(R + 1)) (min (θ q) (R + 1))) p x := by
  induction S with
  | leaf a => intro p; rfl
  | split i l r ihl ihr =>
    intro p
    have hiff := le_clamp_iff (x i) (θ p) R (hx i)
    simp only [Tree.act]
    by_cases h : x i ≤ θ p
    · rw [if_pos h, if_pos (hiff.1 h)]; exact ihl _
    · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]; exact ihr _

/-- If the policy stops in the first period, the reward is `g(1, x(1))`. -/
lemma reward_stop {n T : ℕ} (hT : 0 < T) (β : ℝ) (g : Fin T → (Fin n → ℝ) → ℝ)
    (π : (Fin n → ℝ) → Act) (x : Fin T → Fin n → ℝ) (h : π (x ⟨0, hT⟩) = Act.stop) :
    reward β g π x = g ⟨0, hT⟩ (x ⟨0, hT⟩) := by
  rw [reward_eq_sum, Finset.sum_eq_single ⟨0, hT⟩]
  · rw [if_pos ⟨h, fun j hj => absurd hj (by rw [Fin.lt_def]; simp)⟩]
    simp
  · intro k _ hk
    rw [if_neg]
    rintro ⟨_, hmin⟩
    refine hmin ⟨0, hT⟩ ?_ h
    rw [Fin.lt_def]
    have : (k : ℕ) ≠ 0 := fun h0 => hk (Fin.ext h0)
    simp only
    omega
  · simp

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
    ∀ (S : Tree n) (ε : ℝ), 0 < ε → ∀ᵐ ω ∂P, ∃ Ω₁ : ℕ, ∀ m ≥ Ω₁, ∀ θ : Thresholds,
      |J μ β g (policy S θ) - Jhat (fun k => ξ k ω) m β g (policy S θ)| ≤ ε := by
  intro S ε hε
  obtain ⟨x0, hx0⟩ := hinX.exists
  have hG : 0 ≤ G := le_trans (hg ⟨0, hT⟩ _ (hx0 ⟨0, hT⟩)).1 (hg ⟨0, hT⟩ _ (hx0 ⟨0, hT⟩)).2
  -- a bounding box for `𝒳`
  set y0 := x0 ⟨0, hT⟩ with hy0
  set R : ℝ := ‖y0‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  have hXR : ∀ y ∈ X, ∀ i, |y i| ≤ R := by
    intro y hy i
    have h1 := hXdiam y hy y0 (hx0 _)
    have h2 := norm_le_pi_norm (y - y0) i
    have h3 := norm_le_pi_norm y0 i
    simp only [Pi.sub_apply, Real.norm_eq_abs] at h2 h3
    have := abs_sub_abs_le_abs_sub (y i) (y0 i)
    linarith
  -- clamping the split points
  set cl : Thresholds → Thresholds := fun θ q => max (-(R + 1)) (min (θ q) (R + 1)) with hcl
  have hcl_path : ∀ θ x, (∀ k, x k ∈ X) →
      reward β g (policy S θ) x = reward β g (policy S (cl θ)) x := by
    intro θ x hx
    apply reward_congr
    intro j
    exact act_clamp S θ R (x j) (hXR _ (hx j)) []
  have hgood : ∀ᵐ ω ∂P, ∀ k, (∀ j, ξ k ω j ∈ X) ∧ ξ k ω ⟨0, hT⟩ = xbar := by
    rw [ae_all_iff]
    intro k
    have : ∀ᵐ y ∂(P.map (ξ k)), (∀ j, y j ∈ X) ∧ y ⟨0, hT⟩ = xbar := by
      rw [hlaw k]; exact hinX.and hstart
    exact ae_of_ae_map (hξm k).aemeasurable this
  have hJcl : ∀ θ, J μ β g (policy S θ) = J μ β g (policy S (cl θ)) := by
    intro θ
    unfold J
    apply integral_congr_ae
    filter_upwards [hinX] with x hx
    exact hcl_path θ x hx
  have hJhatcl : ∀ ω, (∀ k, (∀ j, ξ k ω j ∈ X) ∧ ξ k ω ⟨0, hT⟩ = xbar) → ∀ m θ,
      Jhat (fun k => ξ k ω) m β g (policy S θ) = Jhat (fun k => ξ k ω) m β g (policy S (cl θ)) := by
    intro ω hω m θ
    unfold Jhat
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact hcl_path θ _ (hω k).1
  -- split points as a finite-dimensional vector
  set A : Finset (List Bool) := S.splits.image Prod.fst with hA
  set ext : (A → ℝ) → Thresholds := fun u p => if h : p ∈ A then u ⟨p, h⟩ else 0 with hext
  set restr : Thresholds → (A → ℝ) := fun θ a => θ a.1 with hrestr
  have hext_restr : ∀ θ, ∀ s ∈ S.splits, ext (restr θ) s.1 = θ s.1 := by
    intro θ s hs
    have : s.1 ∈ A := Finset.mem_image_of_mem _ hs
    simp [hext, hrestr, this]
  have hpol_restr : ∀ θ, policy S (ext (restr θ)) = policy S θ := by
    intro θ
    funext x
    exact act_congr S _ _ x [] (fun s hs => hext_restr θ s hs)
  -- properties of `f`
  have hfnn : ∀ r, 0 ≤ r → 0 ≤ f r := by
    intro r hr
    have := hfmono.monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hr) hr
    rwa [hf0] at this
  have hfmon : ∀ r r', 0 ≤ r → r ≤ r' → f r ≤ f r' := fun r r' hr hrr' =>
    hfmono.monotoneOn (Set.mem_Ici.mpr hr) (Set.mem_Ici.mpr (le_trans hr hrr')) hrr'
  -- choice of `δ` and `γ`
  set C : ℝ := G * T * S.splits.card with hCdef
  have hC : 0 ≤ C := by positivity
  set η : ℝ := ε / (6 * (C + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ0, hδ0, hδ0f⟩ := Metric.continuousWithinAt_iff.1 (hfcont 0 (Set.mem_Ici.2 le_rfl)) η hη
  set δ : ℝ := δ0 / 4 with hδdef
  have hδ : 0 < δ := by positivity
  have hf2δ : f (2 * δ) < η := by
    have h := hδ0f (x := 2 * δ) (Set.mem_Ici.2 (by positivity))
      (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    rw [Real.dist_eq, hf0, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hCf : C * f (2 * δ) ≤ ε / 6 := by
    have h1 : C * f (2 * δ) ≤ C * η := mul_le_mul_of_nonneg_left hf2δ.le hC
    have h2 : C * η ≤ ε / 6 := by
      rw [hηdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  set γ : ℝ := ε / (6 * (G + 1)) with hγdef
  have hγ : 0 < γ := by positivity
  have hGγ : G * γ ≤ ε / 6 := by
    rw [hγdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- a finite `δ`-net of the continuing split points
  set Vgo : Set (A → ℝ) :=
    {u | (∀ a, u a ∈ Set.Icc (-(R + 1)) (R + 1)) ∧ policy S (ext u) xbar = Act.go} with hVgo
  have htb : TotallyBounded Vgo :=
    (isCompact_univ_pi (fun _ : A => isCompact_Icc (a := -(R + 1)) (b := R + 1))).totallyBounded.subset
      (fun u hu => fun a _ => hu.1 a)
  obtain ⟨N, hNsub, hNfin, hNcov⟩ := Metric.finite_approx_of_totallyBounded htb δ hδ
  -- the envelope functions
  set F := Finset.univ.filter (fun j : Fin T => (j : ℕ) ≠ 0) with hF
  set B : (A → ℝ) → Fin T → (List Bool × Fin n) → Set (Fin T → Fin n → ℝ) := fun u j s =>
    {x | x j s.2 ∈ Set.Icc (ext u s.1 - δ) (ext u s.1 + δ)} with hB
  have hBm : ∀ u j s, MeasurableSet (B u j s) := by
    intro u j s
    have hm : Measurable (fun x : Fin T → Fin n → ℝ => x j s.2) :=
      (measurable_pi_apply s.2).comp (measurable_pi_apply j)
    exact hm measurableSet_Icc
  set e : (A → ℝ) → (Fin T → Fin n → ℝ) → ℝ := fun u x =>
    ∑ j ∈ F, ∑ s ∈ S.splits, (B u j s).indicator 1 x with he
  have he_meas : ∀ u, Measurable (e u) := by
    intro u
    exact Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun s _ =>
      measurable_const.indicator (hBm u j s)
  have hBint : ∀ u j s, Integrable ((B u j s).indicator (1 : (Fin T → Fin n → ℝ) → ℝ)) μ :=
    fun u j s => (integrable_const (1 : ℝ)).indicator (hBm u j s)
  have he_int : ∀ u, Integrable (e u) μ := fun u =>
    integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun s _ => hBint u j s
  have hslab := InterpOptStop.SAA.slab_bound hT X Xi hXprod hXtb hXdiam μ hinX f hf0 hfmono
    hfcont hA3
  have he_bound : ∀ u, ∫ x, e u x ∂μ ≤ T * S.splits.card * f (2 * δ) := by
    intro u
    rw [he]
    simp only
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun s _ => hBint u j s]
    have : ∀ j ∈ F, ∫ x, ∑ s ∈ S.splits, (B u j s).indicator 1 x ∂μ ≤ S.splits.card * f (2 * δ) := by
      intro j hj
      rw [integral_finset_sum _ fun s _ => hBint u j s]
      have hj0 : (j : ℕ) ≠ 0 := by simpa [hF] using hj
      calc ∑ s ∈ S.splits, ∫ x, (B u j s).indicator 1 x ∂μ
          ≤ ∑ s ∈ S.splits, f (2 * δ) := by
            apply Finset.sum_le_sum
            intro s _
            rw [integral_indicator_one (hBm u j s), measureReal_def]
            have h := hslab j hj0 s.2 (ext u s.1 - δ) (ext u s.1 + δ)
            rw [Set.uIcc_of_le (by linarith)] at h
            have h2 : |ext u s.1 - δ - (ext u s.1 + δ)| = 2 * δ := by
              rw [show ext u s.1 - δ - (ext u s.1 + δ) = -(2 * δ) by ring, abs_neg,
                abs_of_pos (by positivity)]
            rw [h2] at h
            exact h
        _ = S.splits.card * f (2 * δ) := by rw [Finset.sum_const, nsmul_eq_mul]
    calc ∑ j ∈ F, ∫ x, ∑ s ∈ S.splits, (B u j s).indicator 1 x ∂μ
        ≤ ∑ j ∈ F, (S.splits.card * f (2 * δ)) := Finset.sum_le_sum this
      _ = F.card * (S.splits.card * f (2 * δ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ T * (S.splits.card * f (2 * δ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) (hfnn _ (by positivity)))
          have : F.card ≤ T := by
            calc F.card ≤ (Finset.univ : Finset (Fin T)).card := Finset.card_filter_le _ _
              _ = T := by simp
          exact_mod_cast this
      _ = T * S.splits.card * f (2 * δ) := by ring
  -- almost sure convergence on the finite net
  have hE2 : ∀ᵐ ω ∂P, ∀ u ∈ N, Tendsto (fun m : ℕ => Jhat (fun k => ξ k ω) m β g (policy S (ext u)))
      atTop (𝓝 (J μ β g (policy S (ext u)))) :=
    (ae_ball_iff hNfin.countable).2 (fun u _ => InterpOptStop.SAA.fixed_policy_slln X Xi hXprod μ
      hinX β hβ0 hβ1 g hgm G hg P ξ hξm hind hlaw S (ext u))
  have hE3 : ∀ᵐ ω ∂P, ∀ u ∈ N, Tendsto (fun m : ℕ => (∑ k ∈ Finset.range m, e u (ξ k ω)) / m)
      atTop (𝓝 (∫ x, e u x ∂μ)) :=
    (ae_ball_iff hNfin.countable).2 (fun u _ => slln_comp μ P ξ hξm hind hlaw (e u) (he_meas u)
      (he_int u))
  filter_upwards [hgood, hE2, hE3] with ω hω hω2 hω3
  have hev : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧ ∀ u ∈ N,
      |J μ β g (policy S (ext u)) - Jhat (fun k => ξ k ω) m β g (policy S (ext u))| ≤ ε / 3 ∧
      (∑ k ∈ Finset.range m, e u (ξ k ω)) / m ≤ ∫ x, e u x ∂μ + γ := by
    refine (eventually_ge_atTop 1).and ((hNfin.eventually_all).2 fun u hu => ?_)
    have e1 := (Metric.tendsto_nhds.1 (hω2 u hu)) (ε / 3) (by positivity)
    have e2 := (hω3 u hu).eventually (gt_mem_nhds (show ∫ x, e u x ∂μ < ∫ x, e u x ∂μ + γ by linarith))
    filter_upwards [e1, e2] with m hm1 hm2
    refine ⟨?_, hm2.le⟩
    rw [Real.dist_eq] at hm1
    rw [abs_sub_comm]
    exact hm1.le
  obtain ⟨Ω₁, hΩ₁⟩ := eventually_atTop.1 hev
  refine ⟨Ω₁, fun m hm θ => ?_⟩
  obtain ⟨hm1, hmN⟩ := hΩ₁ m hm
  rw [hJcl θ, hJhatcl ω hω m θ]
  set θc := cl θ with hθc
  by_cases hstop : policy S θc xbar = Act.stop
  · -- the policy stops immediately: both values equal `g(1, x̄)`
    have hJ : J μ β g (policy S θc) = g ⟨0, hT⟩ xbar := by
      unfold J
      rw [integral_congr_ae (g := fun _ => g ⟨0, hT⟩ xbar)]
      · simp
      · filter_upwards [hstart] with x hx
        rw [reward_stop hT β g _ x (by rw [hx]; exact hstop), hx]
    have hJh : Jhat (fun k => ξ k ω) m β g (policy S θc) = g ⟨0, hT⟩ xbar := by
      unfold Jhat
      rw [Finset.sum_congr rfl (g := fun _ => g ⟨0, hT⟩ xbar) (fun k _ => by
        show reward β g (policy S θc) (ξ k ω) = g ⟨0, hT⟩ xbar
        rw [reward_stop hT β g _ _ (by rw [(hω k).2]; exact hstop), (hω k).2])]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      field_simp
    rw [hJ, hJh, sub_self, abs_zero]
    linarith
  · have hgo : policy S θc xbar = Act.go := by
      cases h : policy S θc xbar
      · exact absurd h hstop
      · rfl
    set u0 := restr θc with hu0def
    have hu0 : u0 ∈ Vgo := by
      refine ⟨fun a => ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩, ?_⟩
      exact (congrFun (hpol_restr θc) xbar).trans hgo
    obtain ⟨ut, hutN, hut⟩ := Set.mem_iUnion₂.1 (hNcov hu0)
    set θt := ext ut with hθt
    have hgo_t : policy S θt xbar = Act.go := (hNsub hutN).2
    have hclose : ∀ s ∈ S.splits, |θc s.1 - θt s.1| < δ := by
      intro s hs
      have hAs : s.1 ∈ A := Finset.mem_image_of_mem _ hs
      have h1 := dist_le_pi_dist u0 ut ⟨s.1, hAs⟩
      rw [Metric.mem_ball] at hut
      have h2 : θt s.1 = ut ⟨s.1, hAs⟩ := by simp [hθt, hext, hAs]
      rw [h2]
      rw [Real.dist_eq] at h1
      exact lt_of_le_of_lt h1 hut
    -- (a)
    have ha := InterpOptStop.SAA.lemma_EC_2 hT xbar X Xi hXprod hXtb hXdiam μ hstart hinX β hβ0
      hβ1 g hgm G hg f hf0 hfmono hfcont hA3 S θc θt hgo hgo_t
    have ha' : G * T * ∑ s ∈ S.splits, f |θc s.1 - θt s.1| ≤ ε / 6 := by
      have hsum : ∑ s ∈ S.splits, f |θc s.1 - θt s.1| ≤ S.splits.card * f (2 * δ) := by
        calc ∑ s ∈ S.splits, f |θc s.1 - θt s.1| ≤ ∑ s ∈ S.splits, f (2 * δ) := by
              apply Finset.sum_le_sum
              intro s hs
              exact hfmon _ _ (abs_nonneg _) (by linarith [hclose s hs])
          _ = S.splits.card * f (2 * δ) := by rw [Finset.sum_const, nsmul_eq_mul]
      have : G * T * ∑ s ∈ S.splits, f |θc s.1 - θt s.1| ≤ G * T * (S.splits.card * f (2 * δ)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have h2 : G * T * (S.splits.card * f (2 * δ)) = C * f (2 * δ) := by rw [hCdef]; ring
      linarith
    -- (b)
    have hb := (hmN ut hutN).1
    -- (c)
    have hc := InterpOptStop.SAA.lemma_EC_3 hT xbar X Xi hXprod β hβ0 hβ1 g G hg
      (fun k => ξ k ω) m (fun k _ => (hω k).2) (fun k _ j => (hω k).1 j) S θc θt hgo hgo_t
    have hind_le : ∀ k, ∀ j, ∀ s ∈ S.splits,
        (Set.uIcc (θc s.1) (θt s.1)).indicator (fun _ => (1 : ℝ)) (ξ k ω j s.2) ≤
          (B ut j s).indicator 1 (ξ k ω) := by
      intro k j s hs
      have hsub : Set.uIcc (θc s.1) (θt s.1) ⊆ Set.Icc (ext ut s.1 - δ) (ext ut s.1 + δ) := by
        have hcs := hclose s hs
        rw [abs_lt] at hcs
        apply Set.uIcc_subset_Icc
        · constructor <;> linarith
        · constructor <;> linarith
      by_cases hmem : ξ k ω j s.2 ∈ Set.uIcc (θc s.1) (θt s.1)
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show ξ k ω ∈ B ut j s from hsub hmem)]
        simp
      · rw [Set.indicator_of_notMem hmem]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hc' : G / m * ∑ k ∈ Finset.range m, ∑ j ∈ F, ∑ s ∈ S.splits,
        (Set.uIcc (θc s.1) (θt s.1)).indicator (fun _ => (1 : ℝ)) (ξ k ω j s.2) ≤
        G * ((∑ k ∈ Finset.range m, e ut (ξ k ω)) / m) := by
      rw [mul_div_assoc', div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
      apply mul_le_mul_of_nonneg_left _ hG
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro s hs
      exact hind_le k j s hs
    have hc'' : G * ((∑ k ∈ Finset.range m, e ut (ξ k ω)) / m) ≤ ε / 3 := by
      have h1 := (hmN ut hutN).2
      have h2 := he_bound ut
      have h3 : G * ((∑ k ∈ Finset.range m, e ut (ξ k ω)) / m) ≤
          G * (T * S.splits.card * f (2 * δ) + γ) :=
        mul_le_mul_of_nonneg_left (by linarith) hG
      have h4 : G * (T * S.splits.card * f (2 * δ) + γ) = C * f (2 * δ) + G * γ := by
        rw [hCdef]; ring
      linarith
    have tri : ∀ a b c d : ℝ, |a - d| ≤ |a - b| + |b - c| + |c - d| := by
      intro a b c d
      have := abs_sub_le a b d
      have := abs_sub_le b c d
      linarith
    have := tri (J μ β g (policy S θc)) (J μ β g (policy S θt))
      (Jhat (fun k => ξ k ω) m β g (policy S θt)) (Jhat (fun k => ξ k ω) m β g (policy S θc))
    rw [abs_sub_comm (Jhat (fun k => ξ k ω) m β g (policy S θt))] at this
    linarith
