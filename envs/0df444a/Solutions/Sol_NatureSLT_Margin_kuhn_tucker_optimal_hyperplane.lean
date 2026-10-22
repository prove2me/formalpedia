-- Prove2me | solution 1 for NatureSLT.Margin.kuhn_tucker_optimal_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:48:49.390651+00:00
-- url     : https://prove2.me/submissions/660cbc7a-9db7-4ba2-bcc2-01ab8f3c8cfa

import Mathlib
import Definitions.Def_NatureSLT_Margin_optimalHyperplane
open scoped InnerProductSpace
open NatureSLT.Margin
open Matrix
theorem g69a1_cara {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E] (v : ι → E)
    (t : Finset ι) : ∀ l : ι → ℝ, (∀ i, 0 ≤ l i) → ∃ s ⊆ t, ∃ l' : ι → ℝ, (∀ i, 0 ≤ l' i) ∧
      LinearIndepOn ℝ v (s : Set ι) ∧ ∑ i ∈ s, l' i • v i = ∑ i ∈ t, l i • v i := by
  induction t using Finset.strongInduction with
  | H t ih =>
  intro l hl
  by_cases hli : LinearIndepOn ℝ v (t : Set ι)
  · exact ⟨t, subset_rfl, l, hl, hli, rfl⟩
  rw [not_linearIndepOn_finset_iffₛ] at hli
  obtain ⟨f, g, hfg, i0, hi0t, hi0⟩ := hli
  have hsum0 : ∑ i ∈ t, (f i - g i) • v i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hfg, sub_self]
  -- get ν supported on t with positive entry
  obtain ⟨ν, hνsum, hνsupp, i1, hi1t, hi1⟩ : ∃ ν : ι → ℝ, ∑ i ∈ t, ν i • v i = 0 ∧
      (∀ i, i ∉ t → ν i = 0) ∧ ∃ i ∈ t, 0 < ν i := by
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hi0) with h | h
    · refine ⟨fun i => if i ∈ t then -(f i - g i) else 0, ?_, ?_, i0, hi0t, ?_⟩
      · have hc : ∀ i ∈ t, (if i ∈ t then -(f i - g i) else 0) • v i = -((f i - g i) • v i) := by
          intro i hi; rw [if_pos hi, neg_smul]
        beta_reduce
        rw [Finset.sum_congr rfl hc, Finset.sum_neg_distrib, hsum0, neg_zero]
      · intro i hi; simp [hi]
      · simp only [hi0t, if_true]; linarith
    · refine ⟨fun i => if i ∈ t then (f i - g i) else 0, ?_, ?_, i0, hi0t, ?_⟩
      · have hc : ∀ i ∈ t, (if i ∈ t then (f i - g i) else 0) • v i = (f i - g i) • v i := by
          intro i hi; rw [if_pos hi]
        beta_reduce
        rw [Finset.sum_congr rfl hc, hsum0]
      · intro i hi; simp [hi]
      · simp only [hi0t, if_true]; linarith
  set P := t.filter (fun i => 0 < ν i) with hP
  have hPne : P.Nonempty := ⟨i1, by simp [hP, hi1t, hi1]⟩
  obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image P (fun i => l i / ν i) hPne
  have hjt : j ∈ t := (Finset.mem_filter.mp hjP).1
  have hjpos : 0 < ν j := (Finset.mem_filter.mp hjP).2
  set θ := l j / ν j with hθ
  have hθnn : 0 ≤ θ := div_nonneg (hl j) hjpos.le
  set l' : ι → ℝ := fun i => l i - θ * ν i with hl'
  have hl'nn : ∀ i, 0 ≤ l' i := by
    intro i
    simp only [hl']
    by_cases hit : i ∈ t
    · by_cases hνi : 0 < ν i
      · have hiP : i ∈ P := by simp [hP, hit, hνi]
        have := hjmin i hiP
        rw [le_div_iff₀ hνi] at this
        linarith
      · push Not at hνi
        nlinarith [hl i]
    · rw [hνsupp i hit]; simp [hl i]
  have hl'j : l' j = 0 := by
    simp only [hl', hθ]; field_simp; ring
  have hsum' : ∑ i ∈ t.erase j, l' i • v i = ∑ i ∈ t, l i • v i := by
    rw [Finset.sum_erase _ (by rw [hl'j, zero_smul])]
    simp only [hl', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hνsum,
      smul_zero, sub_zero]
  obtain ⟨s, hs, l'', hl'', hli, hs'⟩ := ih (t.erase j) (Finset.erase_ssubset hjt) l' hl'nn
  exact ⟨s, hs.trans (Finset.erase_subset _ _), l'', hl'', hli, hs'.trans hsum'⟩

theorem g69a1_cone_closed {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] (v : ι → κ → ℝ) :
    IsClosed {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} := by
  classical
  have heq : {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} =
      ⋃ s ∈ {s : Finset ι | LinearIndepOn ℝ v (s : Set ι)},
        (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) '' {m | ∀ i, 0 ≤ m i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨s, -, l', hl', hli, hs⟩ := g69a1_cara v Finset.univ l hl
      refine ⟨s, hli, fun i => l' i, fun i => hl' i, ?_⟩
      rw [Fintype.linearCombination_apply, ← hs]
      exact (Finset.sum_coe_sort s (fun i => l' i • v i))
    · rintro ⟨s, -, m, hm, rfl⟩
      refine ⟨fun i => if h : i ∈ s then m ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i; by_cases h : i ∈ s <;> simp [h, hm]
      · rw [Fintype.linearCombination_apply]
        rw [← Finset.sum_subset (Finset.subset_univ s)]
        · rw [← Finset.sum_coe_sort s]
          apply Finset.sum_congr rfl
          intro i _
          simp
        · intro i _ hi; simp [hi]
  rw [heq]
  apply Set.Finite.isClosed_biUnion (Set.toFinite _)
  intro s hs
  have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (linearIndependent_iff_injective_fintypeLinearCombination).mp hs
  apply (LinearMap.isClosedEmbedding_of_injective hinj).isClosedMap
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

theorem g69a1_farkas {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : ι → κ → ℝ) (a : κ → ℝ)
    (ha : ¬ ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ a = ∑ i, l i • v i) :
    ∃ x : κ → ℝ, a ⬝ᵥ x < 0 ∧ ∀ i, 0 ≤ v i ⬝ᵥ x := by
  classical
  set C := {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} with hC
  have hconv : Convex ℝ C := by
    rintro y ⟨l, hl, rfl⟩ z ⟨m, hm, rfl⟩ α β hα hβ _
    refine ⟨fun i => α * l i + β * m i, fun i => by have := hl i; have := hm i; positivity, ?_⟩
    simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]
  obtain ⟨f, u, hfa, hfC⟩ := geometric_hahn_banach_point_closed hconv (g69a1_cone_closed v) ha
  have hu : u < 0 := by
    have := hfC 0 ⟨0, fun _ => le_rfl, by simp⟩
    simpa using this
  have hfnn : ∀ y ∈ C, 0 ≤ f y := by
    intro y hy
    by_contra hneg
    push Not at hneg
    obtain ⟨l, hl, rfl⟩ := hy
    set t : ℝ := u / f (∑ i, l i • v i) with ht
    have htpos : 0 < t := div_pos_of_neg_of_neg hu hneg
    have hmem : t • (∑ i, l i • v i) ∈ C :=
      ⟨fun i => t * l i, fun i => mul_nonneg htpos.le (hl i), by
        simp only [Finset.smul_sum, mul_smul]⟩
    have := hfC _ hmem
    rw [map_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  let x : κ → ℝ := fun j => f (Pi.single j 1)
  have hfx : ∀ y : κ → ℝ, f y = y ⬝ᵥ x := by
    intro y
    conv_lhs => rw [show y = ∑ j, y j • Pi.single j (1:ℝ) by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, dotProduct, x]
  refine ⟨x, ?_, ?_⟩
  · rw [← hfx]; linarith
  · intro i
    rw [← hfx]
    apply hfnn
    refine ⟨Pi.single i 1, fun j => ?_, ?_⟩
    · by_cases h : j = i <;> simp [Pi.single_apply, h]
    · simp [Pi.single_apply]
open Filter Topology

theorem g70slt_inner_eq {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, v⟫_ℝ = ∑ j, u j * v j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem g70slt_kkt_exists {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (w₀ : EuclideanSpace ℝ (Fin n)) (b₀ : ℝ)
    (hopt : IsOptimalHyperplane x y w₀ b₀) :
    ∃ α₀ : Fin ℓ → ℝ, (∀ i, 0 ≤ α₀ i) ∧ ∑ i, α₀ i * y i = 0 ∧
        w₀ = ∑ i, (y i * α₀ i) • x i ∧
        w₀ = ∑ i ∈ supportVectors x y w₀ b₀, (y i * α₀ i) • x i ∧
        ∀ i, α₀ i * ((⟪x i, w₀⟫_ℝ - b₀) * y i - 1) = 0 := by
  classical
  set SV := supportVectors x y w₀ b₀ with hSV
  have hmemSV : ∀ i, i ∈ SV ↔ y i * (⟪x i, w₀⟫_ℝ - b₀) = 1 := by
    intro i; rw [hSV, supportVectors, Finset.mem_filter]; simp
  let v : Fin ℓ → Option (Fin n) → ℝ := fun i o =>
    if i ∈ SV then Option.elim o (-y i) (fun j => y i * x i j) else 0
  let a : Option (Fin n) → ℝ := fun o => Option.elim o 0 (fun j => w₀ j)
  by_cases hc : ∃ l : Fin ℓ → ℝ, (∀ i, 0 ≤ l i) ∧ a = ∑ i, l i • v i
  · obtain ⟨l, hl, hal⟩ := hc
    set α : Fin ℓ → ℝ := fun i => if i ∈ SV then l i else 0 with hα
    have hnone := congrFun hal none
    have hsome : ∀ j, w₀ j = ∑ i, (y i * α i) * x i j := by
      intro j
      have := congrFun hal (some j)
      simp only [a, v, Option.elim, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hα]; split_ifs <;> ring
    have hw : w₀ = ∑ i, (y i * α i) • x i := by
      ext j; rw [hsome j]; simp [Finset.sum_apply]
    refine ⟨α, fun i => by simp only [hα]; split_ifs; exact hl i; exact le_rfl, ?_, hw, ?_, ?_⟩
    · simp only [a, v, Option.elim, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hnone
      have : ∑ i, α i * y i = -∑ i, l i * (if i ∈ SV then -y i else 0) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hα]; split_ifs <;> ring
      rw [this, ← hnone, neg_zero]
    · conv_lhs => rw [hw]
      rw [hSV, supportVectors, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs with h1
      · rfl
      · have : i ∉ SV := fun h => h1 ((hmemSV i).mp h)
        simp [hα, this]
    · intro i
      simp only [hα]
      split_ifs with h
      · have := (hmemSV i).mp h
        rw [show (⟪x i, w₀⟫_ℝ - b₀) * y i = y i * (⟪x i, w₀⟫_ℝ - b₀) by ring, this]; ring
      · ring
  · obtain ⟨d, hd1, hd2⟩ := g69a1_farkas v a hc
    set dw : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => d (some j)) with hdw
    set db := d none
    have hdwj : ∀ j, dw j = d (some j) := fun j => rfl
    have hneg : ⟪w₀, dw⟫_ℝ < 0 := by
      rw [g70slt_inner_eq]
      simp only [dotProduct, Fintype.sum_option, a, Option.elim, zero_mul, zero_add] at hd1
      simpa [hdwj] using hd1
    have hact : ∀ i ∈ SV, 0 ≤ y i * (⟪dw, x i⟫_ℝ - db) := by
      intro i hi
      have := hd2 i
      simp only [dotProduct, Fintype.sum_option, v, if_pos hi, Option.elim] at this
      rw [g70slt_inner_eq]
      have e : y i * (∑ j, dw j * x i j - db) = -y i * d none + ∑ j, y i * x i j * d (some j) := by
        rw [mul_sub, Finset.mul_sum]; simp only [hdwj]
        have : ∀ j, y i * (d (some j) * x i j) = y i * x i j * d (some j) := fun j => by ring
        simp only [this]; ring
      rw [e]; exact this
    -- perturbation
    have hcons : ∀ i, ∀ᶠ t in 𝓝[>] (0:ℝ),
        1 ≤ y i * (⟪w₀ + t • dw, x i⟫_ℝ - (b₀ + t * db)) := by
      intro i
      have e : ∀ t : ℝ, y i * (⟪w₀ + t • dw, x i⟫_ℝ - (b₀ + t * db)) =
          y i * (⟪w₀, x i⟫_ℝ - b₀) + t * (y i * (⟪dw, x i⟫_ℝ - db)) := by
        intro t; rw [inner_add_left, real_inner_smul_left]; ring
      simp only [e]
      have hs := hopt.1 i
      by_cases hi : i ∈ SV
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have := hact i hi
        have h2 : 0 ≤ t * (y i * (⟪dw, x i⟫_ℝ - db)) := mul_nonneg (le_of_lt ht) this
        linarith
      · have hgt : 1 < y i * (⟪w₀, x i⟫_ℝ - b₀) := by
          rcases hs.lt_or_eq with h | h
          · exact h
          · exfalso; apply hi; rw [hmemSV, real_inner_comm]; exact h.symm
        have ht : Tendsto (fun t : ℝ => y i * (⟪w₀, x i⟫_ℝ - b₀) + t * (y i * (⟪dw, x i⟫_ℝ - db)))
            (𝓝[>] 0) (𝓝 (y i * (⟪w₀, x i⟫_ℝ - b₀) + 0 * (y i * (⟪dw, x i⟫_ℝ - db)))) :=
          tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto (by fun_prop) 0)
        rw [zero_mul, add_zero] at ht
        filter_upwards [ht.eventually (lt_mem_nhds hgt)] with t h using h.le
    have hnorm : ∀ᶠ t in 𝓝[>] (0:ℝ), 2 * ⟪w₀, dw⟫_ℝ + t * ‖dw‖ ^ 2 < 0 := by
      have ht : Tendsto (fun t : ℝ => 2 * ⟪w₀, dw⟫_ℝ + t * ‖dw‖ ^ 2) (𝓝[>] 0)
          (𝓝 (2 * ⟪w₀, dw⟫_ℝ + 0 * ‖dw‖ ^ 2)) :=
        tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto (by fun_prop) 0)
      rw [zero_mul, add_zero] at ht
      exact ht.eventually (gt_mem_nhds (by linarith))
    obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := (((Filter.eventually_all.mpr hcons).and hnorm).and
      self_mem_nhdsWithin).exists
    have hle := hopt.2 (w₀ + t • dw) (b₀ + t * db) ht1
    have e : ‖w₀ + t • dw‖ ^ 2 = ‖w₀‖ ^ 2 + t * (2 * ⟪w₀, dw⟫_ℝ + t * ‖dw‖ ^ 2) := by
      rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have ht3' : (0:ℝ) < t := ht3
    nlinarith

theorem g70slt_quad {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n)) (y α : Fin ℓ → ℝ) :
    ‖∑ i, (y i * α i) • x i‖ ^ 2 = ∑ i, ∑ j, α i * α j * y i * y j * ⟪x i, x j⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [real_inner_smul_left, real_inner_smul_right]; ring

/-- weak duality pieces: for feasible α and canonical (w,b), ∑ α ≤ ⟪w(α), w⟫ -/
theorem g70slt_weak_dual {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (α : Fin ℓ → ℝ) (hα : (∀ i, 0 ≤ α i) ∧ ∑ i, α i * y i = 0)
    (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) (hs : IsCanonicalSeparating x y w b) :
    ∑ i, α i * (y i * (⟪w, x i⟫_ℝ - b) - 1) = ⟪∑ i, (y i * α i) • x i, w⟫_ℝ - ∑ i, α i ∧
    0 ≤ ∑ i, α i * (y i * (⟪w, x i⟫_ℝ - b) - 1) := by
  constructor
  · rw [sum_inner]
    have : ∑ i, α i * (y i * (⟪w, x i⟫_ℝ - b) - 1) =
        ∑ i, (y i * α i) * ⟪x i, w⟫_ℝ - b * ∑ i, α i * y i - ∑ i, α i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_comm]; ring
    rw [this, hα.2]
    simp only [real_inner_smul_left]; ring
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hα.1 i) (by linarith [hs i])


/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §5.5, p. 134, (5.13)–(5.16):
by the Kühn–Tucker theorem, necessary and sufficient conditions for the separating hyperplane
`(w₀, b₀)` (satisfying (5.11)) to be the optimal hyperplane are that there exist coefficients
`α⁰₁, …, α⁰_ℓ` with
* (5.13) `∑ᵢ α⁰ᵢ yᵢ = 0`, `α⁰ᵢ ≥ 0`;
* (5.14) `w₀ = ∑ᵢ yᵢ α⁰ᵢ xᵢ`;
* (5.15) `w₀ = ∑_{support vectors} yᵢ α⁰ᵢ xᵢ`;
* (5.16) `α⁰ᵢ {[(xᵢ · w₀) − b₀] yᵢ − 1} = 0`, `i = 1, …, ℓ`.

Training data `(x₁, y₁), …, (x_ℓ, y_ℓ)`, `xᵢ ∈ ℝⁿ`, `yᵢ ∈ {+1, −1}`, both classes present
(§5.5: "belonging to two different classes"). Optimality is `IsOptimalHyperplane`
(minimizing `‖w‖²`, equivalently `½(w · w)` of (5.10), over `w` and `b` under (5.11)). -/
theorem solution {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hboth : (∃ i, y i = 1) ∧ ∃ j, y j = -1)
    (w₀ : EuclideanSpace ℝ (Fin n)) (b₀ : ℝ) (hsep : IsCanonicalSeparating x y w₀ b₀) :
    IsOptimalHyperplane x y w₀ b₀ ↔
      ∃ α₀ : Fin ℓ → ℝ, (∀ i, 0 ≤ α₀ i) ∧ ∑ i, α₀ i * y i = 0 ∧
        w₀ = ∑ i, (y i * α₀ i) • x i ∧
        w₀ = ∑ i ∈ supportVectors x y w₀ b₀, (y i * α₀ i) • x i ∧
        ∀ i, α₀ i * ((⟪x i, w₀⟫_ℝ - b₀) * y i - 1) = 0 := by
  constructor
  · exact g70slt_kkt_exists x y w₀ b₀
  · rintro ⟨α, hα0, hαy, hw, -, hcs⟩
    refine ⟨hsep, fun w b hwb => ?_⟩
    have hy2 : ∀ i, y i * y i = 1 := fun i => by rcases hy i with h | h <;> rw [h] <;> norm_num
    obtain ⟨e1, -⟩ := g70slt_weak_dual x y α ⟨hα0, hαy⟩ w₀ b₀ hsep
    obtain ⟨e2, h2⟩ := g70slt_weak_dual x y α ⟨hα0, hαy⟩ w b hwb
    have hz : ∑ i, α i * (y i * (⟪w₀, x i⟫_ℝ - b₀) - 1) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [real_inner_comm]; have := hcs i; linear_combination this
    rw [← hw] at e1 e2
    have hn : ‖w₀‖ ^ 2 = ∑ i, α i := by rw [← real_inner_self_eq_norm_sq]; linarith
    have hcs' : ⟪w₀, w⟫_ℝ ≤ ‖w₀‖ * ‖w‖ := real_inner_le_norm _ _
    have : ‖w₀‖ ≤ ‖w‖ := by
      rcases (norm_nonneg w₀).lt_or_eq with h | h
      · nlinarith
      · rw [← h]; exact norm_nonneg _
    exact pow_le_pow_left₀ (norm_nonneg _) this 2

