-- Prove2me | solution 1 for GroupMetrization.struble
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:48:11.832282+00:00
-- url     : https://prove2.me/submissions/94323ea4-6f72-400f-924d-058c620de482

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_GroupMetrization_struble

open Set Function List

/-- Arbitrarily small powers of two in `ℝ≥0`. -/
private theorem exists_zpow_lt_nnreal (ε : ℝ≥0) (hε : 0 < ε) : ∃ n : ℤ, (2 : ℝ≥0) ^ n < ε := by
  obtain ⟨k, hk⟩ := NNReal.exists_pow_lt_of_lt_one hε
    (show (2⁻¹ : ℝ≥0) < 1 from inv_lt_one_of_one_lt₀ one_lt_two)
  refine ⟨-(k : ℤ), ?_⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact hk

/-- Arbitrarily small powers of two in `ℝ`. -/
private theorem exists_zpow_lt_real (ε : ℝ) (hε : 0 < ε) : ∃ n : ℤ, (2 : ℝ) ^ n < ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε
    (show (2⁻¹ : ℝ) < 1 from inv_lt_one_of_one_lt₀ one_lt_two)
  refine ⟨-(k : ℤ), ?_⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact hk

/-- **The chain metric of a `ℤ`-indexed family.** Let `V n`, `n ∈ ℤ`, be an increasing family of
symmetric subsets of a group `G` containing `1`, with `V n * V n * V n ⊆ V (n + 1)`, with
intersection `{1}` and with union `G`. Then there is a left-invariant metric `d` on `G` with
`d x y ≤ 2 ^ n` whenever `x⁻¹ * y ∈ V n`, and `x⁻¹ * y ∈ V (n + 1)` whenever `d x y < 2 ^ n`. -/
theorem exists_metric_of_family (G : Type*) [Group G] (V : ℤ → Set G)
    (hmono : Monotone V) (hsymm : ∀ n g, g ∈ V n → g⁻¹ ∈ V n) (hone : ∀ n, (1 : G) ∈ V n)
    (h3 : ∀ n a b c, a ∈ V n → b ∈ V n → c ∈ V n → a * b * c ∈ V (n + 1))
    (hInter : ∀ g, (∀ n, g ∈ V n) → g = 1) (hUnion : ∀ g, ∃ n, g ∈ V n) :
    ∃ d : MetricSpace G, (∀ g x y : G, d.dist (g * x) (g * y) = d.dist x y) ∧
      (∀ (x y : G) (n : ℤ), x⁻¹ * y ∈ V n → d.dist x y ≤ 2 ^ n) ∧
      (∀ (x y : G) (n : ℤ), d.dist x y < 2 ^ n → x⁻¹ * y ∈ V (n + 1)) := by
  classical
  -- the gauge of the family
  let p : G → ℝ≥0 := fun g => ⨅ n : {n : ℤ // g ∈ V n}, (2 : ℝ≥0) ^ (n : ℤ)
  have hne : ∀ g, Nonempty {n : ℤ // g ∈ V n} := fun g =>
    let ⟨n, hn⟩ := hUnion g; ⟨⟨n, hn⟩⟩
  have hp_le : ∀ g n, g ∈ V n → p g ≤ 2 ^ n := fun g n hn =>
    ciInf_le (OrderBot.bddBelow _) (⟨n, hn⟩ : {n : ℤ // g ∈ V n})
  have hp_lt : ∀ g c, p g < c → ∃ n, g ∈ V n ∧ (2 : ℝ≥0) ^ n < c := by
    intro g c hc
    have := hne g
    obtain ⟨⟨n, hn⟩, h⟩ := exists_lt_of_ciInf_lt hc
    exact ⟨n, hn, h⟩
  have hp_one : p 1 = 0 := by
    by_contra h
    obtain ⟨n, hn⟩ := exists_zpow_lt_nnreal (p 1) (pos_iff_ne_zero.2 h)
    exact absurd (hp_le 1 n (hone n)) (not_le.2 hn)
  have hp_inv : ∀ g, p g⁻¹ = p g := by
    have key : ∀ g, p g⁻¹ ≤ p g := by
      intro g
      have := hne g
      exact le_ciInf fun n => hp_le _ _ (hsymm _ _ n.2)
    intro g
    refine le_antisymm (key g) ?_
    have h := key g⁻¹
    rwa [inv_inv] at h
  have hp_mul : ∀ a b c, p (a * b * c) ≤ 2 * max (p a) (max (p b) (p c)) := by
    intro a b c
    by_contra hlt
    rw [not_le] at hlt
    have hc : max (p a) (max (p b) (p c)) < p (a * b * c) / 2 := by
      rw [lt_div_iff₀' two_pos]; exact hlt
    obtain ⟨na, ha, ha'⟩ := hp_lt a _ ((le_max_left _ _).trans_lt hc)
    obtain ⟨nb, hb, hb'⟩ := hp_lt b _ (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hc)
    obtain ⟨nc, hcc, hc'⟩ :=
      hp_lt c _ (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hc)
    obtain ⟨n, hna, hnb, hnc, h2n⟩ : ∃ n : ℤ, na ≤ n ∧ nb ≤ n ∧ nc ≤ n ∧
        (2 : ℝ≥0) ^ n < p (a * b * c) / 2 := by
      refine ⟨max na (max nb nc), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
        (le_max_right _ _).trans (le_max_right _ _), ?_⟩
      rcases max_choice na (max nb nc) with h | h
      · rw [h]; exact ha'
      · rcases max_choice nb nc with h' | h'
        · rw [h, h']; exact hb'
        · rw [h, h']; exact hc'
    have hmem : a * b * c ∈ V (n + 1) :=
      h3 n a b c (hmono hna ha) (hmono hnb hb) (hmono hnc hcc)
    have h5 := hp_le _ _ hmem
    rw [zpow_add_one₀ two_ne_zero] at h5
    have h4 : (2 : ℝ≥0) ^ n * 2 < p (a * b * c) / 2 * 2 := mul_lt_mul_of_pos_right h2n two_pos
    rw [div_mul_cancel₀ _ two_ne_zero] at h4
    exact absurd h5 (not_le.2 h4)
  -- the pre-distance
  let δ : G → G → ℝ≥0 := fun x y => p (x⁻¹ * y)
  have hδ_self : ∀ x, δ x x = 0 := by
    intro x
    change p (x⁻¹ * x) = 0
    rw [inv_mul_cancel]; exact hp_one
  have hδ_comm : ∀ x y, δ x y = δ y x := by
    intro x y
    change p (x⁻¹ * y) = p (y⁻¹ * x)
    rw [← hp_inv (y⁻¹ * x), mul_inv_rev, inv_inv]
  have hδ_four : ∀ x₁ x₂ x₃ x₄, δ x₁ x₄ ≤ 2 * max (δ x₁ x₂) (max (δ x₂ x₃) (δ x₃ x₄)) := by
    intro x₁ x₂ x₃ x₄
    have e : x₁⁻¹ * x₄ = x₁⁻¹ * x₂ * (x₂⁻¹ * x₃) * (x₃⁻¹ * x₄) := by group
    change p (x₁⁻¹ * x₄) ≤ _
    rw [e]
    exact hp_mul _ _ _
  have hδ_inv : ∀ g x y, δ (g * x) (g * y) = δ x y := by
    intro g x y
    have e : (g * x)⁻¹ * (g * y) = x⁻¹ * y := by group
    change p ((g * x)⁻¹ * (g * y)) = p (x⁻¹ * y)
    rw [e]
  let I : PseudoMetricSpace G := PseudoMetricSpace.ofPreNNDist δ hδ_self hδ_comm
  have hdist_le : ∀ x y, I.dist x y ≤ δ x y :=
    PseudoMetricSpace.dist_ofPreNNDist_le δ hδ_self hδ_comm
  have hle_dist : ∀ x y, (δ x y : ℝ) ≤ 2 * I.dist x y :=
    PseudoMetricSpace.le_two_mul_dist_ofPreNNDist δ hδ_self hδ_comm hδ_four
  -- left-invariance of the chain pseudometric
  have key : ∀ g x y : G, I.dist (g * x) (g * y) ≤ I.dist x y := by
    intro g x y
    change ((⨅ l : List G, ((g * x :: l).zipWith δ (l ++ [g * y])).sum : ℝ≥0) : ℝ) ≤
      ((⨅ l : List G, ((x :: l).zipWith δ (l ++ [y])).sum : ℝ≥0) : ℝ)
    rw [NNReal.coe_le_coe]
    refine le_ciInf fun l => ?_
    refine (ciInf_le (OrderBot.bddBelow _) (l.map fun a => g * a)).trans ?_
    have hmap : zipWith δ (g * x :: l.map fun a => g * a) ((l.map fun a => g * a) ++ [g * y]) =
        zipWith (fun a b => δ (g * a) (g * b)) (x :: l) (l ++ [y]) := by
      rw [← List.map_cons (f := fun a => g * a),
        show (l.map fun a => g * a) ++ [g * y] = (l ++ [y]).map (fun a => g * a) by simp,
        List.zipWith_map]
    have hfun : (fun a b => δ (g * a) (g * b)) = δ := by
      funext a b; exact hδ_inv g a b
    rw [hmap, hfun]
  have hinv : ∀ g x y : G, I.dist (g * x) (g * y) = I.dist x y := by
    intro g x y
    refine le_antisymm (key g x y) ?_
    have h := key g⁻¹ (g * x) (g * y)
    rwa [inv_mul_cancel_left, inv_mul_cancel_left] at h
  have hupper : ∀ (x y : G) (n : ℤ), x⁻¹ * y ∈ V n → I.dist x y ≤ 2 ^ n := by
    intro x y n h
    refine (hdist_le x y).trans ?_
    have h' : δ x y ≤ 2 ^ n := hp_le _ _ h
    have h'' := NNReal.coe_le_coe.2 h'
    rwa [NNReal.coe_zpow, NNReal.coe_ofNat] at h''
  have hlower : ∀ (x y : G) (n : ℤ), I.dist x y < 2 ^ n → x⁻¹ * y ∈ V (n + 1) := by
    intro x y n h
    have h1 : δ x y < 2 ^ (n + 1) := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_zpow, NNReal.coe_ofNat, zpow_add_one₀ two_ne_zero]
      have := hle_dist x y
      linarith
    obtain ⟨m, hm, hm'⟩ := hp_lt _ _ h1
    have hmn : m < n + 1 := (zpow_lt_zpow_iff_right₀ (one_lt_two : (1 : ℝ≥0) < 2)).1 hm'
    exact hmono hmn.le hm
  have hsep : ∀ x y : G, I.dist x y = 0 → x = y := by
    intro x y h
    refine inv_mul_eq_one.1 (hInter _ fun n => ?_)
    have h0 : I.dist x y < 2 ^ (n - 1) := by
      rw [h]; positivity
    have h1 := hlower x y (n - 1) h0
    rwa [sub_add_cancel] at h1
  exact ⟨{ I with eq_of_dist_eq_zero := fun {x y} h => hsep x y h }, hinv, hupper, hlower⟩

/-- The metric topology of a pseudometric which is comparable, in the sense of
`exists_metric_of_family`, to a `ℤ`-indexed family of neighbourhoods of `1` containing arbitrarily
small ones, is the topology of the group. -/
theorem topology_eq_of_family (G : Type*) [Group G] [t : TopologicalSpace G]
    [IsTopologicalGroup G] (V : ℤ → Set G) (hV : ∀ n, V n ∈ 𝓝 (1 : G))
    (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ n, V n ⊆ U) (d : PseudoMetricSpace G)
    (hupper : ∀ (x y : G) (n : ℤ), x⁻¹ * y ∈ V n → d.dist x y ≤ 2 ^ n)
    (hlower : ∀ (x y : G) (n : ℤ), d.dist x y < 2 ^ n → x⁻¹ * y ∈ V (n + 1)) :
    d.toUniformSpace.toTopologicalSpace = t := by
  refine TopologicalSpace.ext_nhds fun x => Filter.ext fun s => ?_
  rw [@Metric.mem_nhds_iff G d x s]
  constructor
  · rintro ⟨ε, hε, hs⟩
    obtain ⟨n, hn⟩ := exists_zpow_lt_real ε hε
    have hmem : (fun y => x⁻¹ * y) ⁻¹' V n ∈ 𝓝 x := by
      have hc : ContinuousAt (fun y => x⁻¹ * y) x := (continuous_const_mul x⁻¹).continuousAt
      refine hc.preimage_mem_nhds ?_
      change V n ∈ 𝓝 (x⁻¹ * x)
      rw [inv_mul_cancel]
      exact hV n
    refine mem_of_superset hmem fun y hy => hs ?_
    rw [@Metric.mem_ball G d, @dist_comm G d]
    exact (hupper x y n hy).trans_lt hn
  · intro hs
    have hmem : (fun g => x * g) ⁻¹' s ∈ 𝓝 (1 : G) := by
      have hc : ContinuousAt (fun g => x * g) 1 := (continuous_const_mul x).continuousAt
      refine hc.preimage_mem_nhds ?_
      change s ∈ 𝓝 (x * 1)
      rwa [mul_one]
    obtain ⟨n, hn⟩ := hbasis _ hmem
    refine ⟨2 ^ (n - 1), by positivity, fun y hy => ?_⟩
    rw [@Metric.mem_ball G d, @dist_comm G d] at hy
    have h1 := hlower x y (n - 1) hy
    rw [sub_add_cancel] at h1
    have h2 : x * (x⁻¹ * y) ∈ s := hn h1
    rwa [mul_inv_cancel_left] at h2

/-- Every neighbourhood `W` of `1` in a locally compact Hausdorff group contains a compact
symmetric neighbourhood `K` of `1` with `K * K * K ⊆ W`. -/
theorem exists_compact_symm_nhds_cube_subset (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (W : Set G)
    (hW : W ∈ 𝓝 (1 : G)) :
    ∃ K : Set G, K ∈ 𝓝 (1 : G) ∧ IsCompact K ∧ (∀ g ∈ K, g⁻¹ ∈ K) ∧ K ⊆ W ∧
      ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, a * b * c ∈ W := by
  obtain ⟨V₁, hV₁, hV₁W⟩ := exists_nhds_one_split4 hW
  obtain ⟨K, hK, hKV, hKc⟩ := local_compact_nhds hV₁
  have h1 : (1 : G) ∈ V₁ := mem_of_mem_nhds hV₁
  have hcube : ∀ a ∈ V₁, ∀ b ∈ V₁, ∀ c ∈ V₁, a * b * c ∈ W := by
    intro a ha b hb c hc
    have h := hV₁W ha hb hc h1
    rwa [mul_one] at h
  refine ⟨K ∩ K⁻¹, inter_mem hK (inv_mem_nhds_one G hK), hKc.inter hKc.inv, ?_, ?_, ?_⟩
  · rintro g ⟨hg, hg'⟩
    exact ⟨hg', by simpa using hg⟩
  · intro g hg
    have h := hcube g (hKV hg.1) 1 h1 1 h1
    rwa [mul_one, mul_one] at h
  · intro a ha b hb c hc
    exact hcube a (hKV ha.1) b (hKV hb.1) c (hKV hc.1)

/-- **Struble's family.** A second countable locally compact Hausdorff group has an increasing
`ℤ`-indexed family of compact symmetric neighbourhoods `V n` of `1` with
`V n * V n * V n ⊆ V (n + 1)`, containing arbitrarily small neighbourhoods of `1` and covering
the group. -/
theorem exists_family (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ V : ℤ → Set G, (∀ n, V n ∈ 𝓝 (1 : G)) ∧ (∀ n, IsCompact (V n)) ∧
      (∀ n g, g ∈ V n → g⁻¹ ∈ V n) ∧
      (∀ n a b c, a ∈ V n → b ∈ V n → c ∈ V n → a * b * c ∈ V (n + 1)) ∧
      (∀ U ∈ 𝓝 (1 : G), ∃ n, V n ⊆ U) ∧ ∀ g, ∃ n, g ∈ V n := by
  classical
  choose! shrink hs_nhds hs_cpt hs_symm hs_sub hs_cube using
    exists_compact_symm_nhds_cube_subset G
  obtain ⟨B, hB⟩ := (𝓝 (1 : G)).exists_antitone_basis
  -- the large sets
  obtain ⟨P, hP0, hPs⟩ : ∃ P : ℕ → Set G, P 0 = shrink univ ∧ ∀ k, P (k + 1) =
      P k * P k * P k ∪ (compactCovering G k ∪ (compactCovering G k)⁻¹) :=
    ⟨fun k => Nat.rec (shrink univ)
      (fun k Q => Q * Q * Q ∪ (compactCovering G k ∪ (compactCovering G k)⁻¹)) k,
      rfl, fun k => rfl⟩
  have hP_nhds : ∀ k, P k ∈ 𝓝 (1 : G) := by
    intro k
    induction k with
    | zero => rw [hP0]; exact hs_nhds _ univ_mem
    | succ k ih =>
      rw [hPs]
      have h1 : (1 : G) ∈ P k := mem_of_mem_nhds ih
      refine mem_of_superset ih fun g hg => Or.inl ?_
      exact ⟨g * 1, ⟨g, hg, 1, h1, rfl⟩, 1, h1, by simp⟩
  have hP_cpt : ∀ k, IsCompact (P k) := by
    intro k
    induction k with
    | zero => rw [hP0]; exact hs_cpt _ univ_mem
    | succ k ih =>
      rw [hPs]
      exact ((ih.mul ih).mul ih).union
        ((isCompact_compactCovering G k).union (isCompact_compactCovering G k).inv)
  have hP_symm : ∀ k g, g ∈ P k → g⁻¹ ∈ P k := by
    intro k
    induction k with
    | zero => rw [hP0]; exact hs_symm _ univ_mem
    | succ k ih =>
      rw [hPs]
      rintro g (⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ | hg | hg)
      · refine Or.inl ⟨c⁻¹ * b⁻¹, ⟨c⁻¹, ih c hc, b⁻¹, ih b hb, rfl⟩, a⁻¹, ih a ha, ?_⟩
        simp [mul_assoc]
      · exact Or.inr (Or.inr (by simpa using hg))
      · exact Or.inr (Or.inl hg)
  -- the small sets
  obtain ⟨N, hN0, hNs⟩ : ∃ N : ℕ → Set G, N 0 = shrink (P 0 ∩ B 0) ∧
      ∀ k, N (k + 1) = shrink (N k ∩ B (k + 1)) :=
    ⟨fun k => Nat.rec (shrink (P 0 ∩ B 0)) (fun k Q => shrink (Q ∩ B (k + 1))) k,
      rfl, fun k => rfl⟩
  have hN_nhds : ∀ k, N k ∈ 𝓝 (1 : G) := by
    intro k
    induction k with
    | zero => rw [hN0]; exact hs_nhds _ (inter_mem (hP_nhds 0) (hB.mem 0))
    | succ k ih => rw [hNs]; exact hs_nhds _ (inter_mem ih (hB.mem _))
  have hN_arg : ∀ k, N k = shrink (P 0 ∩ B 0) ∨ ∃ j, N k = shrink (N j ∩ B (j + 1)) := by
    intro k
    cases k with
    | zero => exact Or.inl hN0
    | succ k => exact Or.inr ⟨k, hNs k⟩
  have hN_cpt : ∀ k, IsCompact (N k) := by
    intro k
    rcases hN_arg k with h | ⟨j, h⟩
    · rw [h]; exact hs_cpt _ (inter_mem (hP_nhds 0) (hB.mem 0))
    · rw [h]; exact hs_cpt _ (inter_mem (hN_nhds j) (hB.mem _))
  have hN_symm : ∀ k g, g ∈ N k → g⁻¹ ∈ N k := by
    intro k
    rcases hN_arg k with h | ⟨j, h⟩
    · rw [h]; exact hs_symm _ (inter_mem (hP_nhds 0) (hB.mem 0))
    · rw [h]; exact hs_symm _ (inter_mem (hN_nhds j) (hB.mem _))
  have hN_B : ∀ k, N k ⊆ B k := by
    intro k
    cases k with
    | zero =>
      rw [hN0]
      exact (hs_sub _ (inter_mem (hP_nhds 0) (hB.mem 0))).trans inter_subset_right
    | succ k =>
      rw [hNs]
      exact (hs_sub _ (inter_mem (hN_nhds k) (hB.mem _))).trans inter_subset_right
  have hN_cube0 : ∀ a ∈ N 0, ∀ b ∈ N 0, ∀ c ∈ N 0, a * b * c ∈ P 0 := by
    intro a ha b hb c hc
    rw [hN0] at ha hb hc
    exact (hs_cube _ (inter_mem (hP_nhds 0) (hB.mem 0)) a ha b hb c hc).1
  have hN_cube : ∀ k, ∀ a ∈ N (k + 1), ∀ b ∈ N (k + 1), ∀ c ∈ N (k + 1), a * b * c ∈ N k := by
    intro k a ha b hb c hc
    rw [hNs] at ha hb hc
    exact (hs_cube _ (inter_mem (hN_nhds k) (hB.mem _)) a ha b hb c hc).1
  -- the family
  obtain ⟨V, hVP, hVN⟩ : ∃ V : ℤ → Set G, (∀ k : ℕ, V (Int.ofNat k) = P k) ∧
      ∀ k : ℕ, V (Int.negSucc k) = N k :=
    ⟨fun n => Int.rec P N n, fun k => rfl, fun k => rfl⟩
  refine ⟨V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (k | k)
    · rw [hVP]; exact hP_nhds k
    · rw [hVN]; exact hN_nhds k
  · rintro (k | k)
    · rw [hVP]; exact hP_cpt k
    · rw [hVN]; exact hN_cpt k
  · rintro (k | k)
    · rw [hVP]; exact hP_symm k
    · rw [hVN]; exact hN_symm k
  · rintro (k | k) a b c ha hb hc
    · have e : Int.ofNat k + 1 = Int.ofNat (k + 1) := rfl
      rw [e, hVP, hPs]
      rw [hVP] at ha hb hc
      exact Or.inl ⟨a * b, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    · cases k with
      | zero =>
        have e : Int.negSucc 0 + 1 = Int.ofNat 0 := rfl
        rw [e, hVP]
        rw [hVN] at ha hb hc
        exact hN_cube0 a ha b hb c hc
      | succ k =>
        have e : Int.negSucc (k + 1) + 1 = Int.negSucc k := by
          rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring
        rw [e, hVN]
        rw [hVN] at ha hb hc
        exact hN_cube k a ha b hb c hc
  · intro U hU
    obtain ⟨k, -, hk⟩ := hB.toHasBasis.mem_iff.1 hU
    exact ⟨Int.negSucc k, by rw [hVN]; exact (hN_B k).trans hk⟩
  · intro g
    have hg : g ∈ ⋃ k, compactCovering G k := by rw [iUnion_compactCovering]; trivial
    obtain ⟨k, hk⟩ := mem_iUnion.1 hg
    exact ⟨Int.ofNat (k + 1), by rw [hVP, hPs]; exact Or.inr (Or.inl hk)⟩

end Sol_GroupMetrization_struble

open Sol_GroupMetrization_struble in
theorem solution (G : Type*) [Group G] [t : TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    SecondCountableTopology G ↔
      ∃ d : MetricSpace G, d.toUniformSpace.toTopologicalSpace = t ∧
        (∀ g x y : G, d.dist (g * x) (g * y) = d.dist x y) ∧
        ∀ (x : G) (r : ℝ), IsCompact (@Metric.closedBall G d.toPseudoMetricSpace x r) := by
  constructor
  · intro h
    obtain ⟨V, hV_nhds, hV_cpt, hV_symm, hV_cube, hV_basis, hV_union⟩ := exists_family G
    have hV_one : ∀ n, (1 : G) ∈ V n := fun n => mem_of_mem_nhds (hV_nhds n)
    have hV_mono : Monotone V := by
      refine monotone_int_of_le_succ fun n g hg => ?_
      have h := hV_cube n g 1 1 hg (hV_one n) (hV_one n)
      rwa [mul_one, mul_one] at h
    have hV_inter : ∀ g : G, (∀ n, g ∈ V n) → g = 1 := by
      intro g hg
      by_contra hne
      have hU : ({g}ᶜ : Set G) ∈ 𝓝 (1 : G) :=
        isOpen_compl_singleton.mem_nhds (fun h1 : (1 : G) = g => hne h1.symm)
      obtain ⟨n, hn⟩ := hV_basis _ hU
      exact hn (hg n) rfl
    obtain ⟨d, hinv, hupper, hlower⟩ :=
      exists_metric_of_family G V hV_mono hV_symm hV_one hV_cube hV_inter hV_union
    have htop : d.toUniformSpace.toTopologicalSpace = t :=
      topology_eq_of_family G V hV_nhds hV_basis d.toPseudoMetricSpace hupper hlower
    refine ⟨d, htop, hinv, fun x r => ?_⟩
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt r (one_lt_two : (1 : ℝ) < 2)
    have hclosed : IsClosed (@Metric.closedBall G d.toPseudoMetricSpace x r) := by
      have h1 := @Metric.isClosed_closedBall G d.toPseudoMetricSpace x r
      rwa [htop] at h1
    have hcpt : IsCompact ((fun g => x * g) '' V ((k : ℤ) + 1)) :=
      (hV_cpt _).image (continuous_const_mul x)
    refine hcpt.of_isClosed_subset hclosed fun y hy => ?_
    rw [@Metric.mem_closedBall G d.toPseudoMetricSpace, @dist_comm G d.toPseudoMetricSpace] at hy
    have hlt : d.dist x y < 2 ^ (k : ℤ) := by
      rw [zpow_natCast]; exact hy.trans_lt hk
    exact ⟨x⁻¹ * y, hlower x y k hlt, mul_inv_cancel_left x y⟩
  · rintro ⟨d, rfl, -, hc⟩
    have : @ProperSpace G d.toPseudoMetricSpace := ⟨hc⟩
    infer_instance
