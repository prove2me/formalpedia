-- Prove2me | solution 1 for GroupMetrization.birkhoff_kakutani
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:41:40.345039+00:00
-- url     : https://prove2.me/submissions/b21b4c95-0059-4833-bf74-ac816f7be348

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_GroupMetrization_birkhoff_kakutani

open Set Function List
open scoped SetRel Uniformity

/-- Replacing a pre-distance `d` by `(a, b) ↦ d (f a) (f b)`, where `f` does not increase `d`,
does not increase the sum of `d` along a chain. -/
private theorem sum_zipWith_comp_le {X : Type*} (d : X → X → ℝ≥0) (f : X → X)
    (hf : ∀ x y, d (f x) (f y) ≤ d x y) :
    ∀ l₁ l₂ : List X,
      (zipWith (fun a b => d (f a) (f b)) l₁ l₂).sum ≤ (zipWith d l₁ l₂).sum := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp
  | cons a l₁ ih =>
    intro l₂
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      simp only [zipWith_cons_cons, sum_cons]
      exact add_le_add (hf a b) (ih l₂)

/-- Variant of `UniformSpace.metrizable_uniformity` (same construction, same proof) that starts
from a prescribed countable antitone basis `V` of symmetric entourages and records that every
self-map preserving each `V n` is `1`-Lipschitz for the pseudometric which is produced. -/
theorem metrizable_uniformity_of_basis (X : Type*) [UniformSpace X] (V : ℕ → SetRel X X)
    (hVB : (𝓤 X).HasAntitoneBasis V) (hV_symm : ∀ n, (V n).IsSymm) :
    ∃ I : PseudoMetricSpace X, I.toUniformSpace = ‹_› ∧
      ∀ f : X → X, (∀ n x y, (x, y) ∈ V n → (f x, f y) ∈ V n) →
        ∀ x y, I.dist (f x) (f y) ≤ I.dist x y := by
  classical
  obtain ⟨U, hU_symm, hU_comp, hB, hUV⟩ :
    ∃ U : ℕ → SetRel X X,
      (∀ n, (U n).IsSymm) ∧
        (∀ ⦃m n⦄, m < n → U n ○ (U n ○ U n) ⊆ U m) ∧ (𝓤 X).HasAntitoneBasis U ∧
          ∀ n, ∃ k, U n = V k := by
    rcases hVB.subbasis_with_rel fun m =>
        hVB.tendsto_smallSets.eventually
          (eventually_uniformity_iterate_comp_subset (hVB.mem m) 2) with
      ⟨φ, -, hφ_comp, hφB⟩
    exact ⟨V ∘ φ, fun n => hV_symm _, hφ_comp, hφB, fun n => ⟨φ n, rfl⟩⟩
  set d : X → X → ℝ≥0 := fun x y => if h : ∃ n, (x, y) ∉ U n then (1 / 2) ^ Nat.find h else 0
  have hd₀ : ∀ {x y}, d x y = 0 ↔ Inseparable x y := by
    intro x y
    refine Iff.trans ?_ hB.inseparable_iff_uniformity.symm
    simp only [d, true_imp_iff]
    split_ifs with h
    · simp [h, pow_eq_zero_iff']
    · simpa only [not_exists, Classical.not_not, eq_self_iff_true, true_iff] using h
  have hd_symm x y : d x y = d y x := by simp only [d, (U _).comm]
  have hr : (1 / 2 : ℝ≥0) ∈ Ioo (0 : ℝ≥0) 1 := ⟨half_pos one_pos, NNReal.half_lt_self one_ne_zero⟩
  let I := PseudoMetricSpace.ofPreNNDist d (fun x => hd₀.2 rfl) hd_symm
  have hdist_le : ∀ x y, dist x y ≤ d x y := PseudoMetricSpace.dist_ofPreNNDist_le _ _ _
  have hle_d : ∀ {x y : X} {n : ℕ}, (1 / 2) ^ n ≤ d x y ↔ (x, y) ∉ U n := by
    intro x y n
    dsimp only [d]
    split_ifs with h
    · rw [(pow_right_strictAnti₀ hr.1 hr.2).le_iff_ge, Nat.find_le_iff]
      exact ⟨fun ⟨m, hmn, hm⟩ hn => hm (hB.antitone hmn hn), fun h => ⟨n, le_rfl, h⟩⟩
    · push Not at h
      simp only [h, not_true, (pow_pos hr.1 _).not_ge]
  have hd_le : ∀ x y, ↑(d x y) ≤ 2 * dist x y := by
    refine PseudoMetricSpace.le_two_mul_dist_ofPreNNDist _ _ _ fun x₁ x₂ x₃ x₄ => ?_
    by_cases H : ∃ n, (x₁, x₄) ∉ U n
    · refine (dif_pos H).trans_le ?_
      rw [← div_le_iff₀' zero_lt_two, ← mul_one_div (_ ^ _), ← pow_succ]
      simp only [le_max_iff, hle_d, ← not_and_or]
      rintro ⟨h₁₂, h₂₃, h₃₄⟩
      refine Nat.find_spec H (hU_comp (lt_add_one <| Nat.find H) ?_)
      exact ⟨x₂, h₁₂, x₃, h₂₃, h₃₄⟩
    · exact (dif_neg H).trans_le zero_le
  -- the additional information: maps preserving the entourages `V n` do not increase `d`
  have hd_f : ∀ f : X → X, (∀ n x y, (x, y) ∈ V n → (f x, f y) ∈ V n) →
      ∀ x y, d (f x) (f y) ≤ d x y := by
    intro f hf x y
    by_cases H : ∃ n, (f x, f y) ∉ U n
    · have hfx : d (f x) (f y) = (1 / 2) ^ Nat.find H := dif_pos H
      rw [hfx, hle_d]
      intro hxy
      obtain ⟨k, hk⟩ := hUV (Nat.find H)
      refine Nat.find_spec H ?_
      rw [hk] at hxy ⊢
      exact hf k x y hxy
    · exact (dif_neg H).trans_le zero_le
  have hI_f : ∀ f : X → X, (∀ n x y, (x, y) ∈ V n → (f x, f y) ∈ V n) →
      ∀ x y, I.dist (f x) (f y) ≤ I.dist x y := by
    intro f hf x y
    change ((⨅ l : List X, ((f x :: l).zipWith d (l ++ [f y])).sum : ℝ≥0) : ℝ) ≤
      ((⨅ l : List X, ((x :: l).zipWith d (l ++ [y])).sum : ℝ≥0) : ℝ)
    rw [NNReal.coe_le_coe]
    refine le_ciInf fun l => ?_
    refine (ciInf_le (OrderBot.bddBelow _) (l.map f)).trans ?_
    have hmap : zipWith d (f x :: l.map f) (l.map f ++ [f y]) =
        zipWith (fun a b => d (f a) (f b)) (x :: l) (l ++ [y]) := by
      rw [← List.map_cons, show l.map f ++ [f y] = (l ++ [y]).map f by simp, List.zipWith_map]
    rw [hmap]
    exact sum_zipWith_comp_le d f (hd_f f hf) _ _
  rw [mem_Ioo, ← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hr
  refine ⟨I, UniformSpace.ext <| (uniformity_basis_dist_pow hr.1 hr.2).ext hB.toHasBasis ?_ ?_,
    hI_f⟩
  · refine fun n hn => ⟨n, hn, fun x hx => (hdist_le _ _).trans_lt ?_⟩
    rwa [← NNReal.coe_pow, NNReal.coe_lt_coe, ← not_le, hle_d, Classical.not_not]
  · refine fun n _ => ⟨n + 1, trivial, fun x hx => ?_⟩
    rw [mem_ofPred_eq] at hx
    contrapose! hx
    refine le_trans ?_ ((div_le_iff₀' zero_lt_two).2 (hd_le x.1 x.2))
    rwa [← NNReal.coe_two, ← NNReal.coe_div, ← NNReal.coe_pow, NNReal.coe_le_coe, pow_succ,
      mul_one_div, div_le_iff₀ zero_lt_two, div_mul_cancel₀ _ two_ne_zero, hle_d]

/-- A first countable topological group carries a left-invariant pseudometric inducing its
topology. -/
theorem exists_leftInvariant_pseudoMetric (G : Type*) [Group G] [t : TopologicalSpace G]
    [IsTopologicalGroup G] [FirstCountableTopology G] :
    ∃ I : PseudoMetricSpace G, I.toUniformSpace.toTopologicalSpace = t ∧
      ∀ g x y : G, I.dist (g * x) (g * y) = I.dist x y := by
  let u : UniformSpace G := IsTopologicalGroup.leftUniformSpace G
  obtain ⟨W, hW⟩ := (𝓝 (1 : G)).exists_antitone_basis
  -- a countable antitone basis of symmetric neighbourhoods of `1`
  have hW'B : (𝓝 (1 : G)).HasAntitoneBasis (fun n => W n ∩ (W n)⁻¹) := by
    refine ⟨hW.toHasBasis.to_hasBasis (fun n _ => ⟨n, trivial, inter_subset_left⟩)
      (fun n _ => ?_), ?_⟩
    · have hmem : W n ∩ (W n)⁻¹ ∈ 𝓝 (1 : G) :=
        inter_mem (hW.mem n) (inv_mem_nhds_one G (hW.mem n))
      obtain ⟨m, -, hm⟩ := hW.toHasBasis.mem_iff.1 hmem
      exact ⟨m, trivial, hm⟩
    · intro m n hmn
      exact Set.inter_subset_inter (hW.antitone hmn) (Set.inv_subset_inv.2 (hW.antitone hmn))
  -- the corresponding left-invariant symmetric entourages of the left uniformity
  have hVB : (𝓤 G).HasAntitoneBasis
      (fun n => (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' (W n ∩ (W n)⁻¹)) := hW'B.comap _
  have hV_symm : ∀ n,
      SetRel.IsSymm ((fun p : G × G => p.1⁻¹ * p.2) ⁻¹' (W n ∩ (W n)⁻¹) : SetRel G G) := by
    intro n
    refine ⟨fun x y h => ?_⟩
    have h' : x⁻¹ * y ∈ W n ∧ (x⁻¹ * y)⁻¹ ∈ W n := h
    have e : (y⁻¹ * x)⁻¹ = x⁻¹ * y := by group
    have e' : (x⁻¹ * y)⁻¹ = y⁻¹ * x := by group
    change y⁻¹ * x ∈ W n ∧ (y⁻¹ * x)⁻¹ ∈ W n
    rw [e]
    rw [e'] at h'
    exact ⟨h'.2, h'.1⟩
  obtain ⟨I, hI, hinv⟩ := metrizable_uniformity_of_basis G _ hVB hV_symm
  have htop : I.toUniformSpace.toTopologicalSpace = t :=
    congrArg (fun v : UniformSpace G => v.toTopologicalSpace) hI
  refine ⟨I, htop, ?_⟩
  have key : ∀ g x y : G, I.dist (g * x) (g * y) ≤ I.dist x y := by
    intro g
    refine hinv (fun x => g * x) (fun n x y h => ?_)
    have e : (g * x)⁻¹ * (g * y) = x⁻¹ * y := by group
    change (g * x)⁻¹ * (g * y) ∈ W n ∩ (W n)⁻¹
    rw [e]
    exact h
  intro g x y
  refine le_antisymm (key g x y) ?_
  have h := key g⁻¹ (g * x) (g * y)
  rwa [inv_mul_cancel_left, inv_mul_cancel_left] at h

end Sol_GroupMetrization_birkhoff_kakutani

open Sol_GroupMetrization_birkhoff_kakutani in
theorem solution (G : Type*) [Group G] [t : TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] :
    FirstCountableTopology G ↔
      ∃ d : MetricSpace G, d.toUniformSpace.toTopologicalSpace = t ∧
        ∀ g x y : G, d.dist (g * x) (g * y) = d.dist x y := by
  constructor
  · intro h
    obtain ⟨I, hI, hinv⟩ := exists_leftInvariant_pseudoMetric G
    have hT0 : @T0Space G I.toUniformSpace.toTopologicalSpace := by
      rw [hI]; infer_instance
    exact ⟨@MetricSpace.ofT0PseudoMetricSpace G I hT0, hI, hinv⟩
  · rintro ⟨d, rfl, -⟩
    infer_instance
