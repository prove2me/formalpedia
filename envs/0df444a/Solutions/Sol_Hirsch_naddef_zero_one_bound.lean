-- Prove2me | solution 1 for Hirsch.naddef_zero_one_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T04:59:56.355593+00:00
-- url     : https://prove2.me/submissions/ffad0e9e-6aa4-46f1-9aa6-5a6ebb2d0dca

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_ActiveConstraints
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_lp_basic_solutions_finite

open scoped RealInnerProductSpace
open Hirsch

namespace HirschLib

/-! ## Walks -/

/-- A constant walk witnesses `DiamLE` between equal endpoints. -/
theorem diamLE_of_subsingleton {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (B : ℕ)
    (h : ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P, u = v) :
    DiamLE P B := by
  intro u hu v hv
  exact ⟨fun _ => u, rfl, h u hu v hv, fun i _ => Or.inl rfl⟩

/-- One edge, then stay put: a walk of any positive length. -/
theorem diamLE_of_adj {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (B : ℕ)
    (hB : 1 ≤ B)
    (h : ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P, u = v ∨ Adj P u v) :
    DiamLE P B := by
  intro u hu v hv
  rcases h u hu v hv with heq | hadj
  · exact ⟨fun _ => u, rfl, heq, fun i _ => Or.inl rfl⟩
  · have hB0 : B ≠ 0 := by omega
    refine ⟨fun i => if i = 0 then u else v, by simp, by simp [hB0], ?_⟩
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact Or.inr (by simpa using hadj)
    · have hi0 : i ≠ 0 := by omega
      have hi1 : i + 1 ≠ 0 := by omega
      left; simp [hi0, hi1]

/-! ## Convex sets in a space of dimension at most one -/

/-- In a space of dimension at most one, a convex set with two distinct extreme
points is exactly the segment between them. -/
theorem eq_segment_of_finrank_le_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (h1 : Module.finrank ℝ E ≤ 1) (P : Set E) (hP : Convex ℝ P)
    {u v : E} (hu : u ∈ Set.extremePoints ℝ P) (hv : v ∈ Set.extremePoints ℝ P)
    (huv : u ≠ v) : P = segment ℝ u v := by
  classical
  set e : E := v - u with he
  have hene : e ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  -- the line through `u` and `v` is everything
  have hspan : Submodule.span ℝ ({e} : Set E) = ⊤ := by
    have h2 : Module.finrank ℝ (Submodule.span ℝ ({e} : Set E)) = 1 :=
      finrank_span_singleton hene
    have h3 : 1 ≤ Module.finrank ℝ E := h2 ▸ Submodule.finrank_le _
    exact Submodule.eq_top_of_finrank_eq (by omega)
  have hline : ∀ x : E, ∃ t : ℝ, x = u + t • e := by
    intro x
    have : x - u ∈ Submodule.span ℝ ({e} : Set E) := by rw [hspan]; trivial
    rw [Submodule.mem_span_singleton] at this
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by rw [ht]; abel⟩
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨t, rfl⟩ := hline x
    have hvu : v = u + (1:ℝ) • e := by rw [he]; module
    -- `t < 0` would exhibit `u` inside an open segment of `P`
    have ht0 : 0 ≤ t := by
      by_contra hlt
      push_neg at hlt
      have hden : (0:ℝ) < 1 - t := by linarith
      refine huv (((mem_extremePoints.mp hu).2 _ hx _ (extremePoints_subset hv) ?_).2).symm
      refine ⟨1 / (1 - t), -t / (1 - t), div_pos one_pos hden,
        div_pos (by linarith) hden, by field_simp <;> ring, ?_⟩
      have h1 : (1:ℝ) / (1 - t) + -t / (1 - t) = 1 := by field_simp <;> ring
      have h2 : (1:ℝ) / (1 - t) * t + (-t / (1 - t)) * 1 = 0 := by field_simp <;> ring
      rw [hvu]
      calc (1 / (1 - t)) • (u + t • e) + (-t / (1 - t)) • (u + (1:ℝ) • e)
          = ((1:ℝ) / (1 - t) + -t / (1 - t)) • u
            + ((1:ℝ) / (1 - t) * t + (-t / (1 - t)) * 1) • e := by module
        _ = u := by rw [h1, h2]; module
    -- `t > 1` would exhibit `v` inside an open segment of `P`
    have ht1 : t ≤ 1 := by
      by_contra hgt
      push_neg at hgt
      have hden : (0:ℝ) < t := by linarith
      refine huv (((mem_extremePoints.mp hv).2 _ (extremePoints_subset hu) _ hx ?_).1)
      refine ⟨(t - 1) / t, 1 / t, div_pos (by linarith) hden, div_pos one_pos hden,
        by field_simp <;> ring, ?_⟩
      have h1 : (t - 1) / t + 1 / t * 1 = 1 := by field_simp <;> ring
      have h2 : (1:ℝ) / t * t = 1 := by field_simp <;> ring
      rw [hvu]
      calc ((t - 1) / t) • u + (1 / t) • (u + t • e)
          = ((t - 1) / t + 1 / t * 1) • u + ((1:ℝ) / t * t) • e := by module
        _ = u + (1:ℝ) • e := by rw [h1, h2]; module
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    rw [he]; module
  · exact hP.segment_subset (extremePoints_subset hu) (extremePoints_subset hv)


/-! ## H-polytopes -/

theorem hpoly_convex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy s t hs ht hst i
  have h1 := hx i
  have h2 := hy i
  have hexp : ⟪a i, s • x + t • y⟫ = s * ⟪a i, x⟫ + t * ⟪a i, y⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [hexp]
  have e1 : s * ⟪a i, x⟫ ≤ s * b i := mul_le_mul_of_nonneg_left h1 hs
  have e2 : t * ⟪a i, y⟫ ≤ t * b i := mul_le_mul_of_nonneg_left h2 ht
  have e3 : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
  linarith

/-- If the polytope is bounded, every nonzero direction is cut off by some
inequality: no ray can survive inside a bounded set. -/
theorem exists_pos_inner_of_bounded {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b)) (e : EuclideanSpace ℝ (Fin d)) (he : e ≠ 0) :
    ∃ i, 0 < ⟪a i, e⟫ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbd
  have hepos : (0:ℝ) < ‖e‖ := norm_pos_iff.mpr he
  set t : ℝ := (R + ‖x0‖ + 1) / ‖e‖ with htdef
  have hRnn : 0 ≤ R := le_trans (norm_nonneg _) (hR _ hx0)
  have ht : 0 ≤ t := by rw [htdef]; positivity
  have hmem : x0 + t • e ∈ Hpoly a b := by
    intro i
    have hexp : ⟪a i, x0 + t • e⟫ = ⟪a i, x0⟫ + t * ⟪a i, e⟫ := by
      rw [inner_add_right, real_inner_smul_right]
    rw [hexp]
    have h1 := hx0 i
    nlinarith [hcon i]
  have h1 := hR _ hmem
  have hnorm : ‖t • e‖ ≤ ‖x0 + t • e‖ + ‖x0‖ := by
    calc ‖t • e‖ = ‖(x0 + t • e) - x0‖ := by congr 1; abel
      _ ≤ ‖x0 + t • e‖ + ‖x0‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hnorm
  have hte : t * ‖e‖ = R + ‖x0‖ + 1 := by
    rw [htdef]; field_simp
  linarith

/-- In dimension at least one, a bounded nonempty H-polytope needs at least two
inequalities: one to cut off each of two opposite directions. -/
theorem two_le_of_bounded {d n : ℕ} (hd : 1 ≤ d) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b)) : 2 ≤ n := by
  set e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ (1:ℝ) with hedef
  have he : e ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x ⟨0, hd⟩) h
    simp [hedef] at this
  obtain ⟨i, hi⟩ := exists_pos_inner_of_bounded a b hne hbd e he
  obtain ⟨j, hj⟩ := exists_pos_inner_of_bounded a b hne hbd (-e) (neg_ne_zero.mpr he)
  rw [inner_neg_right] at hj
  have hij : i ≠ j := by
    intro h; subst h; linarith
  haveI : Nontrivial (Fin n) := ⟨i, j, hij⟩
  have hcard := Fintype.one_lt_card_iff_nontrivial.mpr ‹Nontrivial (Fin n)›
  rw [Fintype.card_fin] at hcard
  omega

/-- **The Hirsch bound in dimension at most one.**  For `d = 0` the polytope is a
point; for `d = 1` it is a segment, its two extreme points are joined by the single
edge `P` itself, and boundedness forces `n ≥ 2`, so one step is available. -/
theorem dim_le_one_bound {d n : ℕ} (hd : d ≤ 1)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · refine diamLE_of_subsingleton _ _ fun u _ v _ => ?_
    exact Subsingleton.elim u v
  · have hd1' : d = 1 := le_antisymm hd hd1
    subst hd1'
    have h2 : 2 ≤ n := two_le_of_bounded le_rfl a b hne hbd
    refine diamLE_of_adj _ _ (by omega) fun u hu v hv => ?_
    by_cases huv : u = v
    · exact Or.inl huv
    · refine Or.inr ⟨huv, ?_⟩
      have hrk : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) ≤ 1 := by simp
      have hseg := eq_segment_of_finrank_le_one hrk _ (hpoly_convex a b) hu hv huv
      rw [← hseg]
      exact IsExtreme.refl ℝ _


/-- **Exposed faces are edges.**  If a linear functional attains its minimum over
`P` exactly on the segment `[u, v]`, then `u` and `v` are adjacent.  This is the
workhorse for exhibiting edges: extremeness of a minimizing face is immediate,
because an affine function that is minimal at an interior point of a segment must
be minimal at both of its endpoints. -/
theorem adj_of_exposed {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E)
    (c : E →ₗ[ℝ] ℝ) (t : ℝ) (u v : E) (huv : u ≠ v)
    (hmin : ∀ x ∈ P, t ≤ c x)
    (hface : {x | x ∈ P ∧ c x = t} = segment ℝ u v) : Adj P u v := by
  refine ⟨huv, ?_⟩
  rw [← hface]
  constructor
  · exact fun x hx => hx.1
  · rintro x₁ hx₁ x₂ hx₂ x ⟨hxP, hxt⟩ ⟨p, q, hp, hq, hpq, hx⟩
    have hc : c x = p * c x₁ + q * c x₂ := by
      rw [← hx, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 := hmin _ hx₁
    have h2 := hmin _ hx₂
    have h3 : p * c x₁ + q * c x₂ = t := by rw [← hc, hxt]
    have key : p * (c x₁ - t) + q * (c x₂ - t) = 0 := by
      linear_combination h3 - t * hpq
    have hz1 : 0 ≤ p * (c x₁ - t) := mul_nonneg hp.le (by linarith)
    have hz2 : 0 ≤ q * (c x₂ - t) := mul_nonneg hq.le (by linarith)
    have he1 : c x₁ = t := by
      have : p * (c x₁ - t) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hp)
      · linarith
    exact ⟨hx₁, he1⟩

/-- **A bounded H-polytope needs more inequalities than the ambient dimension.**
The map `x ↦ (⟪aᵢ, x⟫)ᵢ` is injective, since a vector in its kernel would give a
direction no inequality cuts off; so `d ≤ n`.  If `d = n` it is also surjective,
and pulling back `-e₀` produces a direction that no inequality cuts off after all. -/
theorem succ_le_of_bounded {d n : ℕ} (hd : 1 ≤ d) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b)) : d + 1 ≤ n := by
  classical
  set T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x i => ⟪a i, x⟫
      map_add' := by intro x y; funext i; simp [inner_add_right]
      map_smul' := by intro r x; funext i; simp [real_inner_smul_right] } with hT
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    by_contra hne0
    obtain ⟨i, hi⟩ := exists_pos_inner_of_bounded a b hne hbd e hne0
    have : (T e) i = 0 := by rw [he]; rfl
    simp only [hT, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  have hdn : d ≤ n := by
    have h1 := LinearMap.finrank_le_finrank_of_injective (f := T) hinj
    simpa using h1
  rcases Nat.lt_or_ge d n with h | h
  · omega
  · -- `d = n` is impossible
    exfalso
    have hdeq : d = n := le_antisymm hdn h
    have hn : 0 < n := by omega
    have hrange : LinearMap.range T = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h2 : Module.finrank ℝ (LinearMap.range T) = d := by
        rw [LinearMap.finrank_range_of_inj hinj]; simp
      rw [h2]; simp [hdeq]
    set f : Fin n → ℝ := -(Pi.single (⟨0, hn⟩ : Fin n) (1:ℝ)) with hf
    obtain ⟨e, he⟩ : ∃ e, T e = f := by
      have hmem : f ∈ LinearMap.range T := by rw [hrange]; trivial
      exact hmem
    have hcoord : ∀ i, ⟪a i, e⟫ = f i := fun i => congrFun he i
    have hzero : f (⟨0, hn⟩ : Fin n) = -1 := by simp [hf]
    have he0 : e ≠ 0 := by
      intro h
      have h1 := hcoord ⟨0, hn⟩
      rw [h, hzero] at h1
      simp at h1
    obtain ⟨i, hi⟩ := exists_pos_inner_of_bounded a b hne hbd e he0
    rw [hcoord i] at hi
    rcases eq_or_ne i (⟨0, hn⟩ : Fin n) with rfl | hne'
    · rw [hzero] at hi; linarith
    · have : f i = 0 := by simp [hf, hne']
      rw [this] at hi; linarith


/-- The minimising face of a linear functional over a convex hull is the hull of the
minimising generators. -/
theorem hull_inter_eq {E : Type*} [AddCommGroup E] [Module ℝ E] (V : Set E)
    (c : E →ₗ[ℝ] ℝ) (t : ℝ) (hV : ∀ z ∈ V, t ≤ c z) (W : Set E)
    (hW : ∀ z ∈ V, c z = t → z ∈ W) (hWne : (V ∩ W).Nonempty) :
    ∀ x ∈ convexHull ℝ V, c x = t → x ∈ convexHull ℝ (V ∩ W) := by
  classical
  intro x hx hcx
  obtain ⟨wV, hwV⟩ := hWne
  rw [convexHull_eq] at hx
  obtain ⟨ι, s, wt, z, hw0, hw1, hzV, hcm⟩ := hx
  -- points carrying no weight may be replaced by a fixed minimiser
  have hsum : ∑ i ∈ s, wt i • z i = x := by
    rw [← hcm, Finset.centerMass, hw1]; simp
  have hct : ∑ i ∈ s, wt i * (c (z i) - t) = 0 := by
    have h1 : ∑ i ∈ s, wt i * c (z i) = t := by
      have : c x = ∑ i ∈ s, wt i * c (z i) := by
        rw [← hsum, map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
      rw [← this, hcx]
    have h2 : ∑ i ∈ s, wt i * t = t := by rw [← Finset.sum_mul, hw1, one_mul]
    have : ∑ i ∈ s, wt i * (c (z i) - t)
        = (∑ i ∈ s, wt i * c (z i)) - ∑ i ∈ s, wt i * t := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h1, h2, sub_self]
  have hterm : ∀ i ∈ s, wt i * (c (z i) - t) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hct
    exact fun i hi => mul_nonneg (hw0 i hi) (by linarith [hV _ (hzV i hi)])
  -- replace zero-weight points by `wV`
  set z' : ι → E := fun i => if wt i = 0 then wV else z i with hz'
  have hz'mem : ∀ i ∈ s, z' i ∈ V ∩ W := by
    intro i hi
    by_cases h0 : wt i = 0
    · simp only [hz', if_pos h0]
      exact hwV
    · simp only [hz', if_neg h0]
      have := hterm i hi
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h0
      · exact ⟨hzV i hi, hW _ (hzV i hi) (by linarith)⟩
  have hsum' : ∑ i ∈ s, wt i • z' i = x := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : wt i = 0
    · simp [h0]
    · simp [hz', if_neg h0]
  rw [← hsum', convexHull_eq]
  refine ⟨ι, s, wt, z', hw0, hw1, hz'mem, ?_⟩
  rw [Finset.centerMass, hw1]
  simp

/-- **Building an edge from a separating functional.**  If `P` is the convex hull of
`V` and a linear functional attains its minimum over `V` exactly at the two points
`u ≠ w`, then `u` and `w` are adjacent in `P`. -/
theorem adj_of_separating {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V P : Set E) (hP : P = convexHull ℝ V)
    (c : E →ₗ[ℝ] ℝ) (t : ℝ) (u w : E) (huw : u ≠ w)
    (huV : u ∈ V) (hwV : w ∈ V) (hu : c u = t) (hw : c w = t)
    (hother : ∀ z ∈ V, z ≠ u → z ≠ w → t < c z) : Adj P u w := by
  classical
  have hVge : ∀ z ∈ V, t ≤ c z := by
    intro z hz
    by_cases h1 : z = u
    · rw [h1, hu]
    by_cases h2 : z = w
    · rw [h2, hw]
    · exact (hother z hz h1 h2).le
  have hmin : ∀ x ∈ P, t ≤ c x := by
    rw [hP]
    refine convexHull_min hVge ?_
    exact convex_halfSpace_ge (LinearMap.isLinear c) t
  have hVW : V ∩ ({u, w} : Set E) = ({u, w} : Set E) := by
    apply Set.inter_eq_right.mpr
    rintro z (rfl | rfl)
    · exact huV
    · exact hwV
  refine adj_of_exposed P c t u w huw hmin ?_
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨hxP, hxt⟩
    rw [hP] at hxP
    have := hull_inter_eq V c t hVge ({u, w} : Set E)
      (fun z hz hz' => by
        by_contra hcon
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
        exact absurd hz' (ne_of_gt (hother z hz hcon.1 hcon.2)))
      ⟨u, huV, Or.inl rfl⟩ x hxP hxt
    rwa [hVW, convexHull_pair] at this
  · intro x hx
    have hseg : segment ℝ u w ⊆ P := by
      rw [hP]
      exact (convex_convexHull ℝ V).segment_subset (subset_convexHull ℝ V huV)
        (subset_convexHull ℝ V hwV)
    refine ⟨hseg hx, ?_⟩
    obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hx
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hu, hw]
    linear_combination t * hpq


/-- **Rotating a supporting functional.**  Let `g` be minimised over `V` uniquely at
`u`, and let `c` be any functional that `u` does *not* minimise.  Rotating `g` towards
`c` — that is, following `c + λ g` as `λ` decreases from `+∞` — the vertex `u` stops
being the unique minimiser at a first value `λ > 0`, where a second vertex `w` joins
it on the supporting hyperplane.  That `w` has strictly smaller `c`-value, so this is
simultaneously the improving-direction step of the simplex method. -/
theorem exists_rotated_functional {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V : Finset E) (u : E) (g c : E →ₗ[ℝ] ℝ)
    (hg : ∀ z ∈ V, z ≠ u → g u < g z) (hex : ∃ z ∈ V, c z < c u) :
    ∃ (lam : ℝ) (w : E), 0 < lam ∧ w ∈ V ∧ w ≠ u ∧ c w < c u ∧
      c w + lam * g w = c u + lam * g u ∧
      ∀ z ∈ V, c u + lam * g u ≤ c z + lam * g z := by
  classical
  set S := V.filter (fun z => c z < c u) with hS
  have hSne : S.Nonempty := by
    obtain ⟨z, hzV, hzc⟩ := hex
    exact ⟨z, Finset.mem_filter.mpr ⟨hzV, hzc⟩⟩
  set r : E → ℝ := fun z => (c u - c z) / (g z - g u) with hr
  obtain ⟨w, hwS, hwmax⟩ := S.exists_max_image r hSne
  have hwV : w ∈ V := (Finset.mem_filter.mp hwS).1
  have hwc : c w < c u := (Finset.mem_filter.mp hwS).2
  have hwu : w ≠ u := by intro h; rw [h] at hwc; exact lt_irrefl _ hwc
  have hgw : g u < g w := hg w hwV hwu
  have hden : (0:ℝ) < g w - g u := by linarith
  have hne : g w - g u ≠ 0 := ne_of_gt hden
  have hpos : 0 < r w := div_pos (by linarith) hden
  refine ⟨r w, w, hpos, hwV, hwu, hwc, ?_, ?_⟩
  · have : r w * (g w - g u) = c u - c w := by
      rw [hr]; field_simp
    linarith
  · intro z hzV
    rcases eq_or_ne z u with rfl | hzu
    · exact le_refl _
    · have hgz : g u < g z := hg z hzV hzu
      have hdz : (0:ℝ) < g z - g u := by linarith
      rcases lt_or_ge (c z) (c u) with hlt | hge
      · have hzS : z ∈ S := Finset.mem_filter.mpr ⟨hzV, hlt⟩
        have hle := hwmax z hzS
        have hkey : c u - c z ≤ r w * (g z - g u) := by
          rw [hr, div_le_iff₀ hdz] at hle
          exact hle
        linarith
      · nlinarith


/-- The middle of three distinct collinear points of `P` is never extreme. -/
theorem not_extreme_of_between {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E)
    (z₀ e : E) (he : e ≠ 0) (r₁ r₂ r₃ : ℝ) (h12 : r₁ < r₂) (h23 : r₂ < r₃)
    (h1 : z₀ + r₁ • e ∈ P) (h3 : z₀ + r₃ • e ∈ P) :
    z₀ + r₂ • e ∉ Set.extremePoints ℝ P := by
  intro hmid
  have hd : (0:ℝ) < r₃ - r₁ := by linarith
  set p : ℝ := (r₃ - r₂) / (r₃ - r₁) with hp
  set q : ℝ := (r₂ - r₁) / (r₃ - r₁) with hq
  have hp0 : 0 < p := div_pos (by linarith) hd
  have hq0 : 0 < q := div_pos (by linarith) hd
  have hpq : p + q = 1 := by rw [hp, hq]; field_simp; ring
  have hcomb : p • (z₀ + r₁ • e) + q • (z₀ + r₃ • e) = z₀ + r₂ • e := by
    have hcoef : p * r₁ + q * r₃ = r₂ := by rw [hp, hq]; field_simp; ring
    calc p • (z₀ + r₁ • e) + q • (z₀ + r₃ • e)
        = (p + q) • z₀ + (p * r₁ + q * r₃) • e := by module
      _ = z₀ + r₂ • e := by rw [hpq, hcoef]; module
  have hopen : z₀ + r₂ • e ∈ openSegment ℝ (z₀ + r₁ • e) (z₀ + r₃ • e) :=
    ⟨p, q, hp0, hq0, hpq, hcomb⟩
  have heq := (mem_extremePoints.mp hmid).2 _ h1 _ h3 hopen
  have : (r₁ - r₂) • e = 0 := by
    have := heq.1
    have h' : z₀ + r₁ • e - (z₀ + r₂ • e) = 0 := by rw [this]; abel
    calc (r₁ - r₂) • e = z₀ + r₁ • e - (z₀ + r₂ • e) := by module
      _ = 0 := h'
  rcases smul_eq_zero.mp this with h | h
  · have : r₁ = r₂ := by linarith [sub_eq_zero.mp h]
    linarith
  · exact he h

/-- **At most two vertices on a supporting line.**  In a plane, a nonzero linear
functional is constant on a line, and three distinct extreme points cannot be
collinear. -/
theorem card_le_two_on_level {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (h2 : Module.finrank ℝ E ≤ 2) (P : Set E)
    (cc : E →ₗ[ℝ] ℝ) (hc : cc ≠ 0) (t : ℝ)
    {z₁ z₂ z₃ : E} (h1 : z₁ ∈ Set.extremePoints ℝ P) (hz2 : z₂ ∈ Set.extremePoints ℝ P)
    (h3 : z₃ ∈ Set.extremePoints ℝ P)
    (e1 : cc z₁ = t) (e2 : cc z₂ = t) (e3 : cc z₃ = t)
    (n12 : z₁ ≠ z₂) (n13 : z₁ ≠ z₃) (n23 : z₂ ≠ z₃) : False := by
  classical
  -- the differences all lie in `ker cc`, which has dimension at most one
  have hker : Module.finrank ℝ (LinearMap.ker cc) ≤ 1 := by
    have hrange : 1 ≤ Module.finrank ℝ (LinearMap.range cc) := by
      obtain ⟨x, hx⟩ : ∃ x, cc x ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hc (LinearMap.ext fun y => by simp [hcon y])
      haveI : Nontrivial (LinearMap.range cc) := by
        refine ⟨⟨⟨cc x, ⟨x, rfl⟩⟩, 0, ?_⟩⟩
        simpa [Subtype.ext_iff] using hx
      exact Module.finrank_pos
    have := LinearMap.finrank_range_add_finrank_ker cc
    omega
  set e : E := z₂ - z₁ with he
  have hene : e ≠ 0 := sub_ne_zero.mpr (Ne.symm n12)
  have hemem : e ∈ LinearMap.ker cc := by
    simp [LinearMap.mem_ker, he, map_sub, e1, e2]
  have hspan : Submodule.span ℝ ({(⟨e, hemem⟩ : LinearMap.ker cc)} : Set _) = ⊤ := by
    have hne0 : (⟨e, hemem⟩ : LinearMap.ker cc) ≠ 0 := by
      simpa [Subtype.ext_iff] using hene
    have hfr : Module.finrank ℝ (Submodule.span ℝ
        ({(⟨e, hemem⟩ : LinearMap.ker cc)} : Set _)) = 1 := finrank_span_singleton hne0
    have hle : 1 ≤ Module.finrank ℝ (LinearMap.ker cc) := hfr ▸ Submodule.finrank_le _
    exact Submodule.eq_top_of_finrank_eq (by omega)
  have hparam : ∀ z : E, cc z = t → ∃ r : ℝ, z = z₁ + r • e := by
    intro z hz
    have hmem : (⟨z - z₁, by simp [LinearMap.mem_ker, map_sub, hz, e1]⟩ :
        LinearMap.ker cc) ∈ Submodule.span ℝ ({(⟨e, hemem⟩ : LinearMap.ker cc)} : Set _) := by
      rw [hspan]; trivial
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hrr⟩ := hmem
    have hcoe : r • e = z - z₁ := by
      have h' := congrArg Subtype.val hrr
      simpa using h'
    exact ⟨r, by rw [hcoe]; abel⟩
  obtain ⟨r₁, hr₁⟩ := hparam z₁ e1
  obtain ⟨r₂, hr₂⟩ := hparam z₂ e2
  obtain ⟨r₃, hr₃⟩ := hparam z₃ e3
  have hinj : ∀ (s s' : ℝ), z₁ + s • e = z₁ + s' • e → s = s' := by
    intro s s' hss
    have : (s - s') • e = 0 := by
      have h' : s • e - s' • e = 0 := by
        have := hss
        have h2' : (z₁ + s • e) - (z₁ + s' • e) = 0 := by rw [this]; abel
        calc s • e - s' • e = (z₁ + s • e) - (z₁ + s' • e) := by abel
          _ = 0 := h2'
      rw [sub_smul]; exact h'
    rcases smul_eq_zero.mp this with h | h
    · linarith [sub_eq_zero.mp h]
    · exact absurd h hene
  have d12 : r₁ ≠ r₂ := fun h => n12 (by rw [hr₁, hr₂, h])
  have d13 : r₁ ≠ r₃ := fun h => n13 (by rw [hr₁, hr₃, h])
  have d23 : r₂ ≠ r₃ := fun h => n23 (by rw [hr₂, hr₃, h])
  -- the middle parameter gives a non-extreme point
  have key : ∀ (x y z : E) (rx ry rz : ℝ), x = z₁ + rx • e → y = z₁ + ry • e →
      z = z₁ + rz • e → rx < ry → ry < rz → x ∈ Set.extremePoints ℝ P →
      z ∈ Set.extremePoints ℝ P → y ∈ Set.extremePoints ℝ P → False := by
    intro x y z rx ry rz hx hy hz hxy hyz hxe hze hye
    refine not_extreme_of_between P z₁ e hene rx ry rz hxy hyz ?_ ?_ ?_
    · rw [← hx]; exact hxe.1
    · rw [← hz]; exact hze.1
    · rw [← hy]; exact hye
  rcases lt_trichotomy r₁ r₂ with h12' | h12' | h12'
  · rcases lt_trichotomy r₂ r₃ with h23' | h23' | h23'
    · exact key z₁ z₂ z₃ r₁ r₂ r₃ hr₁ hr₂ hr₃ h12' h23' h1 h3 hz2
    · exact d23 h23'
    · rcases lt_trichotomy r₁ r₃ with h13' | h13' | h13'
      · exact key z₁ z₃ z₂ r₁ r₃ r₂ hr₁ hr₃ hr₂ h13' h23' h1 hz2 h3
      · exact d13 h13'
      · exact key z₃ z₁ z₂ r₃ r₁ r₂ hr₃ hr₁ hr₂ h13' h12' h3 hz2 h1
  · exact d12 h12'
  · rcases lt_trichotomy r₁ r₃ with h13' | h13' | h13'
    · exact key z₂ z₁ z₃ r₂ r₁ r₃ hr₂ hr₁ hr₃ h12' h13' hz2 h3 h1
    · exact d13 h13'
    · rcases lt_trichotomy r₂ r₃ with h23' | h23' | h23'
      · exact key z₂ z₃ z₁ r₂ r₃ r₁ hr₂ hr₃ hr₁ h23' h13' hz2 h1 h3
      · exact d23 h23'
      · exact key z₃ z₂ z₁ r₃ r₂ r₁ hr₃ hr₂ hr₁ h23' h12' h3 h1 hz2


/-! ## Coordinates in the plane -/

/-- The standard basis vectors of the plane. -/
noncomputable abbrev pe (i : Fin 2) : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single i (1:ℝ)

theorem pe_apply (i j : Fin 2) : pe i j = if j = i then (1:ℝ) else 0 := by
  simp [pe, EuclideanSpace.single_apply]

theorem plane_ext (x : EuclideanSpace ℝ (Fin 2)) : x = x 0 • pe 0 + x 1 • pe 1 := by
  refine PiLp.ext fun j => ?_
  fin_cases j <;> simp [pe_apply]

theorem plane_eval (g : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    g x = x 0 * g (pe 0) + x 1 * g (pe 1) := by
  conv_lhs => rw [plane_ext x]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Rotation by a quarter turn, as a linear map on the plane. -/
noncomputable def rot : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := (-(x 1)) • pe 0 + (x 0) • pe 1
  map_add' x y := by
    simp only [PiLp.add_apply]
    module
  map_smul' r x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    module

theorem rot_pe0 : rot (pe 0) = pe 1 := by
  simp [rot, pe_apply]

theorem rot_pe1 : rot (pe 1) = -pe 0 := by
  simp [rot]

/-- A quarter turn produces a functional independent from the given one. -/
theorem perp_indep (g : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ) (hg : g ≠ 0) (α β : ℝ)
    (h : α • g + β • (g.comp rot) = 0) : α = 0 ∧ β = 0 := by
  have hne : g (pe 0) ≠ 0 ∨ g (pe 1) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hg (LinearMap.ext fun x => by rw [plane_eval g x, hcon.1, hcon.2]; simp)
  have h0 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ => f (pe 0)) h
  have h1 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ => f (pe 1)) h
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, smul_eq_mul, rot_pe0, rot_pe1, map_neg] at h0 h1
  -- `α a + β b = 0` and `α b - β a = 0` with `(a,b) ≠ 0`
  have hsq : ∀ r : ℝ, r ≠ 0 → 0 < r ^ 2 := by
    intro r hr
    rcases lt_trichotomy r 0 with h | h | h
    · nlinarith
    · exact absurd h hr
    · nlinarith
  have hpos : 0 < g (pe 0) ^ 2 + g (pe 1) ^ 2 := by
    rcases hne with hA | hB
    · nlinarith [hsq _ hA, sq_nonneg (g (pe 1))]
    · nlinarith [hsq _ hB, sq_nonneg (g (pe 0))]
  constructor
  · have hz : α * (g (pe 0) ^ 2 + g (pe 1) ^ 2) = 0 := by
      linear_combination g (pe 0) * h0 + g (pe 1) * h1
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (ne_of_gt hpos)
  · have hz : β * (g (pe 0) ^ 2 + g (pe 1) ^ 2) = 0 := by
      linear_combination g (pe 1) * h0 - g (pe 0) * h1
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (ne_of_gt hpos)


/-- The plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The first coordinate, as a nonzero functional on the plane. -/
noncomputable def coord0 : E2 →ₗ[ℝ] ℝ where
  toFun x := x 0
  map_add' := by intro x y; simp
  map_smul' := by intro r x; simp

theorem coord0_pe0 : coord0 (pe 0) = 1 := by
  change (pe 0) 0 = 1
  simp [pe_apply]

/-- A strict functional at `u` can always be perturbed so that no rotation towards `c`
degenerates to the zero functional. -/
theorem exists_strict_avoiding (V : Finset E2) (u : E2) (g : E2 →ₗ[ℝ] ℝ)
    (hg : ∀ z ∈ V, z ≠ u → g u < g z) (hV : ∃ z ∈ V, z ≠ u)
    (c : E2 →ₗ[ℝ] ℝ) (hc : c ≠ 0) :
    ∃ g' : E2 →ₗ[ℝ] ℝ, (∀ z ∈ V, z ≠ u → g' u < g' z) ∧ ∀ lam : ℝ, c + lam • g' ≠ 0 := by
  classical
  by_cases hgood : ∀ lam : ℝ, c + lam • g ≠ 0
  · exact ⟨g, hg, hgood⟩
  push_neg at hgood
  obtain ⟨lam₀, hlam₀⟩ := hgood
  have hgne : g ≠ 0 := by
    obtain ⟨z, hzV, hzu⟩ := hV
    intro h
    have := hg z hzV hzu
    rw [h] at this
    simp at this
  set h : E2 →ₗ[ℝ] ℝ := g.comp rot with hh
  set T := V.filter (fun z => z ≠ u) with hT
  have hTne : T.Nonempty := by
    obtain ⟨z, hzV, hzu⟩ := hV
    exact ⟨z, Finset.mem_filter.mpr ⟨hzV, hzu⟩⟩
  set δ : ℝ := T.inf' hTne (fun z => g z - g u) with hδ
  set M : ℝ := T.sup' hTne (fun z => |h u - h z|) with hM
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro z hz
    have := Finset.mem_filter.mp hz
    linarith [hg z this.1 this.2]
  have hMnn : 0 ≤ M := by
    obtain ⟨z, hz⟩ := hTne
    exact le_trans (abs_nonneg _) (Finset.le_sup' (fun z => |h u - h z|) hz)
  set ε : ℝ := δ / (2 * (M + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  refine ⟨g + ε • h, ?_, ?_⟩
  · intro z hzV hzu
    have hzT : z ∈ T := Finset.mem_filter.mpr ⟨hzV, hzu⟩
    have h1 : δ ≤ g z - g u := Finset.inf'_le (fun z => g z - g u) hzT
    have h2 : |h u - h z| ≤ M := Finset.le_sup' (fun z => |h u - h z|) hzT
    have h3 : h u - h z ≤ M := le_trans (le_abs_self _) h2
    have h4 : ε * M < δ := by
      rw [hε]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    nlinarith
  · intro lam heq
    have hz : (lam - lam₀) • g + (lam * ε) • h = 0 := by
      have hc' : c = (-lam₀) • g := by
        have := hlam₀
        have : c + lam₀ • g = 0 := this
        ext x
        have := congrArg (fun f : E2 →ₗ[ℝ] ℝ => f x) this
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
          smul_eq_mul] at this
        simp only [LinearMap.smul_apply, smul_eq_mul]
        linarith
      ext x
      have := congrArg (fun f : E2 →ₗ[ℝ] ℝ => f x) heq
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        smul_eq_mul] at this
      rw [hc'] at this
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at this
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        smul_eq_mul]
      linarith
    obtain ⟨ha, hb⟩ := perp_indep g hgne _ _ hz
    have hlam0 : lam = 0 := by
      rcases mul_eq_zero.mp hb with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hεpos)
    have : lam₀ = 0 := by linarith [ha, hlam0]
    apply hc
    have : c + (0:ℝ) • g = 0 := by rw [← this]; exact hlam₀
    simpa using this


/-- **The improving-edge step in the plane.**  If `u` is a vertex at which the linear
functional `c` is not minimal, then some edge at `u` leads to a vertex with strictly
smaller `c`-value.  The rotated supporting functional carries exactly two vertices,
because a supporting line of a planar polytope cannot hold three. -/
theorem improving_edge_plane (V : Finset E2) (P : Set E2)
    (hP : P = convexHull ℝ (V : Set E2))
    (hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ P)
    (u : E2) (hu : u ∈ V) (g : E2 →ₗ[ℝ] ℝ) (hg : ∀ z ∈ V, z ≠ u → g u < g z)
    (c : E2 →ₗ[ℝ] ℝ) (hex : ∃ z ∈ V, c z < c u) :
    ∃ w ∈ V, c w < c u ∧ Adj P u w := by
  classical
  obtain ⟨z₀, hz₀V, hz₀c⟩ := hex
  have hz₀u : z₀ ≠ u := by intro h; rw [h] at hz₀c; exact lt_irrefl _ hz₀c
  have hc : c ≠ 0 := by intro h; rw [h] at hz₀c; simp at hz₀c
  obtain ⟨g', hg', havoid⟩ := exists_strict_avoiding V u g hg ⟨z₀, hz₀V, hz₀u⟩ c hc
  obtain ⟨lam, w, hlam, hwV, hwu, hwc, hfeq, hfmin⟩ :=
    exists_rotated_functional V u g' c hg' ⟨z₀, hz₀V, hz₀c⟩
  set f : E2 →ₗ[ℝ] ℝ := c + lam • g' with hf
  have hfapp : ∀ x, f x = c x + lam * g' x := by intro x; simp [hf]
  have hfne : f ≠ 0 := havoid lam
  have hfw : f w = f u := by rw [hfapp, hfapp]; linarith
  have hrk : Module.finrank ℝ E2 ≤ 2 := by simp
  refine ⟨w, hwV, hwc, ?_⟩
  refine adj_of_separating (V : Set E2) P hP f (f u) u w (Ne.symm hwu)
    (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hwV) rfl hfw ?_
  intro z hzV hzu hzw
  have hzV' : z ∈ V := Finset.mem_coe.mp hzV
  have hge : f u ≤ f z := by rw [hfapp, hfapp]; exact hfmin z hzV'
  rcases lt_or_eq_of_le hge with h | h
  · exact h
  · exact absurd (card_le_two_on_level hrk P f hfne (f u)
      (hVext u hu) (hVext w hwV) (hVext z hzV') rfl hfw h.symm
      (Ne.symm hwu) (Ne.symm hzu) (Ne.symm hzw)) (fun x => x)


/-- **Every vertex of a two-dimensional polytope has two neighbours.**  Rotating the
supporting functional at `u` in both directions produces neighbours on either side of a
level line through `u`; such a line exists because the vertices do not all lie on one
line. -/
theorem two_neighbours_plane (V : Finset E2) (P : Set E2)
    (hP : P = convexHull ℝ (V : Set E2))
    (hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ P)
    (hnl : ∀ (q : E2 →ₗ[ℝ] ℝ) (t : ℝ), (∀ z ∈ V, q z = t) → q = 0)
    (u : E2) (hu : u ∈ V) (g : E2 →ₗ[ℝ] ℝ) (hg : ∀ z ∈ V, z ≠ u → g u < g z) :
    ∃ w₁ ∈ V, ∃ w₂ ∈ V, w₁ ≠ w₂ ∧ Adj P u w₁ ∧ Adj P u w₂ := by
  classical
  set h : E2 →ₗ[ℝ] ℝ := g.comp rot with hh
  set ρ : E2 → ℝ := fun z => (h z - h u) / (g z - g u) with hρ
  -- a functional taking values on both sides of its value at `u`
  have hsplit : ∃ cc : E2 →ₗ[ℝ] ℝ, (∃ z ∈ V, cc z < cc u) ∧ (∃ z ∈ V, cc u < cc z) := by
    by_cases hall : ∃ z₁ ∈ V, ∃ z₂ ∈ V, z₁ ≠ u ∧ z₂ ≠ u ∧ ρ z₁ ≠ ρ z₂
    · obtain ⟨z₁, hz₁, z₂, hz₂, hz₁u, hz₂u, hne⟩ := hall
      set c₀ : ℝ := (ρ z₁ + ρ z₂) / 2 with hc₀
      refine ⟨h - c₀ • g, ?_, ?_⟩
      · rcases lt_or_gt_of_ne hne with hlt | hlt
        · refine ⟨z₁, hz₁, ?_⟩
          have hd : 0 < g z₁ - g u := by linarith [hg z₁ hz₁ hz₁u]
          have hr : ρ z₁ < c₀ := by rw [hc₀]; linarith
          have hval : h z₁ - h u = ρ z₁ * (g z₁ - g u) := by
            rw [hρ]; field_simp
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          nlinarith
        · refine ⟨z₂, hz₂, ?_⟩
          have hd : 0 < g z₂ - g u := by linarith [hg z₂ hz₂ hz₂u]
          have hr : ρ z₂ < c₀ := by rw [hc₀]; linarith
          have hval : h z₂ - h u = ρ z₂ * (g z₂ - g u) := by
            rw [hρ]; field_simp
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          nlinarith
      · rcases lt_or_gt_of_ne hne with hlt | hlt
        · refine ⟨z₂, hz₂, ?_⟩
          have hd : 0 < g z₂ - g u := by linarith [hg z₂ hz₂ hz₂u]
          have hr : c₀ < ρ z₂ := by rw [hc₀]; linarith
          have hval : h z₂ - h u = ρ z₂ * (g z₂ - g u) := by
            rw [hρ]; field_simp
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          nlinarith
        · refine ⟨z₁, hz₁, ?_⟩
          have hd : 0 < g z₁ - g u := by linarith [hg z₁ hz₁ hz₁u]
          have hr : c₀ < ρ z₁ := by rw [hc₀]; linarith
          have hval : h z₁ - h u = ρ z₁ * (g z₁ - g u) := by
            rw [hρ]; field_simp
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          nlinarith
    · -- all ratios agree: the vertices lie on a line, contradicting `hnl`
      exfalso
      push_neg at hall
      have hex_ne : ∃ z ∈ V, z ≠ u := by
        by_contra hcon
        push_neg at hcon
        have hall0 : ∀ q : E2 →ₗ[ℝ] ℝ, q = 0 :=
          fun q => hnl q (q u) (fun z hz => by rw [hcon z hz])
        have h0 := hall0 coord0
        have h1 : coord0 (pe 0) = 1 := coord0_pe0
        rw [h0] at h1
        simp at h1
      obtain ⟨z₀, hz₀V, hz₀u⟩ := hex_ne
      have hgne : g ≠ 0 := by
        intro hz
        have := hg z₀ hz₀V hz₀u
        rw [hz] at this
        simp at this
      set c₀ : ℝ := ρ z₀ with hc₀
      have hconst : ∀ z ∈ V, (h - c₀ • g) z = (h - c₀ • g) u := by
        intro z hzV
        rcases eq_or_ne z u with rfl | hzu
        · rfl
        · have hr : ρ z = c₀ := by
            by_contra hcon
            exact hcon (hall z hzV z₀ hz₀V hzu hz₀u)
          have hd : 0 < g z - g u := by linarith [hg z hzV hzu]
          have hval : h z - h u = ρ z * (g z - g u) := by rw [hρ]; field_simp
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [hr] at hval
          linarith
      have hzero := hnl (h - c₀ • g) ((h - c₀ • g) u) hconst
      have hcomb : (-c₀) • g + (1:ℝ) • h = 0 := by
        rw [← hzero]; ext x
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
          smul_eq_mul, one_mul]
        ring
      obtain ⟨-, hb⟩ := perp_indep g hgne _ _ hcomb
      exact absurd hb one_ne_zero
  obtain ⟨cc, hlt, hgt⟩ := hsplit
  obtain ⟨w₁, hw₁V, hw₁c, hw₁adj⟩ := improving_edge_plane V P hP hVext u hu g hg cc hlt
  obtain ⟨w₂, hw₂V, hw₂c, hw₂adj⟩ := improving_edge_plane V P hP hVext u hu g hg (-cc)
    (by obtain ⟨z, hzV, hz⟩ := hgt; exact ⟨z, hzV, by simpa using hz⟩)
  refine ⟨w₁, hw₁V, w₂, hw₂V, ?_, hw₁adj, hw₂adj⟩
  intro heq
  rw [heq] at hw₁c
  simp only [LinearMap.neg_apply, neg_lt_neg_iff] at hw₂c
  linarith

end HirschLib

open Hirsch

namespace HirschWalk

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `Reach P L u v`: a walk of exactly `L` steps from `u` to `v`, each step either
stationary or along an edge.  This is the body of `DiamLE`. -/
def Reach (P : Set E) (L : ℕ) (u v : E) : Prop :=
  ∃ w : ℕ → E, w 0 = u ∧ w L = v ∧ ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1))

theorem reach_zero (P : Set E) (u : E) : Reach P 0 u u :=
  ⟨fun _ => u, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

theorem reach_succ (P : Set E) (L : ℕ) (u v : E) (h : Reach P L u v) :
    Reach P (L + 1) u v := by
  classical
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨fun i => if i ≤ L then w i else v, by simpa using h0, by simp, ?_⟩
  intro i hi
  rcases lt_or_ge i L with h1 | h1
  · have hi1 : i + 1 ≤ L := h1
    simp only [if_pos h1.le, if_pos hi1]
    exact hstep i h1
  · have hiL : i = L := by omega
    subst hiL
    left
    simp [hL]

theorem reach_mono (P : Set E) {L L' : ℕ} (hLL : L ≤ L') {u v : E} (h : Reach P L u v) :
    Reach P L' u v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hLL
  clear hLL
  induction k with
  | zero => simpa using h
  | succ m ih => exact (Nat.add_succ L m) ▸ reach_succ P _ u v ih

/-- `DiamLE` is exactly reachability in `B` steps between vertices. -/
theorem diamLE_of_reach (P : Set E) (B : ℕ)
    (h : ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P,
      ∃ L ≤ B, Reach P L u v) : DiamLE P B := by
  intro u hu v hv
  obtain ⟨L, hLB, hL⟩ := h u hu v hv
  exact reach_mono P hLB hL

/-- Splicing out a repeat shortens a walk. -/
theorem reach_of_repeat (P : Set E) (L : ℕ) (u v : E) (w : ℕ → E)
    (h0 : w 0 = u) (hL : w L = v)
    (hstep : ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1)))
    {i j : ℕ} (hij : i < j) (hjL : j ≤ L) (heq : w i = w j) :
    Reach P (L - (j - i)) u v := by
  classical
  refine ⟨fun k => if k ≤ i then w k else w (k + (j - i)), ?_, ?_, ?_⟩
  · simpa using h0
  · dsimp only
    by_cases hc : L - (j - i) ≤ i
    · have hEq : L - (j - i) = i := by omega
      have hjeq : j = L := by omega
      rw [if_pos hc, hEq, heq, hjeq]
      exact hL
    · rw [if_neg hc]
      have hEq : L - (j - i) + (j - i) = L := by omega
      rw [hEq]
      exact hL
  · intro k hk
    dsimp only
    by_cases hc : k ≤ i
    · by_cases hc1 : k + 1 ≤ i
      · rw [if_pos hc, if_pos hc1]
        exact hstep k (by omega)
      · have hki : k = i := by omega
        subst hki
        rw [if_pos hc, if_neg hc1]
        have : k + 1 + (j - k) = j + 1 := by omega
        rw [this]
        rw [heq]
        exact hstep j (by omega)
    · rw [if_neg hc, if_neg (by omega : ¬ (k + 1 ≤ i))]
      have : k + 1 + (j - i) = (k + (j - i)) + 1 := by omega
      rw [this]
      exact hstep _ (by omega)


/-- The endpoints of an edge are vertices. -/
theorem adj_right_mem_extremePoints {P : Set E} {a b : E} (h : Adj P a b) :
    b ∈ Set.extremePoints ℝ P := by
  have hb : b ∈ Set.extremePoints ℝ (segment ℝ a b) := by
    refine ⟨right_mem_segment ℝ a b, ?_⟩
    rintro x hx y hy ⟨p, q, hp, hq, hpq, hxy⟩
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h.1)
    rw [segment_eq_image'] at hx hy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have hb' : b = a + (1:ℝ) • (b - a) := by module
    have hcomb : p • (a + s • (b - a)) + q • (a + t • (b - a))
        = a + (p * s + q * t) • (b - a) := by
      calc p • (a + s • (b - a)) + q • (a + t • (b - a))
          = (p + q) • a + (p * s + q * t) • (b - a) := by module
        _ = a + (p * s + q * t) • (b - a) := by rw [hpq]; module
    have hb2 : a + (p * s + q * t) • (b - a) = b := by rw [← hcomb]; exact hxy
    have hco : p * s + q * t = 1 := by
      have h3 : ((p * s + q * t) - 1) • (b - a) = 0 := by
        have e1 : ((p * s + q * t) - 1) • (b - a)
            = (a + (p * s + q * t) • (b - a)) - (a + (1:ℝ) • (b - a)) := by module
        rw [e1, hb2, ← hb', sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · linarith [sub_eq_zero.mp h4]
      · exact absurd h4 hba
    have hs1 : s = 1 := by
      have h5 : p * s + q * t ≤ p * 1 + q * 1 := by
        have := hs.2; have := ht.2
        nlinarith
      nlinarith [hs.2, ht.2, hs.1, ht.1]
    rw [hs1]
    module
  have := h.2.extremePoints_eq (𝕜 := ℝ)
  rw [this] at hb
  exact hb.2

theorem reach_one_of_adj (P : Set E) {u v : E} (h : Adj P u v) : Reach P 1 u v := by
  classical
  refine ⟨fun i => if i = 0 then u else v, by simp, by simp, ?_⟩
  intro i hi
  have : i = 0 := by omega
  subst this
  exact Or.inr (by simpa using h)

theorem reach_trans (P : Set E) {L₁ L₂ : ℕ} {u x v : E}
    (h₁ : Reach P L₁ u x) (h₂ : Reach P L₂ x v) : Reach P (L₁ + L₂) u v := by
  classical
  obtain ⟨w₁, a1, b1, s1⟩ := h₁
  obtain ⟨w₂, a2, b2, s2⟩ := h₂
  refine ⟨fun i => if i ≤ L₁ then w₁ i else w₂ (i - L₁), by simpa using a1, ?_, ?_⟩
  · dsimp only
    by_cases hc : L₁ + L₂ ≤ L₁
    · have hz : L₂ = 0 := by omega
      subst hz
      rw [if_pos hc]
      simpa using b1.trans (by rw [← a2, ← b2])
    · rw [if_neg hc]
      have : L₁ + L₂ - L₁ = L₂ := by omega
      rw [this]; exact b2
  · intro i hi
    dsimp only
    by_cases hc : i ≤ L₁
    · by_cases hc1 : i + 1 ≤ L₁
      · rw [if_pos hc, if_pos hc1]; exact s1 i (by omega)
      · have hiL : i = L₁ := by omega
        subst hiL
        rw [if_pos hc, if_neg hc1]
        have : i + 1 - i = 1 := by omega
        rw [this, b1, ← a2]
        exact s2 0 (by omega)
    · rw [if_neg hc, if_neg (by omega : ¬ (i + 1 ≤ L₁))]
      have : i + 1 - L₁ = (i - L₁) + 1 := by omega
      rw [this]
      exact s2 _ (by omega)

theorem reach_tail (P : Set E) {L : ℕ} {v : E} {w : ℕ → E}
    (hL : w L = v) (hstep : ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1)))
    {k : ℕ} (hk : k ≤ L) : Reach P (L - k) (w k) v := by
  refine ⟨fun i => w (i + k), by simp, ?_, ?_⟩
  · dsimp only
    have hEq : L - k + k = L := by omega
    rw [hEq]; exact hL
  · intro i hi
    dsimp only
    have hEq : i + 1 + k = (i + k) + 1 := by omega
    rw [hEq]
    exact hstep _ (by omega)


/-- **A connected vertex-edge graph of minimum degree two has diameter at most
`|V| - 2`.**  On a shortest walk all vertices are distinct, so its length is at most
`|V| - 1`; and a walk of that length visits every vertex, so the second neighbour of
its starting point is a later vertex on the walk and provides a shortcut. -/
theorem diam_le_card_sub_two (P : Set E) (V : Finset E)
    (hextV : ∀ z ∈ Set.extremePoints ℝ P, z ∈ V)
    (hconn : ∀ u ∈ V, ∀ v ∈ V, ∃ L, Reach P L u v)
    (hdeg : ∀ u ∈ V, ∃ w₁ ∈ V, ∃ w₂ ∈ V, w₁ ≠ w₂ ∧ Adj P u w₁ ∧ Adj P u w₂) :
    DiamLE P (V.card - 2) := by
  classical
  refine diamLE_of_reach P _ (fun u hu v hv => ?_)
  have huV := hextV u hu
  have hvV := hextV v hv
  have hex : ∃ L, Reach P L u v := hconn u huV v hvV
  have hfind : Reach P (Nat.find hex) u v := Nat.find_spec hex
  have hmin : ∀ L, L < Nat.find hex → ¬ Reach P L u v := fun L hL => Nat.find_min hex hL
  set L₀ := Nat.find hex with hL₀def
  obtain ⟨w, h0, hLw, hstep⟩ := hfind
  have hmem : ∀ i, i ≤ L₀ → w i ∈ V := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact huV
    | succ m ih =>
        intro hm
        rcases hstep m (by omega) with he | hadj
        · rw [← he]; exact ih (by omega)
        · exact hextV _ (adj_right_mem_extremePoints hadj)
  have hinj : ∀ i, i ≤ L₀ → ∀ j, j ≤ L₀ → w i = w j → i = j := by
    intro i hi j hj hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hmin _ (by omega) (reach_of_repeat P L₀ u v w h0 hLw hstep hlt hj hij)
    · exact hmin _ (by omega) (reach_of_repeat P L₀ u v w h0 hLw hstep hlt hi hij.symm)
  -- the walk injects into the vertex set
  have hcard : L₀ + 1 ≤ V.card := by
    have himg : ((Finset.range (L₀ + 1)).image w) ⊆ V := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact hmem i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi)
    have hcardimg : ((Finset.range (L₀ + 1)).image w).card = L₀ + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      exact hinj i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi) j
        (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj) hij
    calc L₀ + 1 = ((Finset.range (L₀ + 1)).image w).card := hcardimg.symm
      _ ≤ V.card := Finset.card_le_card himg
  -- three distinct vertices exist
  obtain ⟨y₁, hy₁V, y₂, hy₂V, hy12, hadj1, hadj2⟩ := hdeg u huV
  have hy1u : y₁ ≠ u := fun h => hadj1.1 h.symm
  have hy2u : y₂ ≠ u := fun h => hadj2.1 h.symm
  have hcard3 : 3 ≤ V.card := by
    have hsub : ({u, y₁, y₂} : Finset E) ⊆ V := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact huV
      · exact hy₁V
      · exact hy₂V
    have : ({u, y₁, y₂} : Finset E).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hy1u, Ne.symm hy2u]),
        Finset.card_insert_of_notMem (by simp [hy12]), Finset.card_singleton]
    calc (3:ℕ) = ({u, y₁, y₂} : Finset E).card := this.symm
      _ ≤ V.card := Finset.card_le_card hsub
  by_cases hshort : L₀ ≤ V.card - 2
  · exact ⟨L₀, hshort, ⟨w, h0, hLw, hstep⟩⟩
  -- otherwise the walk visits every vertex and the second neighbour is a shortcut
  exfalso
  have hL₀eq : L₀ = V.card - 1 := by omega
  have hsurj : ∀ y ∈ V, ∃ k ≤ L₀, w k = y := by
    intro y hyV
    by_contra hcon
    push_neg at hcon
    have hsub : (insert y ((Finset.range (L₀ + 1)).image w)) ⊆ V := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hyV
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz'
        exact hmem i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi)
    have hnotmem : y ∉ ((Finset.range (L₀ + 1)).image w) := by
      intro hy
      obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hy
      exact absurd hiy (hcon i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi))
    have hcardimg : ((Finset.range (L₀ + 1)).image w).card = L₀ + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      exact hinj i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi) j
        (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj) hij
    have : L₀ + 2 ≤ V.card := by
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnotmem, hcardimg] at this
      omega
    omega
  -- pick a neighbour of `u` different from the walk's first step
  have hL1 : 1 ≤ L₀ := by omega
  obtain ⟨y, hyV, hyadj, hy1⟩ : ∃ y ∈ V, Adj P u y ∧ y ≠ w 1 := by
    by_cases hc : y₁ = w 1
    · exact ⟨y₂, hy₂V, hadj2, by rw [← hc]; exact hy12.symm⟩
    · exact ⟨y₁, hy₁V, hadj1, hc⟩
  obtain ⟨k, hk, hky⟩ := hsurj y hyV
  have hk0 : k ≠ 0 := by
    intro h; rw [h, h0] at hky; exact hyadj.1 hky
  have hk1 : k ≠ 1 := by intro h; rw [h] at hky; exact hy1 hky.symm
  have hk2 : 2 ≤ k := by omega
  have hshort2 : Reach P (1 + (L₀ - k)) u v :=
    reach_trans P (reach_one_of_adj P hyadj) (hky ▸ reach_tail P hLw hstep hk)
  exact hmin _ (by omega) hshort2

end HirschWalk

open scoped RealInnerProductSpace
open Hirsch LinearOptimization

namespace HirschBridge

variable {d n : ℕ}

/-- The mission's H-polytope, read as a Bertsimas--Tsitsiklis constraint system. -/
def constrOf (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Fin n → LinearConstraint d :=
  fun i => ⟨fun j => a i j, b i, .le⟩

/-- The type synonym `EuclideanSpace ℝ (Fin d) = WithLp 2 (Fin d → ℝ)` as a linear
equivalence, used to move between the mission's model and the B&T one. -/
noncomputable def eqv (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (Fin d → ℝ) :=
  WithLp.linearEquiv 2 ℝ (Fin d → ℝ)

theorem eqv_apply (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) : eqv d x j = x j := rfl

theorem inner_eq_dotProduct (a x : EuclideanSpace ℝ (Fin d)) :
    ⟪a, x⟫ = (fun j => a j) ⬝ᵥ (eqv d x) := by
  simp [PiLp.inner_apply, dotProduct, eqv_apply, mul_comm]

theorem image_hpoly (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    (eqv d) '' (Hpoly a b) = constraintSet (constrOf a b) := by
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨x, hx, rfl⟩ i
    have := hx i
    simpa [constrOf, LinearConstraint.IsSatisfiedAt, ← inner_eq_dotProduct] using this
  · intro y hy
    refine ⟨(eqv d).symm y, fun i => ?_, (eqv d).apply_symm_apply y⟩
    have := hy i
    simp only [constrOf, LinearConstraint.IsSatisfiedAt] at this
    have hrw : ⟪a i, (eqv d).symm y⟫ = (fun j => a i j) ⬝ᵥ y := by
      rw [inner_eq_dotProduct, (eqv d).apply_symm_apply]
    rw [hrw]
    exact this

/-- **The vertex set of an H-polytope is finite.**  Transported from the platform's
`LinearOptimization` layer: extreme points of a constraint system are exactly its
basic feasible solutions (B&T Thm. 2.3), and there are only finitely many of those
(B&T Cor. 2.1). -/
theorem extremePoints_finite (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    (Set.extremePoints ℝ (Hpoly a b)).Finite := by
  classical
  rcases Set.eq_empty_or_nonempty (Set.extremePoints ℝ (Hpoly a b)) with h | ⟨x0, hx0⟩
  · rw [h]; exact Set.finite_empty
  have hne : (Hpoly a b).Nonempty := ⟨x0, hx0.1⟩
  have hCne : (constraintSet (constrOf a b)).Nonempty := by
    rw [← image_hpoly a b]
    exact ⟨eqv d x0, x0, hx0.1, rfl⟩
  -- extreme points of the constraint system are basic feasible solutions
  have hsub : Set.extremePoints ℝ (constraintSet (constrOf a b))
      ⊆ {x | IsBasicFeasibleSolution (constrOf a b) x} := by
    intro x hx
    exact ((lp_vertex_extreme_bfs_equiv (constrOf a b) x hCne hx.1).out 1 2).mp hx
  have hfin : (Set.extremePoints ℝ (constraintSet (constrOf a b))).Finite :=
    Set.Finite.subset (lp_basic_solutions_finite (constrOf a b)).2 hsub
  -- transport back along the linear equivalence
  have himg : (eqv d) '' (Set.extremePoints ℝ (Hpoly a b))
      = Set.extremePoints ℝ (constraintSet (constrOf a b)) := by
    rw [image_extremePoints (eqv d) (Hpoly a b), image_hpoly a b]
  have : ((eqv d) '' (Set.extremePoints ℝ (Hpoly a b))).Finite := himg ▸ hfin
  exact Set.Finite.of_finite_image this ((eqv d).injective.injOn)


/-- An H-polytope is closed: it is an intersection of closed half-spaces. -/
theorem hpoly_closed (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    IsClosed (Hpoly a b) := by
  have : Hpoly a b = ⋂ i, {x : EuclideanSpace ℝ (Fin d) | ⟪a i, x⟫ ≤ b i} := by
    ext x; simp [Hpoly, Set.mem_iInter]
  rw [this]
  refine isClosed_iInter fun i => ?_
  exact isClosed_le (continuous_const.inner continuous_id) continuous_const

theorem hpoly_compact (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) : IsCompact (Hpoly a b) :=
  Metric.isCompact_of_isClosed_isBounded (hpoly_closed a b) hbd

/-- **Minkowski's theorem for H-polytopes.**  A bounded H-polytope is the convex hull
of its finitely many vertices.  Krein--Milman gives the closure of the hull; the hull
of a finite set is already compact, hence closed, so the closure is redundant. -/
theorem hpoly_eq_convexHull (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    Hpoly a b = convexHull ℝ (Set.extremePoints ℝ (Hpoly a b)) := by
  have hcomp := hpoly_compact a b hbd
  have hconv : Convex ℝ (Hpoly a b) := by
    intro x hx y hy s t hs ht hst i
    have h1 := hx i
    have h2 := hy i
    have hexp : ⟪a i, s • x + t • y⟫ = s * ⟪a i, x⟫ + t * ⟪a i, y⟫ := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [hexp]
    have e1 : s * ⟪a i, x⟫ ≤ s * b i := mul_le_mul_of_nonneg_left h1 hs
    have e2 : t * ⟪a i, y⟫ ≤ t * b i := mul_le_mul_of_nonneg_left h2 ht
    have e3 : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
    linarith
  have hcl := closure_convexHull_extremePoints hcomp hconv
  have hfin := extremePoints_finite a b
  have hhullcomp : IsCompact (convexHull ℝ (Set.extremePoints ℝ (Hpoly a b))) :=
    hfin.isCompact_convexHull ℝ
  calc Hpoly a b = closure (convexHull ℝ (Set.extremePoints ℝ (Hpoly a b))) := hcl.symm
    _ = convexHull ℝ (Set.extremePoints ℝ (Hpoly a b)) := hhullcomp.isClosed.closure_eq


/-- **Every vertex is exposed by a strictly separating functional.**  Transported
from B&T Thm. 2.3: an extreme point of a constraint system is a *vertex* in the
book's sense, i.e. the unique minimiser of some linear cost. -/
theorem exists_strict_functional (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) :
    ∃ g : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ, ∀ y ∈ Hpoly a b, y ≠ u → g u < g y := by
  classical
  have hCne : (constraintSet (constrOf a b)).Nonempty := by
    rw [← image_hpoly a b]; exact ⟨eqv d u, u, hu.1, rfl⟩
  have humem : eqv d u ∈ constraintSet (constrOf a b) := by
    rw [← image_hpoly a b]; exact ⟨u, hu.1, rfl⟩
  have huext : eqv d u ∈ Set.extremePoints ℝ (constraintSet (constrOf a b)) := by
    rw [← image_hpoly a b, ← image_extremePoints (eqv d) (Hpoly a b)]
    exact ⟨u, hu, rfl⟩
  obtain ⟨-, c, hc⟩ :=
    ((lp_vertex_extreme_bfs_equiv (constrOf a b) (eqv d u) hCne humem).out 1 0).mp huext
  let g0 : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun y => c ⬝ᵥ y
      map_add' := fun x y => by simp [dotProduct_add]
      map_smul' := fun r x => by simp [dotProduct_smul] }
  refine ⟨g0.comp (eqv d).toLinearMap, ?_⟩
  intro y hy hyu
  have hymem : eqv d y ∈ constraintSet (constrOf a b) := by
    rw [← image_hpoly a b]; exact ⟨y, hy, rfl⟩
  exact hc _ hymem (fun h => hyu ((eqv d).injective h))


/-- **Every vertex has `d` linearly independent active constraints** (B&T Thm. 2.3 +
Def. 2.9).  In particular their normals are nonzero. -/
theorem exists_active_basis (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) :
    ∃ s : Finset (Fin n), s.card = d ∧ (∀ i ∈ s, ⟪a i, u⟫ = b i) ∧ (∀ i ∈ s, a i ≠ 0) := by
  classical
  have hCne : (constraintSet (constrOf a b)).Nonempty := by
    rw [← image_hpoly a b]; exact ⟨eqv d u, u, hu.1, rfl⟩
  have humem : eqv d u ∈ constraintSet (constrOf a b) := by
    rw [← image_hpoly a b]; exact ⟨u, hu.1, rfl⟩
  have huext : eqv d u ∈ Set.extremePoints ℝ (constraintSet (constrOf a b)) := by
    rw [← image_hpoly a b, ← image_extremePoints (eqv d) (Hpoly a b)]
    exact ⟨u, hu, rfl⟩
  obtain ⟨⟨-, s, hcard, hact, hindep⟩, -⟩ :=
    ((lp_vertex_extreme_bfs_equiv (constrOf a b) (eqv d u) hCne humem).out 1 2).mp huext
  refine ⟨s, hcard, ?_, ?_⟩
  · intro i hi
    have := hact i hi
    simp only [LinearConstraint.IsActiveAt, constrOf] at this
    rw [inner_eq_dotProduct]
    exact this
  · intro i hi
    have hz := hindep.ne_zero (⟨i, hi⟩ : {x // x ∈ s})
    intro hcon
    apply hz
    simp only [constrOf]
    funext j
    have : a i j = 0 := by rw [hcon]; rfl
    simpa using this

end HirschBridge

open Hirsch HirschLib

namespace HirschFace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `S` is a face of the finite point set `V`: the set of minimisers over `V` of some
linear functional. -/
def IsFaceSet (V S : Finset E) : Prop :=
  S ⊆ V ∧ ∃ (f : E →ₗ[ℝ] ℝ) (t : ℝ), (∀ z ∈ V, t ≤ f z) ∧ (∀ z ∈ V, z ∈ S ↔ f z = t)

theorem IsFaceSet.subset {V S : Finset E} (h : IsFaceSet V S) : S ⊆ V := h.1

theorem isFaceSet_self (V : Finset E) : IsFaceSet V V :=
  ⟨Finset.Subset.refl V, 0, 0, fun z _ => le_refl 0, fun z hz => ⟨fun _ => rfl, fun _ => hz⟩⟩

/-- A face of a face is a face. -/
theorem IsFaceSet.trans {V S T : Finset E} (hS : IsFaceSet V S) (hT : IsFaceSet S T)
    (hSV : S ⊆ V) : IsFaceSet V T := by
  classical
  have hTS : T ⊆ S := hT.1
  by_cases hVS : (V \ S).Nonempty
  · obtain ⟨-, f, t, hfmin, hfmem⟩ := hS
    obtain ⟨-, h, s, hhmin, hhmem⟩ := hT
    set δ : ℝ := (V \ S).inf' hVS (fun z => f z - t) with hδ
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]
      intro z hz
      obtain ⟨hzV, hzS⟩ := Finset.mem_sdiff.mp hz
      have := hfmin z hzV
      rcases lt_or_eq_of_le this with hlt | heq
      · linarith
      · exact absurd ((hfmem z hzV).mpr heq.symm) hzS
    have hVne : V.Nonempty := ⟨(hVS.choose), (Finset.mem_sdiff.mp hVS.choose_spec).1⟩
    set M : ℝ := V.sup' hVne (fun z => |s - h z|) with hM
    have hMnn : 0 ≤ M := by
      obtain ⟨z, hz⟩ := hVne
      exact le_trans (abs_nonneg _) (Finset.le_sup' (fun z => |s - h z|) hz)
    set ε : ℝ := δ / (2 * (M + 1)) with hε
    have hεpos : 0 < ε := by rw [hε]; positivity
    have hεM : ε * M < δ := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    refine ⟨hTS.trans hSV, f + ε • h, t + ε * s, ?_, ?_⟩
    · intro z hzV
      by_cases hzS : z ∈ S
      · have hfz : f z = t := (hfmem z hzV).mp hzS
        have hhz : s ≤ h z := hhmin z hzS
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        nlinarith
      · have hzd : z ∈ V \ S := Finset.mem_sdiff.mpr ⟨hzV, hzS⟩
        have h1 : δ ≤ f z - t := Finset.inf'_le (fun z => f z - t) hzd
        have h2 : |s - h z| ≤ M := Finset.le_sup' (fun z => |s - h z|) hzV
        have h3 : s - h z ≤ M := le_trans (le_abs_self _) h2
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        nlinarith
    · intro z hzV
      constructor
      · intro hzT
        have hzS : z ∈ S := hTS hzT
        have hfz : f z = t := (hfmem z hzV).mp hzS
        have hhz : h z = s := (hhmem z hzS).mp hzT
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [hfz, hhz]
      · intro heq
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at heq
        have hzS : z ∈ S := by
          by_contra hzS
          have hzd : z ∈ V \ S := Finset.mem_sdiff.mpr ⟨hzV, hzS⟩
          have h1 : δ ≤ f z - t := Finset.inf'_le (fun z => f z - t) hzd
          have h2 : |s - h z| ≤ M := Finset.le_sup' (fun z => |s - h z|) hzV
          have h3 : s - h z ≤ M := le_trans (le_abs_self _) h2
          nlinarith
        have hfz : f z = t := (hfmem z hzV).mp hzS
        have hhz : h z = s := by
          have := hhmin z hzS
          nlinarith
        exact (hhmem z hzS).mpr hhz
  · -- `S = V`
    have hSeq : S = V := by
      apply Finset.Subset.antisymm hSV
      intro z hzV
      by_contra hzS
      exact hVS ⟨z, Finset.mem_sdiff.mpr ⟨hzV, hzS⟩⟩
    rw [← hSeq]
    exact hT


/-- Three distinct points on a line cannot all be extreme. -/
theorem three_collinear_absurd (P : Set E) (z₀ v : E) (hv : v ≠ 0)
    {r₁ r₂ r₃ : ℝ} (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃)
    (e1 : z₀ + r₁ • v ∈ Set.extremePoints ℝ P)
    (e2 : z₀ + r₂ • v ∈ Set.extremePoints ℝ P)
    (e3 : z₀ + r₃ • v ∈ Set.extremePoints ℝ P) : False := by
  have key : ∀ (s₁ s₂ s₃ : ℝ), s₁ < s₂ → s₂ < s₃ →
      z₀ + s₁ • v ∈ Set.extremePoints ℝ P → z₀ + s₃ • v ∈ Set.extremePoints ℝ P →
      z₀ + s₂ • v ∈ Set.extremePoints ℝ P → False := by
    intro s₁ s₂ s₃ h1 h2 hx hz hy
    exact not_extreme_of_between P z₀ v hv s₁ s₂ s₃ h1 h2 hx.1 hz.1 hy
  rcases lt_trichotomy r₁ r₂ with a | a | a
  · rcases lt_trichotomy r₂ r₃ with b | b | b
    · exact key r₁ r₂ r₃ a b e1 e3 e2
    · exact h23 b
    · rcases lt_trichotomy r₁ r₃ with cc | cc | cc
      · exact key r₁ r₃ r₂ cc b e1 e2 e3
      · exact h13 cc
      · exact key r₃ r₁ r₂ cc a e3 e2 e1
  · exact h12 a
  · rcases lt_trichotomy r₁ r₃ with cc | cc | cc
    · exact key r₂ r₁ r₃ a cc e2 e3 e1
    · exact h13 cc
    · rcases lt_trichotomy r₂ r₃ with b | b | b
      · exact key r₂ r₃ r₁ b cc e2 e1 e3
      · exact h23 b
      · exact key r₃ r₂ r₁ b a e3 e1 e2

/-- Three or more vertices are never all on one line through `u`. -/
theorem exists_off_line (P : Set E) (S : Finset E) (u : E)
    (hSext : ∀ z ∈ S, z ∈ Set.extremePoints ℝ P) (hu : u ∈ S) (hcard : 3 ≤ S.card)
    (v : E) (hv : v ≠ 0) : ∃ z ∈ S, ∀ r : ℝ, z ≠ u + r • v := by
  classical
  by_contra hcon
  push_neg at hcon
  choose r hr using hcon
  have h2S : 2 < S.card := by omega
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp h2S
  have hinj : ∀ (p : E) (hp : p ∈ S) (q : E) (hq : q ∈ S), r p hp = r q hq → p = q := by
    intro p hp q hq hpq
    rw [hr p hp, hr q hq, hpq]
  exact three_collinear_absurd P u v hv
    (fun h => hxy (hinj x hx y hy h)) (fun h => hxz (hinj x hx z hz h))
    (fun h => hyz (hinj y hy z hz h))
    ((hr x hx) ▸ hSext x hx) ((hr y hy) ▸ hSext y hy) ((hr z hz) ▸ hSext z hz)


section Euclid

open scoped RealInnerProductSpace

variable {d : ℕ}

local notation "Ed" => EuclideanSpace ℝ (Fin d)

/-- Gram--Schmidt: a functional killing `v₁` but not `v₂`, when `v₂ ∉ ℝ v₁`. -/
theorem exists_sep_functional (v₁ v₂ : Ed) (h1 : v₁ ≠ 0) (h2 : ∀ μ : ℝ, v₂ ≠ μ • v₁) :
    ∃ h : Ed →ₗ[ℝ] ℝ, h v₁ = 0 ∧ h v₂ ≠ 0 := by
  have hn1 : (0:ℝ) < ⟪v₁, v₁⟫ := real_inner_self_pos.mpr h1
  set μ : ℝ := ⟪v₁, v₂⟫ / ⟪v₁, v₁⟫ with hμ
  set q : Ed := v₂ - μ • v₁ with hq
  have hqne : q ≠ 0 := by
    intro hz
    exact h2 μ (by rw [hq] at hz; linear_combination (norm := module) hz)
  have hqv1 : ⟪q, v₁⟫ = 0 := by
    rw [hq, inner_sub_left, real_inner_smul_left, hμ, real_inner_comm v₁ v₂]
    field_simp
    ring
  have hqv2 : ⟪q, v₂⟫ = ⟪q, q⟫ := by
    have : v₂ = q + μ • v₁ := by rw [hq]; module
    rw [this, inner_add_right, real_inner_smul_right, hqv1]
    ring
  refine ⟨(innerSL ℝ q).toLinearMap, hqv1, ?_⟩
  have : ((innerSL ℝ q).toLinearMap) v₂ = ⟪q, q⟫ := hqv2
  rw [this]
  exact ne_of_gt (real_inner_self_pos.mpr hqne)

/-- A functional strict at `u` stays strict after a small perturbation. -/
theorem strict_perturb (S : Finset Ed) (u : Ed) (g h : Ed →ₗ[ℝ] ℝ)
    (hg : ∀ z ∈ S, z ≠ u → g u < g z) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| ≤ ε₀ → ∀ z ∈ S, z ≠ u → (g + ε • h) u < (g + ε • h) z := by
  classical
  by_cases hSne : (S.filter (fun z => z ≠ u)).Nonempty
  · set T := S.filter (fun z => z ≠ u) with hT
    set δ : ℝ := T.inf' hSne (fun z => g z - g u) with hδ
    set M : ℝ := T.sup' hSne (fun z => |h u - h z|) with hM
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]
      intro z hz
      obtain ⟨hzS, hzu⟩ := Finset.mem_filter.mp hz
      linarith [hg z hzS hzu]
    have hMnn : 0 ≤ M := by
      obtain ⟨z, hz⟩ := hSne
      exact le_trans (abs_nonneg _) (Finset.le_sup' (fun z => |h u - h z|) hz)
    refine ⟨δ / (2 * (M + 1)), by positivity, ?_⟩
    intro ε hε z hzS hzu
    have hzT : z ∈ T := Finset.mem_filter.mpr ⟨hzS, hzu⟩
    have h1 : δ ≤ g z - g u := Finset.inf'_le (fun z => g z - g u) hzT
    have h2 : |h u - h z| ≤ M := Finset.le_sup' (fun z => |h u - h z|) hzT
    have h3 : |ε * (h u - h z)| ≤ (δ / (2 * (M + 1))) * M := by
      rw [abs_mul]
      exact mul_le_mul hε h2 (abs_nonneg _) (by positivity)
    have h4 : (δ / (2 * (M + 1))) * M < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have h5 : ε * (h u - h z) ≤ |ε * (h u - h z)| := le_abs_self _
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    nlinarith
  · refine ⟨1, one_pos, ?_⟩
    intro ε _ z hzS hzu
    exact absurd (Finset.mem_filter.mpr ⟨hzS, hzu⟩) (by
      intro hmem; exact hSne ⟨z, hmem⟩)

/-- **The improving-edge step in any dimension.**  Inside a face `S` of the vertex set,
if `c` is not minimal at the vertex `u`, some *edge* of `S` at `u` improves `c`.  The
proof rotates the supporting functional at `u` towards `c`, which cuts `S` down to a
proper subface still containing `u` and an improving vertex, and recurses. -/
theorem improving_face (P : Set Ed) (V : Finset Ed)
    (hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ P)
    (hvert : ∀ z ∈ V, ∃ g : Ed →ₗ[ℝ] ℝ, ∀ y ∈ V, y ≠ z → g z < g y)
    (c : Ed →ₗ[ℝ] ℝ) :
    ∀ (m : ℕ) (S : Finset Ed), S.card ≤ m → IsFaceSet V S → ∀ u ∈ S,
      (∃ w ∈ S, c w < c u) → ∃ w ∈ S, c w < c u ∧ IsFaceSet V ({u, w} : Finset Ed) := by
  classical
  intro m
  induction m with
  | zero =>
      intro S hScard _ u huS _
      exact absurd (Finset.card_pos.mpr ⟨u, huS⟩) (by omega)
  | succ m ih =>
      intro S hScard hSface u huS hex
      obtain ⟨w₀, hw₀S, hw₀c⟩ := hex
      have hw₀u : w₀ ≠ u := by intro hh; rw [hh] at hw₀c; exact lt_irrefl _ hw₀c
      by_cases hcard3 : 3 ≤ S.card
      · obtain ⟨g, hgV⟩ := hvert u (hSface.1 huS)
        have hgS : ∀ z ∈ S, z ≠ u → g u < g z := fun z hz hzu => hgV z (hSface.1 hz) hzu
        have hv1 : w₀ - u ≠ 0 := sub_ne_zero.mpr hw₀u
        obtain ⟨z₂, hz₂S, hz₂⟩ :=
          exists_off_line P S u (fun z hz => hVext z (hSface.1 hz)) huS hcard3 (w₀ - u) hv1
        have hv2 : ∀ μ : ℝ, z₂ - u ≠ μ • (w₀ - u) := by
          intro μ hcon
          exact hz₂ μ (by rw [← hcon]; abel)
        obtain ⟨h, hhv1, hhv2⟩ := exists_sep_functional (w₀ - u) (z₂ - u) hv1 hv2
        obtain ⟨ε₀, hε₀, hstrict⟩ := strict_perturb S u g h hgS
        have hgv1 : 0 < g w₀ - g u := by linarith [hgS w₀ hw₀S hw₀u]
        have hcv1 : c w₀ - c u < 0 := by linarith
        have hh1 : h w₀ - h u = 0 := by rw [← map_sub]; exact hhv1
        have hh2 : h z₂ - h u ≠ 0 := by rw [← map_sub]; exact hhv2
        -- a rotated functional can be constant on `S` for at most one perturbation size
        have hbad : ∀ ε₁ ε₂ : ℝ,
            (∃ l₁ : ℝ, ∀ z ∈ S, c z + l₁ * (g z + ε₁ * h z) = c u + l₁ * (g u + ε₁ * h u)) →
            (∃ l₂ : ℝ, ∀ z ∈ S, c z + l₂ * (g z + ε₂ * h z) = c u + l₂ * (g u + ε₂ * h u)) →
            ε₁ = ε₂ := by
          rintro ε₁ ε₂ ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩
          have hh1' : h w₀ = h u := by linarith
          have e1 := hl₁ w₀ hw₀S
          have e2 := hl₂ w₀ hw₀S
          rw [hh1'] at e1 e2
          have hd1 : l₁ * (g w₀ - g u) = -(c w₀ - c u) := by linear_combination e1
          have hd2 : l₂ * (g w₀ - g u) = -(c w₀ - c u) := by linear_combination e2
          have hl12 : l₁ = l₂ := by
            have : (l₁ - l₂) * (g w₀ - g u) = 0 := by linarith
            rcases mul_eq_zero.mp this with hz | hz
            · linarith [sub_eq_zero.mp hz]
            · linarith
          have hlne : l₁ ≠ 0 := by
            intro hz
            rw [hz] at hd1
            simp at hd1
            linarith
          have f1 := hl₁ z₂ hz₂S
          have f2 := hl₂ z₂ hz₂S
          rw [← hl12] at f2
          have hkey : l₁ * (h z₂ - h u) * (ε₁ - ε₂) = 0 := by linear_combination f1 - f2
          rcases mul_eq_zero.mp hkey with hz | hz
          · rcases mul_eq_zero.mp hz with hz' | hz'
            · exact absurd hz' hlne
            · exact absurd hz' hh2
          · linarith [sub_eq_zero.mp hz]
        have hchoose : ∃ ε : ℝ, |ε| ≤ ε₀ ∧
            ¬ (∃ l : ℝ, ∀ z ∈ S, c z + l * (g z + ε * h z) = c u + l * (g u + ε * h u)) := by
          by_contra hcon
          push_neg at hcon
          have hA := hcon ε₀ (by rw [abs_of_pos hε₀])
          have hB := hcon (ε₀ / 2) (by rw [abs_of_pos (by linarith)]; linarith)
          have := hbad ε₀ (ε₀ / 2) hA hB
          linarith
        obtain ⟨ε, hεle, hεgood⟩ := hchoose
        set g' : Ed →ₗ[ℝ] ℝ := g + ε • h with hg'
        have hg'S : ∀ z ∈ S, z ≠ u → g' u < g' z := hstrict ε hεle
        obtain ⟨lam, w, hlam, hwS, hwu, hwc, hfeq, hfmin⟩ :=
          exists_rotated_functional S u g' c hg'S ⟨w₀, hw₀S, hw₀c⟩
        set T : Finset Ed := S.filter (fun z => c z + lam * g' z = c u + lam * g' u) with hT
        have huT : u ∈ T := Finset.mem_filter.mpr ⟨huS, rfl⟩
        have hwT : w ∈ T := Finset.mem_filter.mpr ⟨hwS, by linarith⟩
        have hTface : IsFaceSet S T := by
          refine ⟨Finset.filter_subset _ _, c + lam • g', c u + lam * g' u, ?_, ?_⟩
          · intro z hz
            simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
            exact hfmin z hz
          · intro z hz
            simp only [hT, Finset.mem_filter, LinearMap.add_apply, LinearMap.smul_apply,
              smul_eq_mul]
            exact ⟨fun hh => hh.2, fun hh => ⟨hz, hh⟩⟩
        have hTsub : T ⊂ S := by
          refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr ?_
          by_contra hcon
          push_neg at hcon
          refine hεgood ⟨lam, fun z hz => ?_⟩
          have : z ∈ T := hcon z hz
          have h2 := (Finset.mem_filter.mp this).2
          simp only [hg', LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h2
          linarith
        have hTcard : T.card ≤ m := by
          have := Finset.card_lt_card hTsub
          omega
        obtain ⟨w', hw'T, hw'c, hw'face⟩ :=
          ih T hTcard (hSface.trans hTface hSface.1) u huT ⟨w, hwT, hwc⟩
        exact ⟨w', (Finset.filter_subset _ _) hw'T, hw'c, hw'face⟩
      · have hsub : ({u, w₀} : Finset Ed) ⊆ S := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact huS
          · exact hw₀S
        have hc2 : ({u, w₀} : Finset Ed).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simp [Ne.symm hw₀u]), Finset.card_singleton]
        have heq : ({u, w₀} : Finset Ed) = S :=
          Finset.eq_of_subset_of_card_le hsub (by omega)
        exact ⟨w₀, hw₀S, hw₀c, heq ▸ hSface⟩

end Euclid

end HirschFace

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschBridge HirschFace

namespace HirschNaddef

variable {d : ℕ}

/-- An edge of the vertex set is an edge of the polytope. -/
theorem adj_of_faceSet (V : Finset (EuclideanSpace ℝ (Fin d))) (P : Set (EuclideanSpace ℝ (Fin d)))
    (hP : P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d)))) (u w : EuclideanSpace ℝ (Fin d))
    (huw : u ≠ w) (hface : IsFaceSet V ({u, w} : Finset _)) : Adj P u w := by
  obtain ⟨hsub, f, t, hmin, hmem⟩ := hface
  have huV : u ∈ V := hsub (by simp)
  have hwV : w ∈ V := hsub (by simp)
  refine adj_of_separating (V : Set _) P hP f t u w huw (Finset.mem_coe.mpr huV)
    (Finset.mem_coe.mpr hwV) ((hmem u huV).mp (by simp)) ((hmem w hwV).mp (by simp)) ?_
  intro z hz hzu hzw
  have hzV : z ∈ V := Finset.mem_coe.mp hz
  rcases lt_or_eq_of_le (hmin z hzV) with h | h
  · exact h
  · exact absurd ((hmem z hzV).mpr h.symm) (by simp [hzu, hzw])

/-- **The improving-edge step for a polytope.** -/
theorem improving_edge (V : Finset (EuclideanSpace ℝ (Fin d)))
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (hP : P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ P)
    (hvert : ∀ z ∈ V, ∃ g : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ, ∀ y ∈ V, y ≠ z → g z < g y)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) (c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ)
    (hex : ∃ z ∈ V, c z < c u) : ∃ w ∈ V, c w < c u ∧ Adj P u w := by
  obtain ⟨w, hwV, hwc, hwface⟩ :=
    improving_face P V hVext hvert c V.card V le_rfl (isFaceSet_self V) u hu hex
  have hwu : u ≠ w := by intro hh; rw [← hh] at hwc; exact lt_irrefl _ hwc
  exact ⟨w, hwV, hwc, adj_of_faceSet V P hP u w hwu hwface⟩

/-- The Hamming objective: for `0/1` points, `hamFun v x` is the Hamming distance from
`x` to `v` up to an additive constant. -/
noncomputable def hamFun (v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, (1 - 2 * v i) * x i
  map_add' x y := by
    simp only [PiLp.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Hamming distance between two points, as a natural number. -/
noncomputable def ham (x v : EuclideanSpace ℝ (Fin d)) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ v i)).card

theorem ham_le (x v : EuclideanSpace ℝ (Fin d)) : ham x v ≤ d := by
  have := Finset.card_filter_le (Finset.univ : Finset (Fin d)) (fun i => x i ≠ v i)
  simpa [ham] using this

theorem ham_eq_zero {x v : EuclideanSpace ℝ (Fin d)} (h : ham x v = 0) : x = v := by
  refine PiLp.ext fun i => ?_
  by_contra hne
  have : i ∈ Finset.univ.filter (fun i => x i ≠ v i) := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
  rw [ham, Finset.card_eq_zero] at h
  rw [h] at this
  exact absurd this (Finset.notMem_empty i)

/-- On `0/1` points the linear objective differs from the Hamming distance by a constant. -/
theorem hamFun_eq (v x : EuclideanSpace ℝ (Fin d))
    (hv : ∀ i, v i = 0 ∨ v i = 1) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    hamFun v x = (ham x v : ℝ) - ∑ i, v i := by
  have hterm : ∀ i : Fin d, (1 - 2 * v i) * x i
      = (if x i ≠ v i then (1:ℝ) else 0) - v i := by
    intro i
    rcases hv i with h1 | h1 <;> rcases hx i with h2 | h2 <;>
      simp [h1, h2] <;> norm_num
  simp only [hamFun, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
  congr 1
  rw [ham, Finset.sum_boole]


/-- **Naddef 1989.**  A bounded H-polytope all of whose vertices are `0/1` vectors has
combinatorial diameter at most `d`: from any vertex the Hamming distance to the target
can be decreased by one along an edge. -/
theorem naddef_bound (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (h01 : ∀ x ∈ Set.extremePoints ℝ (Hpoly a b), ∀ i, x i = 0 ∨ x i = 1) :
    DiamLE (Hpoly a b) d := by
  classical
  set V : Finset (EuclideanSpace ℝ (Fin d)) := (extremePoints_finite a b).toFinset with hVdef
  have hmemV : ∀ z, z ∈ V ↔ z ∈ Set.extremePoints ℝ (Hpoly a b) := by
    intro z; rw [hVdef]; exact Set.Finite.mem_toFinset _
  have hcoeV : (V : Set (EuclideanSpace ℝ (Fin d))) = Set.extremePoints ℝ (Hpoly a b) := by
    ext z; rw [Finset.mem_coe, hmemV]
  have hP : Hpoly a b = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))) := by
    rw [hcoeV]; exact hpoly_eq_convexHull a b hbd
  have hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ (Hpoly a b) := fun z hz => (hmemV z).mp hz
  have hvert : ∀ z ∈ V, ∃ g : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ, ∀ y ∈ V, y ≠ z → g z < g y := by
    intro z hzV
    obtain ⟨g, hg⟩ := exists_strict_functional a b ((hmemV z).mp hzV)
    exact ⟨g, fun y hyV hyz => hg y (((hmemV y).mp hyV).1) hyz⟩
  refine diamLE_of_reach _ _ (fun u hu v hv => ?_)
  have huV : u ∈ V := (hmemV u).mpr hu
  have hvV : v ∈ V := (hmemV v).mpr hv
  have hv01 : ∀ i, v i = 0 ∨ v i = 1 := h01 v hv
  -- descent on the Hamming distance to `v`
  have key : ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin d)), x ∈ V → ham x v ≤ m →
      Reach (Hpoly a b) (ham x v) x v := by
    intro m
    induction m with
    | zero =>
        intro x hxV hx0
        have : ham x v = 0 := by omega
        rw [this, ham_eq_zero this]
        exact reach_zero _ v
    | succ m ih =>
        intro x hxV hxm
        rcases Nat.eq_zero_or_pos (ham x v) with h0 | hpos
        · rw [h0, ham_eq_zero h0]; exact reach_zero _ v
        · have hx01 : ∀ i, x i = 0 ∨ x i = 1 := h01 x ((hmemV x).mp hxV)
          have hcx : hamFun v x = (ham x v : ℝ) - ∑ i, v i := hamFun_eq v x hv01 hx01
          have hcv : hamFun v v = (ham v v : ℝ) - ∑ i, v i := hamFun_eq v v hv01 hv01
          have hvv : ham v v = 0 := by
            simp [ham]
          have hlt : hamFun v v < hamFun v x := by
            rw [hcx, hcv, hvv, Nat.cast_zero]
            have : (0:ℝ) < (ham x v : ℝ) := by exact_mod_cast hpos
            linarith
          obtain ⟨w, hwV, hwc, hadj⟩ :=
            improving_edge V (Hpoly a b) hP hVext hvert x hxV (hamFun v) ⟨v, hvV, hlt⟩
          have hw01 : ∀ i, w i = 0 ∨ w i = 1 := h01 w ((hmemV w).mp hwV)
          have hcw : hamFun v w = (ham w v : ℝ) - ∑ i, v i := hamFun_eq v w hv01 hw01
          have hhamlt : ham w v < ham x v := by
            have : (ham w v : ℝ) < (ham x v : ℝ) := by rw [hcw, hcx] at hwc; linarith
            exact_mod_cast this
          have hrec : Reach (Hpoly a b) (ham w v) w v := ih w hwV (by omega)
          have : Reach (Hpoly a b) (1 + ham w v) x v :=
            reach_trans _ (reach_one_of_adj _ hadj) hrec
          exact reach_mono _ (by omega) this
  exact ⟨ham u v, ham_le u v, key (ham u v) u huV le_rfl⟩

end HirschNaddef


open HirschNaddef

theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (h01 : ∀ x ∈ Set.extremePoints ℝ (Hpoly a b), ∀ i, x i = 0 ∨ x i = 1) :
    DiamLE (Hpoly a b) d :=
  naddef_bound n a b hne hbd h01
