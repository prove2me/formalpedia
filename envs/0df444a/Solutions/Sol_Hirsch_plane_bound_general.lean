-- Prove2me | solution 1 for Hirsch.plane_bound_general
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T08:43:58.054473+00:00
-- url     : https://prove2.me/submissions/774f3348-0705-4e77-b4ec-9f2273fdb2a5

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_ActiveConstraints
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_lp_basic_solutions_finite
import Theorems.Thm_Hirsch_graph_connected_general

open scoped RealInnerProductSpace
open Hirsch LinearOptimization

open scoped RealInnerProductSpace
open Hirsch

namespace HirschLib



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

/-- The plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

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

end HirschWalk

open Hirsch HirschLib

namespace HirschFace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The minimising face of a linear functional over a convex set is an extreme subset. -/
theorem exposed_isExtreme (P : Set E) (f : E →ₗ[ℝ] ℝ) (t : ℝ)
    (hmin : ∀ x ∈ P, t ≤ f x) : IsExtreme ℝ P {x | x ∈ P ∧ f x = t} := by
  constructor
  · exact fun x hx => hx.1
  · rintro x₁ hx₁ x₂ hx₂ x ⟨hxP, hxt⟩ ⟨p, q, hp, hq, hpq, hx⟩
    have hc : f x = p * f x₁ + q * f x₂ := by
      rw [← hx, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 := hmin _ hx₁
    have h2 := hmin _ hx₂
    have h3 : p * f x₁ + q * f x₂ = t := by rw [← hc, hxt]
    have key : p * (f x₁ - t) + q * (f x₂ - t) = 0 := by linear_combination h3 - t * hpq
    have hz1 : 0 ≤ p * (f x₁ - t) := mul_nonneg hp.le (by linarith)
    have hz2 : 0 ≤ q * (f x₂ - t) := mul_nonneg hq.le (by linarith)
    refine ⟨hx₁, ?_⟩
    have : p * (f x₁ - t) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hp)
    · linarith

end HirschFace

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


/-- The active basis at a vertex, with the linear independence of its normals. -/
theorem exists_active_basis_indep (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) :
    ∃ s : Finset (Fin n), s.card = d ∧ (∀ i ∈ s, ⟪a i, u⟫ = b i) ∧
      LinearIndependent ℝ (fun i : s => a i.1) := by
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
  · have h1 : LinearIndependent ℝ (fun i : s => (constrOf a b i.1).a) := hindep
    have h2 := h1.map' (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap
      (LinearMap.ker_eq_bot_of_injective (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.injective)
    exact h2

end HirschBridge

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschBridge HirschFace LinearOptimization

namespace HirschSimple

variable {d n : ℕ}

/-- The set of inequalities tight at a point. -/
noncomputable def tightSet (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ⟪a i, x⟫ = b i)

/-- **The tight set determines the smallest face.**  If a face contains `m`, it contains
every point of the polytope whose tight set includes that of `m`: pushing slightly past
`m` away from such a point stays in the polytope, exhibiting `m` inside an open segment. -/
theorem mem_face_of_tightSet_subset (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : IsExtreme ℝ (Hpoly a b) F)
    {m z : EuclideanSpace ℝ (Fin d)} (hm : m ∈ F) (hmP : m ∈ Hpoly a b) (hz : z ∈ Hpoly a b)
    (hsub : tightSet a b m ⊆ tightSet a b z) : z ∈ F := by
  classical
  rcases eq_or_ne z m with rfl | hzm
  · exact hm
  -- a small step past `m` away from `z` stays inside
  obtain ⟨ε, hε, hmem⟩ : ∃ ε : ℝ, 0 < ε ∧ m + ε • (m - z) ∈ Hpoly a b := by
    by_cases hSne : (Finset.univ.filter (fun j => j ∉ tightSet a b m)).Nonempty
    · set M : ℝ := (Finset.univ.filter (fun j => j ∉ tightSet a b m)).sup' hSne
        (fun j => |⟪a j, m - z⟫|) with hM
      set c : ℝ := (Finset.univ.filter (fun j => j ∉ tightSet a b m)).inf' hSne
        (fun j => b j - ⟪a j, m⟫) with hc
      have hcpos : 0 < c := by
        rw [hc, Finset.lt_inf'_iff]
        intro j hj
        have hjm := (Finset.mem_filter.mp hj).2
        rcases lt_or_eq_of_le (hmP j) with h | h
        · linarith
        · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩) hjm
      have hMnn : 0 ≤ M := by
        obtain ⟨j, hj⟩ := hSne
        exact le_trans (abs_nonneg _) (Finset.le_sup' (fun j => |⟪a j, m - z⟫|) hj)
      refine ⟨c / (2 * (M + 1)), by positivity, ?_⟩
      intro j
      have hexp : ⟪a j, m + (c / (2 * (M + 1))) • (m - z)⟫
          = ⟪a j, m⟫ + (c / (2 * (M + 1))) * ⟪a j, m - z⟫ := by
        rw [inner_add_right, real_inner_smul_right]
      rw [hexp]
      by_cases hjt : j ∈ tightSet a b m
      · have h1 : ⟪a j, m⟫ = b j := (Finset.mem_filter.mp hjt).2
        have h2 : ⟪a j, z⟫ = b j := (Finset.mem_filter.mp (hsub hjt)).2
        have : ⟪a j, m - z⟫ = 0 := by rw [inner_sub_right, h1, h2, sub_self]
        rw [this]; linarith
      · have hjm : j ∈ Finset.univ.filter (fun j => j ∉ tightSet a b m) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjt⟩
        have h1 : c ≤ b j - ⟪a j, m⟫ := Finset.inf'_le (fun j => b j - ⟪a j, m⟫) hjm
        have h2 : |⟪a j, m - z⟫| ≤ M := Finset.le_sup' (fun j => |⟪a j, m - z⟫|) hjm
        have h3 : ⟪a j, m - z⟫ ≤ M := le_trans (le_abs_self _) h2
        have h4 : c / (2 * (M + 1)) * M < c := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
        nlinarith [(by positivity : (0:ℝ) < c / (2 * (M + 1)))]
    · refine ⟨1, one_pos, ?_⟩
      intro j
      have hjt : j ∈ tightSet a b m := by
        by_contra hcon
        exact hSne ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcon⟩⟩
      have h1 : ⟪a j, m⟫ = b j := (Finset.mem_filter.mp hjt).2
      have h2 : ⟪a j, z⟫ = b j := (Finset.mem_filter.mp (hsub hjt)).2
      have hexp : ⟪a j, m + (1:ℝ) • (m - z)⟫ = ⟪a j, m⟫ + ⟪a j, m - z⟫ := by
        rw [inner_add_right, one_smul]
      rw [hexp, inner_sub_right, h1, h2]
      linarith
  -- `m` sits strictly between `z` and that point
  set m' : EuclideanSpace ℝ (Fin d) := m + ε • (m - z) with hm'
  have hne : (1 : ℝ) + ε ≠ 0 := by positivity
  have hopen : m ∈ openSegment ℝ z m' := by
    refine ⟨ε / (1 + ε), 1 / (1 + ε), by positivity, by positivity, ?_, ?_⟩
    · field_simp
      ring
    · rw [hm']
      have hcoef1 : ε / (1 + ε) - (1 / (1 + ε)) * ε = 0 := by field_simp; ring
      have hcoef2 : (1 / (1 + ε)) * (1 + ε) = 1 := by field_simp
      calc (ε / (1 + ε)) • z + (1 / (1 + ε)) • (m + ε • (m - z))
          = (ε / (1 + ε) - (1 / (1 + ε)) * ε) • z + ((1 / (1 + ε)) * (1 + ε)) • m := by
            module
        _ = (0:ℝ) • z + (1:ℝ) • m := by rw [hcoef1, hcoef2]
        _ = m := by module
  exact hF.2 hz hmem hm hopen

/-- A segment has only its two endpoints as extreme points. -/
theorem extremePoints_segment_subset {u v : EuclideanSpace ℝ (Fin d)} :
    Set.extremePoints ℝ (segment ℝ u v) ⊆ ({u, v} : Set (EuclideanSpace ℝ (Fin d))) := by
  intro z hz
  rcases eq_or_ne u v with rfl | huv
  · left
    have hzs : z ∈ segment ℝ u u := hz.1
    rw [segment_same] at hzs
    exact hzs
  have hzs : z ∈ segment ℝ u v := hz.1
  rw [segment_eq_image ℝ u v] at hzs
  obtain ⟨t, ht, hzt⟩ := hzs
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · left; rw [← hzt, ← h0]; module
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · right; rw [← hzt, h1]; module
  · exfalso
    have hopen : z ∈ openSegment ℝ u v := ⟨1 - t, t, by linarith, h0, by ring, hzt⟩
    obtain ⟨e1, e2⟩ := (mem_extremePoints.mp hz).2 _ (left_mem_segment ℝ u v) _
      (right_mem_segment ℝ u v) hopen
    exact huv (e1.trans e2.symm)

set_option maxHeartbeats 1000000 in
/-- **The adjacency criterion for arbitrary H-polyhedra.**  Boundedness is not needed:
the shared tight equations cut out a line, its trace on the polyhedron is a convex subset
of that line with `u` and `v` as extreme points, and a convex subset of a line with two
distinct extreme points is exactly the segment between them. -/
theorem face_eq_segment (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v) {T : Finset (Fin n)}
    (hTu : ∀ i ∈ T, ⟪a i, u⟫ = b i) (hTv : ∀ i ∈ T, ⟪a i, v⟫ = b i)
    (hT : T.card = d - 1) (hind : LinearIndependent ℝ (fun i : T => a i.1)) (hd : 1 ≤ d) :
    {x | x ∈ Hpoly a b ∧ ∀ i ∈ T, ⟪a i, x⟫ = b i} = segment ℝ u v := by
  classical
  -- the line cut out by the shared equations
  set U : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
    Submodule.span ℝ (Set.range (fun j : T => a j.1)) with hU
  have hUfr : Module.finrank ℝ U = d - 1 := by
    rw [hU, finrank_span_eq_card hind]; simp [hT]
  have hKfr : Module.finrank ℝ (Uᗮ) = 1 := by
    have hadd := Submodule.finrank_add_finrank_orthogonal (K := U)
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
    omega
  haveI hnt : Nontrivial (Uᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) := by
    rw [← Module.finrank_pos_iff (R := ℝ), hKfr]; norm_num
  obtain ⟨e0, he0⟩ := exists_ne (0 : (Uᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin d))))
  set e : EuclideanSpace ℝ (Fin d) := (e0 : EuclideanSpace ℝ (Fin d)) with hedef
  have he : e ≠ 0 := fun hcon => he0 (Submodule.coe_eq_zero.mp hcon)
  have hspan : Submodule.span ℝ ({e} : Set (EuclideanSpace ℝ (Fin d))) = Uᗮ := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_singleton he, hKfr])
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact e0.2
  have hline : ∀ y : EuclideanSpace ℝ (Fin d), (∀ i ∈ T, ⟪a i, y⟫ = b i) →
      ∃ r : ℝ, y = u + r • e := by
    intro y hy
    have hyu : y - u ∈ Uᗮ := by
      rw [Submodule.mem_orthogonal]
      intro z hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          show ⟪a j.1, y - u⟫ = 0
          rw [inner_sub_right, hy j.1 j.2, hTu j.1 j.2, sub_self]
      | zero => simp
      | add x y' _ _ hx hy' => rw [inner_add_left, hx, hy']; ring
      | smul c x _ hx => rw [real_inner_smul_left, hx]; ring
    rw [← hspan, Submodule.mem_span_singleton] at hyu
    obtain ⟨r, hr⟩ := hyu
    exact ⟨r, by rw [sub_eq_iff_eq_add.mp hr.symm]; abel⟩
  -- the trace of the polyhedron on that line
  set A : Set ℝ := {r : ℝ | u + r • e ∈ Hpoly a b} with hA
  have hAconv : Convex ℝ A := by
    intro s hs t ht p q hp hq hpq
    have hcomb : u + (p * s + q * t) • e = p • (u + s • e) + q • (u + t • e) := by
      have h0 : (p + q) • u = u := by rw [hpq, one_smul]
      calc u + (p * s + q * t) • e = (p + q) • u + (p * s + q * t) • e := by rw [h0]
        _ = p • (u + s • e) + q • (u + t • e) := by module
    show u + (p • s + q • t) • e ∈ Hpoly a b
    simp only [smul_eq_mul]
    rw [hcomb]
    exact HirschLib.hpoly_convex a b hs ht hp hq hpq
  obtain ⟨rv, hrv⟩ := hline v hTv
  have hrvne : rv ≠ 0 := by
    intro h
    apply huv
    have hvu : v = u := by rw [hrv, h]; module
    exact hvu.symm
  have h0A : (0:ℝ) ∈ A := by show u + (0:ℝ) • e ∈ Hpoly a b; simpa using hu.1
  have hrvA : rv ∈ A := by show u + rv • e ∈ Hpoly a b; rw [← hrv]; exact hv.1
  -- `0` and `rv` are extreme points of that trace
  have hextr : ∀ r ∈ A, (u + r • e) ∈ Set.extremePoints ℝ (Hpoly a b) →
      r ∈ Set.extremePoints ℝ A := by
    intro r hrA hrext
    refine ⟨hrA, ?_⟩
    rintro s hs t ht ⟨p, q, hp, hq, hpq, hsum⟩
    have hcomb : p • (u + s • e) + q • (u + t • e) = u + r • e := by
      have h0 : (p + q) • u = u := by rw [hpq, one_smul]
      calc p • (u + s • e) + q • (u + t • e)
          = (p + q) • u + (p * s + q * t) • e := by module
        _ = u + r • e := by rw [h0, show p * s + q * t = r by
              simpa [smul_eq_mul] using hsum]
    have := (mem_extremePoints.mp hrext).2 _ hs _ ht ⟨p, q, hp, hq, hpq, hcomb⟩
    have hus : u + s • e = u + r • e := this.1
    have hd0 : (s - r) • e = 0 := by
      calc (s - r) • e = (u + s • e) - (u + r • e) := by module
        _ = 0 := by rw [hus]; abel
    rcases smul_eq_zero.mp hd0 with h | h
    · linarith [sub_eq_zero.mp h]
    · exact absurd h he
  have h0ext : (0:ℝ) ∈ Set.extremePoints ℝ A := by
    refine hextr 0 h0A ?_
    have hz : u + (0:ℝ) • e = u := by module
    rw [hz]; exact hu
  have hrvext : rv ∈ Set.extremePoints ℝ A := by
    refine hextr rv hrvA ?_
    rw [← hrv]; exact hv
  -- a convex subset of a line with two extreme points is the segment between them
  have hAseg : A = segment ℝ 0 rv :=
    HirschLib.eq_segment_of_finrank_le_one (by simp) A hAconv h0ext hrvext (Ne.symm hrvne)
  -- transport back
  have happ : ∀ y : EuclideanSpace ℝ (Fin d),
      (-∑ i ∈ T, (innerSL ℝ (a i)).toLinearMap) y = -∑ i ∈ T, ⟪a i, y⟫ := by
    intro y; simp [LinearMap.sum_apply]
  have hG : {x | x ∈ Hpoly a b ∧ (-∑ i ∈ T, (innerSL ℝ (a i)).toLinearMap) x
      = -∑ i ∈ T, b i} = segment ℝ u v := by
    apply Set.eq_of_subset_of_subset
    · rintro x ⟨hxP, hxt⟩
      have hxT : ∀ i ∈ T, ⟪a i, x⟫ = b i := by
        have hsum : ∑ i ∈ T, (b i - ⟪a i, x⟫) = 0 := by
          rw [happ] at hxt
          rw [Finset.sum_sub_distrib]
          linarith
        intro i hi
        have hnn : ∀ j ∈ T, 0 ≤ b j - ⟪a j, x⟫ := fun j _ => by linarith [hxP j]
        linarith [(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i hi]
      obtain ⟨r, hr⟩ := hline x hxT
      have hrA : r ∈ A := by show u + r • e ∈ Hpoly a b; rw [← hr]; exact hxP
      rw [hAseg] at hrA
      obtain ⟨p, q, hp, hq, hpq, hpq'⟩ := hrA
      refine ⟨p, q, hp, hq, hpq, ?_⟩
      rw [hr, hrv]
      have hr' : r = q * rv := by simpa using hpq'.symm
      rw [hr']
      have h0 : (p + q) • u = u := by rw [hpq, one_smul]
      calc p • u + q • (u + rv • e) = (p + q) • u + (q * rv) • e := by module
        _ = u + (q * rv) • e := by rw [h0]
    · intro x hx
      obtain ⟨p, q, hp, hq, hpq, hsum⟩ := hx
      have hxP : x ∈ Hpoly a b := by
        rw [← hsum]; exact HirschLib.hpoly_convex a b hu.1 hv.1 hp hq hpq
      refine ⟨hxP, ?_⟩
      rw [happ]
      refine congrArg Neg.neg (Finset.sum_congr rfl fun i hi => ?_)
      show ⟪a i, x⟫ = b i
      rw [← hsum, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        hTu i hi, hTv i hi]
      linear_combination (b i) * hpq
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨hxP, hxT⟩
    have hxG : x ∈ {x | x ∈ Hpoly a b ∧ (-∑ i ∈ T, (innerSL ℝ (a i)).toLinearMap) x
        = -∑ i ∈ T, b i} := by
      refine ⟨hxP, ?_⟩
      rw [happ]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun i hi => hxT i hi)
    rw [hG] at hxG
    exact hxG
  · intro x hx
    have hxG : x ∈ {x | x ∈ Hpoly a b ∧ (-∑ i ∈ T, (innerSL ℝ (a i)).toLinearMap) x
        = -∑ i ∈ T, b i} := by rw [hG]; exact hx
    obtain ⟨hxP, hxt⟩ := hxG
    refine ⟨hxP, ?_⟩
    rw [happ] at hxt
    intro i hi
    have hsum : ∑ j ∈ T, (b j - ⟪a j, x⟫) = 0 := by
      rw [Finset.sum_sub_distrib]; linarith
    have hnn : ∀ j ∈ T, 0 ≤ b j - ⟪a j, x⟫ := fun j _ => by linarith [hxP j]
    linarith [(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i hi]

/-- **The adjacency criterion for arbitrary H-polyhedra.** -/
theorem adj_of_indep_tight_gen (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v) {T : Finset (Fin n)}
    (hTu : ∀ i ∈ T, ⟪a i, u⟫ = b i) (hTv : ∀ i ∈ T, ⟪a i, v⟫ = b i)
    (hT : T.card = d - 1) (hind : LinearIndependent ℝ (fun i : T => a i.1)) (hd : 1 ≤ d) :
    Adj (Hpoly a b) u v := by
  classical
  have happ : ∀ x : EuclideanSpace ℝ (Fin d),
      (-∑ i ∈ T, (innerSL ℝ (a i)).toLinearMap) x = -∑ i ∈ T, ⟪a i, x⟫ := by
    intro x; simp [LinearMap.sum_apply]
  have hsets : {x | x ∈ Hpoly a b ∧ (-∑ i ∈ T, (innerSL ℝ (a i)).toLinearMap) x
      = -∑ i ∈ T, b i} = {x | x ∈ Hpoly a b ∧ ∀ i ∈ T, ⟪a i, x⟫ = b i} := by
    ext x
    constructor
    · rintro ⟨hxP, hxt⟩
      refine ⟨hxP, ?_⟩
      rw [happ] at hxt
      intro i hi
      have hsum : ∑ j ∈ T, (b j - ⟪a j, x⟫) = 0 := by rw [Finset.sum_sub_distrib]; linarith
      have hnn : ∀ j ∈ T, 0 ≤ b j - ⟪a j, x⟫ := fun j _ => by linarith [hxP j]
      linarith [(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i hi]
    · rintro ⟨hxP, hxT⟩
      refine ⟨hxP, ?_⟩
      rw [happ]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun i hi => hxT i hi)
  refine ⟨huv, ?_⟩
  rw [← face_eq_segment a b hu hv huv hTu hTv hT hind hd, ← hsets]
  refine HirschFace.exposed_isExtreme (Hpoly a b) _ (-∑ i ∈ T, b i) ?_
  intro x hx
  rw [happ, neg_le_neg_iff]
  exact Finset.sum_le_sum fun i _ => hx i

end HirschSimple

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschBridge

namespace HirschCount

variable {n : ℕ}

/-- The functional `⟪a, ·⟫`. -/
noncomputable def innerFun (v : E2) : E2 →ₗ[ℝ] ℝ := (innerSL ℝ v).toLinearMap

theorem innerFun_apply (v x : E2) : innerFun v x = ⟪v, x⟫ := rfl

theorem innerFun_ne_zero {v : E2} (hv : v ≠ 0) : innerFun v ≠ 0 := by
  intro h
  have h1 : innerFun v v = 0 := by rw [h]; rfl
  rw [innerFun_apply, real_inner_self_eq_norm_sq] at h1
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact hv (norm_eq_zero.mp this)

end HirschCount

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschFace HirschBridge HirschSimple LinearOptimization

namespace HirschShare

variable {d n : ℕ}

/-- A vertex touches at least `d` inequalities. -/
theorem d_le_card_tightSet (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) :
    d ≤ (tightSet a b u).card := by
  classical
  obtain ⟨s, hscard, hstight, -⟩ := exists_active_basis_indep a b hu
  have hsub : s ⊆ tightSet a b u := fun i hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hstight i hi⟩
  calc d = s.card := hscard.symm
    _ ≤ (tightSet a b u).card := Finset.card_le_card hsub

end HirschShare

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschFace HirschBridge HirschSimple HirschCount
open HirschShare LinearOptimization

namespace HirschPlaneB

variable {n : ℕ}

/-- Two distinct vertices of a plane polyhedron that share a tight inequality with nonzero
normal are adjacent. -/
theorem adj_of_shared_row (a : Fin n → E2) (b : Fin n → ℝ) {u v : E2}
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v) {r : Fin n} (har : a r ≠ 0) (hru : ⟪a r, u⟫ = b r) (hrv : ⟪a r, v⟫ = b r) :
    Adj (Hpoly a b) u v := by
  classical
  refine adj_of_indep_tight_gen a b hu hv huv (T := ({r} : Finset (Fin n))) ?_ ?_ ?_ ?_ ?_
  · intro i hi; rw [Finset.mem_singleton.mp hi]; exact hru
  · intro i hi; rw [Finset.mem_singleton.mp hi]; exact hrv
  · simp
  · haveI : Unique ({r} : Finset (Fin n)) :=
      ⟨⟨⟨r, Finset.mem_singleton_self r⟩⟩, fun x => Subtype.ext (Finset.mem_singleton.mp x.2)⟩
    rw [linearIndependent_unique_iff]
    have hdef : ((default : ({r} : Finset (Fin n))) : Fin n) = r :=
      Finset.mem_singleton.mp (default : ({r} : Finset (Fin n))).2
    rw [hdef]
    exact har
  · norm_num

/-- Adjacent vertices share a tight inequality, unless the polyhedron is that very edge. -/
theorem exists_shared_of_adj (a : Fin n → E2) (b : Fin n → ℝ) {u v : E2}
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hadj : Adj (Hpoly a b) u v) :
    (∃ r : Fin n, ⟪a r, u⟫ = b r ∧ ⟪a r, v⟫ = b r) ∨ Hpoly a b = segment ℝ u v := by
  classical
  by_cases hex : ∃ r : Fin n, ⟪a r, u⟫ = b r ∧ ⟪a r, v⟫ = b r
  · exact Or.inl hex
  right
  push_neg at hex
  refine Set.Subset.antisymm ?_ ((hpoly_convex a b).segment_subset hu.1 hv.1)
  intro z hz
  refine mem_face_of_tightSet_subset a b hadj.2 (m := (1/2 : ℝ) • u + (1/2 : ℝ) • v) ?_ ?_ hz ?_
  · exact ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩
  · exact (hpoly_convex a b) hu.1 hv.1 (by norm_num) (by norm_num) (by norm_num)
  · intro i hi
    exfalso
    have hm : ⟪a i, (1/2 : ℝ) • u + (1/2 : ℝ) • v⟫ = b i := (Finset.mem_filter.mp hi).2
    have hexp : ⟪a i, (1/2 : ℝ) • u + (1/2 : ℝ) • v⟫
        = (1/2 : ℝ) * ⟪a i, u⟫ + (1/2 : ℝ) * ⟪a i, v⟫ := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h1 : ⟪a i, u⟫ ≤ b i := hu.1 i
    have h2 : ⟪a i, v⟫ ≤ b i := hv.1 i
    rw [hexp] at hm
    exact hex i (by linarith) (by linarith)

set_option maxHeartbeats 4000000 in
/-- **`Δ(2,n) ≤ n-2` for every plane H-polyhedron**, bounded or not. -/
theorem plane_bound (a : Fin n → E2) (b : Fin n → ℝ) (hane : ∀ i, a i ≠ 0) :
    DiamLE (Hpoly a b) (n - 2) := by
  classical
  refine diamLE_of_reach _ _ (fun u hu v hv => ?_)
  have hex : ∃ L, Reach (Hpoly a b) L u v := Hirsch.graph_connected_general 2 n a b u v hu hv
  have hfind : Reach (Hpoly a b) (Nat.find hex) u v := Nat.find_spec hex
  have hmin : ∀ L, L < Nat.find hex → ¬ Reach (Hpoly a b) L u v := fun L hL =>
    Nat.find_min hex hL
  set L₀ := Nat.find hex with hL₀
  obtain ⟨w, h0, hLw, hstep⟩ := hfind
  refine ⟨L₀, ?_, ⟨w, h0, hLw, hstep⟩⟩
  have hmem : ∀ i, i ≤ L₀ → w i ∈ Set.extremePoints ℝ (Hpoly a b) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact hu
    | succ m ih =>
        intro hm
        rcases hstep m (by omega) with he | hadj
        · rw [← he]; exact ih (by omega)
        · exact adj_right_mem_extremePoints hadj
  have hinj : ∀ i, i ≤ L₀ → ∀ j, j ≤ L₀ → w i = w j → i = j := by
    intro i hi j hj hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hmin _ (by omega) (reach_of_repeat _ L₀ u v w h0 hLw hstep hlt hj hij)
    · exact hmin _ (by omega) (reach_of_repeat _ L₀ u v w h0 hLw hstep hlt hi hij.symm)
  have hedge : ∀ j, j < L₀ → Adj (Hpoly a b) (w j) (w (j + 1)) := by
    intro j hj
    rcases hstep j hj with he | hadj
    · exact absurd (hinj j (by omega) (j + 1) (by omega) he) (by omega)
    · exact hadj
  have hcu : 2 ≤ (tightSet a b u).card := d_le_card_tightSet a b hu
  have hcv : 2 ≤ (tightSet a b v).card := d_le_card_tightSet a b hv
  have hnpos : 0 < n := by
    have h := Finset.card_le_univ (tightSet a b u)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  have hsubeq : ∀ x y : E2, x ∈ Set.extremePoints ℝ (Hpoly a b) →
      y ∈ Set.extremePoints ℝ (Hpoly a b) → tightSet a b x ⊆ tightSet a b y → x = y := by
    intro x y hx hy hsub
    obtain ⟨s, hscard, hstight, hsind⟩ := exists_active_basis_indep a b hx
    have hspan : Submodule.span ℝ (Set.range (fun i : s => a i.1)) = ⊤ := by
      have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : s => a i.1))) = 2 := by
        rw [finrank_span_eq_card hsind]; simp [hscard]
      exact Submodule.eq_top_of_finrank_eq (by rw [hfr]; simp)
    have hdiff : ∀ i ∈ s, ⟪a i, x - y⟫ = 0 := by
      intro i hi
      have h1 : ⟪a i, x⟫ = b i := hstight i hi
      have h2 : ⟪a i, y⟫ = b i :=
        (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩))).2
      rw [inner_sub_right, h1, h2, sub_self]
    have hzero : ∀ z : E2, ⟪z, x - y⟫ = 0 := by
      intro z
      have hz : z ∈ Submodule.span ℝ (Set.range (fun i : s => a i.1)) := by rw [hspan]; trivial
      induction hz using Submodule.span_induction with
      | mem q hq => obtain ⟨i, rfl⟩ := hq; exact hdiff i.1 i.2
      | zero => simp
      | add p q _ _ hp hq => rw [inner_add_left, hp, hq]; ring
      | smul c p _ hp => rw [real_inner_smul_left, hp]; ring
    have hz0 := hzero (x - y)
    rw [real_inner_self_eq_norm_sq] at hz0
    have hnrm : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnrm)
  rcases Nat.lt_or_ge L₀ 2 with hsmall | hL2
  · -- a walk of length at most one
    rcases Nat.lt_or_ge L₀ 1 with h0' | h1'
    · omega
    have huv : u ≠ v := by
      intro h
      exact hmin 0 (by omega) ⟨fun _ => u, rfl, h.symm ▸ rfl, fun i hi => absurd hi (by omega)⟩
    have hn3 : 3 ≤ n := by
      have hnotsub : ¬ tightSet a b u ⊆ tightSet a b v := fun h => huv (hsubeq u v hu hv h)
      obtain ⟨r, hru, hrv⟩ := Finset.not_subset.mp hnotsub
      have hins : (insert r (tightSet a b v)).card ≤ n := by
        have h := Finset.card_le_univ (insert r (tightSet a b v))
        simpa using h
      rw [Finset.card_insert_of_notMem hrv] at hins
      omega
    omega
  -- the long case: count the inequalities used
  have hdisj : ∀ i : Fin n, ⟪a i, u⟫ = b i → ⟪a i, v⟫ = b i → False := by
    intro i h1 h2
    have huv : u ≠ v := by
      intro h
      exact hmin 0 (by omega) ⟨fun _ => u, rfl, h.symm ▸ rfl, fun i hi => absurd hi (by omega)⟩
    have := adj_of_shared_row a b hu hv huv (hane i) h1 h2
    exact hmin 1 (by omega) (reach_one_of_adj _ this)
  have hT : ∀ j, j < L₀ → ∃ r : Fin n, ⟪a r, w j⟫ = b r ∧ ⟪a r, w (j + 1)⟫ = b r := by
    intro j hj
    rcases exists_shared_of_adj a b (hmem j (by omega)) (hmem (j + 1) (by omega))
      (hedge j hj) with h | hseg
    · exact h
    · exfalso
      have hsub : Set.extremePoints ℝ (Hpoly a b) ⊆ ({w j, w (j + 1)} : Set E2) := by
        rw [hseg]; exact extremePoints_segment_subset
      have h0m := hsub (hmem 0 (by omega))
      have h1m := hsub (hmem 1 (by omega))
      have h2m := hsub (hmem 2 (by omega))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0m h1m h2m
      have e01 : (0:ℕ) ≠ 1 := by omega
      have e02 : (0:ℕ) ≠ 2 := by omega
      have e12 : (1:ℕ) ≠ 2 := by omega
      rcases h0m with p0 | p0 <;> rcases h1m with p1 | p1 <;> rcases h2m with p2 | p2 <;>
        first
          | exact e01 (hinj 0 (by omega) 1 (by omega) (p0.trans p1.symm))
          | exact e02 (hinj 0 (by omega) 2 (by omega) (p0.trans p2.symm))
          | exact e12 (hinj 1 (by omega) 2 (by omega) (p1.trans p2.symm))
  have hTall : ∀ j : ℕ, ∃ r : Fin n,
      j < L₀ → ⟪a r, w j⟫ = b r ∧ ⟪a r, w (j + 1)⟫ = b r := by
    intro j
    by_cases hj : j < L₀
    · obtain ⟨r, h1, h2⟩ := hT j hj; exact ⟨r, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨⟨0, hnpos⟩, fun h => absurd h hj⟩
  choose ii hii using hTall
  have hlevel : ∀ (r : Fin n) (p q s : ℕ), p ≤ L₀ → q ≤ L₀ → s ≤ L₀ →
      p ≠ q → p ≠ s → q ≠ s → ⟪a r, w p⟫ = b r → ⟪a r, w q⟫ = b r →
      ⟪a r, w s⟫ = b r → False := by
    intro r p q s hp hq hs hpq hps hqs e1 e2 e3
    have hrk : Module.finrank ℝ E2 ≤ 2 := by simp
    exact card_le_two_on_level hrk (Hpoly a b) (innerFun (a r)) (innerFun_ne_zero (hane r))
      (b r) (hmem p hp) (hmem q hq) (hmem s hs) e1 e2 e3
      (fun h => hpq (hinj p hp q hq h)) (fun h => hps (hinj p hp s hs h))
      (fun h => hqs (hinj q hq s hs h))
  have hiinj : ∀ j, j < L₀ → ∀ k, k < L₀ → ii j = ii k → j = k := by
    have key : ∀ j, j < L₀ → ∀ k, k < L₀ → j < k → ii j = ii k → False := by
      intro j hj k hk hjk heq
      obtain ⟨e1, e2⟩ := hii j hj
      obtain ⟨-, e4⟩ := hii k hk
      rw [← heq] at e4
      exact hlevel (ii j) j (j + 1) (k + 1) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) e1 e2 e4
    intro j hj k hk heq
    rcases lt_trichotomy j k with h | h | h
    · exact absurd (key j hj k hk h heq) (by simp)
    · exact h
    · exact absurd (key k hk j hj h heq.symm) (by simp)
  -- an extra inequality at each end
  have hi0u : ii 0 ∈ tightSet a b u := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← h0]; exact (hii 0 (by omega)).1
  have hiLv : ii (L₀ - 1) ∈ tightSet a b v := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have := (hii (L₀ - 1) (by omega)).2
    rw [show L₀ - 1 + 1 = L₀ by omega, hLw] at this
    exact this
  obtain ⟨r, hr⟩ : ∃ r ∈ tightSet a b u, r ≠ ii 0 := by
    by_contra hc
    push_neg at hc
    have : tightSet a b u ⊆ {ii 0} := fun z hz => Finset.mem_singleton.mpr (hc z hz)
    have := Finset.card_le_card this
    simp at this
    omega
  obtain ⟨r', hr'⟩ : ∃ r' ∈ tightSet a b v, r' ≠ ii (L₀ - 1) := by
    by_contra hc
    push_neg at hc
    have : tightSet a b v ⊆ {ii (L₀ - 1)} := fun z hz => Finset.mem_singleton.mpr (hc z hz)
    have := Finset.card_le_card this
    simp at this
    omega
  obtain ⟨hru, hrne⟩ := hr
  obtain ⟨hrv, hr'ne⟩ := hr'
  have hrtu : ⟪a r, u⟫ = b r := (Finset.mem_filter.mp hru).2
  have hrtv : ⟪a r', v⟫ = b r' := (Finset.mem_filter.mp hrv).2
  have hrr' : r ≠ r' := by
    intro h
    exact hdisj r hrtu (h ▸ hrtv)
  have hrnot : ∀ k, k < L₀ → ii k ≠ r := by
    intro k hk heq
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact hrne heq.symm
    obtain ⟨e1, e2⟩ := hii k hk
    rw [heq] at e1 e2
    exact hlevel r 0 k (k + 1) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [h0]; exact hrtu) e1 e2
  have hr'not : ∀ k, k < L₀ → ii k ≠ r' := by
    intro k hk heq
    rcases Nat.lt_or_ge k (L₀ - 1) with hklt | hkge
    · obtain ⟨e1, e2⟩ := hii k hk
      rw [heq] at e1 e2
      exact hlevel r' L₀ k (k + 1) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by rw [hLw]; exact hrtv) e1 e2
    · have : k = L₀ - 1 := by omega
      rw [this] at heq
      exact hr'ne heq.symm
  -- assemble the count
  set S : Finset (Fin n) := insert r (insert r' ((Finset.range L₀).image ii)) with hS
  have himgcard : ((Finset.range L₀).image ii).card = L₀ := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy hxy
    exact hiinj x (Finset.mem_range.mp hx) y (Finset.mem_range.mp hy) hxy
  have hr'notin : r' ∉ ((Finset.range L₀).image ii) := by
    intro h
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp h
    exact hr'not k (Finset.mem_range.mp hk) hke
  have hrnotin : r ∉ insert r' ((Finset.range L₀).image ii) := by
    intro h
    rcases Finset.mem_insert.mp h with h1 | h1
    · exact hrr' h1
    · obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp h1
      exact hrnot k (Finset.mem_range.mp hk) hke
  have hScard : S.card = L₀ + 2 := by
    rw [hS, Finset.card_insert_of_notMem hrnotin,
      Finset.card_insert_of_notMem hr'notin, himgcard]
  have : S.card ≤ n := by simpa using Finset.card_le_univ S
  omega

end HirschPlaneB

open HirschPlaneB

/-- **`Δ(2,n) ≤ n-2` for every plane H-polyhedron**, bounded or not. -/
theorem solution (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 2)) (b : Fin n → ℝ)
    (hane : ∀ i, a i ≠ 0) : DiamLE (Hpoly a b) (n - 2) :=
  HirschPlaneB.plane_bound a b hane
