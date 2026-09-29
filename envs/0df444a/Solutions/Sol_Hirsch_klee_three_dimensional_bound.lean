-- Prove2me | solution 1 for Hirsch.klee_three_dimensional_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T13:19:13.85371+00:00
-- url     : https://prove2.me/submissions/2330d861-fc19-43ff-b9c5-a9999c95342e

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_ActiveConstraints
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_lp_basic_solutions_finite
import Theorems.Thm_Hirsch_plane_bound_general
import Theorems.Thm_Hirsch_facet_reduction

open scoped RealInnerProductSpace
open Hirsch LinearOptimization

open scoped RealInnerProductSpace
namespace HirschLib
theorem diamLE_of_subsingleton {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (B : ℕ)
    (h : ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P, u = v) :
    DiamLE P B := by
  intro u hu v hv
  exact ⟨fun _ => u, rfl, h u hu v hv, fun i _ => Or.inl rfl⟩

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

abbrev E2 := EuclideanSpace ℝ (Fin 2)

end HirschLib
namespace HirschWalk
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
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

theorem diamLE_of_reach (P : Set E) (B : ℕ)
    (h : ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P,
      ∃ L ≤ B, Reach P L u v) : DiamLE P B := by
  intro u hu v hv
  obtain ⟨L, hLB, hL⟩ := h u hu v hv
  exact reach_mono P hLB hL

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
open HirschLib
namespace HirschFace
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def IsFaceSet (V S : Finset E) : Prop :=
  S ⊆ V ∧ ∃ (f : E →ₗ[ℝ] ℝ) (t : ℝ), (∀ z ∈ V, t ≤ f z) ∧ (∀ z ∈ V, z ∈ S ↔ f z = t)

theorem IsFaceSet.subset {V S : Finset E} (h : IsFaceSet V S) : S ⊆ V := h.1

theorem isFaceSet_self (V : Finset E) : IsFaceSet V V :=
  ⟨Finset.Subset.refl V, 0, 0, fun z _ => le_refl 0, fun z hz => ⟨fun _ => rfl, fun _ => hz⟩⟩

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

section Euclid
open scoped RealInnerProductSpace
variable {d : ℕ}
local notation "Ed" => EuclideanSpace ℝ (Fin d)
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
open LinearOptimization
namespace HirschBridge
variable {d n : ℕ}
def constrOf (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Fin n → LinearConstraint d :=
  fun i => ⟨fun j => a i j, b i, .le⟩

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
open HirschLib HirschWalk HirschBridge HirschFace
namespace HirschNaddef
variable {d : ℕ}
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

theorem reach_of_improving (V : Finset (EuclideanSpace ℝ (Fin d)))
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (hP : P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ P)
    (hvert : ∀ z ∈ V, ∃ g : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ, ∀ y ∈ V, y ≠ z → g z < g y)
    (c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ V)
    (hcv : ∀ y ∈ V, y ≠ v → c v < c y) : ∀ u ∈ V, ∃ L, Reach P L u v := by
  classical
  have key : ∀ (m : ℕ) (u : EuclideanSpace ℝ (Fin d)), u ∈ V →
      (V.filter (fun z => c z < c u)).card = m → ∃ L, Reach P L u v := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro u huV hcard
      by_cases huv : u = v
      · exact ⟨0, huv ▸ reach_zero P u⟩
      · obtain ⟨w, hwV, hwc, hadj⟩ :=
          improving_edge V P hP hVext hvert u huV c ⟨v, hv, hcv u huV huv⟩
        have hsub : V.filter (fun z => c z < c w) ⊆ V.filter (fun z => c z < c u) := by
          intro z hz
          obtain ⟨hzV, hzc⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hzV, lt_trans hzc hwc⟩
        have hss : V.filter (fun z => c z < c w) ⊂ V.filter (fun z => c z < c u) := by
          refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨w, Finset.mem_filter.mpr ⟨hwV, hwc⟩, ?_⟩
          intro hcon
          exact absurd (Finset.mem_filter.mp hcon).2 (lt_irrefl _)
        obtain ⟨L, hL⟩ := ih _ (hcard ▸ Finset.card_lt_card hss) w hwV rfl
        exact ⟨1 + L, reach_trans P (reach_one_of_adj P hadj) hL⟩
  intro u huV
  exact key _ u huV rfl

theorem graph_connected (V : Finset (EuclideanSpace ℝ (Fin d)))
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (hP : P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ P)
    (hvert : ∀ z ∈ V, ∃ g : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ, ∀ y ∈ V, y ≠ z → g z < g y) :
    ∀ u ∈ V, ∀ v ∈ V, ∃ L, Reach P L u v := by
  intro u huV v hvV
  obtain ⟨c, hc⟩ := hvert v hvV
  exact reach_of_improving V P hP hVext hvert c v hvV hc u huV

end HirschNaddef
open scoped RealInnerProductSpace
open HirschLib HirschWalk HirschFace HirschNaddef
namespace HirschDescent
variable {d : ℕ}
def ReachC (P : Set (EuclideanSpace ℝ (Fin d))) (V : Finset (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (t : ℝ) (L : ℕ)
    (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w L = v ∧
    (∀ i ≤ L, w i ∈ V ∧ c (w i) ≤ t) ∧
    ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1))

theorem reachC_zero (P : Set (EuclideanSpace ℝ (Fin d))) (V : Finset _)
    (c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (t : ℝ) {u : EuclideanSpace ℝ (Fin d)}
    (huV : u ∈ V) (hu : c u ≤ t) : ReachC P V c t 0 u u :=
  ⟨fun _ => u, rfl, rfl, fun _ _ => ⟨huV, hu⟩, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

theorem reachC_cons (P : Set (EuclideanSpace ℝ (Fin d))) (V : Finset _)
    (c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (t : ℝ) {L : ℕ}
    {u x v : EuclideanSpace ℝ (Fin d)} (huV : u ∈ V) (hu : c u ≤ t)
    (hadj : Adj P u x) (h : ReachC P V c t L x v) : ReachC P V c t (L + 1) u v := by
  classical
  obtain ⟨w, h0, hL, hmem, hstep⟩ := h
  refine ⟨fun i => if i = 0 then u else w (i - 1), by simp, ?_, ?_, ?_⟩
  · simp only [Nat.add_eq_zero, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
    exact hL
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa using ⟨huV, hu⟩
    · have hne : i ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      simp only [hne, if_false]
      exact hmem (i - 1) (by omega)
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · refine Or.inr ?_
      simp only [if_pos rfl, Nat.zero_add, one_ne_zero, if_false, Nat.sub_self]
      rw [h0]
      exact hadj
    · have hne : i ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
      have hne1 : i + 1 ≠ 0 := Nat.succ_ne_zero i
      simp only [hne, hne1, if_false]
      have hidx : i + 1 - 1 = (i - 1) + 1 := by omega
      rw [hidx]
      exact hstep (i - 1) (by omega)

theorem reachC_of_improving (V : Finset (EuclideanSpace ℝ (Fin d)))
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (hP : P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ P)
    (hvert : ∀ z ∈ V, ∃ g : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ, ∀ y ∈ V, y ≠ z → g z < g y)
    (c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ V)
    (hcv : ∀ y ∈ V, y ≠ v → c v < c y) :
    ∀ u ∈ V, ∃ L, ReachC P V c (c u) L u v := by
  classical
  have key : ∀ (m : ℕ) (u : EuclideanSpace ℝ (Fin d)), u ∈ V →
      (V.filter (fun z => c z < c u)).card = m →
      ∀ t : ℝ, c u ≤ t → ∃ L, ReachC P V c t L u v := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro u huV hcard t hut
      by_cases huv : u = v
      · subst huv
        exact ⟨0, reachC_zero P V c t huV hut⟩
      · obtain ⟨w, hwV, hwc, hadj⟩ :=
          improving_edge V P hP hVext hvert u huV c ⟨v, hv, hcv u huV huv⟩
        have hsub : V.filter (fun z => c z < c w) ⊆ V.filter (fun z => c z < c u) := by
          intro z hz
          obtain ⟨hzV, hzc⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hzV, lt_trans hzc hwc⟩
        have hss : V.filter (fun z => c z < c w) ⊂ V.filter (fun z => c z < c u) := by
          refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨w, Finset.mem_filter.mpr ⟨hwV, hwc⟩, ?_⟩
          intro hcon
          exact absurd (Finset.mem_filter.mp hcon).2 (lt_irrefl _)
        obtain ⟨L, hL⟩ :=
          ih _ (hcard ▸ Finset.card_lt_card hss) w hwV rfl t (le_trans (le_of_lt hwc) hut)
        exact ⟨L + 1, reachC_cons P V c t huV hut hadj hL⟩
  intro u huV
  exact key _ u huV rfl (c u) le_rfl

end HirschDescent
open scoped RealInnerProductSpace
open HirschLib HirschWalk HirschFace
namespace HirschFacet
variable {d n m : ℕ}
variable (ψ : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
variable {ψ}
variable (ψ)
variable {ψ}
theorem hpoly_drop {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin m)) (b : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (ha : a i = 0) (hb : 0 ≤ b i) :
    Hpoly a b = Hpoly (fun j => a (i.succAbove j)) (fun j => b (i.succAbove j)) := by
  ext y
  constructor
  · intro h j; exact h _
  · intro h j
    rcases eq_or_ne j i with rfl | hj
    · rw [ha]; simpa using hb
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
      exact h j'

end HirschFacet
open scoped RealInnerProductSpace
open HirschLib HirschWalk HirschFace HirschFacet
namespace HirschLayer
variable {d n : ℕ}
open scoped Classical in
theorem adj_symm {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E} {x y : E}
    (h : Adj P x y) : Adj P y x := by
  refine ⟨h.1.symm, ?_⟩
  rw [segment_symm]
  exact h.2

end HirschLayer
open scoped RealInnerProductSpace
open HirschLib HirschWalk HirschFace HirschBridge LinearOptimization
namespace HirschRelax
variable {d n : ℕ}
theorem isExtreme_inter {E : Type*} [AddCommGroup E] [Module ℝ E] {Q T S : Set E}
    (h : IsExtreme ℝ Q T) (hSQ : S ⊆ Q) : IsExtreme ℝ S (S ∩ T) := by
  constructor
  · exact Set.inter_subset_left
  · intro x1 h1 x2 h2 z hz hsg
    exact ⟨h1, h.2 (hSQ h1) (hSQ h2) hz.2 hsg⟩

end HirschRelax
open scoped RealInnerProductSpace
open HirschLib HirschWalk
namespace HirschReindex
variable {d n : ℕ}
theorem hpoly_eq_empty (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n)
    (hai : a i = 0) (hbi : b i < 0) : Hpoly a b = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have := hx i
  rw [hai, inner_zero_left] at this
  linarith

theorem diamLE_empty {E : Type*} [AddCommGroup E] [Module ℝ E] (B : ℕ) :
    DiamLE (∅ : Set E) B := by
  intro u hu
  exact absurd hu.1 (by simp)

end HirschReindex
open scoped RealInnerProductSpace
open HirschLib HirschWalk HirschFace HirschBridge HirschFacet
open HirschLayer HirschRelax HirschReindex LinearOptimization
namespace HirschKKb
theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {B B' : ℕ}
    (hB : B ≤ B') (h : DiamLE P B) : DiamLE P B' :=
  diamLE_of_reach P B' (fun u hu v hv => ⟨B, hB, h u hu v hv⟩)

end HirschKKb
open HirschLib HirschWalk
namespace HirschPlane
theorem reach_of_improving (V : Finset E2) (P : Set E2)
    (himp : ∀ u ∈ V, ∀ c : E2 →ₗ[ℝ] ℝ, (∃ z ∈ V, c z < c u) →
      ∃ w ∈ V, c w < c u ∧ Adj P u w)
    (c : E2 →ₗ[ℝ] ℝ) (v : E2) (hv : v ∈ V) (hcv : ∀ y ∈ V, y ≠ v → c v < c y) :
    ∀ u ∈ V, ∃ L, Reach P L u v := by
  classical
  have key : ∀ (m : ℕ) (u : E2), u ∈ V →
      (V.filter (fun z => c z < c u)).card = m → ∃ L, Reach P L u v := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro u huV hcard
      by_cases huv : u = v
      · exact ⟨0, huv ▸ reach_zero P u⟩
      · obtain ⟨w, hwV, hwc, hadj⟩ := himp u huV c ⟨v, hv, hcv u huV huv⟩
        have hsub : V.filter (fun z => c z < c w) ⊆ V.filter (fun z => c z < c u) := by
          intro z hz
          obtain ⟨hzV, hzc⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hzV, lt_trans hzc hwc⟩
        have hss : V.filter (fun z => c z < c w) ⊂ V.filter (fun z => c z < c u) := by
          refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨w, ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨hwV, hwc⟩
          · intro hcon
            exact absurd (Finset.mem_filter.mp hcon).2 (lt_irrefl _)
        have hlt : (V.filter (fun z => c z < c w)).card < m :=
          hcard ▸ Finset.card_lt_card hss
        obtain ⟨L, hL⟩ := ih _ hlt w hwV rfl
        exact ⟨1 + L, reach_trans P (reach_one_of_adj P hadj) hL⟩
  intro u huV
  exact key _ u huV rfl

end HirschPlane
open scoped RealInnerProductSpace
open HirschLib HirschWalk HirschBridge HirschPlane
namespace HirschDim2
theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {B B' : ℕ}
    (hB : B ≤ B') (h : DiamLE P B) : DiamLE P B' := by
  refine diamLE_of_reach P B' (fun u hu v hv => ?_)
  exact ⟨B, hB, h u hu v hv⟩

end HirschDim2
open scoped RealInnerProductSpace
open HirschLib HirschWalk HirschFace HirschBridge HirschNaddef HirschDescent
open HirschLayer HirschFacet
open LinearOptimization
namespace HirschKlee
variable {d n : ℕ}
noncomputable def Vst (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  (extremePoints_finite a b).toFinset

theorem mem_Vst {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin d)} : x ∈ Vst a b ↔ x ∈ Set.extremePoints ℝ (Hpoly a b) :=
  Set.Finite.mem_toFinset _

theorem coe_Vst (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    ((Vst a b : Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.extremePoints ℝ (Hpoly a b) := by
  ext x; simp [Vst]

theorem hull_Vst (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    Hpoly a b = convexHull ℝ ((Vst a b : Finset (EuclideanSpace ℝ (Fin d))) :
      Set (EuclideanSpace ℝ (Fin d))) := by
  rw [coe_Vst]; exact hpoly_eq_convexHull a b hbd

theorem Vst_ext (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    ∀ z ∈ Vst a b, z ∈ Set.extremePoints ℝ (Hpoly a b) := fun _ hz => mem_Vst.mp hz

theorem Vst_vert (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    ∀ z ∈ Vst a b, ∃ g : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ,
      ∀ y ∈ Vst a b, y ≠ z → g z < g y := by
  intro z hz
  obtain ⟨g, hg⟩ := exists_strict_functional a b (mem_Vst.mp hz)
  exact ⟨g, fun y hy hyz => hg y (mem_Vst.mp hy).1 hyz⟩

theorem reachC_symm (P : Set (EuclideanSpace ℝ (Fin d))) (V : Finset _)
    (c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (t : ℝ) {L : ℕ}
    {u v : EuclideanSpace ℝ (Fin d)} (h : ReachC P V c t L u v) : ReachC P V c t L v u := by
  obtain ⟨w, h0, hL, hmem, hstep⟩ := h
  refine ⟨fun i => w (L - i), by simp [hL], by simp [h0], ?_, ?_⟩
  · intro i hi; exact hmem (L - i) (by omega)
  · intro i hi
    have hidx : L - i = (L - (i + 1)) + 1 := by omega
    show w (L - i) = w (L - (i + 1)) ∨ Adj P (w (L - i)) (w (L - (i + 1)))
    rw [hidx]
    rcases hstep (L - (i + 1)) (by omega) with h | h
    · exact Or.inl h.symm
    · exact Or.inr (adj_symm h)

theorem reachC_trans (P : Set (EuclideanSpace ℝ (Fin d))) (V : Finset _)
    (c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (t : ℝ) {L₁ L₂ : ℕ}
    {u x v : EuclideanSpace ℝ (Fin d)} (h₁ : ReachC P V c t L₁ u x)
    (h₂ : ReachC P V c t L₂ x v) : ReachC P V c t (L₁ + L₂) u v := by
  classical
  obtain ⟨w₁, h10, h1L, h1mem, h1step⟩ := h₁
  obtain ⟨w₂, h20, h2L, h2mem, h2step⟩ := h₂
  set w : ℕ → EuclideanSpace ℝ (Fin d) := fun i => if i ≤ L₁ then w₁ i else w₂ (i - L₁) with hw
  have hwlo : ∀ i, i ≤ L₁ → w i = w₁ i := by intro i hi; simp [hw, hi]
  have hwhi : ∀ i, ¬ i ≤ L₁ → w i = w₂ (i - L₁) := by intro i hi; simp [hw, hi]
  refine ⟨w, by rw [hwlo 0 (Nat.zero_le _), h10], ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos L₂ with rfl | hpos
    · rw [Nat.add_zero, hwlo L₁ le_rfl, h1L, ← h2L, h20]
    · rw [hwhi (L₁ + L₂) (by omega), Nat.add_sub_cancel_left]; exact h2L
  · intro i hi
    by_cases hle : i ≤ L₁
    · rw [hwlo i hle]; exact h1mem i hle
    · rw [hwhi i hle]; exact h2mem (i - L₁) (by omega)
  · intro i hi
    by_cases hle : i + 1 ≤ L₁
    · rw [hwlo i (by omega), hwlo (i + 1) hle]; exact h1step i (by omega)
    · by_cases hle' : i ≤ L₁
      · have hEq : i = L₁ := by omega
        rw [hwlo i (by omega), hwhi (i + 1) (by omega)]
        have h1 : i + 1 - L₁ = 1 := by omega
        rw [h1, hEq, h1L, ← h20]
        exact h2step 0 (by omega)
      · rw [hwhi i hle', hwhi (i + 1) (by omega)]
        have hidx : i + 1 - L₁ = (i - L₁) + 1 := by omega
        rw [hidx]
        exact h2step (i - L₁) (by omega)


theorem reachC_mono (P : Set (EuclideanSpace ℝ (Fin d))) (V : Finset _)
    (c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) {t t' : ℝ} (htt : t ≤ t') {L : ℕ}
    {u v : EuclideanSpace ℝ (Fin d)} (h : ReachC P V c t L u v) : ReachC P V c t' L u v := by
  obtain ⟨w, h0, hL, hmem, hstep⟩ := h
  exact ⟨w, h0, hL, fun i hi => ⟨(hmem i hi).1, le_trans (hmem i hi).2 htt⟩, hstep⟩

theorem exists_tiebreak (V : Finset (EuclideanSpace ℝ (Fin d)))
    {x m : EuclideanSpace ℝ (Fin d)} (hm : m ∈ V) (hxm : m ≠ x)
    (g h : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ)
    (hg : ∀ y ∈ V, y ≠ x → g x < g y)
    (hh : ∀ y ∈ V, y ≠ m → h m < h y)
    (hmax : ∀ y ∈ V, g y ≤ g m) :
    ∃ φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ,
      (∀ y ∈ V, y ≠ m → φ m < φ y) ∧ (∀ y ∈ V, y ≠ x → φ y < φ x) := by
  classical
  have hSne : (V.erase x).Nonempty := ⟨m, Finset.mem_erase.mpr ⟨hxm, hm⟩⟩
  obtain ⟨ε, hεpos, hεle⟩ : ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ V, y ≠ x → ε * (|h x - h y| + 1) ≤ g y - g x := by
    refine ⟨(V.erase x).inf' hSne (fun y => (g y - g x) / (|h x - h y| + 1)), ?_, ?_⟩
    · refine (Finset.lt_inf'_iff _).mpr ?_
      intro y hy
      obtain ⟨hyx, hyV⟩ := Finset.mem_erase.mp hy
      exact div_pos (sub_pos.mpr (hg y hyV hyx)) (by positivity)
    · intro y hyV hyx
      have hpos : (0:ℝ) < |h x - h y| + 1 := by positivity
      have hy : y ∈ V.erase x := Finset.mem_erase.mpr ⟨hyx, hyV⟩
      have hle := Finset.inf'_le (fun y => (g y - g x) / (|h x - h y| + 1)) hy
      calc (V.erase x).inf' hSne (fun y => (g y - g x) / (|h x - h y| + 1)) *
              (|h x - h y| + 1)
          ≤ ((g y - g x) / (|h x - h y| + 1)) * (|h x - h y| + 1) :=
            mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
        _ = g y - g x := div_mul_cancel₀ _ (ne_of_gt hpos)
  refine ⟨ε • h - g, ?_, ?_⟩
  · intro y hyV hym
    have h1 : h m < h y := hh y hyV hym
    have h2 : g y ≤ g m := hmax y hyV
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    nlinarith
  · intro y hyV hyx
    have h2 : ε * |h x - h y| + ε ≤ g y - g x := by
      have := hεle y hyV hyx; nlinarith [this]
    have h3 : -|h x - h y| ≤ h x - h y := neg_abs_le _
    have h5 : -(ε * |h x - h y|) ≤ ε * h x - ε * h y := by
      have := mul_le_mul_of_nonneg_left h3 (le_of_lt hεpos)
      nlinarith [this]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    linarith

theorem exists_walk_avoiding (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) {u v x : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Vst a b) (hv : v ∈ Vst a b) (hx : x ∈ Vst a b)
    (hux : u ≠ x) (hvx : v ≠ x) :
    ∃ (L : ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)), w 0 = u ∧ w L = v ∧
      (∀ i ≤ L, w i ∈ Vst a b ∧ w i ≠ x) ∧
      ∀ i < L, w i = w (i + 1) ∨ Adj (Hpoly a b) (w i) (w (i + 1)) := by
  classical
  obtain ⟨g, hg⟩ := exists_strict_functional a b (mem_Vst.mp hx)
  have hg' : ∀ y ∈ Vst a b, y ≠ x → g x < g y := fun y hy hyx => hg y (mem_Vst.mp hy).1 hyx
  have hne : (Vst a b).Nonempty := ⟨u, hu⟩
  obtain ⟨m, hmV, hmmax⟩ := (Vst a b).exists_max_image g hne
  have hmx : m ≠ x := by
    intro hcon
    have := hmmax u hu
    rw [hcon] at this
    exact absurd this (not_le.mpr (hg' u hu hux))
  obtain ⟨hfun, hhh⟩ := Vst_vert a b m hmV
  obtain ⟨φ, hφmin, hφmax⟩ := exists_tiebreak (Vst a b) hmV hmx g hfun hg' hhh hmmax
  have hru := reachC_of_improving (Vst a b) (Hpoly a b) (hull_Vst a b hbd) (Vst_ext a b)
    (Vst_vert a b) φ m hmV hφmin u hu
  have hrv := reachC_of_improving (Vst a b) (Hpoly a b) (hull_Vst a b hbd) (Vst_ext a b)
    (Vst_vert a b) φ m hmV hφmin v hv
  obtain ⟨L₁, h1⟩ := hru
  obtain ⟨L₂, h2⟩ := hrv
  set t : ℝ := max (φ u) (φ v) with ht
  have h1' : ReachC (Hpoly a b) (Vst a b) φ t L₁ u m := reachC_mono _ _ _ (le_max_left _ _) h1
  have h2' : ReachC (Hpoly a b) (Vst a b) φ t L₂ m v :=
    reachC_symm _ _ _ _ (reachC_mono _ _ _ (le_max_right _ _) h2)
  obtain ⟨w, h0, hL, hmem, hstep⟩ := reachC_trans _ _ _ _ h1' h2'
  refine ⟨L₁ + L₂, w, h0, hL, ?_, hstep⟩
  intro i hi
  refine ⟨(hmem i hi).1, ?_⟩
  intro hcon
  have hle : φ (w i) ≤ t := (hmem i hi).2
  rw [hcon] at hle
  have : t < φ x := by
    rw [ht]
    exact max_lt (hφmax u hu hux) (hφmax v hv hvx)
  exact absurd hle (not_le.mpr this)


theorem not_const_of_interior (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hfull : (interior (Hpoly a b)).Nonempty) {c : EuclideanSpace ℝ (Fin d)} (hc : c ≠ 0)
    (t : ℝ) : ¬ (∀ z ∈ Hpoly a b, ⟪c, z⟫ = t) := by
  intro hcon
  obtain ⟨x, hx⟩ := hfull
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hcn : (0:ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  have hcne : ‖c‖ ≠ 0 := ne_of_gt hcn
  have hdist : dist (x + (ε / (2 * ‖c‖)) • c) x < ε := by
    have heq : dist (x + (ε / (2 * ‖c‖)) • c) x = ε / 2 := by
      rw [dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (show (0:ℝ) < ε / (2 * ‖c‖) by positivity)]
      field_simp
    rw [heq]; linarith
  have hyP : x + (ε / (2 * ‖c‖)) • c ∈ Hpoly a b :=
    interior_subset (hball (Metric.mem_ball.mpr hdist))
  have hxP : x ∈ Hpoly a b := interior_subset hx
  have h1 := hcon x hxP
  have h2 := hcon _ hyP
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, h1] at h2
  have hz : ε / (2 * ‖c‖) * ‖c‖ ^ 2 = 0 := by linarith
  have hne : ε / (2 * ‖c‖) * ‖c‖ ^ 2 ≠ 0 := by positivity
  exact hne hz

theorem exists_nbrs (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hfull : (interior (Hpoly a b)).Nonempty)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Vst a b) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin d)), N ⊆ Vst a b ∧ d ≤ N.card ∧
      ∀ w ∈ N, Adj (Hpoly a b) u w := by
  classical
  refine ⟨(Vst a b).filter (fun w => Adj (Hpoly a b) u w), Finset.filter_subset _ _, ?_,
    fun w hw => (Finset.mem_filter.mp hw).2⟩
  by_contra hcard
  push_neg at hcard
  set N := (Vst a b).filter (fun w => Adj (Hpoly a b) u w) with hN
  -- a direction orthogonal to every edge at `u`
  set T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ({ x // x ∈ N } → ℝ) :=
    { toFun := fun z w => ⟪(w : EuclideanSpace ℝ (Fin d)) - u, z⟫
      map_add' := by intro x y; funext w; simp [inner_add_right]
      map_smul' := by intro r x; funext w; simp [real_inner_smul_right] } with hT
  have hcodim : Module.finrank ℝ ({ x // x ∈ N } → ℝ) = N.card := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have hker : 0 < Module.finrank ℝ (LinearMap.ker T) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker T
    have h2 : Module.finrank ℝ (LinearMap.range T) ≤ N.card := by
      rw [← hcodim]; exact Submodule.finrank_le _
    omega
  obtain ⟨c, hcker, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := LinearMap.ker T) (by
      intro hcon
      rw [hcon] at hker
      simp at hker)
  have hcperp : ∀ w ∈ N, ⟪c, w - u⟫ = 0 := by
    intro w hw
    have := LinearMap.mem_ker.mp hcker
    have hval : T c ⟨w, hw⟩ = 0 := by rw [this]; rfl
    rw [real_inner_comm]
    exact hval
  set φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ :=
    { toFun := fun z => ⟪c, z⟫
      map_add' := fun x y => inner_add_right _ _ _
      map_smul' := fun r x => by simpa using real_inner_smul_right c x r } with hφdef
  have hφapp : ∀ z, φ z = ⟪c, z⟫ := fun _ => rfl
  have hφw : ∀ w ∈ N, φ w = φ u := by
    intro w hw
    have := hcperp w hw
    rw [inner_sub_right] at this
    rw [hφapp, hφapp]
    linarith
  have hmin : ∀ z ∈ Vst a b, φ u ≤ φ z := by
    intro z hz
    by_contra hcon
    push_neg at hcon
    obtain ⟨w, hwV, hwc, hadj⟩ := improving_edge (Vst a b) (Hpoly a b) (hull_Vst a b hbd)
      (Vst_ext a b) (Vst_vert a b) u hu φ ⟨z, hz, hcon⟩
    have hwN : w ∈ N := Finset.mem_filter.mpr ⟨hwV, hadj⟩
    rw [hφw w hwN] at hwc
    exact lt_irrefl _ hwc
  have hmax : ∀ z ∈ Vst a b, φ z ≤ φ u := by
    intro z hz
    by_contra hcon
    push_neg at hcon
    obtain ⟨w, hwV, hwc, hadj⟩ := improving_edge (Vst a b) (Hpoly a b) (hull_Vst a b hbd)
      (Vst_ext a b) (Vst_vert a b) u hu (-φ) ⟨z, hz, by simpa using hcon⟩
    have hwN : w ∈ N := Finset.mem_filter.mpr ⟨hwV, hadj⟩
    simp only [LinearMap.neg_apply, neg_lt_neg_iff] at hwc
    rw [hφw w hwN] at hwc
    exact lt_irrefl _ hwc
  have hconvex : Convex ℝ {z : EuclideanSpace ℝ (Fin d) | φ z = φ u} := by
    intro y hy z hz s t hs ht hst
    simp only [Set.mem_setOf_eq] at hy hz ⊢
    rw [map_add, map_smul, map_smul, hy, hz, smul_eq_mul, smul_eq_mul, ← add_mul, hst, one_mul]
  have hconst : ∀ z ∈ Hpoly a b, ⟪c, z⟫ = φ u := by
    have hsub : Hpoly a b ⊆ {z : EuclideanSpace ℝ (Fin d) | φ z = φ u} := by
      rw [hull_Vst a b hbd]
      refine convexHull_min ?_ hconvex
      intro z hz
      rw [coe_Vst] at hz
      exact le_antisymm (hmax z (mem_Vst.mpr hz)) (hmin z (mem_Vst.mpr hz))
    intro z hz
    exact hsub hz
  exact not_const_of_interior a b hfull hc0 (φ u) hconst


noncomputable def gdist (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : ℕ := sInf {M | Reach (Hpoly a b) M u x}

theorem gdist_le {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {u x : EuclideanSpace ℝ (Fin d)} {M : ℕ} (h : Reach (Hpoly a b) M u x) :
    gdist a b u x ≤ M := Nat.sInf_le h

theorem gdist_self (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u : EuclideanSpace ℝ (Fin d)) : gdist a b u u = 0 :=
  Nat.le_zero.mp (gdist_le (reach_zero _ _))

theorem gdist_spec (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) {u x : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Vst a b) (hx : x ∈ Vst a b) : Reach (Hpoly a b) (gdist a b u x) u x :=
  Nat.sInf_mem (graph_connected (Vst a b) (Hpoly a b) (hull_Vst a b hbd) (Vst_ext a b)
    (Vst_vert a b) u hu x hx)

theorem eq_of_gdist_eq_zero {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    (hbd : Bornology.IsBounded (Hpoly a b)) {u x : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Vst a b) (hx : x ∈ Vst a b) (h : gdist a b u x = 0) : x = u := by
  have hr := gdist_spec a b hbd hu hx
  rw [h] at hr
  obtain ⟨w, h0, hL, _⟩ := hr
  rw [← hL, h0]

theorem gdist_succ_le {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    (hbd : Bornology.IsBounded (Hpoly a b)) {u x y : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Vst a b) (hx : x ∈ Vst a b)
    (h : x = y ∨ Adj (Hpoly a b) x y) : gdist a b u y ≤ gdist a b u x + 1 := by
  rcases h with rfl | hadj
  · omega
  · exact gdist_le (reach_trans _ (gdist_spec a b hbd hu hx) (reach_one_of_adj _ hadj))

theorem exists_index_of_le {f : ℕ → ℕ} {M : ℕ} (h0 : f 0 = 0)
    (hstep : ∀ j < M, f (j + 1) ≤ f j + 1) {i : ℕ} (hi : i ≤ f M) :
    ∃ j ≤ M, f j = i := by
  induction M with
  | zero => exact ⟨0, le_rfl, by omega⟩
  | succ M ih =>
      by_cases hle : i ≤ f M
      · obtain ⟨j, hjM, hj⟩ := ih (fun j hj => hstep j (by omega)) hle
        exact ⟨j, by omega, hj⟩
      · push_neg at hle
        have := hstep M (by omega)
        exact ⟨M + 1, le_rfl, by omega⟩





theorem two_mul_gdist_lt_card (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hfull : (interior (Hpoly a b)).Nonempty)
    (hd : 3 ≤ d) {u v : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Vst a b) (hv : v ∈ Vst a b) :
    2 * gdist a b u v + 1 ≤ (Vst a b).card := by
  classical
  obtain ⟨N, hNsub, hNcard, hNadj⟩ := exists_nbrs a b hbd hfull hu
  have h3card : 3 ≤ (Vst a b).card :=
    le_trans (le_trans hd hNcard) (Finset.card_le_card hNsub)
  obtain ⟨L, hL⟩ : ∃ L, gdist a b u v = L := ⟨_, rfl⟩
  rw [hL]
  by_cases hL1 : L ≤ 1
  · omega
  push_neg at hL1
  -- walks stay inside the vertex set
  have hwalk_mem : ∀ (M : ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)), w 0 = u →
      (∀ j < M, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) →
      ∀ j ≤ M, w j ∈ Vst a b := by
    intro M w h0 hstep j
    induction j with
    | zero => intro _; rw [h0]; exact hu
    | succ k ih =>
        intro hk
        have hk' := ih (by omega)
        rcases hstep k (by omega) with h | h
        · rw [← h]; exact hk'
        · exact mem_Vst.mpr (adj_right_mem_extremePoints h)
  -- every walk from `u` to `v` meets every layer
  have hIVT : ∀ (M : ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)), w 0 = u → w M = v →
      (∀ j < M, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) →
      ∀ i ≤ L, ∃ j ≤ M, gdist a b u (w j) = i := by
    intro M w h0 hM hstep i hi
    refine exists_index_of_le (f := fun j => gdist a b u (w j)) ?_ ?_ ?_
    · show gdist a b u (w 0) = 0
      rw [h0]; exact gdist_self a b u
    · intro j hj
      exact gdist_succ_le hbd hu (hwalk_mem M w h0 hstep j (by omega)) (hstep j hj)
    · show i ≤ gdist a b u (w M)
      rw [hM, hL]; exact hi
  set Lay : ℕ → Finset (EuclideanSpace ℝ (Fin d)) :=
    fun i => (Vst a b).filter (fun x => gdist a b u x = i) with hLayDef
  have hmemLay : ∀ i x, x ∈ Lay i ↔ (x ∈ Vst a b ∧ gdist a b u x = i) := by
    intro i x; simp [hLayDef, Finset.mem_filter]
  -- layer 0
  have hLay0 : (Lay 0).card = 1 := by
    have : Lay 0 = {u} := by
      ext x
      rw [hmemLay, Finset.mem_singleton]
      constructor
      · rintro ⟨hxV, hx0⟩; exact eq_of_gdist_eq_zero hbd hu hxV hx0
      · intro hxu; rw [hxu]; exact ⟨hu, gdist_self a b u⟩
    rw [this]; simp
  -- layer 1
  have hLay1 : 3 ≤ (Lay 1).card := by
    refine le_trans (le_trans hd hNcard) (Finset.card_le_card ?_)
    intro w hw
    have hwV : w ∈ Vst a b := hNsub hw
    have hadj := hNadj w hw
    rw [hmemLay]
    refine ⟨hwV, le_antisymm (gdist_le (reach_one_of_adj _ hadj)) ?_⟩
    by_contra hcon
    push_neg at hcon
    have : gdist a b u w = 0 := by omega
    exact hadj.1 (eq_of_gdist_eq_zero hbd hu hwV this).symm
  -- last layer
  have hLayL : 1 ≤ (Lay L).card :=
    Finset.card_pos.mpr ⟨v, (hmemLay L v).mpr ⟨hv, hL⟩⟩
  -- middle layers
  have hLaymid : ∀ i, 1 ≤ i → i < L → 2 ≤ (Lay i).card := by
    intro i hi1 hiL
    by_contra hcon
    push_neg at hcon
    obtain ⟨w, h0, hM, hstep⟩ := gdist_spec a b hbd hu hv
    rw [hL] at hM hstep
    obtain ⟨j, hjL, hj⟩ := hIVT L w h0 hM hstep i (by omega)
    have hxin : w j ∈ Lay i := (hmemLay i _).mpr ⟨hwalk_mem L w h0 hstep j hjL, hj⟩
    have hcard1 : (Lay i).card = 1 := by
      have := Finset.card_pos.mpr ⟨w j, hxin⟩; omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
    have hxLay : x ∈ Lay i := by rw [hx]; simp
    obtain ⟨hxV, hxd⟩ := (hmemLay i x).mp hxLay
    have hxu : u ≠ x := by
      intro hcon2
      rw [← hcon2, gdist_self] at hxd
      omega
    have hxv : v ≠ x := by
      intro hcon2
      rw [← hcon2, hL] at hxd
      omega
    obtain ⟨M, w', hw0, hwM, hwmem, hwstep⟩ :=
      exists_walk_avoiding a b hbd hu hv hxV hxu hxv
    obtain ⟨j', hj'M, hj'⟩ := hIVT M w' hw0 hwM hwstep i (by omega)
    have hin : w' j' ∈ Lay i := (hmemLay i _).mpr ⟨(hwmem j' hj'M).1, hj'⟩
    rw [hx, Finset.mem_singleton] at hin
    exact (hwmem j' hj'M).2 hin
  -- summing the layers
  have hsum : ∑ i ∈ Finset.range (L + 1), (Lay i).card ≤ (Vst a b).card := by
    have hdisj : ∀ i ∈ Finset.range (L + 1), ∀ j ∈ Finset.range (L + 1), i ≠ j →
        Disjoint (Lay i) (Lay j) := by
      intro i _ j _ hij
      refine Finset.disjoint_left.mpr ?_
      intro x hxi hxj
      exact hij (((hmemLay i x).mp hxi).2.symm.trans ((hmemLay j x).mp hxj).2)
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_le_card ?_
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact ((hmemLay i x).mp hxi).1
  have hsplit : Finset.range (L + 1) = insert 0 (insert 1 (insert L (Finset.Ico 2 L))) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hIco : 2 * (L - 2) ≤ ∑ i ∈ Finset.Ico 2 L, (Lay i).card := by
    calc 2 * (L - 2) = ∑ _i ∈ Finset.Ico 2 L, 2 := by
          rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ i ∈ Finset.Ico 2 L, (Lay i).card :=
          Finset.sum_le_sum (fun i hi => hLaymid i (by
            have := (Finset.mem_Ico.mp hi).1; omega) (Finset.mem_Ico.mp hi).2)
  have hlow : 2 * L + 1 ≤ ∑ i ∈ Finset.range (L + 1), (Lay i).card := by
    rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ico]; omega),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ico]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
    omega
  omega


theorem klee_of_vertex_bound (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hfull : (interior (Hpoly a b)).Nonempty)
    (hd : 3 ≤ d) (hV : (Vst a b).card + 4 ≤ 2 * n) : DiamLE (Hpoly a b) (n - 3) := by
  refine diamLE_of_reach _ _ (fun u hu v hv => ?_)
  have hu' : u ∈ Vst a b := mem_Vst.mpr hu
  have hv' : v ∈ Vst a b := mem_Vst.mpr hv
  have h1 := two_mul_gdist_lt_card a b hbd hfull hd hu' hv'
  exact ⟨gdist a b u v, by omega, gdist_spec a b hbd hu' hv'⟩

end HirschKlee
open scoped RealInnerProductSpace
open HirschLib HirschWalk HirschFace HirschBridge HirschNaddef HirschDescent
open HirschLayer HirschRelax HirschKlee LinearOptimization
namespace HirschKlee2
variable {d n : ℕ}
theorem exists_nonvanishing : ∀ (S : Finset (EuclideanSpace ℝ (Fin d))),
    (∀ z ∈ S, z ≠ 0) → ∃ c : EuclideanSpace ℝ (Fin d), ∀ z ∈ S, ⟪c, z⟫ ≠ 0 := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; exact ⟨0, by simp⟩
  | insert z₀ S' hz₀ ih =>
      intro hS
      obtain ⟨c, hc⟩ := ih (fun z hz => hS z (Finset.mem_insert_of_mem hz))
      have hz0ne : z₀ ≠ 0 := hS z₀ (Finset.mem_insert_self _ _)
      by_cases h0 : ⟪c, z₀⟫ = 0
      · obtain ⟨ε, hε⟩ := Infinite.exists_notMem_finset
          (insert (0:ℝ) (S'.image (fun z => -⟪c, z⟫ / ⟪z₀, z⟫)))
        have hε0 : ε ≠ 0 := by
          intro hcon; exact hε (by rw [hcon]; exact Finset.mem_insert_self _ _)
        refine ⟨c + ε • z₀, ?_⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · rw [inner_add_left, real_inner_smul_left, h0, real_inner_self_eq_norm_sq, zero_add]
          have : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0ne
          positivity
        · rw [inner_add_left, real_inner_smul_left]
          intro hcon
          by_cases hzz : ⟪z₀, z⟫ = 0
          · rw [hzz, mul_zero, add_zero] at hcon
            exact hc z hz' hcon
          · refine hε (Finset.mem_insert_of_mem ?_)
            refine Finset.mem_image.mpr ⟨z, hz', ?_⟩
            field_simp
            linarith
      · exact ⟨c, by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact h0
          · exact hc z hz'⟩

theorem exists_generic (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    ∃ c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ,
      ∀ x ∈ Vst a b, ∀ y ∈ Vst a b, x ≠ y → c x ≠ c y := by
  classical
  set S : Finset (EuclideanSpace ℝ (Fin d)) :=
    ((Vst a b) ×ˢ (Vst a b)).image (fun p => p.1 - p.2) \ {0} with hS
  have hSne : ∀ z ∈ S, z ≠ 0 := by
    intro z hz
    exact fun hcon => (Finset.mem_sdiff.mp hz).2 (by simp [hcon])
  obtain ⟨c, hc⟩ := exists_nonvanishing S hSne
  refine ⟨{ toFun := fun z => ⟪c, z⟫
            map_add' := fun x y => inner_add_right _ _ _
            map_smul' := fun r x => by simpa using real_inner_smul_right c x r }, ?_⟩
  intro x hx y hy hxy hcon
  have hmem : x - y ∈ S := by
    rw [hS]
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
    · simp only [Finset.mem_singleton, sub_eq_zero]
      exact hxy
  refine hc (x - y) hmem ?_
  rw [inner_sub_right]
  have h1 : ⟪c, x⟫ = ⟪c, y⟫ := hcon
  linarith


theorem exists_other_vertex_same_value
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (c : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ)
    {v z : EuclideanSpace ℝ (Fin d)} {i j : Fin n}
    (hvP : v ∈ Hpoly a b)
    (hti : ⟪a i, v⟫ = b i) (htj : ⟪a j, v⟫ = b j)
    (hz0 : z ≠ 0) (hcz : c z = 0)
    (hzi : ⟪a i, z⟫ = 0) (hzj : ⟪a j, z⟫ = 0)
    (hline : ∀ w : EuclideanSpace ℝ (Fin d), ⟪a i, w⟫ = 0 → ⟪a j, w⟫ = 0 → ∃ t : ℝ, w = t • z)
    {ε : ℝ} (hε : 0 < ε) (hmem : v + ε • z ∈ Hpoly a b) :
    ∃ y ∈ Set.extremePoints ℝ (Hpoly a b), y ≠ v ∧ c y = c v := by
  classical
  set fi : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ :=
    { toFun := fun x => -⟪a i, x⟫
      map_add' := by
        intro x y
        simp only [inner_add_right]
        ring
      map_smul' := by
        intro r x
        simp only [real_inner_smul_right, RingHom.id_apply, smul_eq_mul]
        ring } with hfi
  set fj : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ :=
    { toFun := fun x => -⟪a j, x⟫
      map_add' := by
        intro x y
        simp only [inner_add_right]
        ring
      map_smul' := by
        intro r x
        simp only [real_inner_smul_right, RingHom.id_apply, smul_eq_mul]
        ring } with hfj
  have hfia : ∀ x, fi x = -⟪a i, x⟫ := fun _ => rfl
  have hfja : ∀ x, fj x = -⟪a j, x⟫ := fun _ => rfl
  have hFi : IsExtreme ℝ (Hpoly a b) {x | x ∈ Hpoly a b ∧ fi x = -(b i)} :=
    exposed_isExtreme _ fi _ (fun x hx => by
      have := hx i
      show -(b i) ≤ -⟪a i, x⟫
      linarith)
  have hFj : IsExtreme ℝ (Hpoly a b) {x | x ∈ Hpoly a b ∧ fj x = -(b j)} :=
    exposed_isExtreme _ fj _ (fun x hx => by
      have := hx j
      show -(b j) ≤ -⟪a j, x⟫
      linarith)
  set G : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | x ∈ Hpoly a b ∧ fi x = -(b i)} ∩ {x | x ∈ Hpoly a b ∧ fj x = -(b j)} with hG
  have hGext : IsExtreme ℝ (Hpoly a b) G :=
    hFi.trans (isExtreme_inter hFj (fun x hx => hx.1))
  have hmemG : ∀ x, x ∈ G ↔ (x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i ∧ ⟪a j, x⟫ = b j) := by
    intro x
    constructor
    · rintro ⟨⟨hx1, hx2⟩, ⟨_, hx3⟩⟩
      rw [hfia] at hx2
      rw [hfja] at hx3
      exact ⟨hx1, by linarith, by linarith⟩
    · rintro ⟨hx1, hx2, hx3⟩
      exact ⟨⟨hx1, by rw [hfia, hx2]⟩, ⟨hx1, by rw [hfja, hx3]⟩⟩
  have hvG : v ∈ G := (hmemG v).mpr ⟨hvP, hti, htj⟩
  have hstepG : v + ε • z ∈ G := by
    refine (hmemG _).mpr ⟨hmem, ?_, ?_⟩
    · rw [inner_add_right, real_inner_smul_right, hti, hzi, mul_zero, add_zero]
    · rw [inner_add_right, real_inner_smul_right, htj, hzj, mul_zero, add_zero]
  -- `G` sits on the line through `v` in direction `z`
  have hGline : ∀ x ∈ G, ∃ t : ℝ, x = v + t • z := by
    intro x hx
    obtain ⟨hxP, hxi, hxj⟩ := (hmemG x).mp hx
    obtain ⟨t, ht⟩ := hline (x - v) (by rw [inner_sub_right, hxi, hti, sub_self])
      (by rw [inner_sub_right, hxj, htj, sub_self])
    exact ⟨t, by rw [← ht]; abel⟩
  -- maximise `⟪z, ·⟫` over the compact set `G`
  have hGcl : IsClosed G := by
    refine IsClosed.inter (IsClosed.inter (hpoly_closed a b) ?_) (IsClosed.inter
      (hpoly_closed a b) ?_)
    · exact isClosed_eq ((innerSL ℝ (a i)).continuous.neg) continuous_const
    · exact isClosed_eq ((innerSL ℝ (a j)).continuous.neg) continuous_const
  have hGcpt : IsCompact G :=
    (hpoly_compact a b hbd).of_isClosed_subset hGcl (fun x hx => ((hmemG x).mp hx).1)
  obtain ⟨y, hyG, hymax⟩ := hGcpt.exists_isMaxOn ⟨v, hvG⟩
    (Continuous.continuousOn (innerSL ℝ z).continuous)
  have hz2 : (0:ℝ) < ⟪z, z⟫ := real_inner_self_pos.mpr hz0
  have hgt : ⟪z, v⟫ < ⟪z, v + ε • z⟫ := by
    rw [inner_add_right, real_inner_smul_right]
    nlinarith
  have hymax' : ∀ x ∈ G, ⟪z, x⟫ ≤ ⟪z, y⟫ := fun x hx => isMaxOn_iff.mp hymax x hx
  have hyv : y ≠ v := by
    intro hcon
    have := hymax' _ hstepG
    rw [hcon] at this
    exact absurd this (not_le.mpr hgt)
  obtain ⟨t, ht⟩ := hGline y hyG
  refine ⟨y, ⟨((hmemG y).mp hyG).1, ?_⟩, hyv, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ hseg
    have hx1G : x₁ ∈ G := hGext.2 hx₁ hx₂ hyG hseg
    have hseg' : y ∈ openSegment ℝ x₂ x₁ := by rw [openSegment_symm]; exact hseg
    have hx2G : x₂ ∈ G := hGext.2 hx₂ hx₁ hyG hseg'
    obtain ⟨p, q, hp, hq, hpq, hy⟩ := hseg
    have e1 : ⟪z, x₁⟫ ≤ ⟪z, y⟫ := hymax' _ hx1G
    have e2 : ⟪z, x₂⟫ ≤ ⟪z, y⟫ := hymax' _ hx2G
    have e3 : ⟪z, y⟫ = p * ⟪z, x₁⟫ + q * ⟪z, x₂⟫ := by
      rw [← hy, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have esum : p * ⟪z, y⟫ + q * ⟪z, y⟫ = ⟪z, y⟫ := by
      rw [← add_mul, hpq, one_mul]
    have e4 : ⟪z, x₁⟫ = ⟪z, y⟫ := by
      by_contra hne
      have hlt : ⟪z, x₁⟫ < ⟪z, y⟫ := lt_of_le_of_ne e1 hne
      have k1 := mul_lt_mul_of_pos_left hlt hp
      have k2 := mul_le_mul_of_nonneg_left e2 (le_of_lt hq)
      linarith
    obtain ⟨t₁, ht₁⟩ := hGline x₁ hx1G
    rw [ht₁, ht] at e4 ⊢
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right] at e4
    have hK : t₁ * ⟪z, z⟫ = t * ⟪z, z⟫ := by linarith
    rw [mul_right_cancel₀ (ne_of_gt hz2) hK]
  · rw [ht, map_add, map_smul, hcz, smul_eq_mul, mul_zero, add_zero]


theorem sign_lemma {x y u w : ℝ} (hu : u < 0) (hw : w < 0) (h : x * u + y * w = 0) :
    (x = 0 ∧ y = 0) ∨ (0 < x ∧ y < 0) ∨ (x < 0 ∧ 0 < y) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exact Or.inr (Or.inr ⟨hx, by nlinarith⟩)
  · refine Or.inl ⟨hx, ?_⟩
    rw [hx, zero_mul, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (ne_of_lt hw)
  · exact Or.inr (Or.inl ⟨hx, by nlinarith⟩)

theorem perp_line {u₁ u₂ z : EuclideanSpace ℝ (Fin 3)}
    (hind : LinearIndependent ℝ ![u₁, u₂])
    (hz : z ≠ 0) (h1 : ⟪u₁, z⟫ = 0) (h2 : ⟪u₂, z⟫ = 0) :
    ∀ w : EuclideanSpace ℝ (Fin 3), ⟪u₁, w⟫ = 0 → ⟪u₂, w⟫ = 0 → ∃ t : ℝ, w = t • z := by
  classical
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.span ℝ {u₁, u₂} with hK
  have hspan : (Set.range ![u₁, u₂]) = ({u₁, u₂} : Set (EuclideanSpace ℝ (Fin 3))) := by
    ext x
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  have hKrank : Module.finrank ℝ K = 2 := by
    rw [hK, ← hspan]
    rw [finrank_span_eq_card hind]
    simp
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hperp : Module.finrank ℝ (Kᗮ) = 1 := by
    have := Submodule.finrank_add_finrank_orthogonal (K := K)
    omega
  have hmemK : ∀ x : EuclideanSpace ℝ (Fin 3), ⟪u₁, x⟫ = 0 → ⟪u₂, x⟫ = 0 → x ∈ Kᗮ := by
    intro x hx1 hx2
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [hK] at hy
    induction hy using Submodule.span_induction with
    | mem g hg =>
        rcases hg with rfl | hg2
        · exact hx1
        · rw [Set.mem_singleton_iff] at hg2
          subst hg2
          exact hx2
    | zero => simp
    | add p q _ _ hp hq => rw [inner_add_left, hp, hq]; ring
    | smul r p _ hp => rw [real_inner_smul_left, hp]; ring
  have hzK : z ∈ Kᗮ := hmemK z h1 h2
  have hle : Submodule.span ℝ {z} ≤ Kᗮ := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hzK
  have hz1 : Module.finrank ℝ (Submodule.span ℝ ({z} : Set (EuclideanSpace ℝ (Fin 3)))) = 1 :=
    finrank_span_singleton hz
  have heq : Submodule.span ℝ ({z} : Set (EuclideanSpace ℝ (Fin 3))) = Kᗮ :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hz1, hperp])
  intro w hw1 hw2
  have : w ∈ Submodule.span ℝ ({z} : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [heq]; exact hmemK w hw1 hw2
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp this
  exact ⟨t, ht.symm⟩


theorem exists_flat_dir (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (s : Finset (Fin n))
    (hpt : ∀ x : EuclideanSpace ℝ (Fin 3), (∀ j ∈ s, ⟪a j, x⟫ = 0) → x = 0)
    {v : EuclideanSpace ℝ (Fin 3)} (hvP : v ∈ Hpoly a b)
    (hst : ∀ j ∈ s, ⟪a j, v⟫ = b j) {i : Fin n} (hti : ⟪a i, v⟫ = b i)
    {yp ym : EuclideanSpace ℝ (Fin 3)} (hypP : yp ∈ Hpoly a b) (hymP : ym ∈ Hpoly a b)
    (hypi : ⟪a i, yp⟫ = b i) (hymi : ⟪a i, ym⟫ = b i)
    (hcp : c v < c yp) (hcm : c ym < c v) :
    ∃ z : EuclideanSpace ℝ (Fin 3), z ≠ 0 ∧ c z = 0 ∧ ⟪a i, z⟫ = 0 ∧
      (∀ j ∈ s, ⟪a j, z⟫ ≤ 0) ∧ ∃ ε : ℝ, 0 < ε ∧ v + ε • z ∈ Hpoly a b := by
  classical
  set p : EuclideanSpace ℝ (Fin 3) := yp - v with hp
  set q : EuclideanSpace ℝ (Fin 3) := ym - v with hq
  set α : ℝ := c yp - c v with hα
  set β : ℝ := c v - c ym with hβ
  have hα0 : 0 < α := by rw [hα]; linarith
  have hβ0 : 0 < β := by rw [hβ]; linarith
  set z : EuclideanSpace ℝ (Fin 3) := α • q + β • p with hz
  have hcq : c q = -β := by rw [hq, map_sub, hβ]; try ring
  have hcp' : c p = α := by rw [hp, map_sub, hα]; try ring
  have hcz : c z = 0 := by
    rw [hz, map_add, map_smul, map_smul, hcq, hcp', smul_eq_mul, smul_eq_mul]; ring
  have hpi : ⟪a i, p⟫ = 0 := by rw [hp, inner_sub_right, hypi, hti, sub_self]
  have hqi : ⟪a i, q⟫ = 0 := by rw [hq, inner_sub_right, hymi, hti, sub_self]
  have hzi : ⟪a i, z⟫ = 0 := by
    rw [hz, inner_add_right, real_inner_smul_right, real_inner_smul_right, hpi, hqi]; ring
  have hpj : ∀ j ∈ s, ⟪a j, p⟫ ≤ 0 := by
    intro j hj
    rw [hp, inner_sub_right, hst j hj]
    linarith [hypP j]
  have hqj : ∀ j ∈ s, ⟪a j, q⟫ ≤ 0 := by
    intro j hj
    rw [hq, inner_sub_right, hst j hj]
    linarith [hymP j]
  have hzj : ∀ j ∈ s, ⟪a j, z⟫ ≤ 0 := by
    intro j hj
    rw [hz, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h1 := hpj j hj
    have h2 := hqj j hj
    nlinarith
  have hz0 : z ≠ 0 := by
    intro hcon
    have hpz : p = 0 := by
      refine hpt p ?_
      intro j hj
      have hsum : α * ⟪a j, q⟫ + β * ⟪a j, p⟫ = 0 := by
        have := congrArg (fun x => ⟪a j, x⟫) hcon
        simp only [hz, inner_add_right, real_inner_smul_right, inner_zero_right] at this
        exact this
      have h1 := hpj j hj
      have h2 := hqj j hj
      nlinarith
    have : yp = v := by rw [hp] at hpz; exact sub_eq_zero.mp hpz
    rw [this] at hcp
    exact lt_irrefl _ hcp
  refine ⟨z, hz0, hcz, hzi, hzj, 1 / (α + β), by positivity, ?_⟩
  have hεs : (1 / (α + β)) * α + (1 / (α + β)) * β = 1 := by
    field_simp
  have hcomb : v + (1 / (α + β)) • z
      = ((1 / (α + β)) * α) • ym + ((1 / (α + β)) * β) • yp := by
    rw [hz, hp, hq]
    match_scalars <;> linarith [hεs]
  rw [hcomb]
  exact hpoly_convex a b hymP hypP (by positivity) (by positivity) hεs


theorem no_flat_dir (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) (c : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (hgen : ∀ x ∈ Vst a b, ∀ y ∈ Vst a b, x ≠ y → c x ≠ c y)
    {v z : EuclideanSpace ℝ (Fin 3)} {i j : Fin n}
    (hv : v ∈ Vst a b)
    (hti : ⟪a i, v⟫ = b i) (htj : ⟪a j, v⟫ = b j)
    (hind : LinearIndependent ℝ ![a i, a j])
    (hz0 : z ≠ 0) (hcz : c z = 0) (hzi : ⟪a i, z⟫ = 0) (hzj : ⟪a j, z⟫ = 0)
    {ε : ℝ} (hε : 0 < ε) (hmem : v + ε • z ∈ Hpoly a b) : False := by
  obtain ⟨y, hyV, hyv, hyc⟩ := exists_other_vertex_same_value a b hbd c
    (mem_Vst.mp hv).1 hti htj hz0 hcz hzi hzj (perp_line hind hz0 hzi hzj) hε hmem
  exact hgen y (mem_Vst.mpr hyV) v hv hyv hyc


theorem pair_indep {s : Finset (Fin n)} {a : Fin n → EuclideanSpace ℝ (Fin 3)}
    (hsind : LinearIndependent ℝ (fun i : s => a i.1))
    {i j : Fin n} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    LinearIndependent ℝ ![a i, a j] := by
  classical
  have hf : Function.Injective (![(⟨i, hi⟩ : {x // x ∈ s}), ⟨j, hj⟩]) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [Subtype.ext_iff]
  have hcomp := hsind.comp _ hf
  have heq : (fun i : s => a i.1) ∘ ![(⟨i, hi⟩ : {x // x ∈ s}), ⟨j, hj⟩] = ![a i, a j] := by
    funext k
    fin_cases k <;> rfl
  rwa [heq] at hcomp

theorem exists_uncut (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) (c : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (hgen : ∀ x ∈ Vst a b, ∀ y ∈ Vst a b, x ≠ y → c x ≠ c y)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : v ∈ Vst a b) :
    ∃ i, ⟪a i, v⟫ = b i ∧
      ((∀ y ∈ Vst a b, ⟪a i, y⟫ = b i → c v ≤ c y) ∨
       (∀ y ∈ Vst a b, ⟪a i, y⟫ = b i → c y ≤ c v)) := by
  classical
  by_contra hcon
  have hcut : ∀ i, ⟪a i, v⟫ = b i →
      (∃ y ∈ Vst a b, ⟪a i, y⟫ = b i ∧ c y < c v) ∧
      (∃ y ∈ Vst a b, ⟪a i, y⟫ = b i ∧ c v < c y) := by
    intro i hti
    constructor
    · by_contra h
      push_neg at h
      exact hcon ⟨i, hti, Or.inl h⟩
    · by_contra h
      push_neg at h
      exact hcon ⟨i, hti, Or.inr h⟩
  obtain ⟨s, hscard, hstight, hsind⟩ := exists_active_basis_indep a b (mem_Vst.mp hv)
  -- the tangent cone of the basis rows is pointed
  have hspanTop : Submodule.span ℝ (Set.range (fun i : s => a i.1)) = ⊤ := by
    have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : s => a i.1))) = 3 := by
      rw [finrank_span_eq_card hsind]; simp [hscard]
    exact Submodule.eq_top_of_finrank_eq (by rw [hfr]; simp)
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3), (∀ j ∈ s, ⟪a j, x⟫ = 0) → x = 0 := by
    intro x hx
    have hzero : ∀ w : EuclideanSpace ℝ (Fin 3), ⟪w, x⟫ = 0 := by
      intro w
      have hw : w ∈ Submodule.span ℝ (Set.range (fun i : s => a i.1)) := by
        rw [hspanTop]; trivial
      induction hw using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hx i.1 i.2
      | zero => simp
      | add p q _ _ hp hq => rw [inner_add_left, hp, hq]; ring
      | smul r p _ hp => rw [real_inner_smul_left, hp]; ring
    have h0 := hzero x
    rw [real_inner_self_eq_norm_sq] at h0
    have hn : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hn
  obtain ⟨i₁, i₂, i₃, h12, h13, h23, hs⟩ := Finset.card_eq_three.mp hscard
  have hm1 : i₁ ∈ s := by rw [hs]; simp
  have hm2 : i₂ ∈ s := by rw [hs]; simp
  have hm3 : i₃ ∈ s := by rw [hs]; simp
  have ht1 := hstight i₁ hm1
  have ht2 := hstight i₂ hm2
  have ht3 := hstight i₃ hm3
  obtain ⟨ym1, hym1V, hym1t, hym1c⟩ := (hcut i₁ ht1).1
  obtain ⟨yp1, hyp1V, hyp1t, hyp1c⟩ := (hcut i₁ ht1).2
  obtain ⟨ym2, hym2V, hym2t, hym2c⟩ := (hcut i₂ ht2).1
  obtain ⟨yp2, hyp2V, hyp2t, hyp2c⟩ := (hcut i₂ ht2).2
  obtain ⟨ym3, hym3V, hym3t, hym3c⟩ := (hcut i₃ ht3).1
  obtain ⟨yp3, hyp3V, hyp3t, hyp3c⟩ := (hcut i₃ ht3).2
  obtain ⟨z₁, hz10, hcz1, hzi1, hzj1, ε₁, hε1, hmem1⟩ :=
    exists_flat_dir a b c s hpt (mem_Vst.mp hv).1 hstight ht1
      (mem_Vst.mp hyp1V).1 (mem_Vst.mp hym1V).1 hyp1t hym1t hyp1c hym1c
  obtain ⟨z₂, hz20, hcz2, hzi2, hzj2, ε₂, hε2, hmem2⟩ :=
    exists_flat_dir a b c s hpt (mem_Vst.mp hv).1 hstight ht2
      (mem_Vst.mp hyp2V).1 (mem_Vst.mp hym2V).1 hyp2t hym2t hyp2c hym2c
  obtain ⟨z₃, hz30, hcz3, hzi3, hzj3, ε₃, hε3, hmem3⟩ :=
    exists_flat_dir a b c s hpt (mem_Vst.mp hv).1 hstight ht3
      (mem_Vst.mp hyp3V).1 (mem_Vst.mp hym3V).1 hyp3t hym3t hyp3c hym3c
  -- if some cross term vanishes we get a second vertex on the level of `v`
  by_cases w12 : ⟪a i₁, z₂⟫ = 0
  · exact no_flat_dir a b hbd c hgen hv ht1 ht2 (pair_indep hsind hm1 hm2 h12)
      hz20 hcz2 w12 hzi2 hε2 hmem2
  by_cases w13 : ⟪a i₁, z₃⟫ = 0
  · exact no_flat_dir a b hbd c hgen hv ht1 ht3 (pair_indep hsind hm1 hm3 h13)
      hz30 hcz3 w13 hzi3 hε3 hmem3
  by_cases w21 : ⟪a i₂, z₁⟫ = 0
  · exact no_flat_dir a b hbd c hgen hv ht2 ht1 (pair_indep hsind hm2 hm1 (Ne.symm h12))
      hz10 hcz1 w21 hzi1 hε1 hmem1
  by_cases w23 : ⟪a i₂, z₃⟫ = 0
  · exact no_flat_dir a b hbd c hgen hv ht2 ht3 (pair_indep hsind hm2 hm3 h23)
      hz30 hcz3 w23 hzi3 hε3 hmem3
  by_cases w31 : ⟪a i₃, z₁⟫ = 0
  · exact no_flat_dir a b hbd c hgen hv ht3 ht1 (pair_indep hsind hm3 hm1 (Ne.symm h13))
      hz10 hcz1 w31 hzi1 hε1 hmem1
  by_cases w32 : ⟪a i₃, z₂⟫ = 0
  · exact no_flat_dir a b hbd c hgen hv ht3 ht2 (pair_indep hsind hm3 hm2 (Ne.symm h23))
      hz20 hcz2 w32 hzi2 hε2 hmem2
  -- otherwise every cross term is strictly negative
  have s12 : ⟪a i₁, z₂⟫ < 0 := lt_of_le_of_ne (hzj2 i₁ hm1) w12
  have s13 : ⟪a i₁, z₃⟫ < 0 := lt_of_le_of_ne (hzj3 i₁ hm1) w13
  have s21 : ⟪a i₂, z₁⟫ < 0 := lt_of_le_of_ne (hzj1 i₂ hm2) w21
  have s23 : ⟪a i₂, z₃⟫ < 0 := lt_of_le_of_ne (hzj3 i₂ hm2) w23
  have s31 : ⟪a i₃, z₁⟫ < 0 := lt_of_le_of_ne (hzj1 i₃ hm3) w31
  have s32 : ⟪a i₃, z₂⟫ < 0 := lt_of_le_of_ne (hzj2 i₃ hm3) w32
  -- the three directions lie in the plane `c = 0`, hence are dependent
  have hdep : ¬ LinearIndependent ℝ ![z₁, z₂, z₃] := by
    intro hind
    have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range ![z₁, z₂, z₃])) = 3 := by
      rw [finrank_span_eq_card hind]; simp
    have htop : Submodule.span ℝ (Set.range ![z₁, z₂, z₃]) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hfr]; simp)
    have hx : c (ym1 - v) ≠ 0 := by
      rw [map_sub]
      intro hcc
      exact absurd hym1c (by linarith)
    have hall : ∀ w ∈ Submodule.span ℝ (Set.range ![z₁, z₂, z₃]), c w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          fin_cases k
          · exact hcz1
          · exact hcz2
          · exact hcz3
      | zero => simp
      | add p q _ _ hp hq => rw [map_add, hp, hq]; ring
      | smul r p _ hp => rw [map_smul, hp, smul_eq_mul]; ring
    exact hx (hall _ (by rw [htop]; trivial))
  obtain ⟨g, hgsum, k0, hk0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hsum : g 0 • z₁ + g 1 • z₂ + g 2 • z₃ = 0 := by
    rw [Fin.sum_univ_three] at hgsum
    simpa using hgsum
  have e1 : g 1 * ⟪a i₁, z₂⟫ + g 2 * ⟪a i₁, z₃⟫ = 0 := by
    have h := congrArg (fun x => ⟪a i₁, x⟫) hsum
    simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at h
    rw [hzi1] at h
    linarith
  have e2 : g 0 * ⟪a i₂, z₁⟫ + g 2 * ⟪a i₂, z₃⟫ = 0 := by
    have h := congrArg (fun x => ⟪a i₂, x⟫) hsum
    simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at h
    rw [hzi2] at h
    linarith
  have e3 : g 0 * ⟪a i₃, z₁⟫ + g 1 * ⟪a i₃, z₂⟫ = 0 := by
    have h := congrArg (fun x => ⟪a i₃, x⟫) hsum
    simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at h
    rw [hzi3] at h
    linarith
  rcases sign_lemma s12 s13 e1 with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · -- `g 1 = g 2 = 0`, hence `g 0 = 0`
    rw [hB, zero_mul, add_zero] at e2
    have h0 : g 0 = 0 := (mul_eq_zero.mp e2).resolve_right (ne_of_lt s21)
    refine hk0 ?_
    fin_cases k0
    · exact h0
    · exact hA
    · exact hB
  · -- `0 < g 1`, `g 2 < 0`
    rcases sign_lemma s21 s23 e2 with ⟨hC, hD⟩ | ⟨hC, hD⟩ | ⟨hC, hD⟩
    · linarith
    · rcases sign_lemma s31 s32 e3 with ⟨hE, hF⟩ | ⟨hE, hF⟩ | ⟨hE, hF⟩ <;> linarith
    · linarith
  · -- `g 1 < 0`, `0 < g 2`
    rcases sign_lemma s21 s23 e2 with ⟨hC, hD⟩ | ⟨hC, hD⟩ | ⟨hC, hD⟩
    · linarith
    · linarith
    · rcases sign_lemma s31 s32 e3 with ⟨hE, hF⟩ | ⟨hE, hF⟩ | ⟨hE, hF⟩ <;> linarith


theorem card_vertices_le (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (hfull : (interior (Hpoly a b)).Nonempty) :
    (Vst a b).card + 4 ≤ 2 * n := by
  classical
  obtain ⟨c, hgen⟩ := exists_generic a b
  have hVne : (Vst a b).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Vst a b) with h | h
    · exfalso
      obtain ⟨x, hx⟩ := hne
      rw [hpoly_eq_convexHull a b hbd] at hx
      have hemp : Set.extremePoints ℝ (Hpoly a b) = ∅ := by
        rw [← coe_Vst, h]; simp
      rw [hemp, convexHull_empty] at hx
      exact hx
    · exact h
  set Nmin : EuclideanSpace ℝ (Fin 3) → Finset (Fin n) := fun x =>
    Finset.univ.filter (fun i => ⟪a i, x⟫ = b i ∧
      ∀ y ∈ Vst a b, ⟪a i, y⟫ = b i → c x ≤ c y) with hNmin
  set Nmax : EuclideanSpace ℝ (Fin 3) → Finset (Fin n) := fun x =>
    Finset.univ.filter (fun i => ⟪a i, x⟫ = b i ∧
      ∀ y ∈ Vst a b, ⟪a i, y⟫ = b i → c y ≤ c x) with hNmax
  -- the fibres are disjoint
  have hdisjmin : ∀ x ∈ Vst a b, ∀ y ∈ Vst a b, x ≠ y → Disjoint (Nmin x) (Nmin y) := by
    intro x hx y hy hxy
    refine Finset.disjoint_left.mpr ?_
    intro i hix hiy
    obtain ⟨-, hxt, hxm⟩ := Finset.mem_filter.mp hix
    obtain ⟨-, hyt, hym⟩ := Finset.mem_filter.mp hiy
    exact hgen x hx y hy hxy (le_antisymm (hxm y hy hyt) (hym x hx hxt))
  have hdisjmax : ∀ x ∈ Vst a b, ∀ y ∈ Vst a b, x ≠ y → Disjoint (Nmax x) (Nmax y) := by
    intro x hx y hy hxy
    refine Finset.disjoint_left.mpr ?_
    intro i hix hiy
    obtain ⟨-, hxt, hxm⟩ := Finset.mem_filter.mp hix
    obtain ⟨-, hyt, hym⟩ := Finset.mem_filter.mp hiy
    exact hgen x hx y hy hxy (le_antisymm (hym x hx hxt) (hxm y hy hyt))
  have hsummin : ∑ x ∈ Vst a b, (Nmin x).card ≤ n := by
    rw [← Finset.card_biUnion hdisjmin]
    calc ((Vst a b).biUnion Nmin).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hsummax : ∑ x ∈ Vst a b, (Nmax x).card ≤ n := by
    rw [← Finset.card_biUnion hdisjmax]
    calc ((Vst a b).biUnion Nmax).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  -- every vertex absorbs at least one row
  have hone : ∀ x ∈ Vst a b, 1 ≤ (Nmin x).card + (Nmax x).card := by
    intro x hx
    obtain ⟨i, hti, hi⟩ := exists_uncut a b hbd c hgen hx
    rcases hi with h | h
    · have : i ∈ Nmin x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hti, h⟩
      have := Finset.card_pos.mpr ⟨i, this⟩
      omega
    · have : i ∈ Nmax x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hti, h⟩
      have := Finset.card_pos.mpr ⟨i, this⟩
      omega
  -- the extreme vertices absorb three
  obtain ⟨xmin, hxminV, hxminle⟩ := (Vst a b).exists_min_image c hVne
  obtain ⟨xmax, hxmaxV, hxmaxle⟩ := (Vst a b).exists_max_image c hVne
  have hthree : ∀ x ∈ Vst a b, (∀ y ∈ Vst a b, c x ≤ c y) → 3 ≤ (Nmin x).card := by
    intro x hx hmin
    obtain ⟨s, hscard, hstight, -⟩ := exists_active_basis_indep a b (mem_Vst.mp hx)
    calc 3 = s.card := hscard.symm
      _ ≤ (Nmin x).card := Finset.card_le_card (fun i hi =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstight i hi, fun y hy _ => hmin y hy⟩)
  have hthree' : ∀ x ∈ Vst a b, (∀ y ∈ Vst a b, c y ≤ c x) → 3 ≤ (Nmax x).card := by
    intro x hx hmax
    obtain ⟨s, hscard, hstight, -⟩ := exists_active_basis_indep a b (mem_Vst.mp hx)
    calc 3 = s.card := hscard.symm
      _ ≤ (Nmax x).card := Finset.card_le_card (fun i hi =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstight i hi, fun y hy _ => hmax y hy⟩)
  have h3min : 3 ≤ (Nmin xmin).card + (Nmax xmin).card := by
    have := hthree xmin hxminV hxminle; omega
  have h3max : 3 ≤ (Nmin xmax).card + (Nmax xmax).card := by
    have := hthree' xmax hxmaxV hxmaxle; omega
  -- the two extreme vertices are distinct
  have hcard2 : 2 ≤ (Vst a b).card := by
    by_contra hcon
    push_neg at hcon
    have hc1 : (Vst a b).card = 1 := by
      have := Finset.card_pos.mpr hVne; omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc1
    have hPeq : Hpoly a b = {w} := by
      rw [hpoly_eq_convexHull a b hbd, ← coe_Vst, hw]
      simp
    obtain ⟨c₀, hc0⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 3))
    refine not_const_of_interior a b hfull hc0 ⟪c₀, w⟫ ?_
    intro z hz
    rw [hPeq, Set.mem_singleton_iff] at hz
    rw [hz]
  have hxne : xmin ≠ xmax := by
    intro hcon
    obtain ⟨x, hxV, y, hyV, hxy⟩ := Finset.one_lt_card.mp hcard2
    have h1 : c xmin ≤ c x := hxminle x hxV
    have h2 : c x ≤ c xmax := hxmaxle x hxV
    have h3 : c xmin ≤ c y := hxminle y hyV
    have h4 : c y ≤ c xmax := hxmaxle y hyV
    rw [hcon] at h1 h3
    exact hgen x hxV y hyV hxy (by linarith [h1, h2, h3, h4])
  -- assemble
  have hsum : ∑ x ∈ Vst a b, ((Nmin x).card + (Nmax x).card) ≤ 2 * n := by
    rw [Finset.sum_add_distrib]
    omega
  have hlow : (Vst a b).card + 4 ≤ ∑ x ∈ Vst a b, ((Nmin x).card + (Nmax x).card) := by
    set f : EuclideanSpace ℝ (Fin 3) → ℕ := fun x => (Nmin x).card + (Nmax x).card with hf
    have hxmaxmem : xmax ∈ (Vst a b).erase xmin := Finset.mem_erase.mpr ⟨Ne.symm hxne, hxmaxV⟩
    have e1 : ∑ x ∈ Vst a b, f x = f xmin + ∑ x ∈ (Vst a b).erase xmin, f x :=
      (Finset.add_sum_erase _ f hxminV).symm
    have e2 : ∑ x ∈ (Vst a b).erase xmin, f x
        = f xmax + ∑ x ∈ ((Vst a b).erase xmin).erase xmax, f x :=
      (Finset.add_sum_erase _ f hxmaxmem).symm
    have e3 : (((Vst a b).erase xmin).erase xmax).card = (Vst a b).card - 2 := by
      rw [Finset.card_erase_of_mem hxmaxmem, Finset.card_erase_of_mem hxminV]
      omega
    have e4 : (((Vst a b).erase xmin).erase xmax).card
        ≤ ∑ x ∈ ((Vst a b).erase xmin).erase xmax, f x := by
      calc (((Vst a b).erase xmin).erase xmax).card
          = ∑ _x ∈ ((Vst a b).erase xmin).erase xmax, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun x hx => hone x
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
    have hf1 : f xmin = (Nmin xmin).card + (Nmax xmin).card := rfl
    have hf2 : f xmax = (Nmin xmax).card + (Nmax xmax).card := rfl
    rw [e1, e2]
    omega
  omega

theorem klee_three (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hfull : (interior (Hpoly a b)).Nonempty) : DiamLE (Hpoly a b) (n - 3) :=
  klee_of_vertex_bound a b hbd hfull (le_refl 3) (card_vertices_le a b hbd hne hfull)

end HirschKlee2
open scoped RealInnerProductSpace
open HirschLib HirschWalk HirschFace HirschBridge HirschFacet HirschLayer
open HirschRelax HirschReindex HirschKKb
open HirschKlee HirschKlee2 LinearOptimization
namespace HirschKlee3
variable {n : ℕ}
theorem exists_strict_point (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) :
    ∀ T : Finset (Fin n), (∀ i ∈ T, ∃ y ∈ Hpoly a b, ⟪a i, y⟫ < b i) →
      ∃ x ∈ Hpoly a b, ∀ i ∈ T, ⟪a i, x⟫ < b i := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; obtain ⟨x, hx⟩ := hne; exact ⟨x, hx, by simp⟩
  | insert j T hj ih =>
      intro hT
      obtain ⟨x, hxP, hx⟩ := ih (fun i hi => hT i (Finset.mem_insert_of_mem hi))
      obtain ⟨y, hyP, hy⟩ := hT j (Finset.mem_insert_self _ _)
      refine ⟨(1/2 : ℝ) • x + (1/2 : ℝ) • y,
        hpoly_convex a b hxP hyP (by norm_num) (by norm_num) (by norm_num), ?_⟩
      intro i hi
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rcases Finset.mem_insert.mp hi with rfl | hiT
      · have h1 : ⟪a i, x⟫ ≤ b i := hxP i
        linarith
      · have h2 : ⟪a i, y⟫ ≤ b i := hyP i
        have h1 := hx i hiT
        linarith

theorem exists_implicit_eq (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hint : interior (Hpoly a b) = ∅) :
    ∃ i, a i ≠ 0 ∧ ∀ x ∈ Hpoly a b, ⟪a i, x⟫ = b i := by
  classical
  by_contra hcon
  push_neg at hcon
  set S : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ 0) with hS
  have hwit : ∀ i ∈ S, ∃ y ∈ Hpoly a b, ⟪a i, y⟫ < b i := by
    intro i hi
    have hai : a i ≠ 0 := (Finset.mem_filter.mp hi).2
    obtain ⟨y, hyP, hy⟩ := hcon i hai
    exact ⟨y, hyP, lt_of_le_of_ne (hyP i) hy⟩
  obtain ⟨x, hxP, hx⟩ := exists_strict_point a b hne S hwit
  -- a ball around `x` lies in `P`
  have hxint : x ∈ interior (Hpoly a b) := by
    rcases Finset.eq_empty_or_nonempty S with hSe | hSne
    · -- every row is degenerate, so `P` is everything
      have huniv : Hpoly a b = Set.univ := by
        ext y
        simp only [Set.mem_univ, iff_true]
        intro i
        have hai : a i = 0 := by
          by_contra hcc
          have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcc⟩
          rw [hSe] at this
          exact absurd this (Finset.notMem_empty i)
        rw [hai, inner_zero_left]
        have := hxP i
        rw [hai, inner_zero_left] at this
        exact this
      rw [huniv]
      simp
    · set r : ℝ := S.inf' hSne (fun i => (b i - ⟪a i, x⟫) / ‖a i‖) with hr
      have hrpos : 0 < r := by
        refine (Finset.lt_inf'_iff _).mpr ?_
        intro i hi
        have hai : a i ≠ 0 := (Finset.mem_filter.mp hi).2
        exact div_pos (by linarith [hx i hi]) (norm_pos_iff.mpr hai)
      refine mem_interior.mpr ⟨Metric.ball x r, ?_, Metric.isOpen_ball, Metric.mem_ball_self hrpos⟩
      intro y hy
      intro i
      by_cases hai : a i = 0
      · rw [hai, inner_zero_left]
        have := hxP i
        rw [hai, inner_zero_left] at this
        exact this
      · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
        have hri : r ≤ (b i - ⟪a i, x⟫) / ‖a i‖ :=
          Finset.inf'_le (fun i => (b i - ⟪a i, x⟫) / ‖a i‖) hiS
        have hna : 0 < ‖a i‖ := norm_pos_iff.mpr hai
        have hcs : ⟪a i, y - x⟫ ≤ ‖a i‖ * ‖y - x‖ := real_inner_le_norm _ _
        have hd : ‖y - x‖ < r := by
          rw [← dist_eq_norm]; exact Metric.mem_ball.mp hy
        have hmul : ‖a i‖ * ‖y - x‖ < ‖a i‖ * r := mul_lt_mul_of_pos_left hd hna
        have hrb : r * ‖a i‖ ≤ b i - ⟪a i, x⟫ := (le_div_iff₀ hna).mp hri
        have : ⟪a i, y⟫ = ⟪a i, x⟫ + ⟪a i, y - x⟫ := by
          rw [inner_sub_right]; ring
        rw [this]
        linarith
  rw [hint] at hxint
  exact hxint


end HirschKlee3
open scoped RealInnerProductSpace
open HirschLib HirschWalk HirschFace HirschBridge HirschFacet HirschReindex
open HirschKKb HirschKlee HirschKlee2 HirschKlee3 LinearOptimization
namespace HirschKleeS
variable {n : ℕ}
theorem plane_bound_all' : ∀ (m : ℕ) (a : Fin m → EuclideanSpace ℝ (Fin 2))
    (b : Fin m → ℝ), DiamLE (Hpoly a b) (m - 2) := by
  intro m
  induction m with
  | zero =>
      intro a b
      refine diamLE_of_subsingleton _ _ (fun u hu v hv => ?_)
      exfalso
      obtain ⟨e, he⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 2))
      have hmem : ∀ y : EuclideanSpace ℝ (Fin 2), y ∈ Hpoly a b := fun y i => Fin.elim0 i
      have hseg : u ∈ openSegment ℝ (u - e) (u + e) :=
        ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by module⟩
      exact he (sub_eq_self.mp (hu.2 (hmem (u - e)) (hmem (u + e)) hseg))
  | succ k ih =>
      intro a b
      by_cases hz : ∃ i, a i = 0
      · obtain ⟨i, hi⟩ := hz
        rcases lt_or_ge (b i) 0 with hb | hb
        · rw [hpoly_eq_empty a b i hi hb]
          exact diamLE_empty _
        · rw [hpoly_drop a b i hi hb]
          exact diamLE_mono _ (by omega) (ih _ _)
      · push_neg at hz
        exact Hirsch.plane_bound_general (k + 1) a b hz

theorem klee_degenerate' (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hint : interior (Hpoly a b) = ∅) : DiamLE (Hpoly a b) (n - 3) := by
  obtain ⟨i, hai, hieq⟩ := exists_implicit_eq a b hne hint
  have hn1 : 0 < n := i.pos
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hfacet : {x : EuclideanSpace ℝ (Fin 3) | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} = Hpoly a b := by
    ext x
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, hieq x h⟩⟩
  refine diamLE_of_reach _ _ (fun u hu v hv => ⟨k - 2, by omega, ?_⟩)
  exact Hirsch.facet_reduction 3 k a b i hai hbd (k - 2)
    (fun a' b' _ => plane_bound_all' k a' b') u v
    (by rw [hfacet]; exact hu) (by rw [hfacet]; exact hv)

theorem klee_final (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - 3) := by
  rcases Set.eq_empty_or_nonempty (interior (Hpoly a b)) with hint | hint
  · exact klee_degenerate' a b hne hbd hint
  · exact klee_three a b hne hbd hint

end HirschKleeS


open HirschKleeS

/-- **Klee 1966.**  A bounded polyhedron in `ℝ³` described by `n` inequalities has
combinatorial diameter at most `n - 3`. -/
theorem solution (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - 3) :=
  HirschKleeS.klee_final n a b hne hbd
