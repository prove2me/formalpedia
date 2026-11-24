-- Prove2me | solution 1 for HirschDim4.unbounded_four_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:50:16.433643+00:00
-- url     : https://prove2.me/submissions/b6b87f43-d0c4-4b7f-b313-7abe6cf58e6a

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

set_option autoImplicit false

open scoped RealInnerProductSpace
open Hirsch Filter Topology

variable {d n : ℕ}

/-- Rows tight at `x`. -/
private noncomputable def tset (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun i => ⟪a i, x⟫ = b i)

private lemma mem_tset (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) : i ∈ tset a b x ↔ ⟪a i, x⟫ = b i := by
  classical
  unfold tset; simp

private lemma perturb (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Hpoly a b) {z : EuclideanSpace ℝ (Fin d)}
    (hz : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, z⟫ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ x + ε • z ∈ Hpoly a b ∧ x - ε • z ∈ Hpoly a b := by
  have key : ∀ i, ∀ᶠ ε in 𝓝 (0:ℝ), ⟪a i, x + ε • z⟫ ≤ b i ∧ ⟪a i, x - ε • z⟫ ≤ b i := by
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · refine Eventually.of_forall fun ε => ?_
      simp [inner_add_right, inner_sub_right, inner_smul_right, hz i hi, hi]
    · have hlt : ⟪a i, x⟫ < b i := lt_of_le_of_ne (hx i) hi
      have c1 : Continuous (fun ε : ℝ => ⟪a i, x + ε • z⟫) := by fun_prop
      have c2 : Continuous (fun ε : ℝ => ⟪a i, x - ε • z⟫) := by fun_prop
      have t1 := c1.tendsto 0
      have t2 := c2.tendsto 0
      simp only [zero_smul, add_zero, sub_zero] at t1 t2
      exact (t1.eventually (Iio_mem_nhds hlt)).and (t2.eventually (Iio_mem_nhds hlt)) |>.mono
        fun ε h => ⟨le_of_lt h.1, le_of_lt h.2⟩
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (eventually_all.2 key)
  have hd : dist (δ / 2) (0:ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  exact ⟨δ / 2, by positivity, fun i => (h hd i).1, fun i => (h hd i).2⟩

/-- A nonzero vector orthogonal to a family of fewer than `d` vectors. -/
private lemma exists_orth (s : Finset (EuclideanSpace ℝ (Fin d))) (hs : s.card < d) :
    ∃ z : EuclideanSpace ℝ (Fin d), z ≠ 0 ∧ ∀ v ∈ s, ⟪v, z⟫ = 0 := by
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℝ (s : Set _)
  have h1 : Module.finrank ℝ K ≤ s.card := finrank_span_finset_le_card s
  have h2 := K.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at h2
  have hne : Kᗮ ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h2
    omega
  obtain ⟨z, hzK, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨z, hz0, fun v hv => ?_⟩
  exact (Submodule.mem_orthogonal K z).1 hzK v (Submodule.subset_span hv)

private lemma open_mid (x z : EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    x ∈ openSegment ℝ (x + ε • z) (x - ε • z) := by
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [smul_add, smul_sub, smul_smul]; module

/-- An extreme point has at least `d` tight rows. -/
private lemma card_tset_of_extreme (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Set.extremePoints ℝ (Hpoly a b)) :
    d ≤ (tset a b x).card := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨z, hz0, hz⟩ := exists_orth ((tset a b x).image a)
    (lt_of_le_of_lt Finset.card_image_le hlt)
  obtain ⟨ε, hε, hp, hm⟩ := perturb a b hx.1 (z := z) (fun i hi =>
    hz _ (Finset.mem_image_of_mem a ((mem_tset a b x i).2 hi)))
  have := hx.2 hp hm (open_mid x z ε)
  have : ε • z = 0 := by
    have h' : x + ε • z - x = 0 := by rw [this, sub_self]
    simpa using h'
  rcases smul_eq_zero.1 this with h | h
  · exact hε.ne' h
  · exact hz0 h

private lemma adj_mem {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E} {x y : E}
    (h : Adj P x y) : x ∈ P ∧ y ∈ P :=
  ⟨h.2.subset (left_mem_segment ℝ x y), h.2.subset (right_mem_segment ℝ x y)⟩

private lemma left_extreme_segment {E : Type*} [AddCommGroup E] [Module ℝ E] (x y : E) :
    x ∈ Set.extremePoints ℝ (segment ℝ x y) := by
  refine ⟨left_mem_segment ℝ x y, ?_⟩
  rintro x1 ⟨p1, q1, hp1, hq1, hpq1, rfl⟩ x2 ⟨p2, q2, hp2, hq2, hpq2, rfl⟩
    ⟨s, t, hs, ht, hst, hx⟩
  have hp1' : p1 = 1 - q1 := by linarith
  have hp2' : p2 = 1 - q2 := by linarith
  have hs' : s = 1 - t := by linarith
  subst hp1' hp2' hs'
  have e : ((1 - t) * q1 + t * q2) • (y - x) = 0 := by
    have : ((1 - t) * q1 + t * q2) • (y - x) =
        (1 - t) • ((1 - q1) • x + q1 • y) + t • ((1 - q2) • x + q2 • y) - x := by module
    rw [this, hx, sub_self]
  rcases smul_eq_zero.1 e with h | h
  · have hq1 : q1 = 0 := by nlinarith [mul_nonneg hs.le hq1, mul_nonneg ht.le hq2]
    subst hq1; simp
  · have : y = x := (sub_eq_zero.1 h)
    subst this
    rw [← add_smul, sub_add_cancel, one_smul]

private lemma adj_extreme {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E} {x y : E}
    (h : Adj P x y) : x ∈ Set.extremePoints ℝ P ∧ y ∈ Set.extremePoints ℝ P := by
  refine ⟨h.2.extremePoints_subset_extremePoints (left_extreme_segment x y), ?_⟩
  have h2 : IsExtreme ℝ P (segment ℝ y x) := by rw [segment_symm]; exact h.2
  exact h2.extremePoints_subset_extremePoints (left_extreme_segment y x)

/-- Adjacent vertices share at least `d - 1` tight rows. -/
private lemma card_inter_of_adj (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x y : EuclideanSpace ℝ (Fin d)} (h : Adj (Hpoly a b) x y) :
    d ≤ (tset a b x ∩ tset a b y).card + 1 := by
  classical
  obtain ⟨hxP, hyP⟩ := adj_mem h
  set m : EuclideanSpace ℝ (Fin d) := (1/2 : ℝ) • x + (1/2 : ℝ) • y with hm
  have hmP : m ∈ Hpoly a b := by
    intro i
    have := hxP i; have := hyP i
    simp only [hm, inner_add_right, inner_smul_right]; linarith
  have hmseg : m ∈ segment ℝ x y := ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨z, hz0, hz⟩ := exists_orth (insert (y - x) ((tset a b x ∩ tset a b y).image a))
    (lt_of_le_of_lt (Finset.card_insert_le _ _)
      (by have := (Finset.card_image_le (s := tset a b x ∩ tset a b y) (f := a)); omega))
  obtain ⟨ε, hε, hp, hmn⟩ := perturb a b hmP (z := z) (fun i hi => by
    have hxi := hxP i; have hyi := hyP i
    simp only [hm, inner_add_right, inner_smul_right] at hi
    have h1 : ⟪a i, x⟫ = b i := by linarith
    have h2 : ⟪a i, y⟫ = b i := by linarith
    exact hz _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem a
      (Finset.mem_inter.2 ⟨(mem_tset a b x i).2 h1, (mem_tset a b y i).2 h2⟩))))
  have hseg := h.2.left_mem_of_mem_openSegment hp hmn hmseg (open_mid m z ε)
  obtain ⟨p, q, hp0, hq0, hpq, he⟩ := hseg
  have hzyx : ⟪y - x, z⟫ = 0 := hz _ (Finset.mem_insert_self _ _)
  -- ε z = p x + q y - m = (q - 1/2) (y - x)
  have hez : ε • z = (q - 1/2) • (y - x) := by
    have hp' : p = 1 - q := by linarith
    subst hp'
    have : m + ε • z - m = (1 - q) • x + q • y - m := by rw [he]
    rw [add_sub_cancel_left] at this
    rw [this, hm]; module
  have : ε * ⟪z, z⟫ = 0 := by
    calc ε * ⟪z, z⟫ = ⟪ε • z, z⟫ := (real_inner_smul_left _ _ _).symm
      _ = ⟪(q - 1/2) • (y - x), z⟫ := by rw [hez]
      _ = 0 := by rw [real_inner_smul_left, hzyx, mul_zero]
  have hzz : ⟪z, z⟫ = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hε.ne'
    · exact h
  exact hz0 (inner_self_eq_zero.1 hzz)

private lemma extreme_of_unique (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Hpoly a b)
    (h : ∀ y ∈ Hpoly a b, (∀ i ∈ tset a b x, ⟪a i, y⟫ = b i) → y = x) :
    x ∈ Set.extremePoints ℝ (Hpoly a b) := by
  refine ⟨hx, fun y1 hy1 y2 hy2 hseg => h y1 hy1 (fun i hi => ?_)⟩
  obtain ⟨s, t, hs, ht, hst, hxe⟩ := hseg
  have hi' := (mem_tset a b x i).1 hi
  have e : s * ⟪a i, y1⟫ + t * ⟪a i, y2⟫ = b i := by
    rw [← hi', ← hxe, inner_add_right, inner_smul_right, inner_smul_right]
  have h1 := hy1 i
  have h2 := hy2 i
  by_contra hne
  have hlt : ⟪a i, y1⟫ < b i := lt_of_le_of_ne h1 hne
  have e1 : s * ⟪a i, y1⟫ < s * b i := mul_lt_mul_of_pos_left hlt hs
  have e2 : t * ⟪a i, y2⟫ ≤ t * b i := mul_le_mul_of_nonneg_left h2 ht.le
  have e3 : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
  linarith

private lemma bounded_of_coord {S : Set (EuclideanSpace ℝ (Fin 4))} (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x ∈ S, ∀ j, |x j| ≤ M) : Bornology.IsBounded S := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨2 * M, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq := EuclideanSpace.real_norm_sq_eq x
  rw [Fin.sum_univ_four] at hsq
  have b0 := sq_le_sq' (abs_le.1 (h x hx 0)).1 (abs_le.1 (h x hx 0)).2
  have b1 := sq_le_sq' (abs_le.1 (h x hx 1)).1 (abs_le.1 (h x hx 1)).2
  have b2 := sq_le_sq' (abs_le.1 (h x hx 2)).1 (abs_le.1 (h x hx 2)).2
  have b3 := sq_le_sq' (abs_le.1 (h x hx 3)).1 (abs_le.1 (h x hx 3)).2
  nlinarith [norm_nonneg x]

private def Am : Fin 8 → Fin 4 → ℝ :=
  ![![8, 4, -6, -7],
    ![6, 3, -5, -7],
    ![8, 8, -7, -2],
    ![8, 8, -6, 0],
    ![8, -2, -8, 0],
    ![19, -1, -7, 10],
    ![15, -1, 0, 12],
    ![4, -1, -7, -2]]

private def aQ (i : Fin 8) : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 (Am i)

private def bQ : Fin 8 → ℝ := fun _ => 1

private lemma inner_aQ (i : Fin 8) (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪aQ i, x⟫ = Am i 0 * x 0 + Am i 1 * x 1 + Am i 2 * x 2 + Am i 3 * x 3 := by
  simp [aQ, PiLp.inner_apply, Fin.sum_univ_four, mul_comm]

private lemma r0 (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪aQ 0, x⟫ = (8) * x 0 + (4) * x 1 + (-6) * x 2 + (-7) * x 3 := by
  rw [inner_aQ]; rfl

private lemma r1 (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪aQ 1, x⟫ = (6) * x 0 + (3) * x 1 + (-5) * x 2 + (-7) * x 3 := by
  rw [inner_aQ]; rfl

private lemma r2 (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪aQ 2, x⟫ = (8) * x 0 + (8) * x 1 + (-7) * x 2 + (-2) * x 3 := by
  rw [inner_aQ]; rfl

private lemma r3 (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪aQ 3, x⟫ = (8) * x 0 + (8) * x 1 + (-6) * x 2 + (0) * x 3 := by
  rw [inner_aQ]; rfl

private lemma r4 (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪aQ 4, x⟫ = (8) * x 0 + (-2) * x 1 + (-8) * x 2 + (0) * x 3 := by
  rw [inner_aQ]; rfl

private lemma r5 (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪aQ 5, x⟫ = (19) * x 0 + (-1) * x 1 + (-7) * x 2 + (10) * x 3 := by
  rw [inner_aQ]; rfl

private lemma r6 (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪aQ 6, x⟫ = (15) * x 0 + (-1) * x 1 + (0) * x 2 + (12) * x 3 := by
  rw [inner_aQ]; rfl

private lemma r7 (x : EuclideanSpace ℝ (Fin 4)) :
    ⟪aQ 7, x⟫ = (4) * x 0 + (-1) * x 1 + (-7) * x 2 + (-2) * x 3 := by
  rw [inner_aQ]; rfl

private lemma memP {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ) :
    (8) * x 0 + (4) * x 1 + (-6) * x 2 + (-7) * x 3 ≤ 1 ∧
    (6) * x 0 + (3) * x 1 + (-5) * x 2 + (-7) * x 3 ≤ 1 ∧
    (8) * x 0 + (8) * x 1 + (-7) * x 2 + (-2) * x 3 ≤ 1 ∧
    (8) * x 0 + (8) * x 1 + (-6) * x 2 + (0) * x 3 ≤ 1 ∧
    (8) * x 0 + (-2) * x 1 + (-8) * x 2 + (0) * x 3 ≤ 1 ∧
    (19) * x 0 + (-1) * x 1 + (-7) * x 2 + (10) * x 3 ≤ 1 ∧
    (15) * x 0 + (-1) * x 1 + (0) * x 2 + (12) * x 3 ≤ 1 ∧
    (4) * x 0 + (-1) * x 1 + (-7) * x 2 + (-2) * x 3 ≤ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hx 0; rw [r0] at h; exact h
  · have h := hx 1; rw [r1] at h; exact h
  · have h := hx 2; rw [r2] at h; exact h
  · have h := hx 3; rw [r3] at h; exact h
  · have h := hx 4; rw [r4] at h; exact h
  · have h := hx 5; rw [r5] at h; exact h
  · have h := hx 6; rw [r6] at h; exact h
  · have h := hx 7; rw [r7] at h; exact h

private lemma nf0 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t0 : ⟪aQ 0, x⟫ = bQ 0) (t3 : ⟪aQ 3, x⟫ = bQ 3) (t4 : ⟪aQ 4, x⟫ = bQ 4) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r0] at t0; rw [r3] at t3; rw [r4] at t4
  simp only [bQ] at *
  linarith

private lemma nf1 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t0 : ⟪aQ 0, x⟫ = bQ 0) (t3 : ⟪aQ 3, x⟫ = bQ 3) (t5 : ⟪aQ 5, x⟫ = bQ 5) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r0] at t0; rw [r3] at t3; rw [r5] at t5
  simp only [bQ] at *
  linarith

private lemma nf2 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t0 : ⟪aQ 0, x⟫ = bQ 0) (t3 : ⟪aQ 3, x⟫ = bQ 3) (t7 : ⟪aQ 7, x⟫ = bQ 7) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r0] at t0; rw [r3] at t3; rw [r7] at t7
  simp only [bQ] at *
  linarith

private lemma nf3 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t0 : ⟪aQ 0, x⟫ = bQ 0) (t4 : ⟪aQ 4, x⟫ = bQ 4) (t6 : ⟪aQ 6, x⟫ = bQ 6) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r0] at t0; rw [r4] at t4; rw [r6] at t6
  simp only [bQ] at *
  linarith

private lemma nf4 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t0 : ⟪aQ 0, x⟫ = bQ 0) (t5 : ⟪aQ 5, x⟫ = bQ 5) (t7 : ⟪aQ 7, x⟫ = bQ 7) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r0] at t0; rw [r5] at t5; rw [r7] at t7
  simp only [bQ] at *
  linarith

private lemma nf5 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t0 : ⟪aQ 0, x⟫ = bQ 0) (t6 : ⟪aQ 6, x⟫ = bQ 6) (t7 : ⟪aQ 7, x⟫ = bQ 7) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r0] at t0; rw [r6] at t6; rw [r7] at t7
  simp only [bQ] at *
  linarith

private lemma nf6 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t1 : ⟪aQ 1, x⟫ = bQ 1) (t2 : ⟪aQ 2, x⟫ = bQ 2) (t4 : ⟪aQ 4, x⟫ = bQ 4) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r1] at t1; rw [r2] at t2; rw [r4] at t4
  simp only [bQ] at *
  linarith

private lemma nf7 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t1 : ⟪aQ 1, x⟫ = bQ 1) (t2 : ⟪aQ 2, x⟫ = bQ 2) (t5 : ⟪aQ 5, x⟫ = bQ 5) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r1] at t1; rw [r2] at t2; rw [r5] at t5
  simp only [bQ] at *
  linarith

private lemma nf8 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t1 : ⟪aQ 1, x⟫ = bQ 1) (t2 : ⟪aQ 2, x⟫ = bQ 2) (t6 : ⟪aQ 6, x⟫ = bQ 6) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r1] at t1; rw [r2] at t2; rw [r6] at t6
  simp only [bQ] at *
  linarith

private lemma nf9 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t1 : ⟪aQ 1, x⟫ = bQ 1) (t3 : ⟪aQ 3, x⟫ = bQ 3) (t4 : ⟪aQ 4, x⟫ = bQ 4) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r1] at t1; rw [r3] at t3; rw [r4] at t4
  simp only [bQ] at *
  linarith

private lemma nf10 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t1 : ⟪aQ 1, x⟫ = bQ 1) (t3 : ⟪aQ 3, x⟫ = bQ 3) (t5 : ⟪aQ 5, x⟫ = bQ 5) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r1] at t1; rw [r3] at t3; rw [r5] at t5
  simp only [bQ] at *
  linarith

private lemma nf11 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t1 : ⟪aQ 1, x⟫ = bQ 1) (t3 : ⟪aQ 3, x⟫ = bQ 3) (t6 : ⟪aQ 6, x⟫ = bQ 6) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r1] at t1; rw [r3] at t3; rw [r6] at t6
  simp only [bQ] at *
  linarith

private lemma nf12 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t1 : ⟪aQ 1, x⟫ = bQ 1) (t3 : ⟪aQ 3, x⟫ = bQ 3) (t7 : ⟪aQ 7, x⟫ = bQ 7) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r1] at t1; rw [r3] at t3; rw [r7] at t7
  simp only [bQ] at *
  linarith

private lemma nf13 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t1 : ⟪aQ 1, x⟫ = bQ 1) (t5 : ⟪aQ 5, x⟫ = bQ 5) (t7 : ⟪aQ 7, x⟫ = bQ 7) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r1] at t1; rw [r5] at t5; rw [r7] at t7
  simp only [bQ] at *
  linarith

private lemma nf14 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t1 : ⟪aQ 1, x⟫ = bQ 1) (t6 : ⟪aQ 6, x⟫ = bQ 6) (t7 : ⟪aQ 7, x⟫ = bQ 7) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r1] at t1; rw [r6] at t6; rw [r7] at t7
  simp only [bQ] at *
  linarith

private lemma nf15 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t2 : ⟪aQ 2, x⟫ = bQ 2) (t4 : ⟪aQ 4, x⟫ = bQ 4) (t6 : ⟪aQ 6, x⟫ = bQ 6) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r2] at t2; rw [r4] at t4; rw [r6] at t6
  simp only [bQ] at *
  linarith

private lemma nf16 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t2 : ⟪aQ 2, x⟫ = bQ 2) (t5 : ⟪aQ 5, x⟫ = bQ 5) (t7 : ⟪aQ 7, x⟫ = bQ 7) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r2] at t2; rw [r5] at t5; rw [r7] at t7
  simp only [bQ] at *
  linarith

private lemma nf17 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t2 : ⟪aQ 2, x⟫ = bQ 2) (t6 : ⟪aQ 6, x⟫ = bQ 6) (t7 : ⟪aQ 7, x⟫ = bQ 7) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r2] at t2; rw [r6] at t6; rw [r7] at t7
  simp only [bQ] at *
  linarith

private lemma nf18 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t3 : ⟪aQ 3, x⟫ = bQ 3) (t4 : ⟪aQ 4, x⟫ = bQ 4) (t6 : ⟪aQ 6, x⟫ = bQ 6) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r3] at t3; rw [r4] at t4; rw [r6] at t6
  simp only [bQ] at *
  linarith

private lemma nf19 {x : EuclideanSpace ℝ (Fin 4)} (hx : x ∈ Hirsch.Hpoly aQ bQ)
    (t3 : ⟪aQ 3, x⟫ = bQ 3) (t6 : ⟪aQ 6, x⟫ = bQ 6) (t7 : ⟪aQ 7, x⟫ = bQ 7) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := memP hx
  rw [r3] at t3; rw [r6] at t6; rw [r7] at t7
  simp only [bQ] at *
  linarith

private lemma no_small {x : EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ Set.extremePoints ℝ (Hirsch.Hpoly aQ bQ)) (R : Finset (Fin 8))
    (hR : 8 < R.card + 4) (h : ∀ i ∈ R, ⟪aQ i, x⟫ ≠ bQ i) : False := by
  have h1 := card_tset_of_extreme aQ bQ hx
  have h2 : tset aQ bQ x ⊆ Rᶜ := fun i hi =>
    Finset.mem_compl.2 (fun hR' => h i hR' ((mem_tset _ _ _ _).1 hi))
  have h3 := Finset.card_le_card h2
  rw [Finset.card_compl, Fintype.card_fin] at h3
  omega

private def Vt : Fin 15 → Finset (Fin 8) :=
  ![{0, 1, 2, 3},
    {0, 1, 2, 7},
    {0, 1, 4, 5},
    {0, 1, 4, 7},
    {0, 1, 5, 6},
    {0, 2, 3, 6},
    {0, 2, 4, 5},
    {0, 2, 4, 7},
    {0, 2, 5, 6},
    {1, 4, 5, 6},
    {2, 3, 4, 5},
    {2, 3, 4, 7},
    {2, 3, 5, 6},
    {3, 4, 5, 7},
    {4, 5, 6, 7}]

private def dl : Fin 15 → ℕ :=
  ![0, 1, 3, 2, 3, 1, 3, 2, 2, 4, 3, 3, 2, 4, 5]

set_option maxHeartbeats 20000000 in
private lemma classify {x : EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ Set.extremePoints ℝ (Hirsch.Hpoly aQ bQ)) :
    ∃ k : Fin 15, tset aQ bQ x = Vt k := by
  by_cases t0 : ⟪aQ 0, x⟫ = bQ 0
  · by_cases t1 : ⟪aQ 1, x⟫ = bQ 1
    · by_cases t2 : ⟪aQ 2, x⟫ = bQ 2
      · by_cases t3 : ⟪aQ 3, x⟫ = bQ 3
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · exact (nf0 hx.1 t0 t3 t4).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · exact (nf1 hx.1 t0 t3 t5).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf8 hx.1 t1 t2 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf2 hx.1 t0 t3 t7).elim
                · have e : tset aQ bQ x = ({0, 1, 2, 3} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨0, e⟩
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · exact (nf6 hx.1 t1 t2 t4).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · exact (nf7 hx.1 t1 t2 t5).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf8 hx.1 t1 t2 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · have e : tset aQ bQ x = ({0, 1, 2, 7} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨1, e⟩
                · exact (no_small hx {3, 4, 5, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
      · by_cases t3 : ⟪aQ 3, x⟫ = bQ 3
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · exact (nf0 hx.1 t0 t3 t4).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · exact (nf1 hx.1 t0 t3 t5).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf11 hx.1 t1 t3 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf2 hx.1 t0 t3 t7).elim
                · exact (no_small hx {2, 4, 5, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf3 hx.1 t0 t4 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf4 hx.1 t0 t5 t7).elim
                · have e : tset aQ bQ x = ({0, 1, 4, 5} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨2, e⟩
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf3 hx.1 t0 t4 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · have e : tset aQ bQ x = ({0, 1, 4, 7} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨3, e⟩
                · exact (no_small hx {2, 3, 5, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf4 hx.1 t0 t5 t7).elim
                · have e : tset aQ bQ x = ({0, 1, 5, 6} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨4, e⟩
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf4 hx.1 t0 t5 t7).elim
                · exact (no_small hx {2, 3, 4, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf5 hx.1 t0 t6 t7).elim
                · exact (no_small hx {2, 3, 4, 5, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
              · exact (no_small hx {2, 3, 4, 5, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
    · by_cases t2 : ⟪aQ 2, x⟫ = bQ 2
      · by_cases t3 : ⟪aQ 3, x⟫ = bQ 3
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · exact (nf0 hx.1 t0 t3 t4).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · exact (nf1 hx.1 t0 t3 t5).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf2 hx.1 t0 t3 t7).elim
                · have e : tset aQ bQ x = ({0, 2, 3, 6} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨5, e⟩
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf2 hx.1 t0 t3 t7).elim
                · exact (no_small hx {1, 4, 5, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf3 hx.1 t0 t4 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf4 hx.1 t0 t5 t7).elim
                · have e : tset aQ bQ x = ({0, 2, 4, 5} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨6, e⟩
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf3 hx.1 t0 t4 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · have e : tset aQ bQ x = ({0, 2, 4, 7} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨7, e⟩
                · exact (no_small hx {1, 3, 5, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf4 hx.1 t0 t5 t7).elim
                · have e : tset aQ bQ x = ({0, 2, 5, 6} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨8, e⟩
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf4 hx.1 t0 t5 t7).elim
                · exact (no_small hx {1, 3, 4, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf5 hx.1 t0 t6 t7).elim
                · exact (no_small hx {1, 3, 4, 5, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
              · exact (no_small hx {1, 3, 4, 5, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
      · by_cases t3 : ⟪aQ 3, x⟫ = bQ 3
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · exact (nf0 hx.1 t0 t3 t4).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · exact (nf1 hx.1 t0 t3 t5).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf2 hx.1 t0 t3 t7).elim
                · exact (no_small hx {1, 2, 4, 5, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
              · exact (no_small hx {1, 2, 4, 5, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf3 hx.1 t0 t4 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf4 hx.1 t0 t5 t7).elim
                · exact (no_small hx {1, 2, 3, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf3 hx.1 t0 t4 t6).elim
              · exact (no_small hx {1, 2, 3, 5, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf4 hx.1 t0 t5 t7).elim
                · exact (no_small hx {1, 2, 3, 4, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
              · exact (no_small hx {1, 2, 3, 4, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · exact (no_small hx {1, 2, 3, 4, 5} (by decide) (by
                intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
  · by_cases t1 : ⟪aQ 1, x⟫ = bQ 1
    · by_cases t2 : ⟪aQ 2, x⟫ = bQ 2
      · by_cases t3 : ⟪aQ 3, x⟫ = bQ 3
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · exact (nf6 hx.1 t1 t2 t4).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · exact (nf7 hx.1 t1 t2 t5).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf8 hx.1 t1 t2 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf12 hx.1 t1 t3 t7).elim
                · exact (no_small hx {0, 4, 5, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · exact (nf6 hx.1 t1 t2 t4).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · exact (nf7 hx.1 t1 t2 t5).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf8 hx.1 t1 t2 t6).elim
              · exact (no_small hx {0, 3, 4, 5, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
      · by_cases t3 : ⟪aQ 3, x⟫ = bQ 3
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · exact (nf9 hx.1 t1 t3 t4).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · exact (nf10 hx.1 t1 t3 t5).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf11 hx.1 t1 t3 t6).elim
              · exact (no_small hx {0, 2, 4, 5, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf13 hx.1 t1 t5 t7).elim
                · have e : tset aQ bQ x = ({1, 4, 5, 6} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨9, e⟩
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf13 hx.1 t1 t5 t7).elim
                · exact (no_small hx {0, 2, 3, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf14 hx.1 t1 t6 t7).elim
                · exact (no_small hx {0, 2, 3, 5, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
              · exact (no_small hx {0, 2, 3, 5, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf13 hx.1 t1 t5 t7).elim
                · exact (no_small hx {0, 2, 3, 4, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
              · exact (no_small hx {0, 2, 3, 4, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · exact (no_small hx {0, 2, 3, 4, 5} (by decide) (by
                intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
    · by_cases t2 : ⟪aQ 2, x⟫ = bQ 2
      · by_cases t3 : ⟪aQ 3, x⟫ = bQ 3
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf15 hx.1 t2 t4 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf16 hx.1 t2 t5 t7).elim
                · have e : tset aQ bQ x = ({2, 3, 4, 5} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨10, e⟩
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf15 hx.1 t2 t4 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · have e : tset aQ bQ x = ({2, 3, 4, 7} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨11, e⟩
                · exact (no_small hx {0, 1, 5, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf16 hx.1 t2 t5 t7).elim
                · have e : tset aQ bQ x = ({2, 3, 5, 6} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨12, e⟩
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf16 hx.1 t2 t5 t7).elim
                · exact (no_small hx {0, 1, 4, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf17 hx.1 t2 t6 t7).elim
                · exact (no_small hx {0, 1, 4, 5, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
              · exact (no_small hx {0, 1, 4, 5, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf15 hx.1 t2 t4 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf16 hx.1 t2 t5 t7).elim
                · exact (no_small hx {0, 1, 3, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf15 hx.1 t2 t4 t6).elim
              · exact (no_small hx {0, 1, 3, 5, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf16 hx.1 t2 t5 t7).elim
                · exact (no_small hx {0, 1, 3, 4, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
              · exact (no_small hx {0, 1, 3, 4, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · exact (no_small hx {0, 1, 3, 4, 5} (by decide) (by
                intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
      · by_cases t3 : ⟪aQ 3, x⟫ = bQ 3
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf18 hx.1 t3 t4 t6).elim
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · have e : tset aQ bQ x = ({3, 4, 5, 7} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨13, e⟩
                · exact (no_small hx {0, 1, 2, 6, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · exact (nf18 hx.1 t3 t4 t6).elim
              · exact (no_small hx {0, 1, 2, 5, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · exact (nf19 hx.1 t3 t6 t7).elim
                · exact (no_small hx {0, 1, 2, 4, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
              · exact (no_small hx {0, 1, 2, 4, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · exact (no_small hx {0, 1, 2, 4, 5} (by decide) (by
                intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
        · by_cases t4 : ⟪aQ 4, x⟫ = bQ 4
          · by_cases t5 : ⟪aQ 5, x⟫ = bQ 5
            · by_cases t6 : ⟪aQ 6, x⟫ = bQ 6
              · by_cases t7 : ⟪aQ 7, x⟫ = bQ 7
                · have e : tset aQ bQ x = ({4, 5, 6, 7} : Finset (Fin 8)) := by
                    ext j; fin_cases j <;> simp [mem_tset, t0, t1, t2, t3, t4, t5, t6, t7]
                  exact ⟨14, e⟩
                · exact (no_small hx {0, 1, 2, 3, 7} (by decide) (by
                    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
              · exact (no_small hx {0, 1, 2, 3, 6} (by decide) (by
                  intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
            · exact (no_small hx {0, 1, 2, 3, 5} (by decide) (by
                intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
                rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim
          · exact (no_small hx {0, 1, 2, 3, 4} (by decide) (by
              intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
              rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption)).elim

set_option maxRecDepth 100000 in
private lemma key : ∀ k l : Fin 15, 4 ≤ (Vt k ∩ Vt l).card + 1 → dl l ≤ dl k + 1 := by
  decide

private lemma vlem : ∀ k : Fin 15, Vt k = {4, 5, 6, 7} → dl k = 5 := by
  decide

private noncomputable def uQ : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 ![1/24, 7/12, 2/3, -1/3]

private noncomputable def vQ : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 ![-7/4, -1, -13/8, 35/16]

private lemma uP : uQ ∈ Hirsch.Hpoly aQ bQ := by
  show ∀ i, ⟪aQ i, uQ⟫ ≤ bQ i
  intro i; fin_cases i
  · show ⟪aQ 0, uQ⟫ ≤ bQ 0
    rw [r0]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 1, uQ⟫ ≤ bQ 1
    rw [r1]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 2, uQ⟫ ≤ bQ 2
    rw [r2]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 3, uQ⟫ ≤ bQ 3
    rw [r3]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 4, uQ⟫ ≤ bQ 4
    rw [r4]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 5, uQ⟫ ≤ bQ 5
    rw [r5]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 6, uQ⟫ ≤ bQ 6
    rw [r6]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 7, uQ⟫ ≤ bQ 7
    rw [r7]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num

private lemma tset_u : tset aQ bQ uQ = ({0, 1, 2, 3} : Finset (Fin 8)) := by
  ext j; rw [mem_tset]; fin_cases j
  · show ⟪aQ 0, uQ⟫ = bQ 0 ↔ (0 : Fin 8) ∈ ({0, 1, 2, 3} : Finset (Fin 8))
    rw [r0]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 1, uQ⟫ = bQ 1 ↔ (1 : Fin 8) ∈ ({0, 1, 2, 3} : Finset (Fin 8))
    rw [r1]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 2, uQ⟫ = bQ 2 ↔ (2 : Fin 8) ∈ ({0, 1, 2, 3} : Finset (Fin 8))
    rw [r2]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 3, uQ⟫ = bQ 3 ↔ (3 : Fin 8) ∈ ({0, 1, 2, 3} : Finset (Fin 8))
    rw [r3]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 4, uQ⟫ = bQ 4 ↔ (4 : Fin 8) ∈ ({0, 1, 2, 3} : Finset (Fin 8))
    rw [r4]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 5, uQ⟫ = bQ 5 ↔ (5 : Fin 8) ∈ ({0, 1, 2, 3} : Finset (Fin 8))
    rw [r5]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 6, uQ⟫ = bQ 6 ↔ (6 : Fin 8) ∈ ({0, 1, 2, 3} : Finset (Fin 8))
    rw [r6]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 7, uQ⟫ = bQ 7 ↔ (7 : Fin 8) ∈ ({0, 1, 2, 3} : Finset (Fin 8))
    rw [r7]; simp only [uQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide

private lemma u_unique (y : EuclideanSpace ℝ (Fin 4)) (h0 : ⟪aQ 0, y⟫ = bQ 0) (h1 : ⟪aQ 1, y⟫ = bQ 1) (h2 : ⟪aQ 2, y⟫ = bQ 2) (h3 : ⟪aQ 3, y⟫ = bQ 3) : y = uQ := by
  rw [r0] at h0; rw [r1] at h1; rw [r2] at h2; rw [r3] at h3
  simp only [bQ] at h0 h1 h2 h3
  ext j; fin_cases j
  · show y 0 = uQ 0
    simp only [uQ, PiLp.toLp_apply, Matrix.cons_val]; linarith
  · show y 1 = uQ 1
    simp only [uQ, PiLp.toLp_apply, Matrix.cons_val]; linarith
  · show y 2 = uQ 2
    simp only [uQ, PiLp.toLp_apply, Matrix.cons_val]; linarith
  · show y 3 = uQ 3
    simp only [uQ, PiLp.toLp_apply, Matrix.cons_val]; linarith

private lemma uExt : uQ ∈ Set.extremePoints ℝ (Hirsch.Hpoly aQ bQ) :=
  extreme_of_unique aQ bQ uP (fun y _ hy => u_unique y (hy 0 (by rw [tset_u]; decide)) (hy 1 (by rw [tset_u]; decide)) (hy 2 (by rw [tset_u]; decide)) (hy 3 (by rw [tset_u]; decide)))

private lemma vP : vQ ∈ Hirsch.Hpoly aQ bQ := by
  show ∀ i, ⟪aQ i, vQ⟫ ≤ bQ i
  intro i; fin_cases i
  · show ⟪aQ 0, vQ⟫ ≤ bQ 0
    rw [r0]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 1, vQ⟫ ≤ bQ 1
    rw [r1]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 2, vQ⟫ ≤ bQ 2
    rw [r2]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 3, vQ⟫ ≤ bQ 3
    rw [r3]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 4, vQ⟫ ≤ bQ 4
    rw [r4]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 5, vQ⟫ ≤ bQ 5
    rw [r5]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 6, vQ⟫ ≤ bQ 6
    rw [r6]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · show ⟪aQ 7, vQ⟫ ≤ bQ 7
    rw [r7]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num

private lemma tset_v : tset aQ bQ vQ = ({4, 5, 6, 7} : Finset (Fin 8)) := by
  ext j; rw [mem_tset]; fin_cases j
  · show ⟪aQ 0, vQ⟫ = bQ 0 ↔ (0 : Fin 8) ∈ ({4, 5, 6, 7} : Finset (Fin 8))
    rw [r0]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 1, vQ⟫ = bQ 1 ↔ (1 : Fin 8) ∈ ({4, 5, 6, 7} : Finset (Fin 8))
    rw [r1]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 2, vQ⟫ = bQ 2 ↔ (2 : Fin 8) ∈ ({4, 5, 6, 7} : Finset (Fin 8))
    rw [r2]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 3, vQ⟫ = bQ 3 ↔ (3 : Fin 8) ∈ ({4, 5, 6, 7} : Finset (Fin 8))
    rw [r3]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 4, vQ⟫ = bQ 4 ↔ (4 : Fin 8) ∈ ({4, 5, 6, 7} : Finset (Fin 8))
    rw [r4]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 5, vQ⟫ = bQ 5 ↔ (5 : Fin 8) ∈ ({4, 5, 6, 7} : Finset (Fin 8))
    rw [r5]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 6, vQ⟫ = bQ 6 ↔ (6 : Fin 8) ∈ ({4, 5, 6, 7} : Finset (Fin 8))
    rw [r6]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide
  · show ⟪aQ 7, vQ⟫ = bQ 7 ↔ (7 : Fin 8) ∈ ({4, 5, 6, 7} : Finset (Fin 8))
    rw [r7]; simp only [vQ, bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num <;> decide

private lemma v_unique (y : EuclideanSpace ℝ (Fin 4)) (h4 : ⟪aQ 4, y⟫ = bQ 4) (h5 : ⟪aQ 5, y⟫ = bQ 5) (h6 : ⟪aQ 6, y⟫ = bQ 6) (h7 : ⟪aQ 7, y⟫ = bQ 7) : y = vQ := by
  rw [r4] at h4; rw [r5] at h5; rw [r6] at h6; rw [r7] at h7
  simp only [bQ] at h4 h5 h6 h7
  ext j; fin_cases j
  · show y 0 = vQ 0
    simp only [vQ, PiLp.toLp_apply, Matrix.cons_val]; linarith
  · show y 1 = vQ 1
    simp only [vQ, PiLp.toLp_apply, Matrix.cons_val]; linarith
  · show y 2 = vQ 2
    simp only [vQ, PiLp.toLp_apply, Matrix.cons_val]; linarith
  · show y 3 = vQ 3
    simp only [vQ, PiLp.toLp_apply, Matrix.cons_val]; linarith

private lemma vExt : vQ ∈ Set.extremePoints ℝ (Hirsch.Hpoly aQ bQ) :=
  extreme_of_unique aQ bQ vP (fun y _ hy => v_unique y (hy 4 (by rw [tset_v]; decide)) (hy 5 (by rw [tset_v]; decide)) (hy 6 (by rw [tset_v]; decide)) (hy 7 (by rw [tset_v]; decide)))

private lemma notReach : ∀ k < 5, ¬ Hirsch.Reach (Hirsch.Hpoly aQ bQ) k uQ vQ := by
  rintro K hK ⟨w, hw0, hwK, hstep⟩
  have claim : ∀ i ≤ K, w i ∈ Set.extremePoints ℝ (Hirsch.Hpoly aQ bQ) ∧
      ∃ k, tset aQ bQ (w i) = Vt k ∧ dl k ≤ i := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hw0]
      exact ⟨uExt, 0, tset_u, by decide⟩
    | succ i ih =>
      intro hi
      obtain ⟨hext, k, hk, hdk⟩ := ih (by omega)
      rcases hstep i (by omega) with h | h
      · rw [← h]; exact ⟨hext, k, hk, by omega⟩
      · have he := (adj_extreme h).2
        obtain ⟨l, hl⟩ := classify he
        refine ⟨he, l, hl, ?_⟩
        have h4 := card_inter_of_adj aQ bQ h
        rw [hk, hl] at h4
        have := key k l h4
        omega
  obtain ⟨_, k, hk, hdk⟩ := claim K le_rfl
  rw [hwK, tset_v] at hk
  have := vlem k hk.symm
  omega

private lemma irrQ : ∀ i, ∃ x : EuclideanSpace ℝ (Fin 4),
    (∀ j, j ≠ i → ⟪aQ j, x⟫ ≤ bQ j) ∧ bQ i < ⟪aQ i, x⟫ := by
  intro i; fin_cases i
  · refine ⟨WithLp.toLp 2 ![3/50, 1/50, 3/50, -3/25], fun j hj => ?_, ?_⟩
    · fin_cases j
      · exact absurd rfl hj
      · show ⟪aQ 1, _⟫ ≤ bQ 1
        rw [r1]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 2, _⟫ ≤ bQ 2
        rw [r2]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 3, _⟫ ≤ bQ 3
        rw [r3]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 4, _⟫ ≤ bQ 4
        rw [r4]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 5, _⟫ ≤ bQ 5
        rw [r5]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 6, _⟫ ≤ bQ 6
        rw [r6]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 7, _⟫ ≤ bQ 7
        rw [r7]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show bQ 0 < ⟪aQ 0, _⟫
      rw [r0]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · refine ⟨WithLp.toLp 2 ![11/128, -7/128, 9/64, -25/128], fun j hj => ?_, ?_⟩
    · fin_cases j
      · show ⟪aQ 0, _⟫ ≤ bQ 0
        rw [r0]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · exact absurd rfl hj
      · show ⟪aQ 2, _⟫ ≤ bQ 2
        rw [r2]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 3, _⟫ ≤ bQ 3
        rw [r3]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 4, _⟫ ≤ bQ 4
        rw [r4]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 5, _⟫ ≤ bQ 5
        rw [r5]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 6, _⟫ ≤ bQ 6
        rw [r6]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 7, _⟫ ≤ bQ 7
        rw [r7]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show bQ 1 < ⟪aQ 1, _⟫
      rw [r1]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · refine ⟨WithLp.toLp 2 ![0, 1/8, 0, -1/16], fun j hj => ?_, ?_⟩
    · fin_cases j
      · show ⟪aQ 0, _⟫ ≤ bQ 0
        rw [r0]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 1, _⟫ ≤ bQ 1
        rw [r1]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · exact absurd rfl hj
      · show ⟪aQ 3, _⟫ ≤ bQ 3
        rw [r3]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 4, _⟫ ≤ bQ 4
        rw [r4]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 5, _⟫ ≤ bQ 5
        rw [r5]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 6, _⟫ ≤ bQ 6
        rw [r6]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 7, _⟫ ≤ bQ 7
        rw [r7]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show bQ 2 < ⟪aQ 2, _⟫
      rw [r2]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · refine ⟨WithLp.toLp 2 ![-3/200, 3/20, 1/100, 1/200], fun j hj => ?_, ?_⟩
    · fin_cases j
      · show ⟪aQ 0, _⟫ ≤ bQ 0
        rw [r0]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 1, _⟫ ≤ bQ 1
        rw [r1]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 2, _⟫ ≤ bQ 2
        rw [r2]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · exact absurd rfl hj
      · show ⟪aQ 4, _⟫ ≤ bQ 4
        rw [r4]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 5, _⟫ ≤ bQ 5
        rw [r5]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 6, _⟫ ≤ bQ 6
        rw [r6]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 7, _⟫ ≤ bQ 7
        rw [r7]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show bQ 3 < ⟪aQ 3, _⟫
      rw [r3]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · refine ⟨WithLp.toLp 2 ![-3/16, -3/16, -9/32, 7/32], fun j hj => ?_, ?_⟩
    · fin_cases j
      · show ⟪aQ 0, _⟫ ≤ bQ 0
        rw [r0]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 1, _⟫ ≤ bQ 1
        rw [r1]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 2, _⟫ ≤ bQ 2
        rw [r2]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 3, _⟫ ≤ bQ 3
        rw [r3]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · exact absurd rfl hj
      · show ⟪aQ 5, _⟫ ≤ bQ 5
        rw [r5]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 6, _⟫ ≤ bQ 6
        rw [r6]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 7, _⟫ ≤ bQ 7
        rw [r7]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show bQ 4 < ⟪aQ 4, _⟫
      rw [r4]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · refine ⟨WithLp.toLp 2 ![-3/25, -4/25, -1/5, 1/5], fun j hj => ?_, ?_⟩
    · fin_cases j
      · show ⟪aQ 0, _⟫ ≤ bQ 0
        rw [r0]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 1, _⟫ ≤ bQ 1
        rw [r1]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 2, _⟫ ≤ bQ 2
        rw [r2]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 3, _⟫ ≤ bQ 3
        rw [r3]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 4, _⟫ ≤ bQ 4
        rw [r4]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · exact absurd rfl hj
      · show ⟪aQ 6, _⟫ ≤ bQ 6
        rw [r6]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 7, _⟫ ≤ bQ 7
        rw [r7]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show bQ 5 < ⟪aQ 5, _⟫
      rw [r5]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · refine ⟨WithLp.toLp 2 ![-21/128, -59/256, -43/256, 69/256], fun j hj => ?_, ?_⟩
    · fin_cases j
      · show ⟪aQ 0, _⟫ ≤ bQ 0
        rw [r0]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 1, _⟫ ≤ bQ 1
        rw [r1]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 2, _⟫ ≤ bQ 2
        rw [r2]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 3, _⟫ ≤ bQ 3
        rw [r3]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 4, _⟫ ≤ bQ 4
        rw [r4]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 5, _⟫ ≤ bQ 5
        rw [r5]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · exact absurd rfl hj
      · show ⟪aQ 7, _⟫ ≤ bQ 7
        rw [r7]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show bQ 6 < ⟪aQ 6, _⟫
      rw [r6]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  · refine ⟨WithLp.toLp 2 ![-9/25, -4/25, -11/25, 9/25], fun j hj => ?_, ?_⟩
    · fin_cases j
      · show ⟪aQ 0, _⟫ ≤ bQ 0
        rw [r0]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 1, _⟫ ≤ bQ 1
        rw [r1]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 2, _⟫ ≤ bQ 2
        rw [r2]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 3, _⟫ ≤ bQ 3
        rw [r3]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 4, _⟫ ≤ bQ 4
        rw [r4]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 5, _⟫ ≤ bQ 5
        rw [r5]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · show ⟪aQ 6, _⟫ ≤ bQ 6
        rw [r6]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
      · exact absurd rfl hj
    · show bQ 7 < ⟪aQ 7, _⟫
      rw [r7]; simp only [bQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num

private lemma intQ : (interior (Hirsch.Hpoly aQ bQ)).Nonempty := by
  refine ⟨0, mem_interior.2 ⟨Metric.ball 0 (1 / 38), fun x hx => ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by norm_num)⟩⟩
  rw [Metric.mem_ball, dist_zero_right] at hx
  have c : ∀ j, |x j| < 1 / 38 := fun j =>
    lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x j) hx
  have c0 := abs_lt.1 (c 0); have c1 := abs_lt.1 (c 1)
  have c2 := abs_lt.1 (c 2); have c3 := abs_lt.1 (c 3)
  show ∀ i, ⟪aQ i, x⟫ ≤ bQ i
  intro i; fin_cases i
  · show ⟪aQ 0, x⟫ ≤ bQ 0
    rw [r0]; simp only [bQ]; linarith [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]
  · show ⟪aQ 1, x⟫ ≤ bQ 1
    rw [r1]; simp only [bQ]; linarith [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]
  · show ⟪aQ 2, x⟫ ≤ bQ 2
    rw [r2]; simp only [bQ]; linarith [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]
  · show ⟪aQ 3, x⟫ ≤ bQ 3
    rw [r3]; simp only [bQ]; linarith [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]
  · show ⟪aQ 4, x⟫ ≤ bQ 4
    rw [r4]; simp only [bQ]; linarith [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]
  · show ⟪aQ 5, x⟫ ≤ bQ 5
    rw [r5]; simp only [bQ]; linarith [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]
  · show ⟪aQ 6, x⟫ ≤ bQ 6
    rw [r6]; simp only [bQ]; linarith [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]
  · show ⟪aQ 7, x⟫ ≤ bQ 7
    rw [r7]; simp only [bQ]; linarith [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]

private lemma cardVt : ∀ k : Fin 15, (Vt k).card = 4 := by
  decide

private lemma simpleU : KleeWalkup67.FiveStep.IsSimple aQ bQ := by
  refine ⟨⟨uQ, uExt⟩, fun x hx => ?_⟩
  have e : KleeWalkup67.FiveStep.TightSet aQ bQ x = ↑(tset aQ bQ x) := by
    ext i; simp [KleeWalkup67.FiveStep.TightSet, mem_tset]
  obtain ⟨k, hk⟩ := classify hx
  rw [e, Set.ncard_coe_finset, hk, cardVt]

private noncomputable def zQ : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 ![-1, 4, 4, -2]

private lemma ray (t : ℝ) (ht : 0 ≤ t) : t • zQ ∈ Hirsch.Hpoly aQ bQ := by
  have hz : ∀ i, ⟪aQ i, zQ⟫ ≤ 0 := by
    intro i; fin_cases i
    · show ⟪aQ 0, zQ⟫ ≤ 0
      rw [r0]; simp only [zQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show ⟪aQ 1, zQ⟫ ≤ 0
      rw [r1]; simp only [zQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show ⟪aQ 2, zQ⟫ ≤ 0
      rw [r2]; simp only [zQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show ⟪aQ 3, zQ⟫ ≤ 0
      rw [r3]; simp only [zQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show ⟪aQ 4, zQ⟫ ≤ 0
      rw [r4]; simp only [zQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show ⟪aQ 5, zQ⟫ ≤ 0
      rw [r5]; simp only [zQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show ⟪aQ 6, zQ⟫ ≤ 0
      rw [r6]; simp only [zQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
    · show ⟪aQ 7, zQ⟫ ≤ 0
      rw [r7]; simp only [zQ, PiLp.toLp_apply, Matrix.cons_val] <;> norm_num
  show ∀ i, ⟪aQ i, t • zQ⟫ ≤ bQ i
  intro i
  rw [inner_smul_right]
  have := mul_nonpos_of_nonneg_of_nonpos ht (hz i)
  simp only [bQ]; linarith

private lemma unbddU : ¬ Bornology.IsBounded (Hirsch.Hpoly aQ bQ) := by
  intro h
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 h
  set t : ℝ := max R 0 + 1 with ht
  have h1 := hR (ray t (by positivity))
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 := PiLp.norm_apply_le (t • zQ) 0
  have h3 : (t • zQ) 0 = t * (-1) := by
    simp [zQ]
  rw [h3, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < t)] at h2
  have h4 : t ≤ R := by
    have : (1:ℝ) ≤ |(-1 : ℝ)| := by norm_num
    nlinarith [le_max_left R 0, le_max_right R 0]
  linarith [le_max_left R 0]

theorem solution :
    ∃ (a : Fin 8 → EuclideanSpace ℝ (Fin 4)) (b : Fin 8 → ℝ)
      (u v : EuclideanSpace ℝ (Fin 4)),
      KleeWalkup67.FiveStep.IsFacetPresentation a b ∧
      KleeWalkup67.FiveStep.IsSimple a b ∧
      ¬ Bornology.IsBounded (Hirsch.Hpoly a b) ∧
      u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧
      v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧
      ∀ k < 5, ¬ Hirsch.Reach (Hirsch.Hpoly a b) k u v :=
  ⟨aQ, bQ, uQ, vQ, ⟨intQ, irrQ⟩, simpleU, unbddU, uExt, vExt, notReach⟩
