-- Prove2me | solution 1 for GeomDL.Cotangent.intrinsic_cotangent_weights
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:12:25.017049+00:00
-- url     : https://prove2.me/submissions/3ccbda94-8a54-4a6a-ba10-b28fd1a03f6c

import Mathlib
import Definitions.Def_GeomDL_Cotangent_Defs

open EuclideanGeometry GeomDL.Cotangent

theorem pair_eq_pair_iff' {n : ℕ} {x y z w : Fin n} :
    ({x, y} : Finset (Fin n)) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  rw [← Finset.coe_inj, Finset.coe_pair, Finset.coe_pair, Set.pair_eq_pair_iff]

theorem triple_cases {n : ℕ} {a b c u v q : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h : ({a, b, c} : Finset (Fin n)) = {u, v, q}) :
    (a = u ∨ a = v ∨ a = q) ∧ (b = u ∨ b = v ∨ b = q) ∧ (c = u ∨ c = v ∨ c = q) ∧
    (u = a ∨ u = b ∨ u = c) ∧ (v = a ∨ v = b ∨ v = c) ∧ (q = a ∨ q = b ∨ q = c) := by
  have mem : ∀ y, (y = a ∨ y = b ∨ y = c) ↔ (y = u ∨ y = v ∨ y = q) := by
    intro y
    have := congrArg (y ∈ ·) h
    simpa using this
  refine ⟨(mem a).1 (by simp), (mem b).1 (by simp), (mem c).1 (by simp),
    (mem u).2 (by simp), (mem v).2 (by simp), (mem q).2 (by simp)⟩

theorem triple_third_ne {n : ℕ} {a b c u v q : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h : ({a, b, c} : Finset (Fin n)) = {u, v, q}) : q ≠ u ∧ q ≠ v := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := triple_cases hab hbc hac h
  constructor <;> rintro rfl <;>
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    rcases h3 with rfl | rfl | rfl <;> simp_all

theorem cotOpp_face {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {n : ℕ} (x : Fin n → P)
    (t : Fin n × Fin n × Fin n) (ht : t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)
    {u v q : Fin n} (huv : u ≠ v) (hvs : vertexSet t = {u, v, q}) :
    cotOpp x t u v = Real.cot (∠ (x u) (x q) (x v)) := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨hab, hbc, hac⟩ := ht
  simp only [vertexSet] at hvs hab hbc hac
  obtain ⟨h1, h2, h3, -, -, -⟩ := triple_cases hab hbc hac hvs
  have hq := triple_third_ne hab hbc hac hvs
  have hq1 := hq.1.symm
  have hq2 := hq.2.symm
  have huv' := huv.symm
  have hab' := hab.symm
  have hbc' := hbc.symm
  have hac' := hac.symm
  simp only [cotOpp, pair_eq_pair_iff']
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    rcases h3 with rfl | rfl | rfl <;> simp_all [angle_comm]
theorem cotHalf_eq_heron {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A B C : P) (hAC : A ≠ C) (hBC : B ≠ C) :
    Real.cot (∠ A C B) / 2 =
      (-(dist A B) ^ 2 + (dist B C) ^ 2 + (dist A C) ^ 2) /
        (8 * heron (dist A B) (dist B C) (dist A C)) := by
  have hlaw := law_cos A C B
  set a := dist B C with ha
  set b := dist A C with hb
  set c := dist A B with hc
  set θ := ∠ A C B with hθ
  have ha0 : 0 < a := dist_pos.2 hBC
  have hb0 : 0 < b := dist_pos.2 hAC
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _ _) (angle_le_pi _ _ _)
  have hsc := Real.sin_sq_add_cos_sq θ
  have hinner : ((c + b + a) / 2) * ((c + b + a) / 2 - c) * ((c + b + a) / 2 - a) *
      ((c + b + a) / 2 - b) = (a * b * Real.sin θ / 2) ^ 2 := by
    linear_combination ((1:ℝ)/16 * (a^2 + b^2 - c^2 + 2*a*b*Real.cos θ)) * hlaw
      - (a^2*b^2/4) * hsc
  have hheron : heron c a b = a * b * Real.sin θ / 2 := by
    rw [heron, hinner, Real.sqrt_sq (by positivity)]
  rw [hheron, Real.cot_eq_cos_div_sin]
  have hnum : -c ^ 2 + a ^ 2 + b ^ 2 = 2 * a * b * Real.cos θ := by
    linear_combination -hlaw
  rw [hnum]
  rcases eq_or_lt_of_le hsin with h0 | hpos
  · rw [← h0]; simp
  · field_simp
    ring

theorem cotOpp_ne_zero_mem {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {n : ℕ} (x : Fin n → P)
    (t : Fin n × Fin n × Fin n) {u v : Fin n} (h : cotOpp x t u v ≠ 0) :
    u ∈ vertexSet t ∧ v ∈ vertexSet t := by
  obtain ⟨a, b, c⟩ := t
  simp only [cotOpp] at h
  simp only [vertexSet]
  split_ifs at h with h1 h2 h3
  · rw [pair_eq_pair_iff'] at h1
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rw [pair_eq_pair_iff'] at h2
    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rw [pair_eq_pair_iff'] at h3
    rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · exact absurd rfl h

theorem sum_cotOpp {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {n : ℕ} (M : TriMesh n) (x : Fin n → P)
    {u v q p : Fin n} (hedge : IsInteriorEdge M u v q p) :
    ∑ t ∈ M.faces, cotOpp x t u v =
      Real.cot (∠ (x u) (x q) (x v)) + Real.cot (∠ (x u) (x p) (x v)) := by
  obtain ⟨huv, hqp, himg⟩ := hedge
  set S := M.faces.filter (fun t => u ∈ vertexSet t ∧ v ∈ vertexSet t) with hS
  have hsum : ∑ t ∈ M.faces, cotOpp x t u v = ∑ t ∈ S, cotOpp x t u v := by
    rw [hS, Finset.sum_filter_of_ne]
    intro t _ ht
    exact cotOpp_ne_zero_mem x t ht
  have hq_mem : ({u, v, q} : Finset (Fin n)) ∈ S.image vertexSet := by rw [himg]; simp
  have hp_mem : ({u, v, p} : Finset (Fin n)) ∈ S.image vertexSet := by rw [himg]; simp
  obtain ⟨tq, htqS, htq⟩ := Finset.mem_image.1 hq_mem
  obtain ⟨tp, htpS, htp⟩ := Finset.mem_image.1 hp_mem
  have htqF : tq ∈ M.faces := (Finset.mem_filter.1 htqS).1
  have htpF : tp ∈ M.faces := (Finset.mem_filter.1 htpS).1
  have dq := M.distinct tq htqF
  have dp := M.distinct tp htpF
  have hne : tq ≠ tp := by
    intro h
    have hq3 := triple_third_ne dq.1 dq.2.1 dq.2.2 htq
    have hmem : q ∈ vertexSet tp := by rw [← h, htq]; simp
    rw [htp] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1
    · exact hq3.1 h1
    · exact hq3.2 h1
    · exact hqp h1
  have hSeq : S = {tq, tp} := by
    ext t
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ht
      have himt : vertexSet t ∈ S.image vertexSet := Finset.mem_image_of_mem _ ht
      rw [himg] at himt
      simp only [Finset.mem_insert, Finset.mem_singleton] at himt
      have htF : t ∈ M.faces := (Finset.mem_filter.1 ht).1
      rcases himt with h | h
      · left; exact M.injective t htF tq htqF (by rw [← vertexSet, ← vertexSet, h, htq])
      · right; exact M.injective t htF tp htpF (by rw [← vertexSet, ← vertexSet, h, htp])
    · rintro (rfl | rfl)
      · exact htqS
      · exact htpS
  rw [hsum, hSeq, Finset.sum_pair hne, cotOpp_face x tq dq huv htq, cotOpp_face x tp dp huv htp]

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {n : ℕ} (M : TriMesh n) (x : Fin n → P) {u v q p : Fin n}
        (hmesh : IsManifoldMesh M) (hedge : IsInteriorEdge M u v q p)
    (hq : AffineIndependent ℝ ![x u, x v, x q]) (hp : AffineIndependent ℝ ![x u, x v, x p]) :
    (Real.cot (∠ (x u) (x q) (x v)) + Real.cot (∠ (x u) (x p) (x v))) / 2 =
        (-(edgeLength x u v) ^ 2 + (edgeLength x v q) ^ 2 + (edgeLength x u q) ^ 2) /
            (8 * heron (edgeLength x u v) (edgeLength x v q) (edgeLength x u q)) +
          (-(edgeLength x u v) ^ 2 + (edgeLength x v p) ^ 2 + (edgeLength x u p) ^ 2) /
            (8 * heron (edgeLength x u v) (edgeLength x v p) (edgeLength x u p)) ∧
      cotWeight M x u v =
        ((-(edgeLength x u v) ^ 2 + (edgeLength x v q) ^ 2 + (edgeLength x u q) ^ 2) /
            (8 * heron (edgeLength x u v) (edgeLength x v q) (edgeLength x u q)) +
          (-(edgeLength x u v) ^ 2 + (edgeLength x v p) ^ 2 + (edgeLength x u p) ^ 2) /
            (8 * heron (edgeLength x u v) (edgeLength x v p) (edgeLength x u p))) /
          vertexArea M x u := by
  have iq := hq.injective
  have ip := hp.injective
  have huq : x u ≠ x q := fun h => absurd (@iq 0 2 h) (by decide)
  have hvq : x v ≠ x q := fun h => absurd (@iq 1 2 h) (by decide)
  have hup : x u ≠ x p := fun h => absurd (@ip 0 2 h) (by decide)
  have hvp : x v ≠ x p := fun h => absurd (@ip 1 2 h) (by decide)
  have h1 : (Real.cot (∠ (x u) (x q) (x v)) + Real.cot (∠ (x u) (x p) (x v))) / 2 =
        (-(edgeLength x u v) ^ 2 + (edgeLength x v q) ^ 2 + (edgeLength x u q) ^ 2) /
            (8 * heron (edgeLength x u v) (edgeLength x v q) (edgeLength x u q)) +
          (-(edgeLength x u v) ^ 2 + (edgeLength x v p) ^ 2 + (edgeLength x u p) ^ 2) /
            (8 * heron (edgeLength x u v) (edgeLength x v p) (edgeLength x u p)) := by
    rw [add_div, cotHalf_eq_heron _ _ _ huq hvq, cotHalf_eq_heron _ _ _ hup hvp]
    rfl
  refine ⟨h1, ?_⟩
  rw [cotWeight, sum_cotOpp M x hedge, ← h1, div_div]
