-- Prove2me | solution 1 for InventoryControl.cs_allocation_min
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T14:59:24.559959+00:00
-- url     : https://prove2.me/submissions/0a7be224-9c7f-4041-84e0-195257771bc6

import Mathlib
import Definitions.Def_InventoryControl_clarkScarf

open MeasureTheory ProbabilityTheory InventoryControl in
instance ac64_isProb (mu sigma : ℝ) (n : ℕ) : IsProbabilityMeasure (csDemand mu sigma n) := by
  unfold csDemand; infer_instance

open MeasureTheory ProbabilityTheory InventoryControl in
lemma ac64_int_id (mu sigma : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x) (csDemand mu sigma n) := by
  unfold csDemand newsboyDemand
  exact (memLp_id_gaussianReal 1).integrable le_rfl

open MeasureTheory ProbabilityTheory InventoryControl in
lemma ac64_int_pos (mu sigma : ℝ) (n : ℕ) (y : ℝ) :
    Integrable (fun x : ℝ => max (x - y) 0) (csDemand mu sigma n) :=
  ((ac64_int_id mu sigma n).sub (integrable_const y)).pos_part

open MeasureTheory ProbabilityTheory in
lemma ac64_cdf_affine (m s x : ℝ) (hs : 0 < s) :
    cdf (gaussianReal m (Real.toNNReal (s ^ 2))) x = cdf (gaussianReal 0 1) ((x - m) / s) := by
  have hmap : gaussianReal m (Real.toNNReal (s ^ 2))
      = ((gaussianReal 0 1).map (s * ·)).map (· + m) := by
    rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
    congr 1
    · simp
    · ext
      simp [sq_nonneg]
  rw [cdf_eq_real, cdf_eq_real, hmap, Measure.map_map (by fun_prop) (by fun_prop)]
  rw [measureReal_def, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext z
  simp only [Set.mem_preimage, Function.comp, Set.mem_Iic]
  rw [le_div_iff₀ hs]
  constructor <;> intro h <;> linarith

open MeasureTheory ProbabilityTheory InventoryControl in
lemma ac64_stage1_convex (e1 e2 b1 mu sigma : ℝ) (L1 : ℕ) (hK : 0 ≤ e1 + e2 + b1) :
    ConvexOn ℝ Set.univ (csStage1Cost e1 e2 b1 mu sigma L1) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  unfold csStage1Cost
  have hx := ac64_int_pos mu sigma (L1 + 1) x
  have hy := ac64_int_pos mu sigma (L1 + 1) y
  have hxy := ac64_int_pos mu sigma (L1 + 1) (a * x + b * y)
  have hle : ∫ u, max (u - (a * x + b * y)) 0 ∂(csDemand mu sigma (L1 + 1))
      ≤ a * ∫ u, max (u - x) 0 ∂(csDemand mu sigma (L1 + 1))
        + b * ∫ u, max (u - y) 0 ∂(csDemand mu sigma (L1 + 1)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hx.const_mul a) (hy.const_mul b)]
    apply integral_mono hxy ((hx.const_mul a).add (hy.const_mul b))
    intro u
    have h1 : u - (a * x + b * y) = a * (u - x) + b * (u - y) := by
      have : u = a * u + b * u := by rw [← add_mul, hab, one_mul]
      linarith
    have h2 : a * (u - x) ≤ a * max (u - x) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
    have h3 : b * (u - y) ≤ b * max (u - y) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hb
    have h4 : 0 ≤ a * max (u - x) 0 := mul_nonneg ha (le_max_right _ _)
    have h5 : 0 ≤ b * max (u - y) 0 := mul_nonneg hb (le_max_right _ _)
    show max (u - (a * x + b * y)) 0 ≤ a * max (u - x) 0 + b * max (u - y) 0
    rw [h1]
    exact max_le (by linarith) (by linarith)
  have hK' := mul_le_mul_of_nonneg_left hle hK
  have hc : (e1 + e2) * ((((L1 + 1 : ℕ) : ℝ)) * mu)
      = a * ((e1 + e2) * ((((L1 + 1 : ℕ) : ℝ)) * mu)) + b * ((e1 + e2) * ((((L1 + 1 : ℕ) : ℝ)) * mu)) := by
    rw [← add_mul, hab, one_mul]
  push_cast at hc hK' ⊢
  nlinarith

open MeasureTheory ProbabilityTheory InventoryControl in
lemma ac64_cdf_S1 (mu sigma : ℝ) (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ) :
    cdf (csDemand mu sigma (L1 + 1)) S1
      = cdf (gaussianReal 0 1) ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) := by
  have hpos : 0 < Real.sqrt ((L1 + 1 : ℕ) : ℝ) * sigma :=
    mul_pos (Real.sqrt_pos.2 (by positivity)) hs
  unfold csDemand newsboyDemand
  rw [ac64_cdf_affine _ _ _ hpos]
  push_cast
  rfl

open MeasureTheory ProbabilityTheory InventoryControl in
lemma ac64_S1_min (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ)
    (hS1 : cdf (gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (y : ℝ) :
    csStage1Cost e1 e2 b1 mu sigma L1 S1 ≤ csStage1Cost e1 e2 b1 mu sigma L1 y := by
  have hK : 0 < e1 + e2 + b1 := by linarith
  have hF : cdf (csDemand mu sigma (L1 + 1)) S1 = (e2 + b1) / (e1 + e2 + b1) := by
    rw [ac64_cdf_S1 mu sigma hs]; exact hS1
  have hP : (csDemand mu sigma (L1 + 1)).real (Set.Ioi S1) = e1 / (e1 + e2 + b1) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, hF]
    field_simp
    ring
  have hy := ac64_int_pos mu sigma (L1 + 1) y
  have hS := ac64_int_pos mu sigma (L1 + 1) S1
  have hind : Integrable (fun x : ℝ => (S1 - y) * (Set.Ioi S1).indicator (fun _ => (1:ℝ)) x)
      (csDemand mu sigma (L1 + 1)) :=
    ((integrable_const (1:ℝ)).indicator measurableSet_Ioi).const_mul _
  have hle : ∫ x, max (x - S1) 0 ∂(csDemand mu sigma (L1 + 1))
      + ∫ x, (S1 - y) * (Set.Ioi S1).indicator (fun _ => (1:ℝ)) x ∂(csDemand mu sigma (L1 + 1))
      ≤ ∫ x, max (x - y) 0 ∂(csDemand mu sigma (L1 + 1)) := by
    rw [← integral_add hS hind]
    apply integral_mono (hS.add hind) hy
    intro x
    show max (x - S1) 0 + (S1 - y) * (Set.Ioi S1).indicator (fun _ => (1:ℝ)) x ≤ max (x - y) 0
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ x - S1)]
      have := le_max_left (x - y) 0
      linarith
    · rw [max_eq_right (by linarith : x - S1 ≤ 0)]
      have := le_max_right (x - y) 0
      linarith
  have hint : ∫ x, (S1 - y) * (Set.Ioi S1).indicator (fun _ => (1:ℝ)) x ∂(csDemand mu sigma (L1 + 1))
      = (S1 - y) * (e1 / (e1 + e2 + b1)) := by
    rw [integral_const_mul, integral_indicator_const _ measurableSet_Ioi, hP, smul_eq_mul, mul_one]
  rw [hint] at hle
  unfold csStage1Cost
  have hm := mul_le_mul_of_nonneg_left hle hK.le
  have hKe : (e1 + e2 + b1) * ((S1 - y) * (e1 / (e1 + e2 + b1))) = (S1 - y) * e1 := by
    field_simp
  rw [mul_add, hKe] at hm
  linarith

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ)
    (hS1 : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (y2 u y1 : ℝ) (hy : y1 ≤ y2 - u) :
    csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y2 - u)) ≤ csStage1Cost e1 e2 b1 mu sigma L1 y1 := by
  have hK : 0 ≤ e1 + e2 + b1 := by linarith
  have hmin := ac64_S1_min e1 e2 b1 mu sigma he1 he2 hb hs L1 S1 hS1
  rcases le_total S1 (y2 - u) with h | h
  · rw [min_eq_left h]
    exact hmin y1
  · rw [min_eq_right h]
    have hconv := ac64_stage1_convex e1 e2 b1 mu sigma L1 hK
    have hmem : y2 - u ∈ segment ℝ y1 S1 := by
      rw [segment_eq_Icc (hy.trans h)]
      exact ⟨hy, h⟩
    have hseg := hconv.le_on_segment (Set.mem_univ _) (Set.mem_univ _) hmem
    exact hseg.trans (max_le le_rfl (hmin y1))
