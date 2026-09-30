-- Prove2me | solution 1 for InventoryControl.clark_scarf_two_level
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T15:20:29.506057+00:00
-- url     : https://prove2.me/submissions/47353ec0-4f2e-4727-83ca-00ad0f994c6f

import Mathlib
import Definitions.Def_InventoryControl_clarkScarf

open MeasureTheory ProbabilityTheory InventoryControl in
instance f61e_isProb (mu sigma : ℝ) (n : ℕ) : IsProbabilityMeasure (csDemand mu sigma n) := by
  unfold csDemand; infer_instance

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f61e_int_id (mu sigma : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x) (csDemand mu sigma n) := by
  unfold csDemand newsboyDemand
  exact (memLp_id_gaussianReal 1).integrable le_rfl

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f61e_int_pos (mu sigma : ℝ) (n : ℕ) (y : ℝ) :
    Integrable (fun x : ℝ => max (x - y) 0) (csDemand mu sigma n) :=
  ((f61e_int_id mu sigma n).sub (integrable_const y)).pos_part

open MeasureTheory ProbabilityTheory in
lemma f61e_cdf_affine (m s x : ℝ) (hs : 0 < s) :
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
lemma f61e_stage1_convex (e1 e2 b1 mu sigma : ℝ) (L1 : ℕ) (hK : 0 ≤ e1 + e2 + b1) :
    ConvexOn ℝ Set.univ (csStage1Cost e1 e2 b1 mu sigma L1) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  unfold csStage1Cost
  have hx := f61e_int_pos mu sigma (L1 + 1) x
  have hy := f61e_int_pos mu sigma (L1 + 1) y
  have hxy := f61e_int_pos mu sigma (L1 + 1) (a * x + b * y)
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
lemma f61e_cdf_S1 (mu sigma : ℝ) (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ) :
    cdf (csDemand mu sigma (L1 + 1)) S1
      = cdf (gaussianReal 0 1) ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) := by
  have hpos : 0 < Real.sqrt ((L1 + 1 : ℕ) : ℝ) * sigma :=
    mul_pos (Real.sqrt_pos.2 (by positivity)) hs
  unfold csDemand newsboyDemand
  rw [f61e_cdf_affine _ _ _ hpos]
  push_cast
  rfl

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f61e_S1_min (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ)
    (hS1 : cdf (gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (y : ℝ) :
    csStage1Cost e1 e2 b1 mu sigma L1 S1 ≤ csStage1Cost e1 e2 b1 mu sigma L1 y := by
  have hK : 0 < e1 + e2 + b1 := by linarith
  have hF : cdf (csDemand mu sigma (L1 + 1)) S1 = (e2 + b1) / (e1 + e2 + b1) := by
    rw [f61e_cdf_S1 mu sigma hs]; exact hS1
  have hP : (csDemand mu sigma (L1 + 1)).real (Set.Ioi S1) = e1 / (e1 + e2 + b1) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, hF]
    field_simp
    ring
  have hy := f61e_int_pos mu sigma (L1 + 1) y
  have hS := f61e_int_pos mu sigma (L1 + 1) S1
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

open MeasureTheory in
lemma f61e_int_comp (g : ℝ → ℝ) (hg : Measurable g) (A B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ t, |g t| ≤ A + B * |t|) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hid : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    Integrable (fun u => g (y - u)) μ := by
  refine Integrable.mono' (g := fun u => A + B * (|y| + |u|)) ?_ ?_ ?_
  · exact (integrable_const A).add (((integrable_const |y|).add hid.abs).const_mul B)
  · exact (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · refine ae_of_all _ (fun u => ?_)
    rw [Real.norm_eq_abs]
    have h1 := hbd (y - u)
    have h2 : |y - u| ≤ |y| + |u| :=
      abs_le.2 ⟨by linarith [neg_abs_le y, le_abs_self u], by linarith [le_abs_self y, neg_abs_le u]⟩
    have h3 := mul_le_mul_of_nonneg_left h2 hB
    linarith

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f61e_C1_upper (e1 e2 b1 mu sigma : ℝ) (L1 : ℕ) (he1 : 0 ≤ e1) (hK : 0 ≤ e1 + e2 + b1) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ z, csStage1Cost e1 e2 b1 mu sigma L1 z ≤ A + B * |z| := by
  have hid := f61e_int_id mu sigma (L1 + 1)
  refine ⟨(e1 + e2 + b1) * ∫ x, |x| ∂(csDemand mu sigma (L1 + 1))
      - (e1 + e2) * (((L1 + 1 : ℕ) : ℝ) * mu), e1 + (e1 + e2 + b1), by linarith, fun z => ?_⟩
  have hle : ∫ x, max (x - z) 0 ∂(csDemand mu sigma (L1 + 1))
      ≤ ∫ x, |x| ∂(csDemand mu sigma (L1 + 1)) + |z| := by
    have hI : Integrable (fun x : ℝ => |x| + |z|) (csDemand mu sigma (L1 + 1)) :=
      hid.abs.add (integrable_const _)
    have := integral_mono (f61e_int_pos mu sigma (L1 + 1) z) hI (fun x => by
      show max (x - z) 0 ≤ |x| + |z|
      exact max_le (by linarith [le_abs_self x, neg_abs_le z]) (by positivity))
    rw [integral_add hid.abs (integrable_const _), integral_const, probReal_univ, one_smul] at this
    exact this
  unfold csStage1Cost
  have h1 := mul_le_mul_of_nonneg_left hle hK
  have h2 : e1 * z ≤ e1 * |z| := mul_le_mul_of_nonneg_left (le_abs_self z) he1
  push_cast
  nlinarith

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f61e_alloc_min (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ)
    (hS1 : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (y2 u y1 : ℝ) (hy : y1 ≤ y2 - u) :
    csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y2 - u)) ≤ csStage1Cost e1 e2 b1 mu sigma L1 y1 := by
  have hK : 0 ≤ e1 + e2 + b1 := by linarith
  have hmin := f61e_S1_min e1 e2 b1 mu sigma he1 he2 hb hs L1 S1 hS1
  rcases le_total S1 (y2 - u) with h | h
  · rw [min_eq_left h]
    exact hmin y1
  · rw [min_eq_right h]
    have hconv := f61e_stage1_convex e1 e2 b1 mu sigma L1 hK
    have hmem : y2 - u ∈ segment ℝ y1 S1 := by
      rw [segment_eq_Icc (hy.trans h)]
      exact ⟨hy, h⟩
    have hseg := hconv.le_on_segment (Set.mem_univ _) (Set.mem_univ _) hmem
    exact hseg.trans (max_le le_rfl (hmin y1))

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f61e_int_minS1 (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 L2 : ℕ) (S1 : ℝ)
    (hS1 : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (y : ℝ) :
    Integrable (fun u => csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y - u))) (csDemand mu sigma L2) := by
  have hK : 0 ≤ e1 + e2 + b1 := by linarith
  have hCconv := f61e_stage1_convex e1 e2 b1 mu sigma L1 hK
  have hmin := f61e_S1_min e1 e2 b1 mu sigma he1 he2 hb hs L1 S1 hS1
  have hCcont : Continuous (csStage1Cost e1 e2 b1 mu sigma L1) :=
    continuousOn_univ.1 (hCconv.continuousOn isOpen_univ)
  obtain ⟨A, B, hB, hup⟩ := f61e_C1_upper e1 e2 b1 mu sigma L1 he1 hK
  have hgm : Measurable (fun t => csStage1Cost e1 e2 b1 mu sigma L1 (min S1 t)) :=
    (hCcont.comp (continuous_const.min continuous_id)).measurable
  have hbd : ∀ t, |csStage1Cost e1 e2 b1 mu sigma L1 (min S1 t)|
      ≤ (|csStage1Cost e1 e2 b1 mu sigma L1 S1| + |A| + B * |S1|) + B * |t| := by
    intro t
    have h1 := hup (min S1 t)
    have h0 := hmin (min S1 t)
    have h2 : |min S1 t| ≤ |t| + |S1| := by
      rcases min_cases S1 t with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        linarith [abs_nonneg t, abs_nonneg S1]
    have h3 := mul_le_mul_of_nonneg_left h2 hB
    have h4 := le_abs_self A
    have h5 := neg_abs_le (csStage1Cost e1 e2 b1 mu sigma L1 S1)
    have h6 := abs_nonneg (csStage1Cost e1 e2 b1 mu sigma L1 S1)
    have h7 : 0 ≤ B * |S1| := mul_nonneg hB (abs_nonneg _)
    have h8 : 0 ≤ B * |t| := mul_nonneg hB (abs_nonneg _)
    have h9 := abs_nonneg A
    rw [abs_le]
    constructor <;> linarith
  exact f61e_int_comp (fun t => csStage1Cost e1 e2 b1 mu sigma L1 (min S1 t)) hgm _ B hB hbd _
    (f61e_int_id mu sigma L2) y

open MeasureTheory ProbabilityTheory InventoryControl in
lemma f61e_total_eq (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 L2 : ℕ) (S1 : ℝ)
    (hS1 : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (y : ℝ) :
    csTotalCost e1 e2 b1 mu sigma L1 L2 S1 y
      = ∫ u, (csStage2Cost e2 mu L2 y + csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y - u)))
          ∂(csDemand mu sigma L2) := by
  have hI := f61e_int_minS1 e1 e2 b1 mu sigma he1 he2 hb hs L1 L2 S1 hS1 y
  have hset : ∫ u in Set.Ioi (y - S1),
        (csStage1Cost e1 e2 b1 mu sigma L1 (y - u) - csStage1Cost e1 e2 b1 mu sigma L1 S1)
          ∂(csDemand mu sigma L2)
      = ∫ u, (csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y - u))
          - csStage1Cost e1 e2 b1 mu sigma L1 S1) ∂(csDemand mu sigma L2) := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1
    funext u
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h
    · rw [min_eq_right (by linarith)]
    · rw [min_eq_left (by linarith), sub_self]
  have hsub : ∫ u, (csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y - u))
          - csStage1Cost e1 e2 b1 mu sigma L1 S1) ∂(csDemand mu sigma L2)
      = ∫ u, csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y - u)) ∂(csDemand mu sigma L2)
          - csStage1Cost e1 e2 b1 mu sigma L1 S1 := by
    rw [integral_sub hI (integrable_const _), integral_const, probReal_univ, one_smul]
  have hadd : ∫ u, (csStage2Cost e2 mu L2 y + csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y - u)))
          ∂(csDemand mu sigma L2)
      = csStage2Cost e2 mu L2 y
          + ∫ u, csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y - u)) ∂(csDemand mu sigma L2) := by
    rw [integral_add (integrable_const _) hI, integral_const, probReal_univ, one_smul]
  rw [hadd]
  unfold csTotalCost
  rw [hset, hsub]
  ring

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 L2 : ℕ) (S1 : ℝ)
    (hS1 : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (S2 : ℝ) (hS2 : ∀ y2 : ℝ, csTotalCost e1 e2 b1 mu sigma L1 L2 S1 S2
      ≤ csTotalCost e1 e2 b1 mu sigma L1 L2 S1 y2) :
    (∀ y2 : ℝ, ∀ a : ℝ → ℝ, (∀ u, a u ≤ y2 - u) →
        MeasureTheory.Integrable (fun u => csStage1Cost e1 e2 b1 mu sigma L1 (a u))
          (csDemand mu sigma L2) →
        csTotalCost e1 e2 b1 mu sigma L1 L2 S1 S2
          ≤ ∫ u, (csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 (a u))
              ∂(csDemand mu sigma L2))
      ∧ csTotalCost e1 e2 b1 mu sigma L1 L2 S1 S2
          = ∫ u, (csStage2Cost e2 mu L2 S2 + csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (S2 - u)))
              ∂(csDemand mu sigma L2) := by
  refine ⟨fun y2 a ha haI => ?_, f61e_total_eq e1 e2 b1 mu sigma he1 he2 hb hs L1 L2 S1 hS1 S2⟩
  refine (hS2 y2).trans ?_
  rw [f61e_total_eq e1 e2 b1 mu sigma he1 he2 hb hs L1 L2 S1 hS1 y2]
  apply integral_mono ((integrable_const _).add
    (f61e_int_minS1 e1 e2 b1 mu sigma he1 he2 hb hs L1 L2 S1 hS1 y2))
    ((integrable_const _).add haI)
  intro u
  simp only [Pi.add_apply]
  exact add_le_add le_rfl
    (f61e_alloc_min e1 e2 b1 mu sigma he1 he2 hb hs L1 S1 hS1 y2 u (a u) (ha u))
