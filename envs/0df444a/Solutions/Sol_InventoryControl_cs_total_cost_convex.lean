-- Prove2me | solution 1 for InventoryControl.cs_total_cost_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T14:11:38.258924+00:00
-- url     : https://prove2.me/submissions/ed4b3a4b-a9e4-409b-99f6-3d0a20eac1ba

import Mathlib
import Definitions.Def_InventoryControl_clarkScarf

open MeasureTheory ProbabilityTheory InventoryControl in
instance fa17_isProb (mu sigma : ℝ) (n : ℕ) : IsProbabilityMeasure (csDemand mu sigma n) := by
  unfold csDemand; infer_instance

open MeasureTheory ProbabilityTheory InventoryControl in
lemma fa17_int_id (mu sigma : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x) (csDemand mu sigma n) := by
  unfold csDemand newsboyDemand
  exact (memLp_id_gaussianReal 1).integrable le_rfl

open MeasureTheory ProbabilityTheory InventoryControl in
lemma fa17_int_pos (mu sigma : ℝ) (n : ℕ) (y : ℝ) :
    Integrable (fun x : ℝ => max (x - y) 0) (csDemand mu sigma n) :=
  ((fa17_int_id mu sigma n).sub (integrable_const y)).pos_part

open MeasureTheory ProbabilityTheory in
lemma fa17_cdf_affine (m s x : ℝ) (hs : 0 < s) :
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
lemma fa17_stage1_convex (e1 e2 b1 mu sigma : ℝ) (L1 : ℕ) (hK : 0 ≤ e1 + e2 + b1) :
    ConvexOn ℝ Set.univ (csStage1Cost e1 e2 b1 mu sigma L1) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  unfold csStage1Cost
  have hx := fa17_int_pos mu sigma (L1 + 1) x
  have hy := fa17_int_pos mu sigma (L1 + 1) y
  have hxy := fa17_int_pos mu sigma (L1 + 1) (a * x + b * y)
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
lemma fa17_cdf_S1 (mu sigma : ℝ) (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ) :
    cdf (csDemand mu sigma (L1 + 1)) S1
      = cdf (gaussianReal 0 1) ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) := by
  have hpos : 0 < Real.sqrt ((L1 + 1 : ℕ) : ℝ) * sigma :=
    mul_pos (Real.sqrt_pos.2 (by positivity)) hs
  unfold csDemand newsboyDemand
  rw [fa17_cdf_affine _ _ _ hpos]
  push_cast
  rfl

open MeasureTheory ProbabilityTheory InventoryControl in
lemma fa17_S1_min (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ)
    (hS1 : cdf (gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1))
    (y : ℝ) :
    csStage1Cost e1 e2 b1 mu sigma L1 S1 ≤ csStage1Cost e1 e2 b1 mu sigma L1 y := by
  have hK : 0 < e1 + e2 + b1 := by linarith
  have hF : cdf (csDemand mu sigma (L1 + 1)) S1 = (e2 + b1) / (e1 + e2 + b1) := by
    rw [fa17_cdf_S1 mu sigma hs]; exact hS1
  have hP : (csDemand mu sigma (L1 + 1)).real (Set.Ioi S1) = e1 / (e1 + e2 + b1) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, hF]
    field_simp
    ring
  have hy := fa17_int_pos mu sigma (L1 + 1) y
  have hS := fa17_int_pos mu sigma (L1 + 1) S1
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

lemma fa17_antitoneOn (C : ℝ → ℝ) (S : ℝ) (hC : ConvexOn ℝ Set.univ C) (hmin : ∀ y, C S ≤ C y) :
    AntitoneOn C (Set.Iic S) := by
  intro x hx y hy hxy
  simp only [Set.mem_Iic] at hx hy
  rcases eq_or_lt_of_le hx with h | h
  · have : y = S := le_antisymm hy (h ▸ hxy)
    rw [this, h]
  · set t := (S - y) / (S - x) with ht
    have hSx : 0 < S - x := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hSx.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hSx]; linarith
    have hcomb : t * x + (1 - t) * S = y := by
      rw [ht]; field_simp; ring
    have h2 := hC.2 (Set.mem_univ x) (Set.mem_univ S) ht0 (by linarith) (by ring : t + (1 - t) = 1)
    simp only [smul_eq_mul] at h2
    rw [hcomb] at h2
    have h3 := hmin x
    nlinarith

lemma fa17_g_convex (C : ℝ → ℝ) (S : ℝ) (hC : ConvexOn ℝ Set.univ C) (hmin : ∀ y, C S ≤ C y) :
    ConvexOn ℝ Set.univ (fun t => C (min t S) - C S) := by
  have hanti := fa17_antitoneOn C S hC hmin
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hp : min x S ≤ S := min_le_right _ _
  have hq : min y S ≤ S := min_le_right _ _
  have hr1 : a * min x S + b * min y S ≤ a * x + b * y := by
    have := mul_le_mul_of_nonneg_left (min_le_left x S) ha
    have := mul_le_mul_of_nonneg_left (min_le_left y S) hb
    linarith
  have hr2 : a * min x S + b * min y S ≤ S := by
    have := mul_le_mul_of_nonneg_left hp ha
    have := mul_le_mul_of_nonneg_left hq hb
    have hS : a * S + b * S = S := by rw [← add_mul, hab, one_mul]
    linarith
  have hr : a * min x S + b * min y S ≤ min (a * x + b * y) S := le_min hr1 hr2
  have h1 : C (min (a * x + b * y) S) ≤ C (a * min x S + b * min y S) :=
    hanti (Set.mem_Iic.2 hr2) (Set.mem_Iic.2 (min_le_right _ _)) hr
  have h2 := hC.2 (Set.mem_univ (min x S)) (Set.mem_univ (min y S)) ha hb hab
  simp only [smul_eq_mul] at h2
  have hCS : a * C S + b * C S = C S := by rw [← add_mul, hab, one_mul]
  nlinarith

lemma fa17_g_antitone (C : ℝ → ℝ) (S : ℝ) (hC : ConvexOn ℝ Set.univ C) (hmin : ∀ y, C S ≤ C y) :
    Antitone (fun t => C (min t S) - C S) := by
  have hanti := fa17_antitoneOn C S hC hmin
  intro x y hxy
  simp only
  have := hanti (Set.mem_Iic.2 (min_le_right x S)) (Set.mem_Iic.2 (min_le_right y S))
    (min_le_min_right S hxy)
  linarith

open MeasureTheory in
lemma fa17_int_comp (g : ℝ → ℝ) (hg : Measurable g) (A B : ℝ) (hB : 0 ≤ B)
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

open MeasureTheory in
lemma fa17_G_convex (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g) (μ : Measure ℝ)
    (hint : ∀ y, Integrable (fun u => g (y - u)) μ) :
    ConvexOn ℝ Set.univ (fun y => ∫ u, g (y - u) ∂μ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint x).const_mul a) ((hint y).const_mul b)]
  apply integral_mono (hint _) (((hint x).const_mul a).add ((hint y).const_mul b))
  intro u
  show g (a * x + b * y - u) ≤ a * g (x - u) + b * g (y - u)
  have h := hg.2 (Set.mem_univ (x - u)) (Set.mem_univ (y - u)) ha hb hab
  simp only [smul_eq_mul] at h
  have he : a * (x - u) + b * (y - u) = a * x + b * y - u := by
    have : u = a * u + b * u := by rw [← add_mul, hab, one_mul]
    linarith
  rw [he] at h
  exact h

open MeasureTheory ProbabilityTheory InventoryControl in
lemma fa17_C1_upper (e1 e2 b1 mu sigma : ℝ) (L1 : ℕ) (he1 : 0 ≤ e1) (hK : 0 ≤ e1 + e2 + b1) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ z, csStage1Cost e1 e2 b1 mu sigma L1 z ≤ A + B * |z| := by
  have hid := fa17_int_id mu sigma (L1 + 1)
  refine ⟨(e1 + e2 + b1) * ∫ x, |x| ∂(csDemand mu sigma (L1 + 1))
      - (e1 + e2) * (((L1 + 1 : ℕ) : ℝ) * mu), e1 + (e1 + e2 + b1), by linarith, fun z => ?_⟩
  have hle : ∫ x, max (x - z) 0 ∂(csDemand mu sigma (L1 + 1))
      ≤ ∫ x, |x| ∂(csDemand mu sigma (L1 + 1)) + |z| := by
    have hI : Integrable (fun x : ℝ => |x| + |z|) (csDemand mu sigma (L1 + 1)) :=
      hid.abs.add (integrable_const _)
    have := integral_mono (fa17_int_pos mu sigma (L1 + 1) z) hI (fun x => by
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
lemma fa17_C1_lower (e1 e2 b1 mu sigma : ℝ) (L1 : ℕ) (hK : 0 ≤ e1 + e2 + b1) :
    ∃ c : ℝ, ∀ z, -(e2 + b1) * z + c ≤ csStage1Cost e1 e2 b1 mu sigma L1 z := by
  have hid := fa17_int_id mu sigma (L1 + 1)
  refine ⟨(e1 + e2 + b1) * ∫ x, x ∂(csDemand mu sigma (L1 + 1))
      - (e1 + e2) * (((L1 + 1 : ℕ) : ℝ) * mu), fun z => ?_⟩
  have hle : ∫ x, x ∂(csDemand mu sigma (L1 + 1)) - z
      ≤ ∫ x, max (x - z) 0 ∂(csDemand mu sigma (L1 + 1)) := by
    have hI : Integrable (fun x : ℝ => x - z) (csDemand mu sigma (L1 + 1)) :=
      hid.sub (integrable_const z)
    have := integral_mono hI (fa17_int_pos mu sigma (L1 + 1) z)
      (fun x => by
        show x - z ≤ max (x - z) 0
        exact le_max_left _ _)
    rw [integral_sub hid (integrable_const _), integral_const, probReal_univ, one_smul] at this
    exact this
  unfold csStage1Cost
  have h1 := mul_le_mul_of_nonneg_left hle hK
  push_cast
  nlinarith

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 L2 : ℕ) (S1 : ℝ)
    (hS1 : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1)) :
    ConvexOn ℝ Set.univ (csTotalCost e1 e2 b1 mu sigma L1 L2 S1)
      ∧ (0 < e2 → ∃ S2 : ℝ, ∀ y2 : ℝ, csTotalCost e1 e2 b1 mu sigma L1 L2 S1 S2
          ≤ csTotalCost e1 e2 b1 mu sigma L1 L2 S1 y2) := by
  have hK : 0 ≤ e1 + e2 + b1 := by linarith
  have hCconv := fa17_stage1_convex e1 e2 b1 mu sigma L1 hK
  have hmin := fa17_S1_min e1 e2 b1 mu sigma he1 he2 hb hs L1 S1 hS1
  have hg_conv := fa17_g_convex _ S1 hCconv hmin
  have hg_anti := fa17_g_antitone _ S1 hCconv hmin
  obtain ⟨A, B, hB, hup⟩ := fa17_C1_upper e1 e2 b1 mu sigma L1 he1 hK
  obtain ⟨c, hlow⟩ := fa17_C1_lower e1 e2 b1 mu sigma L1 hK
  have hg_nonneg : ∀ t, 0 ≤ csStage1Cost e1 e2 b1 mu sigma L1 (min t S1)
      - csStage1Cost e1 e2 b1 mu sigma L1 S1 := fun t => sub_nonneg.2 (hmin _)
  have hg_bd : ∀ t, |csStage1Cost e1 e2 b1 mu sigma L1 (min t S1)
      - csStage1Cost e1 e2 b1 mu sigma L1 S1|
      ≤ (A + B * |S1| - csStage1Cost e1 e2 b1 mu sigma L1 S1) + B * |t| := by
    intro t
    rw [abs_of_nonneg (hg_nonneg t)]
    have h1 := hup (min t S1)
    have h2 : |min t S1| ≤ |t| + |S1| := by
      rcases min_cases t S1 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        linarith [abs_nonneg t, abs_nonneg S1]
    have h3 := mul_le_mul_of_nonneg_left h2 hB
    linarith
  have hg_low : ∀ t, -(e2 + b1) * t + (c - csStage1Cost e1 e2 b1 mu sigma L1 S1)
      ≤ csStage1Cost e1 e2 b1 mu sigma L1 (min t S1) - csStage1Cost e1 e2 b1 mu sigma L1 S1 := by
    intro t
    have h1 := hlow (min t S1)
    have h2 : -(e2 + b1) * t ≤ -(e2 + b1) * min t S1 :=
      mul_le_mul_of_nonpos_left (min_le_left t S1) (by linarith)
    linarith
  have hid2 := fa17_int_id mu sigma L2
  have hint : ∀ y, Integrable (fun u => csStage1Cost e1 e2 b1 mu sigma L1 (min (y - u) S1)
      - csStage1Cost e1 e2 b1 mu sigma L1 S1) (csDemand mu sigma L2) :=
    fun y => fa17_int_comp (fun t => csStage1Cost e1 e2 b1 mu sigma L1 (min t S1)
      - csStage1Cost e1 e2 b1 mu sigma L1 S1) hg_anti.measurable _ B hB hg_bd _ hid2 y
  have hG_conv := fa17_G_convex _ hg_conv (csDemand mu sigma L2) hint
  have heq : csTotalCost e1 e2 b1 mu sigma L1 L2 S1 = fun y => e2 * (y - L2 * mu)
      + csStage1Cost e1 e2 b1 mu sigma L1 S1
      + ∫ u, (csStage1Cost e1 e2 b1 mu sigma L1 (min (y - u) S1)
          - csStage1Cost e1 e2 b1 mu sigma L1 S1) ∂(csDemand mu sigma L2) := by
    funext y
    unfold csTotalCost csStage2Cost
    congr 1
    rw [← integral_indicator measurableSet_Ioi]
    congr 1
    funext u
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h
    · rw [min_eq_left (by linarith)]
    · rw [min_eq_right (by linarith), sub_self]
  have hF_conv : ConvexOn ℝ Set.univ (fun y => e2 * (y - L2 * mu)
      + csStage1Cost e1 e2 b1 mu sigma L1 S1
      + ∫ u, (csStage1Cost e1 e2 b1 mu sigma L1 (min (y - u) S1)
          - csStage1Cost e1 e2 b1 mu sigma L1 S1) ∂(csDemand mu sigma L2)) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have h := hG_conv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    have h1 : a * csStage1Cost e1 e2 b1 mu sigma L1 S1 + b * csStage1Cost e1 e2 b1 mu sigma L1 S1
        = csStage1Cost e1 e2 b1 mu sigma L1 S1 := by rw [← add_mul, hab, one_mul]
    have h2 : a * (e2 * (L2 * mu)) + b * (e2 * (L2 * mu)) = e2 * (L2 * mu) := by
      rw [← add_mul, hab, one_mul]
    nlinarith
  refine ⟨heq ▸ hF_conv, fun he2' => ?_⟩
  rw [heq]
  have hcont := continuousOn_univ.1 (hF_conv.continuousOn isOpen_univ)
  apply hcont.exists_forall_le
  rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
  constructor
  · rw [Filter.tendsto_atBot_atTop]
    intro M
    set E := -e2 * (L2 * mu) + csStage1Cost e1 e2 b1 mu sigma L1 S1
      + ((e2 + b1) * ∫ u, u ∂(csDemand mu sigma L2) + (c - csStage1Cost e1 e2 b1 mu sigma L1 S1))
      with hE
    refine ⟨(E - M) / b1, fun y hy => ?_⟩
    have hGlow : -(e2 + b1) * y + ((e2 + b1) * ∫ u, u ∂(csDemand mu sigma L2)
        + (c - csStage1Cost e1 e2 b1 mu sigma L1 S1))
        ≤ ∫ u, (csStage1Cost e1 e2 b1 mu sigma L1 (min (y - u) S1)
          - csStage1Cost e1 e2 b1 mu sigma L1 S1) ∂(csDemand mu sigma L2) := by
      have hI : Integrable (fun u : ℝ => (-(e2 + b1) * y + (c - csStage1Cost e1 e2 b1 mu sigma L1 S1))
          + (e2 + b1) * u) (csDemand mu sigma L2) :=
        (integrable_const _).add (hid2.const_mul _)
      have hle := integral_mono hI (hint y) (fun u => by
        show (-(e2 + b1) * y + (c - csStage1Cost e1 e2 b1 mu sigma L1 S1)) + (e2 + b1) * u
          ≤ csStage1Cost e1 e2 b1 mu sigma L1 (min (y - u) S1) - csStage1Cost e1 e2 b1 mu sigma L1 S1
        have := hg_low (y - u)
        linarith)
      rw [integral_add (integrable_const _) (hid2.const_mul _), integral_const, probReal_univ,
        one_smul, integral_const_mul] at hle
      linarith
    have hy' : b1 * y ≤ E - M := by
      rw [le_div_iff₀ hb] at hy
      linarith
    show M ≤ e2 * (y - L2 * mu) + csStage1Cost e1 e2 b1 mu sigma L1 S1
      + ∫ u, (csStage1Cost e1 e2 b1 mu sigma L1 (min (y - u) S1)
          - csStage1Cost e1 e2 b1 mu sigma L1 S1) ∂(csDemand mu sigma L2)
    nlinarith
  · rw [Filter.tendsto_atTop_atTop]
    intro M
    refine ⟨L2 * mu + (M - csStage1Cost e1 e2 b1 mu sigma L1 S1) / e2, fun y hy => ?_⟩
    have hG0 : 0 ≤ ∫ u, (csStage1Cost e1 e2 b1 mu sigma L1 (min (y - u) S1)
          - csStage1Cost e1 e2 b1 mu sigma L1 S1) ∂(csDemand mu sigma L2) :=
      integral_nonneg (fun u => hg_nonneg _)
    have h1 : (M - csStage1Cost e1 e2 b1 mu sigma L1 S1) / e2 ≤ y - L2 * mu := by linarith
    rw [div_le_iff₀ he2'] at h1
    show M ≤ e2 * (y - L2 * mu) + csStage1Cost e1 e2 b1 mu sigma L1 S1
      + ∫ u, (csStage1Cost e1 e2 b1 mu sigma L1 (min (y - u) S1)
          - csStage1Cost e1 e2 b1 mu sigma L1 S1) ∂(csDemand mu sigma L2)
    nlinarith
