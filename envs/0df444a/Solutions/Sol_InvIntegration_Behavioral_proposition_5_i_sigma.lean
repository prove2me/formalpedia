-- Prove2me | solution 1 for InvIntegration.Behavioral.proposition_5_i_sigma
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:43:08.147586+00:00
-- url     : https://prove2.me/submissions/0f64b69a-aa7a-43f1-8bdf-9cfbc5b2c4b5

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model


namespace InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory

lemma iib_G_vh (P : Params) (hS : P.Standing) : G P P.vh = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, -, hsupp, -, h1, -⟩ := hS
  unfold G
  have h := integral_add_compl (s := Set.Iic P.vh) measurableSet_Iic hint
  rw [Set.compl_Iic] at h
  have h0 : ∫ t in Set.Ioi P.vh, P.g t = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply hsupp
    intro hx'
    exact absurd hx'.2 (not_lt.mpr (le_of_lt hx))
  linarith

lemma iib_one_sub_G (P : Params) (hS : P.Standing) (x : ℝ) :
    1 - G P x = ∫ t in Set.Ioi x, P.g t := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, -, -, -, h1, -⟩ := hS
  unfold G
  have h := integral_add_compl (s := Set.Iic x) measurableSet_Iic hint
  rw [Set.compl_Iic] at h
  linarith

lemma iib_G_sub (P : Params) (hS : P.Standing) (a b : ℝ) (hab : a ≤ b) :
    G P b - G P a = ∫ t in Set.Ioc a b, P.g t := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, -, -, -, -, -⟩ := hS
  unfold G
  rw [← Set.Iic_union_Ioc_eq_Iic hab, setIntegral_union (Set.Iic_disjoint_Ioc le_rfl)
    measurableSet_Ioc hint.integrableOn hint.integrableOn]
  ring

lemma iib_pos_of_sub (P : Params) (hS : P.Standing) (s a : Set ℝ) (hsub : s ⊆ a)
    (hpos : 0 < ∫ t in s, P.g t) : 0 < ∫ t in a, P.g t := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, hnn, -, -, -, -⟩ := hS
  refine lt_of_lt_of_le hpos ?_
  apply setIntegral_mono_set hint.integrableOn
  · exact Filter.Eventually.of_forall (fun x => hnn x)
  · exact Filter.Eventually.of_forall hsub

lemma iib_G_strict (P : Params) (hS : P.Standing) (a b : ℝ) (ha : P.vl < a) (hab : a < b)
    (hb : b ≤ P.vh) : G P a < G P b := by
  have hsupp := hS.2.2.2.2.2.2.2.2.2.2.2.1
  rw [← sub_pos, iib_G_sub P hS a b hab.le]
  have hvh : a < P.vh := lt_of_lt_of_le hab hb
  set b' := min b ((a + P.vh) / 2)
  have h1 : a < b' := lt_min hab (by linarith)
  have h2 : b' < P.vh := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  apply iib_pos_of_sub P hS (Set.Ioo a b') _ _ (hsupp a b' ha h2 h1)
  intro x hx
  exact ⟨hx.1, le_trans hx.2.le (min_le_left _ _)⟩

lemma iib_Gbar_pos (P : Params) (hS : P.Standing) (v : ℝ) (hv : v < P.vh) (hvl : P.vl < v) :
    0 < Gbar P v := by
  have hsupp := hS.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Gbar
  rw [iib_one_sub_G P hS v]
  apply iib_pos_of_sub P hS (Set.Ioo v ((v + P.vh) / 2)) _ _
    (hsupp v ((v + P.vh) / 2) hvl (by linarith) (by linarith))
  intro x hx; exact hx.1

lemma iib_vstar_ge (P : Params) (hS : P.Standing) (ξ : ℝ) : P.p ≤ vstar P ξ := by
  have hpvh := hS.2.2.2.2.2.2.1
  unfold vstar
  split_ifs
  · exact hpvh.le
  · exact le_min hpvh.le (le_max_right _ _)

lemma iib_frac_le (P : Params) (hS : P.Standing) (ξ : ℝ) (hξ : ξ ≤ 0) :
    (P.p - ξ * P.s) / (1 - ξ * P.δ) ≤ P.p := by
  obtain ⟨-, -, hδ, -, hsδ, -⟩ := hS
  have h1 : 0 < 1 - ξ * P.δ := by nlinarith
  rw [div_le_iff₀ h1]
  nlinarith

lemma iib_frac_ge (P : Params) (hS : P.Standing) (ξ : ℝ) (hξ : 0 ≤ ξ) (h : ξ * P.δ < 1) :
    P.p ≤ (P.p - ξ * P.s) / (1 - ξ * P.δ) := by
  obtain ⟨-, -, hδ, -, hsδ, -⟩ := hS
  have h1 : 0 < 1 - ξ * P.δ := by linarith
  rw [le_div_iff₀ h1]
  nlinarith

lemma iib_vstar_nonpos (P : Params) (hS : P.Standing) (ξ : ℝ) (hξ : ξ ≤ 0) :
    vstar P ξ = P.p := by
  have hpvh := hS.2.2.2.2.2.2.1
  have hδ := hS.2.2.1
  unfold vstar
  rw [if_neg (by nlinarith), max_eq_right (iib_frac_le P hS ξ hξ), min_eq_right hpvh.le]

/-- Any equilibrium has `v < vh`. -/
lemma iib_eq_lt_vh (P : Params) (hS : P.Standing) (m sd q v ξ : ℝ) (hm : 0 ≤ m)
    (hE : IsEquilibrium P m sd q v ξ) : v < P.vh := by
  obtain ⟨hmax, hv, hξ⟩ := hE
  have hsc : P.s < P.c := hS.1
  have hcp : P.c < P.p := hS.2.1
  have hpvh := hS.2.2.2.2.2.2.1
  by_contra hcon
  have hvge : P.vh ≤ v := le_of_not_gt hcon
  have hvle : v ≤ P.vh := by
    rw [hv]; unfold vstar; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hveq : v = P.vh := le_antisymm hvle hvge
  have hGb : Gbar P v = 0 := by rw [hveq]; unfold Gbar; rw [iib_G_vh P hS]; ring
  -- profit is constant in x
  have hprof : ∀ q', profit P m sd v q' = (P.p - P.s) * min q' 0 - (P.c - P.s) * q' := by
    intro q'
    unfold profit demandLaw
    simp [hGb]
  have hq : q ≤ 0 := by
    have := hmax 0
    rw [hprof, hprof] at this
    by_contra hq; push Not at hq
    rw [min_eq_right hq.le] at this
    simp at this
    nlinarith
  have hξle : ξ ≤ 0 := by
    rw [hξ]; unfold fill2
    simp only []
    apply div_nonpos_of_nonpos_of_nonneg
    · apply integral_nonpos
      intro x
      simp only [hGb, zero_mul, sub_zero, max_eq_right hq]
      exact min_le_left _ _
    · exact mul_nonneg (le_max_right _ _) hm
  have := iib_vstar_nonpos P hS ξ hξle
  rw [← hv] at this
  linarith

end InvIntegration.Behavioral


namespace InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory

lemma iib_law_map (m sd : ℝ) (hsd : 0 < sd) :
    demandLaw m sd = (gaussianReal 0 1).map (fun z => m + sd * z) := by
  have h1 := gaussianReal_map_const_mul (μ := 0) (v := 1) sd
  have h2 : ((gaussianReal 0 1).map (fun x => sd * x)).map (fun x => x + m) =
      gaussianReal (sd * 0 + m) (NNReal.mk (sd ^ 2) (sq_nonneg _) * 1) := by
    rw [h1]; exact gaussianReal_map_add_const m
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h2
  unfold demandLaw
  have : (fun z => m + sd * z) = (fun x => x + m) ∘ (fun x => sd * x) := by
    funext z; simp [add_comm]
  rw [this, h2]
  congr 1
  · ring
  · ext; simp [Real.toNNReal_of_nonneg (sq_nonneg sd)]

lemma iib_affine_emb (m sd : ℝ) (hsd : 0 < sd) :
    MeasurableEmbedding (fun z : ℝ => m + sd * z) := by
  have h1 : MeasurableEmbedding (fun z : ℝ => sd * z) :=
    (Homeomorph.mulLeft₀ sd hsd.ne').measurableEmbedding
  have h2 : MeasurableEmbedding (fun z : ℝ => m + z) :=
    (Homeomorph.addLeft m).measurableEmbedding
  exact h2.comp h1

lemma iib_integral_std (m sd : ℝ) (hsd : 0 < sd) (f : ℝ → ℝ) :
    ∫ x, f x ∂demandLaw m sd = ∫ z, f (m + sd * z) ∂gaussianReal 0 1 := by
  rw [iib_law_map m sd hsd, (iib_affine_emb m sd hsd).integral_map]

lemma iib_integrable_id : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  exact this

lemma iib_integrable_lin (A B : ℝ) : Integrable (fun z : ℝ => A + B * z) (gaussianReal 0 1) :=
  (integrable_const A).add (iib_integrable_id.const_mul B)

/-- Any measurable function bounded by an affine function of `|z|` is integrable. -/
lemma iib_integrable_of_bound (f : ℝ → ℝ) (hf : Continuous f) (A B : ℝ)
    (hb : ∀ z, |f z| ≤ A + B * |z|) : Integrable f (gaussianReal 0 1) := by
  refine Integrable.mono' ((integrable_const A).add (iib_integrable_id.abs.const_mul B))
    hf.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
  simpa [Real.norm_eq_abs] using hb z

lemma iib_pos_interval (a b : ℝ) (hab : a < b) (s : Set ℝ) (hs : Set.Ioo a b ⊆ s) :
    gaussianReal 0 1 s ≠ 0 := by
  intro h
  have h0 : volume s = 0 := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
  have : volume (Set.Ioo a b) = 0 := measure_mono_null hs h0
  rw [Real.volume_Ioo] at this
  simp at this
  linarith

lemma iib_tail (z0 : ℝ) :
    (gaussianReal 0 1).real (Set.Ioi z0) = 1 - cdf (gaussianReal 0 1) z0 := by
  rw [cdf_eq_real, ← Set.compl_Iic, measureReal_compl measurableSet_Iic]
  simp

/-- `E[(Z - z0)⁺] = ∫_{z0}^∞ (t - z0) φ(t) dt`. -/
lemma iib_loss (z0 : ℝ) :
    ∫ z, max (z - z0) 0 ∂gaussianReal 0 1 = ∫ t in Set.Ioi z0, (t - z0) * gaussianPDFReal 0 1 t := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi z0)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [smul_eq_mul]
    rw [max_eq_left (by linarith [ht.out])]
    ring
  · intro t ht
    simp only [Set.mem_Ioi, not_lt] at ht
    simp [max_eq_right (by linarith : t - z0 ≤ 0)]

end InvIntegration.Behavioral


namespace InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory

lemma iib_Gbar_nonneg (P : Params) (hS : P.Standing) (v : ℝ) : 0 ≤ Gbar P v := by
  unfold Gbar; rw [iib_one_sub_G P hS v]
  exact setIntegral_nonneg measurableSet_Ioi (fun x _ => hS.2.2.2.2.2.2.2.2.2.1 x)

lemma iib_integrable_min (q a m sd : ℝ) :
    Integrable (fun z : ℝ => min q (a * (m + sd * z))) (gaussianReal 0 1) := by
  apply iib_integrable_of_bound _ (by fun_prop) (|q| + |a| * |m|) (|a| * |sd|)
  intro z
  have h1 : |min q (a * (m + sd * z))| ≤ |q| + |a * (m + sd * z)| := by
    rcases min_choice q (a * (m + sd * z)) with h | h <;> rw [h] <;>
      linarith [abs_nonneg q, abs_nonneg (a * (m + sd * z))]
  have h2 : |a * (m + sd * z)| ≤ |a| * |m| + |a| * |sd| * |z| := by
    rw [abs_mul]
    have := abs_add_le m (sd * z)
    rw [abs_mul] at this
    nlinarith [abs_nonneg a]
  linarith

/-- Value of the profit at the newsvendor quantity. -/
lemma iib_profit_star (P : Params) (hS : P.Standing) (m sd : ℝ) (hsd : 0 < sd) (vt : ℝ) :
    profit P m sd vt (Gbar P vt * (m + P.zh * sd)) = Gbar P vt * Pi P m sd := by
  unfold profit
  rw [iib_integral_std m sd hsd]
  beta_reduce
  set a := Gbar P vt with ha
  have ha0 : 0 ≤ a := iib_Gbar_nonneg P hS vt
  have hpt : ∀ z : ℝ, (P.p - P.s) * min (a * (m + P.zh * sd)) (a * (m + sd * z)) - (P.c - P.s) * (a * (m + P.zh * sd))
      = ((P.p - P.s) * a * m - (P.c - P.s) * (a * (m + P.zh * sd))) + ((P.p - P.s) * a * sd) * z
        - ((P.p - P.s) * a * sd) * max (z - P.zh) 0 := by
    intro z
    rcases le_or_gt P.zh z with h | h
    · rw [min_eq_left (mul_le_mul_of_nonneg_left (by nlinarith) ha0), max_eq_left (by linarith)]
      ring
    · rw [min_eq_right (mul_le_mul_of_nonneg_left (by nlinarith) ha0), max_eq_right (by linarith)]
      ring
  beta_reduce
  simp_rw [hpt]
  have hi1 : Integrable (fun z : ℝ => max (z - P.zh) 0) (gaussianReal 0 1) :=
    (iib_integrable_id.sub (integrable_const _)).pos_part
  have hA : Integrable (fun z : ℝ => ((P.p - P.s) * a * m - (P.c - P.s) * (a * (m + P.zh * sd)))
      + ((P.p - P.s) * a * sd) * z) (gaussianReal 0 1) :=
    (integrable_const _).add (iib_integrable_id.const_mul _)
  have hB : Integrable (fun z : ℝ => ((P.p - P.s) * a * sd) * max (z - P.zh) 0) (gaussianReal 0 1) :=
    hi1.const_mul _
  have hC : Integrable (fun z : ℝ => ((P.p - P.s) * a * sd) * z) (gaussianReal 0 1) :=
    iib_integrable_id.const_mul _
  rw [integral_sub hA hB, integral_add (integrable_const _) hC, integral_const,
    integral_const_mul, integral_const_mul, iib_loss]
  have h0 : ∫ z, z ∂gaussianReal 0 1 = 0 := integral_id_gaussianReal
  rw [h0]
  unfold Pi lossN
  simp
  ring

end InvIntegration.Behavioral

open InvIntegration.Behavioral MeasureTheory ProbabilityTheory in
theorem InvIntegration.Behavioral.iib_prop2 (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd)
    (vt : ℝ) :
    (∀ q : ℝ, q ≠ Gbar P vt * (m + P.zh * sd) →
      profit P m sd vt q < profit P m sd vt (Gbar P vt * (m + P.zh * sd))) ∧
    profit P m sd vt (Gbar P vt * (m + P.zh * sd)) = Gbar P vt * Pi P m sd := by
  refine ⟨?_, iib_profit_star P hS m sd hsd vt⟩
  intro q hq
  have hsc : P.s < P.c := hS.1
  have hcp : P.c < P.p := hS.2.1
  have hΦ : cdf (gaussianReal 0 1) P.zh = (P.p - P.c) / (P.p - P.s) := hS.2.2.2.2.2.2.2.2.2.2.2.2.2
  set a := Gbar P vt with ha
  have ha0 : 0 ≤ a := iib_Gbar_nonneg P hS vt
  set qs := a * (m + P.zh * sd) with hqs
  rcases ha0.lt_or_eq with hapos | ha0'
  swap
  · -- a = 0
    have hprof : ∀ q', profit P m sd vt q' = (P.p - P.s) * min q' 0 - (P.c - P.s) * q' := by
      intro q'; unfold profit demandLaw; simp [← ha, ← ha0']
    rw [hprof, hprof]
    have hqs0 : qs = 0 := by rw [hqs, ← ha0']; ring
    rw [hqs0] at hq ⊢
    rcases lt_or_gt_of_ne hq with h | h
    · rw [min_eq_left h.le]; simp; nlinarith
    · rw [min_eq_right h.le]; simp; nlinarith
  -- a > 0
  unfold profit
  rw [iib_integral_std m sd hsd, iib_integral_std m sd hsd]
  set f : ℝ → ℝ := fun z => (P.p - P.s) * min q (a * (m + sd * z)) - (P.c - P.s) * q with hf
  set I : ℝ → ℝ := (Set.Ioi P.zh).indicator (fun _ => (1:ℝ)) with hI
  set g : ℝ → ℝ := fun z => ((P.p - P.s) * min qs (a * (m + sd * z)) - (P.c - P.s) * qs)
      + (q - qs) * ((P.p - P.s) * I z - (P.c - P.s)) with hg
  have hIint : Integrable I (gaussianReal 0 1) := (integrable_const _).indicator measurableSet_Ioi
  have hfint : Integrable f (gaussianReal 0 1) :=
    ((iib_integrable_min q a m sd).const_mul _).sub (integrable_const _)
  have hg0int : Integrable (fun z : ℝ => (P.p - P.s) * min qs (a * (m + sd * z)) - (P.c - P.s) * qs)
      (gaussianReal 0 1) :=
    ((iib_integrable_min qs a m sd).const_mul _).sub (integrable_const _)
  have hgint : Integrable g (gaussianReal 0 1) :=
    hg0int.add (((hIint.const_mul _).sub (integrable_const _)).const_mul _)
  -- ∫ g = profit at qs
  have hIval : ∫ z, I z ∂gaussianReal 0 1 = (P.p - P.c) / (P.p - P.s) * 0 + (1 - (P.p - P.c) / (P.p - P.s)) := by
    rw [hI, integral_indicator_const _ measurableSet_Ioi, iib_tail, hΦ]; simp
  have hgval : ∫ z, g z ∂gaussianReal 0 1 =
      ∫ z, ((P.p - P.s) * min qs (a * (m + sd * z)) - (P.c - P.s) * qs) ∂gaussianReal 0 1 := by
    have hJ : Integrable (fun z => (q - qs) * ((P.p - P.s) * I z - (P.c - P.s))) (gaussianReal 0 1) :=
      ((hIint.const_mul _).sub (integrable_const _)).const_mul _
    have hJ2 : Integrable (fun z => (P.p - P.s) * I z) (gaussianReal 0 1) := hIint.const_mul _
    rw [hg]; beta_reduce
    rw [integral_add hg0int hJ, integral_const_mul, integral_sub hJ2 (integrable_const _),
      integral_const_mul, hIval]
    have hps : P.p - P.s ≠ 0 := by linarith
    field_simp
    simp
  rw [← hgval]
  -- pointwise comparison
  have hy : ∀ z, (qs < a * (m + sd * z) ↔ P.zh < z) := by
    intro z
    rw [hqs]
    constructor
    · intro h; by_contra h'; push Not at h'
      have : a * (m + sd * z) ≤ a * (m + P.zh * sd) := mul_le_mul_of_nonneg_left (by nlinarith) ha0
      linarith
    · intro h
      exact mul_lt_mul_of_pos_left (by nlinarith) hapos
  have hle : ∀ z, f z ≤ g z := by
    intro z
    simp only [hf, hg, hI]
    by_cases hz : P.zh < z
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hz)]
      have h1 := (hy z).mpr hz
      rw [min_eq_left h1.le]
      have := min_le_left q (a * (m + sd * z))
      nlinarith
    · rw [Set.indicator_of_notMem (by simpa using hz)]
      have h1 : a * (m + sd * z) ≤ qs := not_lt.mp (fun h => hz ((hy z).mp h))
      rw [min_eq_right h1]
      have := min_le_right q (a * (m + sd * z))
      nlinarith
  have hasd : 0 < a * sd := mul_pos hapos hsd
  have hlt : gaussianReal 0 1 (Function.support (fun z => g z - f z)) ≠ 0 := by
    rcases lt_or_gt_of_ne hq with hql | hqg
    · -- q < qs: interval left of zh
      apply iib_pos_interval (P.zh - (qs - q) / (a * sd)) P.zh
        (by have : 0 < (qs - q) / (a * sd) := div_pos (by linarith) hasd; linarith)
      intro z hz
      rw [Function.mem_support]
      have hz2 : ¬ P.zh < z := not_lt.mpr hz.2.le
      have hyz : a * (m + sd * z) < qs := by
        rw [hqs]; exact mul_lt_mul_of_pos_left (by nlinarith [hz.2]) hapos
      have hyq : q < a * (m + sd * z) := by
        have h1 := hz.1
        rw [sub_lt_comm, lt_div_iff₀ hasd] at h1
        rw [hqs] at h1; nlinarith
      simp only [hf, hg, hI, Set.indicator_of_notMem (show z ∉ Set.Ioi P.zh by simpa using hz2),
        min_eq_right hyz.le, min_eq_left hyq.le]
      intro h
      nlinarith
    · apply iib_pos_interval P.zh (P.zh + (q - qs) / (a * sd))
        (by have : 0 < (q - qs) / (a * sd) := div_pos (by linarith) hasd; linarith)
      intro z hz
      rw [Function.mem_support]
      have hz1 : P.zh < z := hz.1
      have hyz : qs < a * (m + sd * z) := (hy z).mpr hz1
      have hyq : a * (m + sd * z) < q := by
        have h1 := hz.2
        rw [← sub_lt_iff_lt_add', lt_div_iff₀ hasd] at h1
        rw [hqs] at h1; nlinarith
      simp only [hf, hg, hI, Set.indicator_of_mem (show z ∈ Set.Ioi P.zh from hz1),
        min_eq_left hyz.le, min_eq_right hyq.le]
      intro h
      nlinarith
  have hpos : 0 < ∫ z, (g z - f z) ∂gaussianReal 0 1 := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall (fun z => sub_nonneg.mpr (hle z))) (hgint.sub hfint)]
    exact pos_iff_ne_zero.mpr hlt
  rw [integral_sub hgint hfint] at hpos
  show ∫ z, f z ∂gaussianReal 0 1 < ∫ z, g z ∂gaussianReal 0 1
  linarith


namespace InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory

lemma iib_d2_pos (P : Params) (hS : P.Standing) (v : ℝ) (hv : P.p ≤ v) :
    0 < G P v - G P (P.s / P.δ) := by
  have hδ : 0 < P.δ := hS.2.2.1
  have hsδ : P.s < P.δ * P.p := hS.2.2.2.2.1
  have hvlp : P.vl < P.p := hS.2.2.2.2.2.1
  have hpvh : P.p < P.vh := hS.2.2.2.2.2.2.1
  have hsupp := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have h1 : P.s / P.δ < P.p := by rw [div_lt_iff₀ hδ]; linarith
  rw [iib_G_sub P hS _ _ (by linarith)]
  set a0 := max (P.s / P.δ) ((P.vl + P.p) / 2)
  have ha1 : P.vl < a0 := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have ha2 : a0 < P.p := max_lt h1 (by linarith)
  apply iib_pos_of_sub P hS (Set.Ioo a0 P.p) _ _ (hsupp a0 P.p ha1 hpvh ha2)
  intro x hx
  exact ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, le_trans hx.2.le hv⟩

end InvIntegration.Behavioral

open InvIntegration.Behavioral MeasureTheory ProbabilityTheory in
theorem InvIntegration.Behavioral.iib_eq14 (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd)
    (q v ξ : ℝ) (hE : IsEquilibrium P m sd q v ξ) :
    ξ = sd / m * ∫ x, min (Gbar P v / (G P v - G P (P.s / P.δ)) * max (P.zh - x) 0) (x + m / sd)
      ∂ gaussianReal 0 1 := by
  obtain ⟨hmax, hv, hξ⟩ := hE
  have hq : q = Gbar P v * (m + P.zh * sd) := by
    by_contra hne
    have h1 := (iib_prop2 P hS m sd hm hsd v).1 q hne
    have h2 := hmax (Gbar P v * (m + P.zh * sd))
    linarith
  have hvp : P.p ≤ v := by rw [hv]; exact iib_vstar_ge P hS ξ
  have hD0' : 0 < G P v - G P (P.s / P.δ) := iib_d2_pos P hS v hvp
  rw [hξ]
  unfold fill2
  simp only []
  rw [max_eq_left hD0'.le, iib_integral_std m sd hsd]
  beta_reduce
  set D := G P v - G P (P.s / P.δ) with hD
  have hD0 : 0 < D := hD0'
  set a := Gbar P v with ha
  have ha0 : 0 ≤ a := iib_Gbar_nonneg P hS v
  have hpt : ∀ z : ℝ, min (max (q - a * (m + sd * z)) 0) (D * (m + sd * z))
      = (D * sd) * min (a / D * max (P.zh - z) 0) (z + m / sd) := by
    intro z
    have e1 : max (q - a * (m + sd * z)) 0 = (D * sd) * (a / D * max (P.zh - z) 0) := by
      rw [hq]
      have : a * (m + P.zh * sd) - a * (m + sd * z) = (a * sd) * (P.zh - z) := by ring
      rw [this]
      field_simp
      rcases le_or_gt z P.zh with h | h
      · rw [max_eq_left (by nlinarith [mul_nonneg ha0 hsd.le]), max_eq_left (by linarith)]
      · rw [max_eq_right (by nlinarith [mul_nonneg ha0 hsd.le]), max_eq_right (by linarith)]
        ring
    have e2 : D * (m + sd * z) = (D * sd) * (z + m / sd) := by field_simp; ring
    rw [e1, e2, mul_min_of_nonneg _ _ (mul_pos hD0 hsd).le]
  simp_rw [hpt]
  rw [integral_const_mul]
  field_simp


namespace InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory

lemma iib_G_mono (P : Params) (hS : P.Standing) (a b : ℝ) (hab : a ≤ b) : G P a ≤ G P b := by
  have := iib_G_sub P hS a b hab
  have h2 : 0 ≤ ∫ t in Set.Ioc a b, P.g t :=
    setIntegral_nonneg measurableSet_Ioc (fun x _ => hS.2.2.2.2.2.2.2.2.2.1 x)
  linarith

lemma iib_frac_mono (P : Params) (hS : P.Standing) (ξ1 ξ2 : ℝ) (h12 : ξ1 ≤ ξ2)
    (h2 : ξ2 * P.δ < 1) :
    (P.p - ξ1 * P.s) / (1 - ξ1 * P.δ) ≤ (P.p - ξ2 * P.s) / (1 - ξ2 * P.δ) := by
  have hδ : 0 < P.δ := hS.2.2.1
  have hsδ : P.s < P.δ * P.p := hS.2.2.2.2.1
  have h1 : 0 < 1 - ξ1 * P.δ := by nlinarith
  have h2' : 0 < 1 - ξ2 * P.δ := by linarith
  rw [div_le_div_iff₀ h1 h2']
  nlinarith

lemma iib_eq8 (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m)
    (q v ξ : ℝ) (hE : IsEquilibrium P m sd q v ξ) :
    ξ * P.δ < 1 ∧
    v = max ((P.p - ξ * P.s) / (1 - ξ * P.δ)) P.p ∧
    (0 ≤ ξ → v = (P.p - ξ * P.s) / (1 - ξ * P.δ)) := by
  have hlt := iib_eq_lt_vh P hS m sd q v ξ hm.le hE
  have hv := hE.2.1
  unfold vstar at hv
  split_ifs at hv with h
  · exact absurd hv (ne_of_lt hlt)
  · push Not at h
    have hv2 : v = max ((P.p - ξ * P.s) / (1 - ξ * P.δ)) P.p := by
      rcases min_choice P.vh (max ((P.p - ξ * P.s) / (1 - ξ * P.δ)) P.p) with hc | hc
      · rw [hc] at hv; exact absurd hv (ne_of_lt hlt)
      · rw [hc] at hv; exact hv
    refine ⟨h, hv2, fun hξ => ?_⟩
    rw [hv2, max_eq_left (iib_frac_ge P hS ξ hξ h)]

/-- The integrand of (14). -/
noncomputable def iibK (P : Params) (B c z : ℝ) : ℝ := min (B * max (P.zh - z) 0) (z + c)

lemma iib_K_integrable (P : Params) (B c : ℝ) :
    Integrable (fun z => iibK P B c z) (gaussianReal 0 1) := by
  unfold iibK
  apply iib_integrable_of_bound _ (by fun_prop) (|B| * |P.zh| + |c|) (|B| + 1)
  intro z
  have hM : |max (P.zh - z) 0| ≤ |P.zh| + |z| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le _ (by positivity)
    have := abs_sub (P.zh) z
    linarith [le_abs_self (P.zh - z)]
  have h1 : |B * max (P.zh - z) 0| ≤ |B| * |P.zh| + |B| * |z| := by
    rw [abs_mul]; nlinarith [abs_nonneg B]
  have h2 : |z + c| ≤ |z| + |c| := abs_add_le _ _
  rcases min_choice (B * max (P.zh - z) 0) (z + c) with h | h <;> rw [h] <;>
    nlinarith [abs_nonneg z, abs_nonneg B, abs_nonneg c, abs_nonneg P.zh]

lemma iib_K_mono (P : Params) (B1 B2 c z : ℝ) (h : B1 ≤ B2) : iibK P B1 c z ≤ iibK P B2 c z := by
  unfold iibK
  exact min_le_min_right _ (mul_le_mul_of_nonneg_right h (le_max_right _ _))

/-- The demand ratio `B(v) = Ḡ(v)/(G(v) − G(s/δ))` is nonincreasing on `[p, ∞)`. -/
lemma iib_B_anti (P : Params) (hS : P.Standing) (v1 v2 : ℝ) (hp : P.p ≤ v1) (h12 : v1 ≤ v2) :
    Gbar P v2 / (G P v2 - G P (P.s / P.δ)) ≤ Gbar P v1 / (G P v1 - G P (P.s / P.δ)) := by
  have hD1 := iib_d2_pos P hS v1 hp
  have hD2 := iib_d2_pos P hS v2 (le_trans hp h12)
  have hG := iib_G_mono P hS v1 v2 h12
  have ha2 := iib_Gbar_nonneg P hS v2
  rw [div_le_div_iff₀ hD2 hD1]
  unfold Gbar at *
  nlinarith

/-- Equilibria with the same coefficient of variation have the same fill rate. -/
lemma iib_xi_unique (P : Params) (hS : P.Standing) (m sd m' sd' : ℝ) (hm : 0 < m) (hsd : 0 < sd)
    (hm' : 0 < m') (hsd' : 0 < sd') (hcv : sd / m = sd' / m')
    (q v ξ q' v' ξ' : ℝ) (hE : IsEquilibrium P m sd q v ξ) (hE' : IsEquilibrium P m' sd' q' v' ξ') :
    ξ = ξ' := by
  have hcv' : m / sd = m' / sd' := by
    rw [← inv_div, hcv, inv_div]
  have key : ∀ (m sd m' sd' : ℝ), 0 < m → 0 < sd → 0 < m' → 0 < sd' → sd / m = sd' / m' →
      m / sd = m' / sd' → ∀ q v ξ q' v' ξ', IsEquilibrium P m sd q v ξ →
      IsEquilibrium P m' sd' q' v' ξ' → ξ < ξ' → False := by
    intro m sd m' sd' hm hsd hm' hsd' hcv hcv' q v ξ q' v' ξ' hE hE' hlt
    have e1 := iib_eq14 P hS m sd hm hsd q v ξ hE
    have e2 := iib_eq14 P hS m' sd' hm' hsd' q' v' ξ' hE'
    obtain ⟨-, hv1, -⟩ := iib_eq8 P hS m sd hm q v ξ hE
    obtain ⟨h2δ, hv2, -⟩ := iib_eq8 P hS m' sd' hm' q' v' ξ' hE'
    have hvp : P.p ≤ v := by rw [hv1]; exact le_max_right _ _
    have hvv : v ≤ v' := by
      rw [hv1, hv2]
      exact max_le_max (iib_frac_mono P hS ξ ξ' hlt.le h2δ) le_rfl
    have hB := iib_B_anti P hS v v' hvp hvv
    have hint : ∫ x, min (Gbar P v' / (G P v' - G P (P.s / P.δ)) * max (P.zh - x) 0) (x + m' / sd')
          ∂gaussianReal 0 1 ≤
        ∫ x, min (Gbar P v / (G P v - G P (P.s / P.δ)) * max (P.zh - x) 0) (x + m / sd)
          ∂gaussianReal 0 1 := by
      rw [← hcv']
      exact integral_mono (iib_K_integrable P _ _) (iib_K_integrable P _ _)
        (fun z => iib_K_mono P _ _ _ z hB)
    rw [← hcv] at e2
    have hc : 0 < sd / m := div_pos hsd hm
    have := mul_le_mul_of_nonneg_left hint hc.le
    linarith
  rcases lt_trichotomy ξ ξ' with h | h | h
  · exact (key m sd m' sd' hm hsd hm' hsd' hcv hcv' q v ξ q' v' ξ' hE hE' h).elim
  · exact h
  · exact (key m' sd' m sd hm' hsd' hm hsd hcv.symm hcv'.symm q' v' ξ' q v ξ hE' hE h).elim

end InvIntegration.Behavioral


namespace InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory

lemma iib_G_cont (P : Params) (hS : P.Standing) : Continuous (G P) := by
  have hint : Integrable P.g := hS.2.2.2.2.2.2.2.2.1
  have hc := intervalIntegral.continuous_primitive (μ := volume) (f := P.g)
    (fun a b => hint.intervalIntegrable) 0
  have heq : G P = fun x => G P 0 + ∫ t in (0:ℝ)..x, P.g t := by
    funext x
    rcases le_total 0 x with h | h
    · rw [intervalIntegral.integral_of_le h, ← iib_G_sub P hS 0 x h]; ring
    · rw [intervalIntegral.integral_of_ge h, ← iib_G_sub P hS x 0 h]; ring
  rw [heq]
  exact continuous_const.add hc

lemma iib_lt_one_mul (P : Params) (hS : P.Standing) (ξ : ℝ) (h : ξ < 1) : ξ * P.δ < 1 := by
  have hδ : 0 < P.δ := hS.2.2.1
  have hδ1 : P.δ ≤ 1 := hS.2.2.2.1
  rcases le_or_gt ξ 0 with h0 | h0
  · nlinarith
  · nlinarith

lemma iib_vstar_eq (P : Params) (hS : P.Standing) (ξ : ℝ) (h : ξ < 1) :
    vstar P ξ = min P.vh (max ((P.p - ξ * P.s) / (1 - ξ * P.δ)) P.p) := by
  unfold vstar
  rw [if_neg (not_le.mpr (iib_lt_one_mul P hS ξ h))]

lemma iib_vstar_contOn (P : Params) (hS : P.Standing) : ContinuousOn (vstar P) (Set.Iio 1) := by
  have : ContinuousOn (fun ξ => min P.vh (max ((P.p - ξ * P.s) / (1 - ξ * P.δ)) P.p)) (Set.Iio 1) := by
    have hfr : ContinuousOn (fun ξ => (P.p - ξ * P.s) / (1 - ξ * P.δ)) (Set.Iio 1) := by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro ξ hξ
      have := iib_lt_one_mul P hS ξ hξ
      linarith
    exact continuousOn_const.inf (hfr.sup continuousOn_const)
  exact this.congr (fun ξ hξ => iib_vstar_eq P hS ξ hξ)

lemma iib_vstar_mono (P : Params) (hS : P.Standing) (ξ1 ξ2 : ℝ) (h12 : ξ1 ≤ ξ2) (h2 : ξ2 < 1) :
    vstar P ξ1 ≤ vstar P ξ2 := by
  rw [iib_vstar_eq P hS ξ1 (lt_of_le_of_lt h12 h2), iib_vstar_eq P hS ξ2 h2]
  exact min_le_min le_rfl (max_le_max
    (iib_frac_mono P hS ξ1 ξ2 h12 (iib_lt_one_mul P hS ξ2 h2)) le_rfl)

noncomputable def iibB (P : Params) (v : ℝ) : ℝ := Gbar P v / (G P v - G P (P.s / P.δ))

lemma iib_B_nonneg (P : Params) (hS : P.Standing) (v : ℝ) (hv : P.p ≤ v) : 0 ≤ iibB P v :=
  div_nonneg (iib_Gbar_nonneg P hS v) (iib_d2_pos P hS v hv).le

lemma iib_B_contOn (P : Params) (hS : P.Standing) : ContinuousOn (iibB P) (Set.Ici P.p) := by
  have hG := iib_G_cont P hS
  unfold iibB Gbar
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro v hv
  exact (iib_d2_pos P hS v hv).ne'

noncomputable def iibT (P : Params) (c k ξ : ℝ) : ℝ :=
  c * ∫ z, iibK P (iibB P (vstar P ξ)) k z ∂gaussianReal 0 1

lemma iib_T_anti (P : Params) (hS : P.Standing) (c k : ℝ) (hc : 0 ≤ c) (ξ1 ξ2 : ℝ)
    (h12 : ξ1 ≤ ξ2) (h2 : ξ2 < 1) : iibT P c k ξ2 ≤ iibT P c k ξ1 := by
  unfold iibT
  apply mul_le_mul_of_nonneg_left _ hc
  apply integral_mono (iib_K_integrable P _ _) (iib_K_integrable P _ _)
  intro z
  apply iib_K_mono
  exact iib_B_anti P hS _ _ (iib_vstar_ge P hS ξ1) (iib_vstar_mono P hS ξ1 ξ2 h12 h2)

lemma iib_K_bound (P : Params) (B k z : ℝ) (hB : 0 ≤ B) :
    |iibK P B k z| ≤ B * (|P.zh| + |z|) + |z| + |k| := by
  unfold iibK
  have hM : |max (P.zh - z) 0| ≤ |P.zh| + |z| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le _ (by positivity)
    have := abs_sub (P.zh) z
    linarith [le_abs_self (P.zh - z)]
  have h1 : |B * max (P.zh - z) 0| ≤ B * (|P.zh| + |z|) := by
    rw [abs_mul, abs_of_nonneg hB]; exact mul_le_mul_of_nonneg_left hM hB
  have h2 : |z + k| ≤ |z| + |k| := abs_add_le _ _
  rcases min_choice (B * max (P.zh - z) 0) (z + k) with h | h <;> rw [h] <;>
    nlinarith [abs_nonneg z, abs_nonneg k, abs_nonneg P.zh, mul_nonneg hB (abs_nonneg z)]

lemma iib_T_contOn (P : Params) (hS : P.Standing) (c k a b : ℝ) (hb : b < 1) :
    ContinuousOn (iibT P c k) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Set.Iio 1 := fun x hx => lt_of_le_of_lt hx.2 hb
  have hβ : ContinuousOn (fun ξ => iibB P (vstar P ξ)) (Set.Icc a b) :=
    (iib_B_contOn P hS).comp ((iib_vstar_contOn P hS).mono hsub)
      (fun ξ _ => Set.mem_Ici.mpr (iib_vstar_ge P hS ξ))
  set Bp := iibB P P.p
  have hBle : ∀ ξ, iibB P (vstar P ξ) ≤ Bp := fun ξ =>
    iib_B_anti P hS P.p _ le_rfl (iib_vstar_ge P hS ξ)
  unfold iibT
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_of_dominated (bound := fun z => Bp * (|P.zh| + |z|) + |z| + |k|)
  · intro ξ _
    exact (iib_K_integrable P _ _).aestronglyMeasurable
  · intro ξ _
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs]
    have hB0 := iib_B_nonneg P hS _ (iib_vstar_ge P hS ξ)
    refine le_trans (iib_K_bound P _ k z hB0) ?_
    have := hBle ξ
    nlinarith [abs_nonneg z, abs_nonneg P.zh]
  · exact ((((integrable_const |P.zh|).add (iib_integrable_id.abs)).const_mul Bp).add
      iib_integrable_id.abs).add (integrable_const |k|)
  · refine Filter.Eventually.of_forall (fun z => ?_)
    unfold iibK
    exact (hβ.mul continuousOn_const).inf continuousOn_const

lemma iib_T0_lt (P : Params) (hS : P.Standing) (c k : ℝ) (hc : 0 < c) (hck : c * k = 1) (ξ : ℝ) :
    iibT P c k ξ < 1 := by
  unfold iibT
  set B := iibB P (vstar P ξ)
  have hB0 : 0 ≤ B := iib_B_nonneg P hS _ (iib_vstar_ge P hS ξ)
  have hlin : Integrable (fun z : ℝ => z + k) (gaussianReal 0 1) :=
    iib_integrable_id.add (integrable_const _)
  have hval : ∫ z, (z + k) ∂gaussianReal 0 1 = k := by
    rw [integral_add iib_integrable_id (integrable_const _), integral_id_gaussianReal]; simp
  have hlt : ∫ z, iibK P B k z ∂gaussianReal 0 1 < ∫ z, (z + k) ∂gaussianReal 0 1 := by
    rw [← sub_pos, ← integral_sub hlin (iib_K_integrable P _ _)]
    rw [integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall (fun z => sub_nonneg.mpr (show iibK P B k z ≤ z + k from min_le_right _ _)))
      (hlin.sub (iib_K_integrable P _ _))]
    apply pos_iff_ne_zero.mpr
    set M := max P.zh (-k)
    apply iib_pos_interval M (M + 1) (by linarith)
    intro z hz
    rw [Function.mem_support]
    have h1 : P.zh < z := lt_of_le_of_lt (le_max_left _ _) hz.1
    have h2 : -k < z := lt_of_le_of_lt (le_max_right _ _) hz.1
    simp only [Pi.sub_apply, iibK, max_eq_right (by linarith : P.zh - z ≤ 0), mul_zero,
      min_eq_left (by linarith : (0:ℝ) ≤ z + k)]
    linarith
  rw [hval] at hlt
  have := mul_lt_mul_of_pos_left hlt hc
  linarith

lemma iib_fixed_point (P : Params) (hS : P.Standing) (c k : ℝ) (hc : 0 < c) (hck : c * k = 1) :
    ∃ ξ, ξ < 1 ∧ iibT P c k ξ = ξ := by
  set T0 := iibT P c k 0
  have hT0 : T0 < 1 := iib_T0_lt P hS c k hc hck 0
  set hi := (max T0 0 + 1) / 2
  have hhi1 : hi < 1 := by
    have : max T0 0 < 1 := max_lt hT0 one_pos
    simp only [hi]; linarith
  have hhi0 : 0 ≤ hi := by simp only [hi]; linarith [le_max_right T0 0]
  have hThi : iibT P c k hi ≤ T0 := iib_T_anti P hS c k hc.le 0 hi hhi0 hhi1
  have hThi' : iibT P c k hi < hi := by
    simp only [hi] at hThi ⊢; linarith [le_max_left T0 0, le_max_right T0 0]
  set lo := iibT P c k hi - 1
  have hlohi : lo ≤ hi := by simp only [lo]; linarith
  have hTlo : iibT P c k hi ≤ iibT P c k lo := iib_T_anti P hS c k hc.le lo hi hlohi hhi1
  have hcont : ContinuousOn (fun ξ => ξ - iibT P c k ξ) (Set.Icc lo hi) :=
    continuousOn_id.sub (iib_T_contOn P hS c k lo hi hhi1)
  have h0 : (0:ℝ) ∈ Set.Icc ((fun ξ => ξ - iibT P c k ξ) lo) ((fun ξ => ξ - iibT P c k ξ) hi) := by
    simp only [Set.mem_Icc]
    constructor <;> simp only [lo] at hTlo ⊢ <;> linarith
  obtain ⟨ξ, hξ, hξ0⟩ := intermediate_value_Icc hlohi hcont h0
  refine ⟨ξ, lt_of_le_of_lt hξ.2 hhi1, ?_⟩
  simp only at hξ0
  linarith

lemma iib_fill2_star (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd)
    (v : ℝ) (hvp : P.p ≤ v) (q : ℝ) (hq : q = Gbar P v * (m + P.zh * sd)) :
    fill2 P m sd q v = sd / m * ∫ x, min (Gbar P v / (G P v - G P (P.s / P.δ)) * max (P.zh - x) 0) (x + m / sd)
      ∂ gaussianReal 0 1 := by
  have hD0' : 0 < G P v - G P (P.s / P.δ) := iib_d2_pos P hS v hvp
  unfold fill2
  simp only []
  rw [max_eq_left hD0'.le, iib_integral_std m sd hsd]
  beta_reduce
  set D := G P v - G P (P.s / P.δ) with hD
  have hD0 : 0 < D := hD0'
  set a := Gbar P v with ha
  have ha0 : 0 ≤ a := iib_Gbar_nonneg P hS v
  have hpt : ∀ z : ℝ, min (max (q - a * (m + sd * z)) 0) (D * (m + sd * z))
      = (D * sd) * min (a / D * max (P.zh - z) 0) (z + m / sd) := by
    intro z
    have e1 : max (q - a * (m + sd * z)) 0 = (D * sd) * (a / D * max (P.zh - z) 0) := by
      rw [hq]
      have : a * (m + P.zh * sd) - a * (m + sd * z) = (a * sd) * (P.zh - z) := by ring
      rw [this]
      field_simp
      rcases le_or_gt z P.zh with h | h
      · rw [max_eq_left (by nlinarith [mul_nonneg ha0 hsd.le]), max_eq_left (by linarith)]
      · rw [max_eq_right (by nlinarith [mul_nonneg ha0 hsd.le]), max_eq_right (by linarith)]
        ring
    have e2 : D * (m + sd * z) = (D * sd) * (z + m / sd) := by field_simp; ring
    rw [e1, e2, mul_min_of_nonneg _ _ (mul_pos hD0 hsd).le]
  simp_rw [hpt]
  rw [integral_const_mul]
  field_simp

end InvIntegration.Behavioral

open InvIntegration.Behavioral MeasureTheory ProbabilityTheory in
theorem InvIntegration.Behavioral.iib_prop3 (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd) :
    (∃ q v ξ : ℝ, IsEquilibrium P m sd q v ξ ∧ v < P.vh) ∧
    (∀ q v ξ q' v' ξ' : ℝ, IsEquilibrium P m sd q v ξ → IsEquilibrium P m sd q' v' ξ' →
      q = q' ∧ v = v' ∧ ξ = ξ') := by
  constructor
  · obtain ⟨ξ, hξ1, hfix⟩ := iib_fixed_point P hS (sd / m) (m / sd) (div_pos hsd hm)
      (by field_simp)
    set v := vstar P ξ
    have hvp : P.p ≤ v := iib_vstar_ge P hS ξ
    set q := Gbar P v * (m + P.zh * sd)
    have hE : IsEquilibrium P m sd q v ξ := by
      refine ⟨?_, rfl, ?_⟩
      · intro q'
        by_cases h : q' = q
        · rw [h]
        · exact ((iib_prop2 P hS m sd hm hsd v).1 q' h).le
      · rw [iib_fill2_star P hS m sd hm hsd v hvp q rfl, ← hfix]
        rfl
    exact ⟨q, v, ξ, hE, iib_eq_lt_vh P hS m sd q v ξ hm.le hE⟩
  · intro q v ξ q' v' ξ' hE hE'
    have hξ := iib_xi_unique P hS m sd m sd hm hsd hm hsd rfl q v ξ q' v' ξ' hE hE'
    have hv : v = v' := by
      rw [hE.2.1, hE'.2.1, hξ]
    have hq : ∀ q v ξ, IsEquilibrium P m sd q v ξ → q = Gbar P v * (m + P.zh * sd) := by
      intro q v ξ hE
      by_contra hne
      have h1 := (iib_prop2 P hS m sd hm hsd v).1 q hne
      have h2 := hE.1 (Gbar P v * (m + P.zh * sd))
      linarith
    refine ⟨?_, hv, hξ⟩
    rw [hq q v ξ hE, hq q' v' ξ' hE', hv]


namespace InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory Filter Topology

/-- The fixed-point map in the form `H(t, c) = E[min(c B(v*(t)) (ẑ − X)⁺, cX + 1)]`. -/
noncomputable def iibH (P : Params) (t c : ℝ) : ℝ :=
  ∫ z, min (c * (iibB P (vstar P t) * max (P.zh - z) 0)) (c * z + 1) ∂gaussianReal 0 1

lemma iib_Hint (P : Params) (B c : ℝ) :
    Integrable (fun z : ℝ => min (c * (B * max (P.zh - z) 0)) (c * z + 1)) (gaussianReal 0 1) := by
  apply iib_integrable_of_bound _ (by fun_prop) (|c| * |B| * |P.zh| + 1) (|c| * |B| + |c|)
  intro z
  have hM : |max (P.zh - z) 0| ≤ |P.zh| + |z| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le _ (by positivity)
    have := abs_sub (P.zh) z
    linarith [le_abs_self (P.zh - z)]
  have h1 : |c * (B * max (P.zh - z) 0)| ≤ |c| * |B| * |P.zh| + |c| * |B| * |z| := by
    rw [abs_mul, abs_mul]
    have := mul_le_mul_of_nonneg_left hM (mul_nonneg (abs_nonneg c) (abs_nonneg B))
    nlinarith
  have h2 : |c * z + 1| ≤ |c| * |z| + 1 := by
    have := abs_add_le (c * z) 1; rw [abs_mul] at this; simpa using this
  rcases min_choice (c * (B * max (P.zh - z) 0)) (c * z + 1) with h | h <;> rw [h] <;>
    nlinarith [abs_nonneg z, abs_nonneg c, abs_nonneg B, abs_nonneg P.zh,
      mul_nonneg (abs_nonneg c) (abs_nonneg z), mul_nonneg (mul_nonneg (abs_nonneg c) (abs_nonneg B)) (abs_nonneg z),
      mul_nonneg (mul_nonneg (abs_nonneg c) (abs_nonneg B)) (abs_nonneg P.zh)]

lemma iib_T_eq_H (P : Params) (t c : ℝ) (hc : 0 < c) : iibT P c (1 / c) t = iibH P t c := by
  unfold iibT iibH
  rw [← integral_const_mul]
  congr 1; funext z
  unfold iibK
  rw [mul_min_of_nonneg _ _ hc.le]
  congr 1
  field_simp

lemma iib_H_anti (P : Params) (hS : P.Standing) (c : ℝ) (hc : 0 ≤ c) (t1 t2 : ℝ) (h12 : t1 ≤ t2)
    (h2 : t2 < 1) : iibH P t2 c ≤ iibH P t1 c := by
  unfold iibH
  apply integral_mono (iib_Hint P _ _) (iib_Hint P _ _)
  intro z
  apply min_le_min_right
  apply mul_le_mul_of_nonneg_left _ hc
  exact mul_le_mul_of_nonneg_right
    (iib_B_anti P hS _ _ (iib_vstar_ge P hS t1) (iib_vstar_mono P hS t1 t2 h12 h2)) (le_max_right _ _)

lemma iib_H_zero (P : Params) (t : ℝ) : iibH P t 0 = 0 := by
  unfold iibH; simp

lemma iib_H_concave (P : Params) (hS : P.Standing) (t c1 c2 c3 : ℝ) (h12 : c1 ≤ c2) (h23 : c2 ≤ c3) :
    (c3 - c2) * iibH P t c1 + (c2 - c1) * iibH P t c3 ≤ (c3 - c1) * iibH P t c2 := by
  set B := iibB P (vstar P t)
  have hB : 0 ≤ B := iib_B_nonneg P hS _ (iib_vstar_ge P hS t)
  unfold iibH
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((iib_Hint P B c1).const_mul _) ((iib_Hint P B c3).const_mul _)]
  apply integral_mono (((iib_Hint P B c1).const_mul _).add ((iib_Hint P B c3).const_mul _))
    ((iib_Hint P B c2).const_mul _)
  intro z
  simp only [Pi.add_apply]
  set a := B * max (P.zh - z) 0
  have ha : 0 ≤ a := mul_nonneg hB (le_max_right _ _)
  have e1 : 0 ≤ c3 - c2 := by linarith
  have e2 : 0 ≤ c2 - c1 := by linarith
  have k1 := min_le_left (c1 * a) (c1 * z + 1)
  have k2 := min_le_right (c1 * a) (c1 * z + 1)
  have k3 := min_le_left (c3 * a) (c3 * z + 1)
  have k4 := min_le_right (c3 * a) (c3 * z + 1)
  rw [mul_min_of_nonneg _ _ (by linarith : (0:ℝ) ≤ c3 - c1)]
  apply le_min
  · nlinarith [mul_le_mul_of_nonneg_left k1 e1, mul_le_mul_of_nonneg_left k3 e2]
  · nlinarith [mul_le_mul_of_nonneg_left k2 e1, mul_le_mul_of_nonneg_left k4 e2]

lemma iib_H_cont (P : Params) (hS : P.Standing) (t : ℝ) : Continuous (fun c => iibH P t c) := by
  set B := iibB P (vstar P t)
  have hB : 0 ≤ B := iib_B_nonneg P hS _ (iib_vstar_ge P hS t)
  unfold iibH
  rw [continuous_iff_continuousAt]
  intro c0
  set C := |c0| + 1
  apply continuousAt_of_dominated
    (bound := fun z => C * (B * (|P.zh| + |z|)) + (C * |z| + 1))
  · exact Eventually.of_forall (fun c => (iib_Hint P B c).aestronglyMeasurable)
  · have hnb : ∀ᶠ c in 𝓝 c0, |c| ≤ C := by
      have : Set.Icc (c0 - 1) (c0 + 1) ∈ 𝓝 c0 := Icc_mem_nhds (by linarith) (by linarith)
      filter_upwards [this] with c hc
      rw [abs_le] at *
      simp only [C]
      constructor <;> cases abs_cases c0 <;> linarith [hc.1, hc.2]
    filter_upwards [hnb] with c hc
    refine Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs]
    have hM : |max (P.zh - z) 0| ≤ |P.zh| + |z| := by
      rw [abs_of_nonneg (le_max_right _ _)]
      apply max_le _ (by positivity)
      have := abs_sub (P.zh) z
      linarith [le_abs_self (P.zh - z)]
    have hBM : |B * max (P.zh - z) 0| ≤ B * (|P.zh| + |z|) := by
      rw [abs_mul, abs_of_nonneg hB]; exact mul_le_mul_of_nonneg_left hM hB
    have h1 : |c * (B * max (P.zh - z) 0)| ≤ C * (B * (|P.zh| + |z|)) := by
      rw [abs_mul]; exact mul_le_mul hc hBM (abs_nonneg _) (by positivity)
    have h2 : |c * z + 1| ≤ C * |z| + 1 := by
      have := abs_add_le (c * z) 1; rw [abs_mul] at this
      have := mul_le_mul_of_nonneg_right hc (abs_nonneg z)
      simp at *; linarith
    have hpos1 : 0 ≤ C * (B * (|P.zh| + |z|)) := by positivity
    have hpos2 : 0 ≤ C * |z| + 1 := by positivity
    rcases min_choice (c * (B * max (P.zh - z) 0)) (c * z + 1) with h | h <;> rw [h] <;> linarith
  · exact (((integrable_const _).add iib_integrable_id.abs).const_mul B |>.const_mul C).add
      ((iib_integrable_id.abs.const_mul C).add (integrable_const 1))
  · exact Eventually.of_forall (fun z => by fun_prop)

/-- The fill rate as a function of the coefficient of variation. -/
noncomputable def iibXi (P : Params) (c : ℝ) : ℝ :=
  Classical.epsilon (fun ξ => ∃ q v, IsEquilibrium P 1 c q v ξ)

lemma iib_Xi_spec (P : Params) (hS : P.Standing) (c : ℝ) (hc : 0 < c) :
    ∃ q v, IsEquilibrium P 1 c q v (iibXi P c) := by
  obtain ⟨q, v, ξ, hE, -⟩ := (iib_prop3 P hS 1 c one_pos hc).1
  exact Classical.epsilon_spec (p := fun ξ => ∃ q v, IsEquilibrium P 1 c q v ξ) ⟨ξ, q, v, hE⟩

lemma iib_Xi_eq (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd)
    (q v ξ : ℝ) (hE : IsEquilibrium P m sd q v ξ) : ξ = iibXi P (sd / m) := by
  obtain ⟨q', v', hE'⟩ := iib_Xi_spec P hS (sd / m) (div_pos hsd hm)
  exact iib_xi_unique P hS m sd 1 (sd / m) hm hsd one_pos (div_pos hsd hm) (by simp)
    q v ξ q' v' _ hE hE'

lemma iib_Xi_fp (P : Params) (hS : P.Standing) (c : ℝ) (hc : 0 < c) :
    iibXi P c = iibH P (iibXi P c) c := by
  obtain ⟨q, v, hE⟩ := iib_Xi_spec P hS c hc
  have e := iib_eq14 P hS 1 c one_pos hc q v _ hE
  have hv : v = vstar P (iibXi P c) := hE.2.1
  rw [hv, div_one] at e
  rw [← iib_T_eq_H P _ c hc]
  unfold iibT iibK iibB
  exact e

lemma iib_Xi_lt_one (P : Params) (hS : P.Standing) (c : ℝ) (hc : 0 < c) : iibXi P c < 1 := by
  rw [iib_Xi_fp P hS c hc, ← iib_T_eq_H P _ c hc]
  exact iib_T0_lt P hS c (1 / c) hc (by field_simp) _

lemma iib_Xi_ge_iff (P : Params) (hS : P.Standing) (c : ℝ) (hc : 0 < c) (t : ℝ) (ht : t < 1) :
    (t ≤ iibXi P c ↔ t ≤ iibH P t c) := by
  have hfp := iib_Xi_fp P hS c hc
  have h1 := iib_Xi_lt_one P hS c hc
  constructor
  · intro h
    have := iib_H_anti P hS c hc.le t _ h h1
    linarith
  · intro h
    by_contra h'
    push Not at h'
    have := iib_H_anti P hS c hc.le _ t h'.le ht
    linarith

lemma iib_Xi_gt_iff (P : Params) (hS : P.Standing) (c : ℝ) (hc : 0 < c) (t : ℝ) (ht : t < 1) :
    (t < iibXi P c ↔ t < iibH P t c) := by
  have hfp := iib_Xi_fp P hS c hc
  have h1 := iib_Xi_lt_one P hS c hc
  constructor
  · intro h
    have := iib_H_anti P hS c hc.le t _ h.le h1
    linarith
  · intro h
    by_contra h'
    push Not at h'
    have := iib_H_anti P hS c hc.le _ t h' ht
    linarith

/-- Strict quasiconcavity: no interior point is a (non-flat) minimum. -/
lemma iib_Xi_SQ (P : Params) (hS : P.Standing) (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (h1 : iibXi P b ≤ iibXi P a) (h2 : iibXi P b ≤ iibXi P c) :
    iibXi P a = iibXi P b ∧ iibXi P c = iibXi P b := by
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  set t := iibXi P b
  have ht : t < 1 := iib_Xi_lt_one P hS b hb
  have hfp : t = iibH P t b := iib_Xi_fp P hS b hb
  have hA : t ≤ iibH P t a := (iib_Xi_ge_iff P hS a ha t ht).mp h1
  have hC : t ≤ iibH P t c := (iib_Xi_ge_iff P hS c hc t ht).mp h2
  have hcc := iib_H_concave P hS t a b c hab.le hbc.le
  constructor
  · by_contra hne
    have hlt : t < iibXi P a := lt_of_le_of_ne h1 (Ne.symm hne)
    have := (iib_Xi_gt_iff P hS a ha t ht).mp hlt
    have e1 : 0 < c - b := by linarith
    have e2 : 0 < b - a := by linarith
    nlinarith
  · by_contra hne
    have hlt : t < iibXi P c := lt_of_le_of_ne h2 (Ne.symm hne)
    have := (iib_Xi_gt_iff P hS c hc t ht).mp hlt
    have e1 : 0 < c - b := by linarith
    have e2 : 0 < b - a := by linarith
    nlinarith

lemma iib_Xi_qc (P : Params) (hS : P.Standing) (a b c : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    min (iibXi P a) (iibXi P c) ≤ iibXi P b := by
  rcases hab.lt_or_eq with hab | hab
  · rcases hbc.lt_or_eq with hbc | hbc
    · by_contra h
      push Not at h
      have := iib_Xi_SQ P hS a b c ha hab hbc (le_of_lt (lt_of_lt_of_le h (min_le_left _ _)))
        (le_of_lt (lt_of_lt_of_le h (min_le_right _ _)))
      rw [this.1] at h
      exact lt_irrefl _ (lt_of_lt_of_le h (min_le_left _ _))
    · rw [hbc]; exact min_le_right _ _
  · rw [hab]; exact min_le_left _ _

lemma iib_Xi_pos_mono (P : Params) (hS : P.Standing) (x' x : ℝ) (hx' : 0 < x') (hxx : x' ≤ x)
    (hpos : 0 < iibXi P x) : 0 < iibXi P x' := by
  have hx : 0 < x := lt_of_lt_of_le hx' hxx
  have h1 := (iib_Xi_gt_iff P hS x hx 0 one_pos).mp hpos
  rw [iib_Xi_gt_iff P hS x' hx' 0 one_pos]
  have hcc := iib_H_concave P hS 0 0 x' x hx'.le hxx
  rw [iib_H_zero] at hcc
  nlinarith

lemma iib_Xi_cont (P : Params) (hS : P.Standing) : ContinuousOn (iibXi P) (Set.Ioi 0) := by
  intro c0 hc0
  have hc0' : (0:ℝ) < c0 := hc0
  apply ContinuousAt.continuousWithinAt
  rw [ContinuousAt, tendsto_order]
  have hpos : ∀ᶠ c in 𝓝 c0, 0 < c := lt_mem_nhds hc0'
  constructor
  · intro a ha
    have ha1 : a < 1 := lt_trans ha (iib_Xi_lt_one P hS c0 hc0')
    have h1 : a < iibH P a c0 := (iib_Xi_gt_iff P hS c0 hc0' a ha1).mp ha
    have h2 : ∀ᶠ c in 𝓝 c0, a < iibH P a c :=
      (iib_H_cont P hS a).continuousAt.eventually (lt_mem_nhds h1)
    filter_upwards [h2, hpos] with c hc hcp
    exact (iib_Xi_gt_iff P hS c hcp a ha1).mpr hc
  · intro b hb
    by_cases hb1 : 1 ≤ b
    · filter_upwards [hpos] with c hcp
      exact lt_of_lt_of_le (iib_Xi_lt_one P hS c hcp) hb1
    · push Not at hb1
      have h1 : iibH P b c0 < b := by
        have := (iib_Xi_ge_iff P hS c0 hc0' b hb1).not.mp (not_le.mpr hb)
        exact not_le.mp this
      have h2 : ∀ᶠ c in 𝓝 c0, iibH P b c < b :=
        (iib_H_cont P hS b).continuousAt.eventually (gt_mem_nhds h1)
      filter_upwards [h2, hpos] with c hc hcp
      by_contra h
      push Not at h
      have := (iib_Xi_ge_iff P hS c hcp b hb1).mp h
      linarith

end InvIntegration.Behavioral


namespace InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory

lemma iib_qc_generic (P : Params) (hS : P.Standing) (S : Set ℝ) (hSo : S.OrdConnected)
    (cf : ℝ → ℝ) (hpos : ∀ x ∈ S, 0 < cf x) (hmono : MonotoneOn cf S) (xi v : ℝ → ℝ)
    (hxi : ∀ x ∈ S, xi x = iibXi P (cf x)) (hv : ∀ x ∈ S, v x = vstar P (xi x)) :
    QuasiconcaveOn ℝ S xi ∧ QuasiconcaveOn ℝ S v := by
  have key : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ Set.Icc x y, z ∈ S ∧ min (xi x) (xi y) ≤ xi z := by
    intro x hx y hy z hz
    have hzS : z ∈ S := hSo.out hx hy hz
    refine ⟨hzS, ?_⟩
    rw [hxi x hx, hxi y hy, hxi z hzS]
    exact iib_Xi_qc P hS _ _ _ (hpos x hx) (hmono hx hzS hz.1) (hmono hzS hy hz.2)
  have hlt : ∀ x ∈ S, xi x < 1 := fun x hx => by rw [hxi x hx]; exact iib_Xi_lt_one P hS _ (hpos x hx)
  constructor
  · intro r
    apply Set.OrdConnected.convex
    refine ⟨fun x hx y hy z hz => ?_⟩
    obtain ⟨hzS, hm⟩ := key x hx.1 y hy.1 z hz
    exact ⟨hzS, le_trans (le_min hx.2 hy.2) hm⟩
  · intro r
    apply Set.OrdConnected.convex
    refine ⟨fun x hx y hy z hz => ?_⟩
    obtain ⟨hzS, hm⟩ := key x hx.1 y hy.1 z hz
    refine ⟨hzS, ?_⟩
    have hx2 := hx.2; have hy2 := hy.2
    rw [hv x hx.1] at hx2; rw [hv y hy.1] at hy2; rw [hv z hzS]
    rcases min_choice (xi x) (xi y) with h | h <;> rw [h] at hm
    · exact le_trans hx2 (iib_vstar_mono P hS _ _ hm (hlt z hzS))
    · exact le_trans hy2 (iib_vstar_mono P hS _ _ hm (hlt z hzS))

end InvIntegration.Behavioral


open InvIntegration.Behavioral in
theorem solution (P : Params) (hS : P.Standing) (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (xiI vI : ℝ → ℝ)
    (hE : ∀ σ : ℝ, 0 < σ → ∃ q : ℝ, IsEquilibrium P (2 * P.μ) (sdI σ ρ) q (vI σ) (xiI σ)) :
    QuasiconcaveOn ℝ (Set.Ioi (0 : ℝ)) xiI ∧ QuasiconcaveOn ℝ (Set.Ioi (0 : ℝ)) vI := by
  have hμ : 0 < P.μ := hS.2.2.2.2.2.2.2.1
  have hr : 0 < Real.sqrt (2 * (1 + ρ)) := Real.sqrt_pos.mpr (by linarith [hρ.1])
  have hsdpos : ∀ σ ∈ Set.Ioi (0 : ℝ), 0 < sdI σ ρ := fun σ hσ => mul_pos hr hσ
  apply iib_qc_generic P hS _ Set.ordConnected_Ioi (fun σ => sdI σ ρ / (2 * P.μ))
  · intro σ hσ; exact div_pos (hsdpos σ hσ) (by linarith)
  · intro a _ b _ hab
    apply div_le_div_of_nonneg_right _ (by linarith)
    unfold sdI
    exact mul_le_mul_of_nonneg_left hab hr.le
  · intro σ hσ
    obtain ⟨q, hq⟩ := hE σ hσ
    exact iib_Xi_eq P hS _ _ (by linarith) (hsdpos σ hσ) _ _ _ hq
  · intro σ hσ
    obtain ⟨q, hq⟩ := hE σ hσ
    exact hq.2.1
