-- Prove2me | solution 1 for InvIntegration.Behavioral.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:25:56.10092+00:00
-- url     : https://prove2.me/submissions/fd9bb687-6ace-4b50-ace0-5a53a59a7353

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
theorem solution (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd)
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
