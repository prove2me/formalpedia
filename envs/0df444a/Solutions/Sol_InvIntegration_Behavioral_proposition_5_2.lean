-- Prove2me | solution 2 for InvIntegration.Behavioral.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:53:43.5821+00:00
-- url     : https://prove2.me/submissions/16322d99-2e4f-412c-98f3-99e599724834

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model
import Theorems.Thm_InvIntegration_Behavioral_behavioral_value_sign
import Theorems.Thm_InvIntegration_Behavioral_proposition_2
import Theorems.Thm_InvIntegration_Behavioral_proposition_3

-- carved verbatim out of submission 930cec70-c1aa-4e84-a014-73ffe403bf42, lines 1367-1472

section
open InvIntegration
open InvIntegration.Behavioral
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

lemma iib_Gbar_nonneg (P : Params) (hS : P.Standing) (v : ℝ) : 0 ≤ Gbar P v := by
  unfold Gbar; rw [iib_one_sub_G P hS v]
  exact setIntegral_nonneg measurableSet_Ioi (fun x _ => hS.2.2.2.2.2.2.2.2.2.1 x)

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

end

section

open InvIntegration.Behavioral MeasureTheory ProbabilityTheory in
theorem InvIntegration.Behavioral.iib_eq14 (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd)
    (q v ξ : ℝ) (hE : IsEquilibrium P m sd q v ξ) :
    ξ = sd / m * ∫ x, min (Gbar P v / (G P v - G P (P.s / P.δ)) * max (P.zh - x) 0) (x + m / sd)
      ∂ gaussianReal 0 1 := by
  obtain ⟨hmax, hv, hξ⟩ := hE
  have hq : q = Gbar P v * (m + P.zh * sd) := by
    by_contra hne
    have h1 := (InvIntegration.Behavioral.proposition_2 P hS m sd hm hsd v).1 q hne
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

end

section
open InvIntegration
open InvIntegration.Behavioral
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

lemma iib_B_anti (P : Params) (hS : P.Standing) (v1 v2 : ℝ) (hp : P.p ≤ v1) (h12 : v1 ≤ v2) :
    Gbar P v2 / (G P v2 - G P (P.s / P.δ)) ≤ Gbar P v1 / (G P v1 - G P (P.s / P.δ)) := by
  have hD1 := iib_d2_pos P hS v1 hp
  have hD2 := iib_d2_pos P hS v2 (le_trans hp h12)
  have hG := iib_G_mono P hS v1 v2 h12
  have ha2 := iib_Gbar_nonneg P hS v2
  rw [div_le_div_iff₀ hD2 hD1]
  unfold Gbar at *
  nlinarith

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

lemma iib_vstar_mono (P : Params) (hS : P.Standing) (ξ1 ξ2 : ℝ) (h12 : ξ1 ≤ ξ2) (h2 : ξ2 < 1) :
    vstar P ξ1 ≤ vstar P ξ2 := by
  rw [iib_vstar_eq P hS ξ1 (lt_of_le_of_lt h12 h2), iib_vstar_eq P hS ξ2 h2]
  exact min_le_min le_rfl (max_le_max
    (iib_frac_mono P hS ξ1 ξ2 h12 (iib_lt_one_mul P hS ξ2 h2)) le_rfl)

noncomputable def iibB (P : Params) (v : ℝ) : ℝ := Gbar P v / (G P v - G P (P.s / P.δ))

lemma iib_B_nonneg (P : Params) (hS : P.Standing) (v : ℝ) (hv : P.p ≤ v) : 0 ≤ iibB P v :=
  div_nonneg (iib_Gbar_nonneg P hS v) (iib_d2_pos P hS v hv).le

noncomputable def iibT (P : Params) (c k ξ : ℝ) : ℝ :=
  c * ∫ z, iibK P (iibB P (vstar P ξ)) k z ∂gaussianReal 0 1

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

end

section
open InvIntegration
open InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory Filter Topology

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

noncomputable def iibXi (P : Params) (c : ℝ) : ℝ :=
  Classical.epsilon (fun ξ => ∃ q v, IsEquilibrium P 1 c q v ξ)

lemma iib_Xi_spec (P : Params) (hS : P.Standing) (c : ℝ) (hc : 0 < c) :
    ∃ q v, IsEquilibrium P 1 c q v (iibXi P c) := by
  obtain ⟨q, v, ξ, hE, -⟩ := (InvIntegration.Behavioral.proposition_3 P hS 1 c one_pos hc).1
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

lemma iib_phi_eq (t : ℝ) :
    gaussianPDFReal 0 1 t = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * t ^ 2) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2; ring

lemma iib_int_t_phi (a : ℝ) :
    ∫ t in Set.Ioi a, t * gaussianPDFReal 0 1 t = gaussianPDFReal 0 1 a := by
  set K := (Real.sqrt (2 * Real.pi))⁻¹
  have hf : ∀ t, HasDerivAt (fun t => -(K * Real.exp (-(1/2) * t ^ 2)))
      (t * (K * Real.exp (-(1/2) * t ^ 2))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(1/2) * t ^ 2) (-(1/2) * (2 * t)) t := by
      have := (hasDerivAt_pow 2 t).const_mul (-(1/2) : ℝ)
      simpa using this
    have h2 : HasDerivAt (fun t => -(K * Real.exp (-(1/2) * t ^ 2)))
        (-(K * (Real.exp (-(1 / 2) * t ^ 2) * (-(1 / 2) * (2 * t))))) t := (h1.exp.const_mul K).neg
    exact h2.congr_deriv (by ring)
  have hlim : Tendsto (fun t : ℝ => -(K * Real.exp (-(1/2) * t ^ 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -(1/2) * t ^ 2) atTop atBot := by
      apply Tendsto.const_mul_atTop_of_neg (by norm_num)
      exact tendsto_pow_atTop (by norm_num)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul K
    simpa using h2.neg
  have hint : IntegrableOn (fun t => t * (K * Real.exp (-(1/2) * t ^ 2))) (Set.Ioi a) := by
    have := (integrable_mul_exp_neg_mul_sq (b := 1/2) (by norm_num)).const_mul K
    refine (this.congr (Eventually.of_forall (fun t => ?_))).integrableOn
    simp only []; ring_nf
  have := integral_Ioi_of_hasDerivAt_of_tendsto (hf a).continuousAt.continuousWithinAt
    (fun t _ => hf t) hint hlim
  simp_rw [iib_phi_eq]
  rw [this]; ring

lemma iib_int_phi (a : ℝ) :
    ∫ t in Set.Ioi a, gaussianPDFReal 0 1 t = 1 - cdf (gaussianReal 0 1) a := by
  rw [← iib_tail]
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero, ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Ioi (fun x _ => gaussianPDFReal_nonneg _ _ _)

lemma iib_lossN (P : Params) :
    lossN P = gaussianPDFReal 0 1 P.zh - P.zh * (1 - cdf (gaussianReal 0 1) P.zh) := by
  unfold lossN
  have hi1 : IntegrableOn (fun t => t * gaussianPDFReal 0 1 t) (Set.Ioi P.zh) := by
    have := (integrable_mul_exp_neg_mul_sq (b := 1/2) (by norm_num)).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹
    refine (this.congr (Eventually.of_forall (fun t => ?_))).integrableOn
    simp only [iib_phi_eq]; ring
  have hi2 : IntegrableOn (fun t => gaussianPDFReal 0 1 t) (Set.Ioi P.zh) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have : (fun t => (t - P.zh) * gaussianPDFReal 0 1 t) =
      fun t => t * gaussianPDFReal 0 1 t - P.zh * gaussianPDFReal 0 1 t := by
    funext t; ring
  rw [this, integral_sub hi1 (hi2.const_mul _), integral_const_mul, iib_int_t_phi, iib_int_phi]

lemma iib_Pi_formula (P : Params) (hS : P.Standing) (m sd : ℝ) :
    Pi P m sd = (P.p - P.c) * m - (P.p - P.s) * gaussianPDFReal 0 1 P.zh * sd := by
  have hΦ : cdf (gaussianReal 0 1) P.zh = (P.p - P.c) / (P.p - P.s) := hS.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hps : P.p - P.s ≠ 0 := by linarith [hS.1, hS.2.1]
  unfold Pi
  rw [iib_lossN, hΦ]
  field_simp
  ring

lemma iib_Pi_pos (P : Params) (hS : P.Standing) (σ : ℝ) (hσ : σ < sigmaMax P) :
    0 < Pi P P.μ σ := by
  rw [iib_Pi_formula P hS]
  have hφ : 0 < gaussianPDFReal 0 1 P.zh := gaussianPDFReal_pos _ _ _ one_ne_zero
  have hps : 0 < P.p - P.s := by linarith [hS.1, hS.2.1]
  have hK : 0 < (P.p - P.s) * gaussianPDFReal 0 1 P.zh := mul_pos hps hφ
  unfold sigmaMax at hσ
  rw [lt_div_iff₀ hK] at hσ
  linarith

lemma iib_sigmaMax_pos (P : Params) (hS : P.Standing) : 0 < sigmaMax P := by
  have hφ : 0 < gaussianPDFReal 0 1 P.zh := gaussianPDFReal_pos _ _ _ one_ne_zero
  have hps : 0 < P.p - P.s := by linarith [hS.1, hS.2.1]
  unfold sigmaMax
  apply div_pos (mul_pos hS.2.2.2.2.2.2.2.1 (by linarith [hS.2.1])) (mul_pos hps hφ)

lemma iib_threshold (lo hi : ℝ) (hlh : lo < hi) (A : ℝ → Prop)
    (hdown : ∀ x y, lo < x → x ≤ y → y < hi → A y → A x)
    (hopen : ∀ x, lo < x → x < hi → A x → ∃ y, x < y ∧ y < hi ∧ A y) :
    ∃! s : ℝ, s ∈ Set.Icc lo hi ∧ ∀ x ∈ Set.Ioo lo hi, (A x ↔ x < s) := by
  set S := {x | lo < x ∧ x < hi ∧ A x}
  have hbdd : BddAbove S := ⟨hi, fun x hx => hx.2.1.le⟩
  have hex : ∃ s : ℝ, s ∈ Set.Icc lo hi ∧ ∀ x ∈ Set.Ioo lo hi, (A x ↔ x < s) := by
    by_cases hne : S.Nonempty
    · refine ⟨sSup S, ⟨?_, csSup_le hne (fun x hx => hx.2.1.le)⟩, ?_⟩
      · obtain ⟨x0, hx0⟩ := hne
        exact le_trans hx0.1.le (le_csSup hbdd hx0)
      · intro x hx
        constructor
        · intro hA
          obtain ⟨y, hxy, hyh, hAy⟩ := hopen x hx.1 hx.2 hA
          exact lt_of_lt_of_le hxy (le_csSup hbdd ⟨by linarith [hx.1], hyh, hAy⟩)
        · intro hlt
          obtain ⟨y, hyS, hxy⟩ := exists_lt_of_lt_csSup hne hlt
          exact hdown x y hx.1 hxy.le hyS.2.1 hyS.2.2
    · refine ⟨lo, ⟨le_rfl, hlh.le⟩, ?_⟩
      intro x hx
      constructor
      · intro hA; exact (hne ⟨x, hx.1, hx.2, hA⟩).elim
      · intro h; exact absurd hx.1 (not_lt.mpr h.le)
  obtain ⟨s, hs, hsA⟩ := hex
  refine ⟨s, ⟨hs, hsA⟩, ?_⟩
  rintro s' ⟨hs', hs'A⟩
  have key : ∀ s1 s2 : ℝ, s1 ∈ Set.Icc lo hi → s2 ∈ Set.Icc lo hi →
      (∀ x ∈ Set.Ioo lo hi, (A x ↔ x < s1)) → (∀ x ∈ Set.Ioo lo hi, (A x ↔ x < s2)) → ¬ s1 < s2 := by
    intro s1 s2 h1 h2 hA1 hA2 hlt
    set x := (s1 + s2) / 2
    have hx : x ∈ Set.Ioo lo hi := ⟨by simp only [x]; linarith [h1.1], by simp only [x]; linarith [h2.2]⟩
    have : A x := (hA2 x hx).mpr (by simp only [x]; linarith)
    have := (hA1 x hx).mp this
    simp only [x] at this; linarith
  rcases lt_trichotomy s' s with h | h | h
  · exact (key s' s hs' hs hs'A hsA h).elim
  · exact h
  · exact (key s s' hs hs' hsA hs'A h).elim

lemma iib_frac_strict (P : Params) (hS : P.Standing) (ξ1 ξ2 : ℝ) (h12 : ξ1 < ξ2)
    (h2 : ξ2 * P.δ < 1) :
    (P.p - ξ1 * P.s) / (1 - ξ1 * P.δ) < (P.p - ξ2 * P.s) / (1 - ξ2 * P.δ) := by
  have hδ : 0 < P.δ := hS.2.2.1
  have hsδ : P.s < P.δ * P.p := hS.2.2.2.2.1
  have h1 : 0 < 1 - ξ1 * P.δ := by nlinarith
  have h2' : 0 < 1 - ξ2 * P.δ := by linarith
  rw [div_lt_div_iff₀ h1 h2']
  nlinarith

lemma iib_vstar_lt_iff (P : Params) (hS : P.Standing) (a b : ℝ) (ha : a < 1) (hb : b < 1)
    (hbvh : vstar P b < P.vh) : vstar P a < vstar P b ↔ a < b ∧ 0 < b := by
  have hδ : 0 < P.δ := hS.2.2.1
  have hsδ : P.s < P.δ * P.p := hS.2.2.2.2.1
  constructor
  · intro h
    constructor
    · by_contra h'; push Not at h'
      exact absurd (iib_vstar_mono P hS b a h' ha) (not_le.mpr h)
    · by_contra h'; push Not at h'
      rw [iib_vstar_nonpos P hS b h'] at h
      exact absurd (iib_vstar_ge P hS a) (not_le.mpr h)
  · rintro ⟨hab, hb0⟩
    have hb1 := iib_lt_one_mul P hS b hb
    have hvb : vstar P b = (P.p - b * P.s) / (1 - b * P.δ) := by
      have e := iib_vstar_eq P hS b hb
      rw [max_eq_left (iib_frac_ge P hS b hb0.le hb1)] at e
      rcases min_choice P.vh ((P.p - b * P.s) / (1 - b * P.δ)) with h | h
      · rw [e, h] at hbvh; exact absurd hbvh (lt_irrefl _)
      · rw [e, h]
    rw [hvb]
    rcases le_or_gt a 0 with ha0 | ha0
    · rw [iib_vstar_nonpos P hS a ha0]
      have h1 : 0 < 1 - b * P.δ := by linarith
      rw [lt_div_iff₀ h1]; nlinarith
    · have e := iib_vstar_eq P hS a ha
      rw [max_eq_left (iib_frac_ge P hS a ha0.le (iib_lt_one_mul P hS a ha))] at e
      rw [e]
      exact lt_of_le_of_lt (min_le_right _ _) (iib_frac_strict P hS a b hab hb1)

lemma iib_v_eq (P : Params) (hS : P.Standing) (m sd : ℝ) (hm : 0 < m) (hsd : 0 < sd)
    (q v ξ : ℝ) (hE : IsEquilibrium P m sd q v ξ) : v = vstar P (iibXi P (sd / m)) := by
  rw [hE.2.1, iib_Xi_eq P hS m sd hm hsd q v ξ hE]

lemma iib_vXi_lt_vh (P : Params) (hS : P.Standing) (c : ℝ) (hc : 0 < c) :
    vstar P (iibXi P c) < P.vh := by
  obtain ⟨q, v, hE⟩ := iib_Xi_spec P hS c hc
  rw [← hE.2.1]
  exact iib_eq_lt_vh P hS _ _ _ _ _ zero_le_one hE

lemma iib_BV_iff (P : Params) (hS : P.Standing) (σ : ℝ) (hσ : 0 < σ) (hPi : 0 < Pi P P.μ σ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) (qm vm ξm qI vI ξI : ℝ)
    (hm : IsEquilibrium P P.μ σ qm vm ξm) (hI : IsEquilibrium P (2 * P.μ) (sdI σ ρ) qI vI ξI) :
    0 < behavioralValue P σ ρ vm vI ↔
      iibXi P (sdI σ ρ / (2 * P.μ)) < iibXi P (σ / P.μ) ∧ 0 < iibXi P (σ / P.μ) := by
  have hμ : 0 < P.μ := hS.2.2.2.2.2.2.2.1
  have hsdI : 0 < sdI σ ρ := mul_pos (Real.sqrt_pos.mpr (by linarith [hρ.1])) hσ
  have hcI : 0 < sdI σ ρ / (2 * P.μ) := div_pos hsdI (by linarith)
  have hcm : 0 < σ / P.μ := div_pos hσ hμ
  have hBV := InvIntegration.Behavioral.behavioral_value_sign P hS σ hσ hPi ρ hρ qm vm ξm qI vI ξI hm hI
  have e1 := iib_v_eq P hS _ _ hμ hσ _ _ _ hm
  have e2 := iib_v_eq P hS _ _ (by linarith) hsdI _ _ _ hI
  rw [← iib_vstar_lt_iff P hS _ _ (iib_Xi_lt_one P hS _ hcI) (iib_Xi_lt_one P hS _ hcm)
    (iib_vXi_lt_vh P hS _ hcm), ← e1, ← e2]
  constructor
  · intro h
    rcases lt_trichotomy vI vm with h' | h' | h'
    · exact h'
    · rw [h'] at h; unfold behavioralValue at h; simp at h
    · exact absurd h (not_lt.mpr (hBV.2 h').le)
  · exact hBV.1

lemma iib_down_k (P : Params) (hS : P.Standing) (c' c x : ℝ) (hc' : 0 < c') (hcc : c' ≤ c)
    (hcx : c ≤ x) (h : iibXi P c < iibXi P x) : iibXi P c' < iibXi P x := by
  have := iib_Xi_qc P hS c' c x hc' hcc hcx
  rcases min_choice (iibXi P c') (iibXi P x) with hm | hm <;> rw [hm] at this
  · linarith
  · linarith

lemma iib_down_x (P : Params) (hS : P.Standing) (k x' x : ℝ) (hk0 : 0 < k) (hk1 : k < 1)
    (hx' : 0 < x') (hxx : x' ≤ x) (h : iibXi P (k * x) < iibXi P x) :
    iibXi P (k * x') < iibXi P x' := by
  rcases hxx.lt_or_eq with hlt | heq
  swap
  · rw [heq]; exact h
  have hkx'x' : k * x' < x' := by nlinarith
  have hkx'kx : k * x' < k * x := by nlinarith
  have hkx'0 : 0 < k * x' := by positivity
  by_contra hcon
  push Not at hcon
  rcases le_or_gt (k * x) x' with hc1 | hc1
  · -- kx' < kx ≤ x' < x
    have hA : iibXi P (k * x') < iibXi P (k * x) := by
      by_contra h'; push Not at h'
      have := iib_Xi_SQ P hS (k * x') (k * x) x hkx'0 hkx'kx (by nlinarith) h' h.le
      linarith [this.2]
    rcases hc1.lt_or_eq with hc1 | hc1
    · have := iib_Xi_SQ P hS (k * x) x' x (mul_pos hk0 (by linarith)) hc1 hlt (by linarith) (by linarith)
      linarith [this.1]
    · rw [hc1] at hA; linarith
  · -- kx' < x' < kx < x
    rcases le_or_gt (iibXi P x') (iibXi P (k * x)) with h2 | h2
    · have := iib_Xi_SQ P hS (k * x') x' (k * x) hkx'0 hkx'x' hc1 hcon h2
      have := iib_Xi_SQ P hS x' (k * x) x (by linarith) hc1 (by nlinarith) (by linarith) h.le
      linarith [this.2]
    · have := iib_Xi_SQ P hS x' (k * x) x (by linarith) hc1 (by nlinarith) h2.le h.le
      linarith [this.2]

end

section

open InvIntegration.Behavioral Filter Topology in
theorem solution (P : Params) (hS : P.Standing)
    (vm : ℝ → ℝ) (hvm : ∀ σ : ℝ, 0 < σ → ∃ q ξ : ℝ, IsEquilibrium P P.μ σ q (vm σ) ξ)
    (vI : ℝ → ℝ → ℝ)
    (hvI : ∀ ρ ∈ Set.Ioo (-1 : ℝ) 1, ∀ σ : ℝ, 0 < σ →
      ∃ q ξ : ℝ, IsEquilibrium P (2 * P.μ) (sdI σ ρ) q (vI ρ σ) ξ) :
    (∀ σ : ℝ, 0 < σ → 0 < Pi P P.μ σ →
      ∃! ρbar : ℝ, ρbar ∈ Set.Icc (-1 : ℝ) 1 ∧ ∀ ρ ∈ Set.Ioo (-1 : ℝ) 1,
        (0 < behavioralValue P σ ρ (vm σ) (vI ρ σ) ↔ ρ < ρbar)) ∧
    (∀ ρ ∈ Set.Ioo (-1 : ℝ) 1,
      ∃! σbar : ℝ, σbar ∈ Set.Icc 0 (sigmaMax P) ∧ ∀ σ ∈ Set.Ioo 0 (sigmaMax P),
        (0 < behavioralValue P σ ρ (vm σ) (vI ρ σ) ↔ σ < σbar)) := by
  have hμ : 0 < P.μ := hS.2.2.2.2.2.2.2.1
  have hXc := iib_Xi_cont P hS
  constructor
  · intro σ hσ hPi
    obtain ⟨qm, ξm, hm⟩ := hvm σ hσ
    set x := σ / P.μ with hx
    have hx0 : 0 < x := div_pos hσ hμ
    have hsq : ∀ ρ ∈ Set.Ioo (-1 : ℝ) 1, 0 < Real.sqrt (2 * (1 + ρ)) := fun ρ hρ =>
      Real.sqrt_pos.mpr (by linarith [hρ.1])
    have hcI : ∀ ρ ∈ Set.Ioo (-1 : ℝ) 1, 0 < sdI σ ρ / (2 * P.μ) := fun ρ hρ =>
      div_pos (mul_pos (hsq ρ hρ) hσ) (by linarith)
    have hiff : ∀ ρ ∈ Set.Ioo (-1 : ℝ) 1, (0 < behavioralValue P σ ρ (vm σ) (vI ρ σ) ↔
        iibXi P (sdI σ ρ / (2 * P.μ)) < iibXi P x ∧ 0 < iibXi P x) := by
      intro ρ hρ
      obtain ⟨qI, ξI, hI⟩ := hvI ρ hρ σ hσ
      exact iib_BV_iff P hS σ hσ hPi ρ hρ _ _ _ _ _ _ hm hI
    apply iib_threshold (-1) 1 (by norm_num)
    · intro a b ha hab hb hAb
      have haI : a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨ha, by linarith⟩
      have hbI : b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hb⟩
      rw [hiff a haI]; rw [hiff b hbI] at hAb
      refine ⟨iib_down_k P hS _ _ x (hcI a haI) ?_ ?_ hAb.1, hAb.2⟩
      · apply div_le_div_of_nonneg_right _ (by linarith)
        unfold sdI
        exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hσ.le
      · rw [hx, div_le_div_iff₀ (by linarith) hμ]
        unfold sdI
        have h4 : Real.sqrt 4 = 2 := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
        have : Real.sqrt (2 * (1 + b)) ≤ 2 := by
          have h5 := Real.sqrt_le_sqrt (show 2 * (1 + b) ≤ (4:ℝ) by linarith)
          rwa [h4] at h5
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hσ.le) hμ.le
        linarith
    · intro a ha ha1 hAa
      have haI : a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨ha, ha1⟩
      rw [hiff a haI] at hAa
      have hcont : ContinuousAt (fun ρ => iibXi P (sdI σ ρ / (2 * P.μ))) a := by
        have h1 : ContinuousAt (fun ρ => sdI σ ρ / (2 * P.μ)) a := by
          unfold sdI; fun_prop
        exact (hXc.continuousAt (Ioi_mem_nhds (hcI a haI))).comp (f := fun ρ => sdI σ ρ / (2 * P.μ)) h1
      have hev : ∀ᶠ y in 𝓝 a, iibXi P (sdI σ y / (2 * P.μ)) < iibXi P x ∧ -1 < y ∧ y < 1 :=
        (hcont.eventually (gt_mem_nhds hAa.1)).and ((eventually_gt_nhds ha).and (eventually_lt_nhds ha1))
      obtain ⟨y, ⟨hy1, hy2, hy3⟩, hya⟩ :=
        ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi a))).exists
      refine ⟨y, hya, hy3, ?_⟩
      rw [hiff y ⟨hy2, hy3⟩]
      exact ⟨hy1, hAa.2⟩
  · intro ρ hρ
    have hsq : 0 < Real.sqrt (2 * (1 + ρ)) := Real.sqrt_pos.mpr (by linarith [hρ.1])
    set k := Real.sqrt (2 * (1 + ρ)) / 2 with hk
    have hk0 : 0 < k := by positivity
    have hk1 : k < 1 := by
      have : Real.sqrt (2 * (1 + ρ)) < 2 := by
        rw [Real.sqrt_lt' (by norm_num)]; nlinarith [hρ.2]
      simp only [hk]; linarith
    have hcI : ∀ σ, sdI σ ρ / (2 * P.μ) = k * (σ / P.μ) := by
      intro σ; unfold sdI; simp only [hk]; field_simp
    have hiff : ∀ σ ∈ Set.Ioo 0 (sigmaMax P), (0 < behavioralValue P σ ρ (vm σ) (vI ρ σ) ↔
        iibXi P (k * (σ / P.μ)) < iibXi P (σ / P.μ) ∧ 0 < iibXi P (σ / P.μ)) := by
      intro σ hσ
      obtain ⟨qm, ξm, hm⟩ := hvm σ hσ.1
      obtain ⟨qI, ξI, hI⟩ := hvI ρ hρ σ hσ.1
      rw [← hcI]
      exact iib_BV_iff P hS σ hσ.1 (iib_Pi_pos P hS σ hσ.2) ρ hρ _ _ _ _ _ _ hm hI
    apply iib_threshold 0 (sigmaMax P) (iib_sigmaMax_pos P hS)
    · intro a b ha hab hb hAb
      have haI : a ∈ Set.Ioo 0 (sigmaMax P) := ⟨ha, by linarith⟩
      have hbI : b ∈ Set.Ioo 0 (sigmaMax P) := ⟨by linarith, hb⟩
      rw [hiff a haI]; rw [hiff b hbI] at hAb
      have hxa : 0 < a / P.μ := div_pos ha hμ
      have hxab : a / P.μ ≤ b / P.μ := div_le_div_of_nonneg_right hab hμ.le
      exact ⟨iib_down_x P hS k _ _ hk0 hk1 hxa hxab hAb.1,
        iib_Xi_pos_mono P hS _ _ hxa hxab hAb.2⟩
    · intro a ha ha1 hAa
      have haI : a ∈ Set.Ioo 0 (sigmaMax P) := ⟨ha, ha1⟩
      rw [hiff a haI] at hAa
      have hxa : 0 < a / P.μ := div_pos ha hμ
      have hc1 : ContinuousAt (fun σ => iibXi P (σ / P.μ)) a :=
        (hXc.continuousAt (Ioi_mem_nhds hxa)).comp (f := fun σ => σ / P.μ) (by fun_prop)
      have hc2 : ContinuousAt (fun σ => iibXi P (k * (σ / P.μ))) a :=
        (hXc.continuousAt (Ioi_mem_nhds (by positivity))).comp (f := fun σ => k * (σ / P.μ))
          (by fun_prop)
      have hd : ContinuousAt (fun σ => iibXi P (σ / P.μ) - iibXi P (k * (σ / P.μ))) a :=
        hc1.sub hc2
      have hev : ∀ᶠ y in 𝓝 a, (0 < iibXi P (y / P.μ) - iibXi P (k * (y / P.μ)) ∧
          0 < iibXi P (y / P.μ)) ∧ 0 < y ∧ y < sigmaMax P :=
        ((hd.eventually (lt_mem_nhds (by linarith [hAa.1]))).and
          (hc1.eventually (lt_mem_nhds hAa.2))).and ((eventually_gt_nhds ha).and (eventually_lt_nhds ha1))
      obtain ⟨y, ⟨⟨hy1, hy2⟩, hy3, hy4⟩, hya⟩ :=
        ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi a))).exists
      refine ⟨y, hya, hy4, ?_⟩
      rw [hiff y ⟨hy3, hy4⟩]
      exact ⟨by linarith, hy2⟩

end
