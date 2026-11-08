-- Prove2me | solution 1 for HedgePSNV.riskneutral_section_maximizers
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T23:15:33.920517+00:00
-- url     : https://prove2.me/submissions/023e294c-82ef-4062-b57d-ea99bd2fe039

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace HedgePSNVC4

open HedgePSNV

/-- The expected overage `G(R) = E[(R - A)^+]`. -/
noncomputable def G (ν : Measure ℝ) (R : ℝ) : ℝ := ∫ a, max (R - a) 0 ∂ν

lemma int_pos (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (R : ℝ) :
    Integrable (fun a : ℝ => max (R - a) 0) ν := by
  refine ((integrable_const |R|).add hint).mono' (by fun_prop) (Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have h1 := le_abs_self R
  have h2 := le_max_left (-a) 0
  have h3 : (0 : ℝ) ≤ max (-a) 0 := le_max_right _ _
  have h4 := abs_nonneg R
  show max (R - a) 0 ≤ |R| + max (-a) 0
  exact max_le (by linarith) (by linarith)

lemma V_eq (p : Params) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (P R : ℝ) :
    nvValue p ν id P R = (P - p.c) * (R - p.b * P) - (P - p.s) * G ν R := by
  unfold nvValue payoff G
  simp only [id]
  rw [integral_sub (integrable_const _) ((int_pos ν hint R).const_mul _), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  congr 1
  exact integral_const_mul (P - p.s) (fun a : ℝ => max (R - a) 0)

lemma G_diff (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (R1 R2 : ℝ) (h : R1 ≤ R2) :
    cdf ν R1 * (R2 - R1) ≤ G ν R2 - G ν R1 ∧ G ν R2 - G ν R1 ≤ cdf ν R2 * (R2 - R1) := by
  have hsub : G ν R2 - G ν R1 = ∫ a, (max (R2 - a) 0 - max (R1 - a) 0) ∂ν := by
    unfold G; rw [integral_sub (int_pos ν hint R2) (int_pos ν hint R1)]
  have hind : ∀ x : ℝ, ∫ a, (Set.Iic x).indicator (fun _ => (R2 - R1)) a ∂ν =
      cdf ν x * (R2 - R1) := by
    intro x
    rw [integral_indicator measurableSet_Iic, setIntegral_const, cdf_eq_real, smul_eq_mul]
  have hii : ∀ x : ℝ, Integrable ((Set.Iic x).indicator (fun _ => (R2 - R1))) ν :=
    fun x => (integrable_const _).indicator measurableSet_Iic
  have hdi : Integrable (fun a => max (R2 - a) 0 - max (R1 - a) 0) ν :=
    (int_pos ν hint R2).sub (int_pos ν hint R1)
  refine ⟨?_, ?_⟩
  · rw [hsub, ← hind]
    refine integral_mono (hii R1) hdi fun a => ?_
    simp only [Set.indicator, Set.mem_Iic]
    split_ifs with ha
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · have := max_le_max_right 0 (show R1 - a ≤ R2 - a by linarith)
      linarith
  · rw [hsub, ← hind]
    refine integral_mono hdi (hii R2) fun a => ?_
    simp only [Set.indicator, Set.mem_Iic]
    split_ifs with ha
    · rcases le_total a R1 with h1 | h1
      · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; simp

lemma G_lip (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) : LipschitzWith 1 (G ν) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total x y with h | h
  · obtain ⟨h1, h2⟩ := G_diff ν hint x y h
    have := cdf_nonneg ν x; have := cdf_le_one ν y
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    nlinarith
  · obtain ⟨h1, h2⟩ := G_diff ν hint y x h
    have := cdf_nonneg ν y; have := cdf_le_one ν x
    rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by linarith)]
    nlinarith

lemma cdf_strictMono (ν : Measure ℝ) [IsProbabilityMeasure ν] (h1 : Assumption1 ν) :
    StrictMono (cdf ν) := by
  obtain ⟨f, r, r', hf, hr, hr', hpos, -, -⟩ := h1
  refine (monotone_cdf ν).strictMono_of_injective fun x y hxy => ?_
  by_contra hne
  wlog hlt : x < y generalizing x y
  · exact this y x hxy.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  have hconst : ∀ z ∈ Set.Ioo x y, cdf ν z = cdf ν x := fun z hz =>
    le_antisymm (hxy ▸ monotone_cdf ν hz.2.le) (monotone_cdf ν hz.1.le)
  have hf0 : ∀ z ∈ Set.Ioo x y, f z = 0 := by
    intro z hz
    have hev : (fun _ : ℝ => cdf ν x) =ᶠ[𝓝 z] fun w => cdf ν w :=
      Filter.mem_of_superset (Ioo_mem_nhds hz.1 hz.2) fun w hw => (hconst w hw).symm
    exact (hf z).unique ((hasDerivAt_const z (cdf ν x)).congr_of_eventuallyEq hev.symm)
  have hr0 : ∀ z ∈ Set.Ioo x y, r z = 0 := fun z hz => by rw [hr z, hf0 z hz, zero_div]
  set a := (x + y) / 2
  have ha : a ∈ Set.Ioo x y := ⟨by simp only [a]; linarith, by simp only [a]; linarith⟩
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 a] r :=
    Filter.mem_of_superset (Ioo_mem_nhds ha.1 ha.2) fun w hw => (hr0 w hw).symm
  have hr'0 : r' a = 0 := (hr' a).unique ((hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq hev.symm)
  have := hpos a
  rw [hr0 a ha, hr'0] at this
  norm_num at this

lemma G_strict (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (h1 : Assumption1 ν) (R1 R2 : ℝ)
    (h : R2 < R1) : 2 * G ν ((R1 + R2) / 2) < G ν R1 + G ν R2 := by
  set m := (R1 + R2) / 2 with hm
  set q := (R2 + m) / 2 with hq
  obtain ⟨-, a1⟩ := G_diff ν hint R2 q (by linarith)
  obtain ⟨-, a2⟩ := G_diff ν hint q m (by linarith)
  obtain ⟨a3, -⟩ := G_diff ν hint m R1 (by linarith)
  have hs : cdf ν q < cdf ν m := cdf_strictMono ν h1 (by linarith)
  have hpos : 0 < (cdf ν m - cdf ν q) * (R1 - R2) := mul_pos (by linarith) (by linarith)
  have e1 : q - R2 = (R1 - R2) / 4 := by rw [hq, hm]; ring
  have e2 : m - q = (R1 - R2) / 4 := by rw [hq, hm]; ring
  have e3 : R1 - m = (R1 - R2) / 2 := by rw [hm]; ring
  rw [e1] at a1; rw [e2] at a2; rw [e3] at a3
  nlinarith

end HedgePSNVC4

open HedgePSNVC4 in
open HedgePSNV in
theorem solution (p : Params) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (h1 : Assumption1 ν) :
    Continuous (fun q : ℝ × ℝ => nvValue p ν id q.1 q.2) ∧
    (∀ P, p.c ≤ P → ∃ R, p.b * P ≤ R ∧
      ∀ R', p.b * P ≤ R' → nvValue p ν id P R' ≤ nvValue p ν id P R) ∧
    (∀ R, p.b * p.c ≤ R → ∃ P, p.c ≤ P ∧ p.b * P ≤ R ∧
      ∀ P', p.c ≤ P' → p.b * P' ≤ R → nvValue p ν id P' R ≤ nvValue p ν id P R) ∧
    (∀ P1 P2 R1 R2, p.c ≤ P1 → P1 ≤ P2 →
      (p.b * P1 ≤ R1 ∧ ∀ R', p.b * P1 ≤ R' → nvValue p ν id P1 R' ≤ nvValue p ν id P1 R1) →
      (p.b * P2 ≤ R2 ∧ ∀ R', p.b * P2 ≤ R' → nvValue p ν id P2 R' ≤ nvValue p ν id P2 R2) →
      R1 ≤ R2) ∧
    (∀ R1 R2 P1 P2, R1 ≤ R2 →
      (p.c ≤ P1 ∧ p.b * P1 ≤ R1 ∧
        ∀ P', p.c ≤ P' → p.b * P' ≤ R1 → nvValue p ν id P' R1 ≤ nvValue p ν id P1 R1) →
      (p.c ≤ P2 ∧ p.b * P2 ≤ R2 ∧
        ∀ P', p.c ≤ P' → p.b * P' ≤ R2 → nvValue p ν id P' R2 ≤ nvValue p ν id P2 R2) →
      P1 ≤ P2) := by
  have hb := p.hb
  have hsc := p.hsc
  have hV := V_eq p ν hint
  have hGc : Continuous (G ν) := (G_lip ν hint).continuous
  have hVc : Continuous (fun q : ℝ × ℝ => nvValue p ν id q.1 q.2) := by
    simp only [hV]; fun_prop
  refine ⟨hVc, ?_, ?_, ?_, ?_⟩
  · -- existence of the R-section maximizer
    intro P hP
    have hκ : (P - p.c) / (P - p.s) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    obtain ⟨K, hK⟩ := ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds hκ)).exists_forall_of_atTop
    set K' := max K (p.b * P) with hK'
    have hFK : (P - p.c) / (P - p.s) < cdf ν K' := hK K' (le_max_left _ _)
    have hFK2 : P - p.c < (P - p.s) * cdf ν K' := by
      rw [div_lt_iff₀ (by linarith)] at hFK; linarith
    have hcont : ContinuousOn (fun R => nvValue p ν id P R) (Set.Icc (p.b * P) K') :=
      (hVc.comp (by fun_prop : Continuous fun R : ℝ => (P, R))).continuousOn
    obtain ⟨R0, hR0, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.2 (le_max_right _ _)) hcont
    refine ⟨R0, hR0.1, fun R' hR' => ?_⟩
    rcases le_total R' K' with h | h
    · exact hmax ⟨hR', h⟩
    · have hK'm : nvValue p ν id P K' ≤ nvValue p ν id P R0 :=
        hmax ⟨le_max_right _ _, le_rfl⟩
      refine le_trans ?_ hK'm
      rw [hV, hV]
      obtain ⟨g1, -⟩ := G_diff ν hint K' R' h
      have : (P - p.s) * (cdf ν K' * (R' - K')) ≤ (P - p.s) * (G ν R' - G ν K') :=
        mul_le_mul_of_nonneg_left g1 (by linarith)
      nlinarith
  · -- existence of the P-section maximizer
    intro R hR
    have hRb : p.c ≤ R / p.b := by rw [le_div_iff₀ hb]; linarith
    have hcont : ContinuousOn (fun P => nvValue p ν id P R) (Set.Icc p.c (R / p.b)) :=
      (hVc.comp (by fun_prop : Continuous fun P : ℝ => (P, R))).continuousOn
    obtain ⟨P0, hP0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hRb) hcont
    refine ⟨P0, hP0.1, ?_, fun P' h1' h2' => hmax ⟨h1', ?_⟩⟩
    · have := hP0.2; rw [le_div_iff₀ hb] at this; linarith
    · rw [le_div_iff₀ hb]; linarith
  · -- monotonicity of the R-section maximizer
    intro P1 P2 R1 R2 hc hP12 ⟨hb1, hm1⟩ ⟨hb2, hm2⟩
    by_contra hlt
    push Not at hlt
    have e1 := hm1 R2 (by nlinarith)
    have e2 := hm2 R1 (by linarith)
    set Rm := (R1 + R2) / 2 with hRm
    have e3 := hm2 Rm (by rw [hRm]; linarith)
    rw [hV, hV] at e1 e2
    rw [hV, hV] at e3
    obtain ⟨-, g2⟩ := G_diff ν hint R2 R1 hlt.le
    have hF := cdf_le_one ν R1
    have hgs := G_strict ν hint h1 R1 R2 hlt
    have hst : 0 < (P2 - p.s) * (G ν R1 + G ν R2 - 2 * G ν Rm) :=
      mul_pos (by linarith) (by linarith)
    have hid : 0 ≤ (P2 - P1) * ((R1 - R2) - (G ν R1 - G ν R2)) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  · -- monotonicity of the P-section maximizer
    intro R1 R2 P1 P2 hR ⟨hc1, hb1, hm1⟩ ⟨hc2, hb2, hm2⟩
    by_contra hlt
    push Not at hlt
    have e1 := hm1 P2 hc2 (by nlinarith)
    have e2 := hm2 P1 hc1 (by linarith)
    set Pm := (P1 + P2) / 2 with hPm
    have e3 := hm2 Pm (by rw [hPm]; linarith) (by rw [hPm]; nlinarith)
    rw [hV, hV] at e1 e2 e3
    obtain ⟨-, g2⟩ := G_diff ν hint R1 R2 hR
    have hF := cdf_le_one ν R2
    have hid : 0 ≤ (P1 - P2) * ((R2 - R1) - (G ν R2 - G ν R1)) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hsq : 0 < p.b * (P1 - P2) ^ 2 := mul_pos hb (by nlinarith)
    rw [hPm] at e3
    nlinarith
