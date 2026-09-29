-- Prove2me | solution 1 for LiuVanRyzin.cutoff_strictMono_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:43:27.643919+00:00
-- url     : https://prove2.me/submissions/8917a954-f404-4991-8245-cd6b5ec24233

import Mathlib
import Definitions.Def_LiuVanRyzin_Model

namespace LiuVanRyzin

lemma aux_lvr_pos {u : ℝ → ℝ} (hu : IsCustomerUtility u) {x : ℝ} (hx : 0 < x) : 0 < u x := by
  rw [← hu.2.2.2.2]; exact hu.1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx

lemma aux_lvr_bdd (u : ℝ → ℝ) (p₁ p₂ q : ℝ) : BddBelow {v : ℝ | buysEarly u p₁ p₂ q v} :=
  ⟨p₁, fun _ hv => hv.1⟩

lemma aux_lvr_mem {u : ℝ → ℝ} (hu : IsCustomerUtility u) {p₁ p₂ : ℝ} (hp : p₂ < p₁) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) : buysEarly u p₁ p₂ q (cutoff u p₁ p₂ q) := by
  have hne : ({v : ℝ | buysEarly u p₁ p₂ q v}).Nonempty := by
    have h1q : 0 < 1 - q := by linarith
    have hd : 0 < p₁ - p₂ := by linarith
    refine ⟨p₁ + q * (p₁ - p₂) / (1 - q), ?_, ?_⟩
    · have : 0 ≤ q * (p₁ - p₂) / (1 - q) := div_nonneg (mul_nonneg hq0 hd.le) h1q.le
      linarith
    · have e1 : p₁ + q * (p₁ - p₂) / (1 - q) - p₂ = (p₁ - p₂) / (1 - q) := by
        field_simp; ring
      have e2 : p₁ + q * (p₁ - p₂) / (1 - q) - p₁
          = q * ((p₁ - p₂) / (1 - q)) + (1 - q) * 0 := by
        ring
      rw [e1, e2]
      have hc := hu.2.1.2 (Set.mem_Ici.2 (div_pos hd h1q).le) (Set.mem_Ici.2 (le_refl (0:ℝ)))
        hq0 h1q.le (by ring)
      simp only [smul_eq_mul] at hc
      rw [hu.2.2.2.2] at hc
      linarith
  have hcl : IsClosed {v : ℝ | buysEarly u p₁ p₂ q v} := by
    have hcont : ContinuousOn (fun v => u (v - p₁) - q * u (v - p₂)) (Set.Ici p₁) := by
      apply ContinuousOn.sub
      · exact hu.2.2.1.comp (continuousOn_id.sub continuousOn_const)
          (fun v hv => Set.mem_Ici.2 (by simp at hv ⊢; linarith))
      · exact continuousOn_const.mul (hu.2.2.1.comp (continuousOn_id.sub continuousOn_const)
          (fun v hv => Set.mem_Ici.2 (by simp at hv ⊢; linarith)))
    have := hcont.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_Ici (a := (0:ℝ)))
    convert this using 1
    ext v
    simp [buysEarly, sub_nonneg]
  exact hcl.csInf_mem hne (aux_lvr_bdd u p₁ p₂ q)

lemma aux_lvr_le {u : ℝ → ℝ} {p₁ p₂ q v : ℝ} (hv : buysEarly u p₁ p₂ q v) :
    cutoff u p₁ p₂ q ≤ v :=
  csInf_le (aux_lvr_bdd u p₁ p₂ q) hv

lemma aux_lvr_strictMono {u : ℝ → ℝ} (hu : IsCustomerUtility u) {p₁ p₂ : ℝ} (hp : p₂ < p₁) :
    StrictMonoOn (fun q => cutoff u p₁ p₂ q) (Set.Ico 0 1) := by
  intro q hq q' hq' hqq'
  simp only
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hq0', hq1'⟩ := hq'
  have hm := aux_lvr_mem hu hp hq0' hq1'
  set v' := cutoff u p₁ p₂ q' with hv'
  obtain ⟨hv1, hv2⟩ := hm
  have hqpos : 0 < q' := lt_of_le_of_lt hq0 hqq'
  have hgt : p₁ < v' := by
    rcases hv1.eq_or_lt with h | h
    · exfalso
      rw [← h, sub_self, hu.2.2.2.2] at hv2
      have := aux_lvr_pos hu (show 0 < p₁ - p₂ by linarith)
      nlinarith
    · exact h
  have hB : 0 < u (v' - p₂) := aux_lvr_pos hu (by linarith)
  have hpos : 0 < u (v' - p₁) - q * u (v' - p₂) := by nlinarith
  have hca : ContinuousAt (fun v => u (v - p₁) - q * u (v - p₂)) v' := by
    have h1 := ((hu.2.2.2.1 (v' - p₁) (by linarith)).1).hasDerivAt.comp_sub_const v' p₁
    have h2 := ((hu.2.2.2.1 (v' - p₂) (by linarith)).1).hasDerivAt.comp_sub_const v' p₂
    exact h1.continuousAt.sub (continuousAt_const.mul h2.continuousAt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hca.eventually (lt_mem_nhds hpos))
  have hmin : 0 < min ε (v' - p₁) := lt_min hε (by linarith)
  have hm1 := min_le_left ε (v' - p₁)
  have hm2 := min_le_right ε (v' - p₁)
  set δ := min ε (v' - p₁) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδε : δ < ε := by rw [hδ]; linarith
  have hδv : δ < v' - p₁ := by rw [hδ]; linarith
  have hmem : buysEarly u p₁ p₂ q (v' - δ) := by
    have hd : dist (v' - δ) v' < ε := by
      rw [Real.dist_eq, show v' - δ - v' = -δ by ring, abs_neg, abs_of_pos hδpos]
      exact hδε
    have := hball hd
    exact ⟨by linarith, by linarith⟩
  have := aux_lvr_le hmem
  linarith

lemma aux_lvr_concave {u : ℝ → ℝ} (hu : IsCustomerUtility u) {p₁ p₂ : ℝ} (hp : p₂ < p₁)
    (h3 : ContDiffOn ℝ 3 u (Set.Ioi 0)) (h3' : ∀ x : ℝ, 0 < x → 0 ≤ iteratedDeriv 3 u x) :
    ConcaveOn ℝ (Set.Ici p₁) (fun v => u (v - p₁) / u (v - p₂)) := by
  obtain ⟨hmono, hconc, hcont, hdiff, h0⟩ := hu
  have hd1 : ∀ y, 0 < y → DifferentiableAt ℝ u y := fun y hy => (hdiff y hy).1
  have hd2 : ∀ y, 0 < y → DifferentiableAt ℝ (deriv u) y := fun y hy => (hdiff y hy).2
  have hC2 : ContDiffOn ℝ 2 (deriv u) (Set.Ioi 0) := h3.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hC1 : ContDiffOn ℝ 1 (deriv (deriv u)) (Set.Ioi 0) :=
    hC2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hd3 : ∀ y, 0 < y → DifferentiableAt ℝ (deriv (deriv u)) y := fun y hy =>
    (hC1.differentiableOn (by norm_num) y hy).differentiableAt (isOpen_Ioi.mem_nhds hy)
  have h3'' : ∀ y, 0 < y → 0 ≤ deriv (deriv (deriv u)) y := by
    intro y hy
    have := h3' y hy
    rw [iteratedDeriv_eq_iterate] at this
    exact this
  have hu2mono : MonotoneOn (deriv (deriv u)) (Set.Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun y hy => (hd3 y hy).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; exact fun y hy => (hd3 y hy).differentiableWithinAt
    · rw [interior_Ioi]; exact h3''
  have hu1anti : AntitoneOn (deriv u) (Set.Ioi 0) :=
    (hconc.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).antitoneOn_deriv hd1
  have hu1nn : ∀ y, 0 < y → 0 ≤ deriv u y := by
    intro y hy
    have := (hmono.mono Set.Ioi_subset_Ici_self).monotoneOn.derivWithin_nonneg (x := y)
    rwa [derivWithin_of_isOpen isOpen_Ioi hy] at this
  have hu2np : ∀ y, 0 < y → deriv (deriv u) y ≤ 0 := by
    intro y hy
    have := hu1anti.derivWithin_nonpos (x := y)
    rwa [derivWithin_of_isOpen isOpen_Ioi hy] at this
  have hupos : ∀ y, 0 < y → 0 < u y := fun y hy => by
    rw [← h0]; exact hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.le) hy
  set G1 : ℝ → ℝ := fun v =>
    (deriv u (v - p₁) * u (v - p₂) - u (v - p₁) * deriv u (v - p₂)) / u (v - p₂) ^ 2 with hG1
  set G2 : ℝ → ℝ := fun v =>
    ((deriv (deriv u) (v - p₁) * u (v - p₂) - u (v - p₁) * deriv (deriv u) (v - p₂))
        * u (v - p₂) ^ 2
      - (deriv u (v - p₁) * u (v - p₂) - u (v - p₁) * deriv u (v - p₂))
        * (2 * u (v - p₂) * deriv u (v - p₂))) / (u (v - p₂) ^ 2) ^ 2 with hG2
  have hG : ∀ v, p₁ < v → HasDerivAt (fun v => u (v - p₁) / u (v - p₂)) (G1 v) v := by
    intro v hv
    have h1 := (hd1 (v - p₁) (by linarith)).hasDerivAt.comp_sub_const v p₁
    have h2 := (hd1 (v - p₂) (by linarith)).hasDerivAt.comp_sub_const v p₂
    exact h1.div h2 (hupos _ (by linarith)).ne'
  have hG1d : ∀ v, p₁ < v → HasDerivAt G1 (G2 v) v := by
    intro v hv
    have h1 := (hd1 (v - p₁) (by linarith)).hasDerivAt.comp_sub_const v p₁
    have h2 := (hd1 (v - p₂) (by linarith)).hasDerivAt.comp_sub_const v p₂
    have k1 := (hd2 (v - p₁) (by linarith)).hasDerivAt.comp_sub_const v p₁
    have k2 := (hd2 (v - p₂) (by linarith)).hasDerivAt.comp_sub_const v p₂
    have hne : u (v - p₂) ^ 2 ≠ 0 := pow_ne_zero 2 (hupos _ (by linarith)).ne'
    have := ((k1.mul h2).sub (h1.mul k2)).div (h2.pow 2) hne
    refine this.congr_deriv ?_
    simp only [hG2, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    norm_num
    ring
  have hGeq : ∀ v, p₁ < v → deriv (fun v => u (v - p₁) / u (v - p₂)) =ᶠ[nhds v] G1 := by
    intro v hv
    filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw
    exact (hG w hw).deriv
  apply concaveOn_of_deriv2_nonpos (convex_Ici p₁)
  · apply ContinuousOn.div
    · exact hcont.comp (continuousOn_id.sub continuousOn_const)
        (fun v hv => Set.mem_Ici.2 (by simp at hv ⊢; linarith))
    · exact hcont.comp (continuousOn_id.sub continuousOn_const)
        (fun v hv => Set.mem_Ici.2 (by simp at hv ⊢; linarith))
    · intro v hv
      exact (hupos _ (by simp at hv; linarith)).ne'
  · rw [interior_Ici]; exact fun v hv => (hG v hv).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro v hv
    exact ((hG1d v hv).differentiableAt.congr_of_eventuallyEq (hGeq v hv)).differentiableWithinAt
  · rw [interior_Ici]
    intro v hv
    have hv' : p₁ < v := hv
    show deriv (deriv (fun v => u (v - p₁) / u (v - p₂))) v ≤ 0
    rw [(hGeq v hv').deriv_eq, (hG1d v hv').deriv]
    have y1 : 0 < v - p₁ := by linarith
    have y2 : 0 < v - p₂ := by linarith
    have y12 : v - p₁ < v - p₂ := by linarith
    have hA : 0 < u (v - p₁) := hupos _ y1
    have hB : 0 < u (v - p₂) := hupos _ y2
    have hAB : u (v - p₁) ≤ u (v - p₂) :=
      (hmono (Set.mem_Ici.2 y1.le) (Set.mem_Ici.2 y2.le) y12).le
    have hB1 : 0 ≤ deriv u (v - p₂) := hu1nn _ y2
    have hA1B1 : deriv u (v - p₂) ≤ deriv u (v - p₁) := hu1anti y1 y2 y12.le
    have hA2 : deriv (deriv u) (v - p₁) ≤ 0 := hu2np _ y1
    have hA2B2 : deriv (deriv u) (v - p₁) ≤ deriv (deriv u) (v - p₂) := hu2mono y1 y2 y12.le
    simp only [hG2]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    set A := u (v - p₁)
    set B := u (v - p₂)
    set A1 := deriv u (v - p₁)
    set B1 := deriv u (v - p₂)
    set A2 := deriv (deriv u) (v - p₁)
    set B2 := deriv (deriv u) (v - p₂)
    have ha : A2 * (B - A) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA2 (by linarith)
    have hb : A * (A2 - B2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA.le (by linarith)
    have t1 : A2 * B - A * B2 ≤ 0 := by nlinarith
    have hc : 0 ≤ (A1 - B1) * B := mul_nonneg (by linarith) hB.le
    have hd : 0 ≤ B1 * (B - A) := mul_nonneg hB1 (by linarith)
    have t2 : 0 ≤ A1 * B - A * B1 := by nlinarith
    have e1 : (A2 * B - A * B2) * B ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg t1 (by positivity)
    have e2 : 0 ≤ (A1 * B - A * B1) * (2 * B * B1) :=
      mul_nonneg t2 (by positivity)
    linarith

end LiuVanRyzin

open LiuVanRyzin

theorem solution (u : ℝ → ℝ) (hu : IsCustomerUtility u) (p₁ p₂ : ℝ)
    (hp : p₂ < p₁) :
    StrictMonoOn (fun q => cutoff u p₁ p₂ q) (Set.Ico 0 1) ∧
      (ContDiffOn ℝ 3 u (Set.Ioi 0) → (∀ x : ℝ, 0 < x → 0 ≤ iteratedDeriv 3 u x) →
        ConvexOn ℝ (Set.Ico 0 1) (fun q => cutoff u p₁ p₂ q)) := by
  refine ⟨aux_lvr_strictMono hu hp, fun h3 h3' => ?_⟩
  have hG := aux_lvr_concave hu hp h3 h3'
  refine ⟨convex_Ico 0 1, ?_⟩
  intro q₁ hq₁ q₂ hq₂ a b ha hb hab
  simp only [smul_eq_mul]
  have m1 := aux_lvr_mem hu hp hq₁.1 hq₁.2
  have m2 := aux_lvr_mem hu hp hq₂.1 hq₂.2
  set v₁ := cutoff u p₁ p₂ q₁
  set v₂ := cutoff u p₁ p₂ q₂
  apply aux_lvr_le
  have hv : p₁ ≤ a * v₁ + b * v₂ := by
    have e : a * p₁ + b * p₁ = p₁ := by rw [← add_mul, hab, one_mul]
    have i1 : a * p₁ ≤ a * v₁ := mul_le_mul_of_nonneg_left m1.1 ha
    have i2 : b * p₁ ≤ b * v₂ := mul_le_mul_of_nonneg_left m2.1 hb
    linarith
  refine ⟨hv, ?_⟩
  have hc := hG.2 (Set.mem_Ici.2 m1.1) (Set.mem_Ici.2 m2.1) ha hb hab
  simp only [smul_eq_mul] at hc
  have B1 : 0 < u (v₁ - p₂) := aux_lvr_pos hu (by linarith [m1.1])
  have B2 : 0 < u (v₂ - p₂) := aux_lvr_pos hu (by linarith [m2.1])
  have B : 0 < u (a * v₁ + b * v₂ - p₂) := aux_lvr_pos hu (by linarith)
  have g1 : q₁ ≤ u (v₁ - p₁) / u (v₁ - p₂) := (le_div_iff₀ B1).2 m1.2
  have g2 : q₂ ≤ u (v₂ - p₁) / u (v₂ - p₂) := (le_div_iff₀ B2).2 m2.2
  rw [← le_div_iff₀ B]
  nlinarith [mul_le_mul_of_nonneg_left g1 ha, mul_le_mul_of_nonneg_left g2 hb]
