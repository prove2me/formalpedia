-- Prove2me | solution 1 for LambdaVaRAmb.Robust.proposition_5_properties
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:41:23.171429+00:00
-- url     : https://prove2.me/submissions/7b29222d-5ccd-4e27-aa64-214e6f02a4bf

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting

open Filter Topology Set LambdaVaRAmb.Robust

namespace LRobP5Aux

/-- the two-point divergence `f(x,t)` -/
noncomputable def F (ψ : ℝ → ℝ) (x t : ℝ) : ℝ := x * ψ (t / x) + (1 - x) * ψ ((1 - t) / (1 - x))

variable {ψ : ℝ → ℝ}

lemma F_self (h1 : ψ 1 = 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : F ψ x x = 0 := by
  rcases hx1.eq_or_lt with h | h
  · subst h; simp [F, h1]
  · have : (1 - x) / (1 - x) = 1 := div_self (by linarith)
    simp [F, div_self hx0.ne', this, h1]

lemma F_pos (hsc : StrictConvexOn ℝ (Ici 0) ψ) (h1 : ψ 1 = 0) {x t : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hne : t ≠ x) : 0 < F ψ x t := by
  have hx1' : 0 < 1 - x := by linarith
  have ha : (0 : ℝ) ≤ t / x := div_nonneg ht0 hx0.le
  have hb : (0 : ℝ) ≤ (1 - t) / (1 - x) := div_nonneg (by linarith) hx1'.le
  have hab : t / x ≠ (1 - t) / (1 - x) := by
    intro h
    rw [div_eq_div_iff hx0.ne' hx1'.ne'] at h
    apply hne; nlinarith
  have := hsc.2 (mem_Ici.2 ha) (mem_Ici.2 hb) hab hx0 hx1' (by ring)
  have hsum : x • (t / x) + (1 - x) • ((1 - t) / (1 - x)) = 1 := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [hsum, h1] at this
  simpa [F, smul_eq_mul] using this

lemma F_nonneg (hsc : StrictConvexOn ℝ (Ici 0) ψ) (h1 : ψ 1 = 0) {x t : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ F ψ x t := by
  by_cases h : t = x
  · subst h; rw [F_self h1 hx0 hx1.le]
  · exact (F_pos hsc h1 hx0 hx1 ht0 ht1 h).le

/-- convexity of `t ↦ F x t` -/
lemma F_convex_t (hc : ConvexOn ℝ (Ici 0) ψ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {a b l m : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hl : 0 ≤ l)
    (hm : 0 ≤ m) (hlm : l + m = 1) :
    F ψ x (l * a + m * b) ≤ l * F ψ x a + m * F ψ x b := by
  have hx1' : 0 < 1 - x := by linarith
  have e1 := hc.2 (mem_Ici.2 (div_nonneg ha0 hx0.le)) (mem_Ici.2 (div_nonneg hb0 hx0.le)) hl hm hlm
  have e2 := hc.2 (mem_Ici.2 (div_nonneg (by linarith : (0:ℝ) ≤ 1 - a) hx1'.le))
    (mem_Ici.2 (div_nonneg (by linarith : (0:ℝ) ≤ 1 - b) hx1'.le)) hl hm hlm
  simp only [smul_eq_mul] at e1 e2
  have q1 : l * (a / x) + m * (b / x) = (l * a + m * b) / x := by field_simp
  have q2 : l * ((1 - a) / (1 - x)) + m * ((1 - b) / (1 - x)) = (1 - (l * a + m * b)) / (1 - x) := by
    rw [show m = 1 - l by linarith]; field_simp; ring
  rw [q1] at e1; rw [q2] at e2
  unfold F
  have := mul_le_mul_of_nonneg_left e1 hx0.le
  have := mul_le_mul_of_nonneg_left e2 hx1'.le
  nlinarith

lemma F_strictMono_t (hsc : StrictConvexOn ℝ (Ici 0) ψ) (h1 : ψ 1 = 0) {x t1 t2 : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (h1t : x ≤ t1) (h12 : t1 < t2) (ht2 : t2 ≤ 1) :
    F ψ x t1 < F ψ x t2 := by
  have hpos : 0 < F ψ x t2 := F_pos hsc h1 hx0 hx1 (by linarith) ht2 (by linarith)
  rcases h1t.eq_or_lt with h | h
  · subst h; rw [F_self h1 hx0 hx1.le]; exact hpos
  have hd : 0 < t2 - x := by linarith
  obtain ⟨l, hl⟩ : ∃ l, l = (t2 - t1) / (t2 - x) := ⟨_, rfl⟩
  have hl0 : 0 < l := hl ▸ div_pos (by linarith) hd
  have hl1 : l < 1 := hl ▸ (div_lt_one hd).2 (by linarith)
  have heq : l * x + (1 - l) * t2 = t1 := by
    rw [hl]; field_simp; ring
  have := F_convex_t hsc.convexOn hx0 hx1 hx0.le hx1.le (by linarith) ht2 hl0.le (by linarith)
    (by ring) (a := x) (b := t2) (l := l) (m := 1 - l)
  rw [heq, F_self h1 hx0 hx1.le] at this
  nlinarith

/-- perspective inequality -/
lemma persp (hc : ConvexOn ℝ (Ici 0) ψ) {s u1 u2 a b : ℝ} (hs : 0 ≤ s) (hu1 : 0 ≤ u1)
    (hu2 : 0 ≤ u2) (hcase : s = 0 ∨ (0 < u1 ∧ 0 < u2)) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * u1 + b * u2) * ψ (s / (a * u1 + b * u2)) ≤ a * (u1 * ψ (s / u1)) + b * (u2 * ψ (s / u2)) := by
  rcases hcase with h | ⟨h1, h2⟩
  · subst h; simp only [zero_div]; ring_nf; linarith
  · have hu : 0 < a * u1 + b * u2 := by
      rcases ha.eq_or_lt with ha' | ha'
      · subst ha'; simp at hab; subst hab; simpa using h2
      · positivity
    have hw1 : 0 ≤ a * u1 / (a * u1 + b * u2) := by positivity
    have hw2 : 0 ≤ b * u2 / (a * u1 + b * u2) := by positivity
    have hw : a * u1 / (a * u1 + b * u2) + b * u2 / (a * u1 + b * u2) = 1 := by
      rw [← add_div, div_self hu.ne']
    have e := hc.2 (mem_Ici.2 (div_nonneg hs h1.le)) (mem_Ici.2 (div_nonneg hs h2.le)) hw1 hw2 hw
    simp only [smul_eq_mul] at e
    have q : a * u1 / (a * u1 + b * u2) * (s / u1) + b * u2 / (a * u1 + b * u2) * (s / u2) =
        s / (a * u1 + b * u2) := by
      field_simp; linear_combination s * hab
    rw [q] at e
    have := mul_le_mul_of_nonneg_left e hu.le
    calc (a * u1 + b * u2) * ψ (s / (a * u1 + b * u2))
        ≤ (a * u1 + b * u2) * (a * u1 / (a * u1 + b * u2) * ψ (s / u1) +
            b * u2 / (a * u1 + b * u2) * ψ (s / u2)) := this
      _ = a * (u1 * ψ (s / u1)) + b * (u2 * ψ (s / u2)) := by field_simp

lemma F_strictAnti_x (hsc : StrictConvexOn ℝ (Ici 0) ψ) (h1 : ψ 1 = 0) {x1 x2 t : ℝ}
    (hx1 : 0 < x1) (h12 : x1 < x2) (h2t : x2 ≤ t) (ht : t ≤ 1) : F ψ x2 t < F ψ x1 t := by
  have hc := hsc.convexOn
  have hpos : 0 < F ψ x1 t := F_pos hsc h1 hx1 (by linarith) (by linarith) ht (by linarith)
  have hd : 0 < t - x1 := by linarith
  obtain ⟨l, hl⟩ : ∃ l, l = (t - x2) / (t - x1) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = (x2 - x1) / (t - x1) := ⟨_, rfl⟩
  have hl0 : 0 ≤ l := hl ▸ div_nonneg (by linarith) hd.le
  have hl1 : l < 1 := hl ▸ (div_lt_one hd).2 (by linarith)
  have hm0 : 0 ≤ m := hm ▸ div_nonneg (by linarith) hd.le
  have hlm : l + m = 1 := by rw [hl, hm]; field_simp; ring
  have hx : l * x1 + m * t = x2 := by rw [hl, hm]; field_simp; ring
  have hx' : l * (1 - x1) + m * (1 - t) = 1 - x2 := by
    rw [← hx]; linear_combination hlm
  have e1 := persp hc (by linarith : (0:ℝ) ≤ t) hx1.le (by linarith : (0:ℝ) ≤ t)
    (Or.inr ⟨hx1, by linarith⟩) hl0 hm0 hlm
  have e2 := persp hc (s := 1 - t) (by linarith) (by linarith : (0:ℝ) ≤ 1 - x1)
    (by linarith : (0:ℝ) ≤ 1 - t)
    (by rcases ht.eq_or_lt with h | h
        · left; linarith
        · right; constructor <;> linarith) hl0 hm0 hlm
  rw [hx] at e1; rw [hx'] at e2
  have hFt : F ψ t t = 0 := F_self h1 (by linarith) ht
  have : F ψ x2 t ≤ l * F ψ x1 t + m * F ψ t t := by
    unfold F; unfold F at hFt; nlinarith
  rw [hFt] at this
  nlinarith


lemma F_contOn_t (hcont : ContinuousOn ψ (Ici 0)) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ContinuousOn (F ψ x) (Icc 0 1) := by
  have hx1' : 0 < 1 - x := by linarith
  unfold F
  apply ContinuousOn.add
  · refine continuousOn_const.mul (hcont.comp (continuousOn_id.div_const x) ?_)
    intro t ht; exact mem_Ici.2 (div_nonneg ht.1 hx0.le)
  · refine continuousOn_const.mul (hcont.comp ((continuousOn_const.sub continuousOn_id).div_const _) ?_)
    intro t ht; exact mem_Ici.2 (div_nonneg (by linarith [ht.2]) hx1'.le)

lemma F_contAt_t (hcont : ContinuousOn ψ (Ici 0)) {x t : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (ht0 : 0 < t) (ht1 : t < 1) : ContinuousAt (F ψ x) t :=
  ((F_contOn_t hcont hx0 hx1).mono Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds ht0 ht1)

lemma F_contOn_x (hcont : ContinuousOn ψ (Ici 0)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ContinuousOn (fun x => F ψ x t) (Ioo 0 1) := by
  unfold F
  apply ContinuousOn.add
  · refine continuousOn_id.mul (hcont.comp (continuousOn_const.div continuousOn_id
      (fun x hx => hx.1.ne')) ?_)
    intro x hx; exact mem_Ici.2 (div_nonneg ht0 hx.1.le)
  · refine (continuousOn_const.sub continuousOn_id).mul (hcont.comp (continuousOn_const.div
      (continuousOn_const.sub continuousOn_id) (fun x hx => by linarith [hx.2])) ?_)
    intro x hx; exact mem_Ici.2 (div_nonneg (by linarith) (by linarith [hx.2]))

lemma bdd_below (hcont : ContinuousOn ψ (Ici 0)) : ∃ M, 0 ≤ M ∧ ∀ y ∈ Icc (0:ℝ) 2, -M ≤ ψ y := by
  obtain ⟨m, hm⟩ := isCompact_Icc.bddBelow_image (hcont.mono (Icc_subset_Ici_self : Icc (0:ℝ) 2 ⊆ Ici 0))
  refine ⟨max (-m) 0, le_max_right _ _, fun y hy => ?_⟩
  have := hm ⟨y, hy, rfl⟩
  have : -max (-m) 0 ≤ m := by rw [neg_le]; exact le_max_left _ _
  linarith

lemma F_large (hcont : ContinuousOn ψ (Ici 0)) (hsl : Tendsto (fun y => ψ y / y) atTop atTop)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (B : ℝ) : ∃ x ∈ Ioo 0 s, B < F ψ x s := by
  obtain ⟨M, hM0, hM⟩ := bdd_below hcont
  obtain ⟨K, hK2, hK⟩ := ((eventually_ge_atTop (2:ℝ)).and
    (hsl.eventually_ge_atTop ((B + M + 1) / s))).exists
  have hK0 : 0 < K := by linarith
  refine ⟨s / K, ⟨div_pos hs0 hK0, (div_lt_self hs0 (by linarith))⟩, ?_⟩
  have hx0 : 0 < s / K := div_pos hs0 hK0
  have hxh : s / K ≤ 1 / 2 := by
    rw [div_le_iff₀ hK0]; nlinarith
  have hsx : s / (s / K) = K := by field_simp
  have e1 : B + M + 1 ≤ s / K * ψ K := by
    have := (div_le_iff₀ hs0).1 hK
    have h2 : ψ K / K * s = s / K * ψ K := by ring
    linarith
  have hy : (1 - s) / (1 - s / K) ∈ Icc (0:ℝ) 2 := by
    have h1x : 0 < 1 - s / K := by linarith
    refine ⟨div_nonneg (by linarith) h1x.le, ?_⟩
    rw [div_le_iff₀ h1x]; linarith
  have e2 := hM _ hy
  have h1x : 0 ≤ 1 - s / K := by linarith
  have e3 : (1 - s / K) * (-M) ≤ (1 - s / K) * ψ ((1 - s) / (1 - s / K)) :=
    mul_le_mul_of_nonneg_left e2 h1x
  have e4 : -M ≤ (1 - s / K) * (-M) := by nlinarith
  unfold F; rw [hsx]; linarith

lemma cont_of_mono_surj {g : ℝ → ℝ} {p q : ℝ} (hmono : MonotoneOn g (Icc p q))
    (hsurj : ∀ y ∈ Icc (g p) (g q), ∃ x ∈ Icc p q, g x = y) : ContinuousOn g (Icc p q) := by
  intro a ha
  have hpq : p ≤ q := ha.1.trans ha.2
  have hp : p ∈ Icc p q := ⟨le_rfl, hpq⟩
  have hq : q ∈ Icc p q := ⟨hpq, le_rfl⟩
  rw [ContinuousWithinAt, tendsto_order]
  constructor
  · intro b hb
    by_cases hbp : b < g p
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact lt_of_lt_of_le hbp (hmono hp hx hx.1)
    · push_neg at hbp
      have hga : g a ≤ g q := hmono ha hq ha.2
      obtain ⟨c, hc, hgc⟩ := hsurj ((b + g a) / 2) ⟨by linarith, by linarith⟩
      have hca : c < a := by
        by_contra h; push_neg at h; have := hmono ha hc h; linarith
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hca)] with x hx hxc
      have := hmono hc hx (le_of_lt hxc)
      linarith
  · intro b hb
    by_cases hbq : g q < b
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact lt_of_le_of_lt (hmono hx hq hx.2) hbq
    · push_neg at hbq
      have hga : g p ≤ g a := hmono hp ha ha.1
      obtain ⟨c, hc, hgc⟩ := hsurj ((b + g a) / 2) ⟨by linarith, by linarith⟩
      have hca : a < c := by
        by_contra h; push_neg at h; have := hmono hc ha h; linarith
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hca)] with x hx hxc
      have := hmono hx hc (le_of_lt hxc)
      linarith

/-- the sublevel set and its supremum -/
def T (ψ : ℝ → ℝ) (δ x : ℝ) : Set ℝ := {t | t ∈ Icc x 1 ∧ F ψ x t ≤ δ}

noncomputable def G (ψ : ℝ → ℝ) (δ x : ℝ) : ℝ := sSup (T ψ δ x)

section
variable (hsc : StrictConvexOn ℝ (Ici 0) ψ) (h1 : ψ 1 = 0) (hcont : ContinuousOn ψ (Ici 0))
include hsc h1 hcont

lemma G_mem {δ x : ℝ} (hδ : 0 ≤ δ) (hx0 : 0 < x) (hx1 : x < 1) : G ψ δ x ∈ T ψ δ x := by
  have hne : (T ψ δ x).Nonempty := ⟨x, ⟨le_rfl, hx1.le⟩, by rw [F_self h1 hx0 hx1.le]; exact hδ⟩
  have hbdd : BddAbove (T ψ δ x) := ⟨1, fun t ht => ht.1.2⟩
  have hcl : IsClosed (T ψ δ x) := by
    have : T ψ δ x = Icc x 1 ∩ F ψ x ⁻¹' Iic δ := rfl
    rw [this]
    exact ((F_contOn_t hcont hx0 hx1).mono (Icc_subset_Icc_left hx0.le)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
  exact hcl.csSup_mem hne hbdd

lemma G_iff {δ x t : ℝ} (hδ : 0 ≤ δ) (hx0 : 0 < x) (hx1 : x < 1) (ht : t ∈ Icc x 1) :
    t ≤ G ψ δ x ↔ F ψ x t ≤ δ := by
  have hm := G_mem hsc h1 hcont hδ hx0 hx1
  constructor
  · intro h
    rcases h.eq_or_lt with h' | h'
    · rw [h']; exact hm.2
    · exact (F_strictMono_t hsc h1 hx0 hx1 ht.1 h' hm.1.2).le.trans hm.2
  · intro h; exact le_csSup ⟨1, fun t ht => ht.1.2⟩ ⟨ht, h⟩

lemma G_gt {δ x t : ℝ} (hδ : 0 ≤ δ) (hx0 : 0 < x) (hx1 : x < 1) (hxt : x ≤ t) (ht1 : t < 1)
    (hF : F ψ x t < δ) : t < G ψ δ x := by
  have hca := F_contAt_t hcont hx0 hx1 (by linarith) ht1
  have hev : ∀ᶠ t' in 𝓝[>] t, F ψ x t' < δ ∧ t' < 1 :=
    nhdsWithin_le_nhds ((hca.eventually (gt_mem_nhds hF)).and (Iio_mem_nhds ht1))
  obtain ⟨t', ⟨h1', h2'⟩, ht'⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht'' : t < t' := ht'
  have := (G_iff hsc h1 hcont hδ hx0 hx1 ⟨by linarith, h2'.le⟩).2 h1'.le
  exact lt_of_lt_of_le ht'' this

end

end LRobP5Aux

open LRobP5Aux in
theorem solution (φ : ℝ → EReal) (hφ : IsPhiFunction φ)
    (hfin : ∀ x : ℝ, 0 ≤ x → φ x ≠ ⊤)
    (hsc : StrictConvexOn ℝ (Set.Ici 0) (fun x => (φ x).toReal))
    (hsl : Tendsto (fun x => (φ x).toReal / x) atTop atTop) :
    (∀ δ : ℝ, 0 < δ → ∃ xδ ∈ Set.Ioo (0 : ℝ) 1,
        xδ * (φ (1 / xδ)).toReal + (1 - xδ) * (φ 0).toReal = δ ∧
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, x * (φ (1 / x)).toReal + (1 - x) * (φ 0).toReal = δ → x = xδ) ∧
        ContinuousOn (gPhi φ δ) (Set.Icc 0 xδ) ∧ StrictMonoOn (gPhi φ δ) (Set.Icc 0 xδ) ∧
        ∀ x ∈ Set.Icc xδ 1, gPhi φ δ x = 1) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1,
        (∀ δ : ℝ, 0 < δ → x < gPhi φ δ x) ∧
        MonotoneOn (fun δ => gPhi φ δ x) (Set.Ioi 0) ∧
        Tendsto (fun δ => gPhi φ δ x) (𝓝[>] 0) (𝓝 x)) := by
  set ψ : ℝ → ℝ := fun x => (φ x).toReal with hψ
  have hφψ : ∀ x, 0 ≤ x → φ x = (ψ x : EReal) := fun x hx =>
    (EReal.coe_toReal (hfin x hx) (hφ.ne_bot x hx)).symm
  have h1 : ψ 1 = 0 := by simp [hψ, hφ.map_one]
  have hc : ConvexOn ℝ (Ici 0) ψ := hsc.convexOn
  have hcont : ContinuousOn ψ (Ici 0) := by
    intro y hy
    rcases (mem_Ici.1 hy).eq_or_lt with h | h
    · rw [← h]
      exact continuousWithinAt_Ioi_iff_Ici.1 <| (EReal.tendsto_toReal (hfin 0 le_rfl) (hφ.ne_bot 0 le_rfl)).comp hφ.map_zero
    · have : ContinuousOn ψ (interior (Ici 0)) := hc.continuousOn_interior
      rw [interior_Ici] at this
      exact (this.continuousAt (Ioi_mem_nhds h)).continuousWithinAt
  have hg : ∀ δ x, 0 < x → x < 1 → gPhi φ δ x = G ψ δ x := by
    intro δ x hx0 hx1
    unfold gPhi G T
    rw [if_neg hx0.ne', if_neg hx1.ne]
    congr 1; ext t
    simp only [mem_setOf_eq]
    constructor <;> rintro ⟨ht, h⟩ <;> refine ⟨ht, ?_⟩
    all_goals
      have e : (x : EReal) * φ (t / x) + ((1 - x : ℝ) : EReal) * φ ((1 - t) / (1 - x)) =
          ((F ψ x t : ℝ) : EReal) := by
        rw [hφψ _ (div_nonneg (hx0.le.trans ht.1) hx0.le),
          hφψ _ (div_nonneg (by linarith [ht.2]) (by linarith))]
        simp only [F, EReal.coe_add, EReal.coe_mul]
    · rw [e] at h; exact_mod_cast h
    · rw [e]; exact_mod_cast h
  have hg0 : ∀ δ, gPhi φ δ 0 = 0 := fun δ => by simp [gPhi]
  have hg1 : ∀ δ, gPhi φ δ 1 = 1 := fun δ => by simp [gPhi]
  have hF1 : ∀ x, F ψ x 1 = x * (φ (1 / x)).toReal + (1 - x) * (φ 0).toReal := by
    intro x; simp [F, hψ]
  refine ⟨fun δ hδ => ?_, fun x hx => ?_⟩
  · -- existence of `x_δ`
    obtain ⟨x0, hx0, hx0δ⟩ := F_large hcont hsl one_pos le_rfl δ
    have hcont1 : ContinuousOn (fun x => F ψ x 1) (Icc x0 1) := by
      have : (fun x => F ψ x 1) = fun x => x * ψ (1 / x) + (1 - x) * ψ 0 := by
        funext x; simp [F]
      rw [this]
      apply ContinuousOn.add
      · refine continuousOn_id.mul (hcont.comp
          ((continuousOn_const (c := (1:ℝ))).div continuousOn_id
          (fun x hx => (hx0.1.trans_le hx.1).ne')) ?_)
        intro x hx; exact mem_Ici.2 (div_nonneg zero_le_one (hx0.1.le.trans hx.1))
      · exact ((continuousOn_const (c := (1:ℝ))).sub continuousOn_id).mul continuousOn_const
    have hF11 : F ψ 1 1 = 0 := F_self h1 one_pos le_rfl
    obtain ⟨xδ, hxδI, hxδ⟩ := intermediate_value_Icc' hx0.2.le hcont1
      ⟨by rw [hF11]; exact hδ.le, hx0δ.le⟩
    have hxδ1 : xδ < 1 := by
      rcases hxδI.2.eq_or_lt with h | h
      · exfalso; simp only at hxδ; rw [h, hF11] at hxδ; linarith
      · exact h
    have hxδ0 : 0 < xδ := hx0.1.trans_le hxδI.1
    simp only at hxδ
    -- strict antitonicity of `h(x) = F x 1`
    have hanti : ∀ a b, 0 < a → a < b → b ≤ 1 → F ψ b 1 < F ψ a 1 :=
      fun a b ha hab hb => F_strictAnti_x hsc h1 ha hab hb le_rfl
    have hgt : ∀ x, 0 < x → x < xδ → δ < F ψ x 1 := fun x hx h => hxδ ▸ hanti x xδ hx h hxδ1.le
    have hle : ∀ x, xδ ≤ x → x ≤ 1 → F ψ x 1 ≤ δ := by
      intro x h h'
      rcases h.eq_or_lt with e | e
      · rw [← e, hxδ]
      · exact hxδ ▸ (hanti xδ x hxδ0 e h').le
    have hone : ∀ x ∈ Icc xδ 1, gPhi φ δ x = 1 := by
      intro x hx
      rcases hx.2.eq_or_lt with e | e
      · rw [e, hg1]
      have hx0' : 0 < x := hxδ0.trans_le hx.1
      rw [hg δ x hx0' e]
      apply le_antisymm (G_mem hsc h1 hcont hδ.le hx0' e).1.2
      exact (G_iff hsc h1 hcont hδ.le hx0' e ⟨e.le, le_rfl⟩).2 (hle x hx.1 hx.2)
    have hmono : StrictMonoOn (gPhi φ δ) (Icc 0 xδ) := by
      intro a ha b hb hab
      have hb0 : 0 < b := ha.1.trans_lt hab
      have hb1 : b < 1 := hb.2.trans_lt hxδ1
      rw [hg δ b hb0 hb1]
      have hGb := G_mem hsc h1 hcont hδ.le hb0 hb1
      rcases ha.1.eq_or_lt with e | e
      · rw [← e, hg0]; exact hb0.trans_le hGb.1.1
      have ha1 : a < 1 := hab.trans hb1
      rw [hg δ a e ha1]
      by_contra hcon
      push_neg at hcon
      have hGa := G_mem hsc h1 hcont hδ.le e ha1
      have hbG : b ≤ G ψ δ b := hGb.1.1
      have f1 : F ψ a (G ψ δ b) ≤ δ :=
        (G_iff hsc h1 hcont hδ.le e ha1 ⟨hab.le.trans hbG, hGb.1.2⟩).1 hcon
      have f2 : F ψ b (G ψ δ b) < F ψ a (G ψ δ b) := F_strictAnti_x hsc h1 e hab hbG hGb.1.2
      rcases hGb.1.2.eq_or_lt with e1 | e1
      · rw [e1] at f2 f1
        rcases hb.2.eq_or_lt with e2 | e2
        · rw [e2] at f2; linarith [hxδ]
        · linarith [hgt b hb0 e2]
      · have := G_gt hsc h1 hcont hδ.le hb0 hb1 hbG e1 (by linarith)
        linarith
    refine ⟨xδ, ⟨hxδ0, hxδ1⟩, (hF1 xδ) ▸ hxδ, ?_, ?_, hmono, hone⟩
    · intro x hx hxe
      rw [← hF1] at hxe
      rcases lt_trichotomy x xδ with h | h | h
      · have := hgt x hx.1 h; linarith
      · exact h
      · have := hanti xδ x hxδ0 h hx.2.le; linarith
    · apply cont_of_mono_surj hmono.monotoneOn
      intro y hy
      rw [hg0, hone xδ ⟨le_rfl, hxδ1.le⟩] at hy
      rcases hy.1.eq_or_lt with e | e
      · exact ⟨0, ⟨le_rfl, hxδ0.le⟩, by rw [hg0, e]⟩
      rcases hy.2.eq_or_lt with e' | e'
      · exact ⟨xδ, ⟨hxδ0.le, le_rfl⟩, by rw [hone xδ ⟨le_rfl, hxδ1.le⟩, e']⟩
      -- solve `F x y = δ` for `x`
      obtain ⟨x1, hx1, hx1δ⟩ := F_large hcont hsl e e'.le δ
      have hcy : ContinuousOn (fun x => F ψ x y) (Icc x1 y) :=
        (F_contOn_x hcont e.le e'.le).mono (fun x hx => ⟨hx1.1.trans_le hx.1, hx.2.trans_lt e'⟩)
      have hFyy : F ψ y y = 0 := F_self h1 e e'.le
      obtain ⟨x2, hx2I, hx2⟩ := intermediate_value_Icc' hx1.2.le hcy
        ⟨by rw [hFyy]; exact hδ.le, hx1δ.le⟩
      simp only at hx2
      have hx20 : 0 < x2 := hx1.1.trans_le hx2I.1
      have hx2y : x2 < y := by
        rcases hx2I.2.eq_or_lt with h | h
        · rw [h, hFyy] at hx2; linarith
        · exact h
      have hx21 : x2 < 1 := hx2y.trans e'
      have hGx2 : G ψ δ x2 = y := by
        have hle' := (G_iff hsc h1 hcont hδ.le hx20 hx21 ⟨hx2y.le, e'.le⟩).2 hx2.le
        have hm := G_mem hsc h1 hcont hδ.le hx20 hx21
        apply le_antisymm _ hle'
        by_contra hlt; push_neg at hlt
        have := F_strictMono_t hsc h1 hx20 hx21 hx2y.le hlt hm.1.2
        linarith [hm.2]
      have hx2δ : x2 < xδ := by
        by_contra h; push_neg at h
        have := hone x2 ⟨h, hx21.le⟩
        rw [hg δ x2 hx20 hx21, hGx2] at this; linarith
      exact ⟨x2, ⟨hx20.le, hx2δ.le⟩, by rw [hg δ x2 hx20 hx21, hGx2]⟩
  · -- part 2
    have hx0 := hx.1; have hx1 := hx.2
    have hFxx : F ψ x x = 0 := F_self h1 hx0 hx1.le
    refine ⟨fun δ hδ => ?_, ?_, ?_⟩
    · rw [hg δ x hx0 hx1]
      exact G_gt hsc h1 hcont hδ.le hx0 hx1 le_rfl hx1 (by rw [hFxx]; exact hδ)
    · intro δ1 hδ1 δ2 hδ2 h12
      simp only
      rw [hg δ1 x hx0 hx1, hg δ2 x hx0 hx1]
      have hm := G_mem hsc h1 hcont (le_of_lt hδ1) hx0 hx1
      exact (G_iff hsc h1 hcont (le_of_lt hδ2) hx0 hx1 hm.1).2 (hm.2.trans h12)
    · rw [tendsto_order]
      constructor
      · intro b hb
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        rw [hg δ x hx0 hx1]
        exact lt_of_lt_of_le hb (G_mem hsc h1 hcont (le_of_lt hδ) hx0 hx1).1.1
      · intro b hb
        set t0 := min b ((x + 1) / 2)
        have ht0x : x < t0 := lt_min hb (by linarith)
        have ht01 : t0 < 1 := (min_le_right _ _).trans_lt (by linarith)
        have hpos : 0 < F ψ x t0 := F_pos hsc h1 hx0 hx1 (by linarith) ht01.le ht0x.ne'
        filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
        rw [hg δ x hx0 hx1]
        have : G ψ δ x < t0 := by
          by_contra hc; push_neg at hc
          have := (G_iff hsc h1 hcont (le_of_lt hδ.1) hx0 hx1 ⟨ht0x.le, ht01.le⟩).1 hc
          linarith [hδ.2]
        exact this.trans_le (min_le_left _ _)
