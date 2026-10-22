-- Prove2me | solution 1 for LeviSampling.BaseStock.error_no_backward_propagation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:18:42.903232+00:00
-- url     : https://prove2.me/submissions/4001b747-34da-435b-9912-8cc825fab57f

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Shadow
open MeasureTheory
open LeviSampling.BaseStock

def g69h2_Lip (f : ℝ → ℝ) (K : ℝ) : Prop := 0 ≤ K ∧ ∀ x x', |f x - f x'| ≤ K * |x - x'|

theorem g69h2_Lip.continuous {f : ℝ → ℝ} {K : ℝ} (hf : g69h2_Lip f K) : Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨K, hf.1⟩) fun x x' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  exact hf.2 x x'

theorem g69h2_int (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    {f : ℝ → ℝ} {K : ℝ} (hf : g69h2_Lip f K) (z : ℝ) : Integrable (fun d => f (z - d)) μ := by
  have hc := hf.continuous
  refine Integrable.mono' (g := fun d => |f 0| + K * |z| + K * |d|) ?_
    (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => ?_)
  · exact ((integrable_const _).add (integrable_const _)).add (hμ.abs.const_mul K)
  · rw [Real.norm_eq_abs]
    have h1 := hf.2 (z - d) 0
    have h2 : |z - d - 0| ≤ |z| + |d| := by rw [sub_zero]; exact abs_sub _ _
    have : |f (z - d)| ≤ |f 0| + |f (z - d) - f 0| := by
      have := abs_sub_abs_le_abs_sub (f (z - d)) (f 0); linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hf.1]

theorem g69h2_int_lip (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    {f : ℝ → ℝ} {K : ℝ} (hf : g69h2_Lip f K) : g69h2_Lip (fun z => ∫ d, f (z - d) ∂μ) K := by
  refine ⟨hf.1, fun z z' => ?_⟩
  rw [← integral_sub (g69h2_int μ hμ hf z) (g69h2_int μ hμ hf z')]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := K * |z - z'|)
    (f := fun d => f (z - d) - f (z' - d)) (Filter.Eventually.of_forall fun d => by
      rw [Real.norm_eq_abs]
      have := hf.2 (z - d) (z' - d)
      rwa [show z - d - (z' - d) = z - z' by ring] at this)
  simpa using this

theorem g69h2_int_convex (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    {f : ℝ → ℝ} {K : ℝ} (hf : g69h2_Lip f K) (hfc : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun z => ∫ d, f (z - d) ∂μ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((g69h2_int μ hμ hf x).const_mul a) ((g69h2_int μ hμ hf y).const_mul b)]
  refine integral_mono (g69h2_int μ hμ hf _)
    (((g69h2_int μ hμ hf x).const_mul a).add ((g69h2_int μ hμ hf y).const_mul b)) fun d => ?_
  have := hfc.2 (Set.mem_univ (x - d)) (Set.mem_univ (y - d)) ha hb hab
  simp only [smul_eq_mul] at this
  have e : a * x + b * y - d = a * (x - d) + b * (y - d) := by
    have : d = (a + b) * d := by rw [hab, one_mul]
    linear_combination (-1:ℝ) * this
  simp only
  rw [e]; exact this

noncomputable def g69h2_phi (h b : ℝ) (u : ℝ) : ℝ := h * max u 0 + b * max (-u) 0

theorem g69h2_nv_eq (μ : Measure ℝ) (h b y : ℝ) :
    nvCost μ h b y = ∫ d, g69h2_phi h b (y - d) ∂μ := by
  unfold nvCost g69h2_phi
  simp only [neg_sub]

theorem g69h2_phi_lip (h b : ℝ) (hh : 0 < h) (hb : 0 < b) : g69h2_Lip (g69h2_phi h b) (h + b) := by
  refine ⟨by linarith, fun x x' => ?_⟩
  unfold g69h2_phi
  have h1 := abs_max_sub_max_le_abs x x' 0
  have h2 := abs_max_sub_max_le_abs (-x) (-x') 0
  rw [show -x - -x' = -(x - x') by ring, abs_neg] at h2
  calc |h * max x 0 + b * max (-x) 0 - (h * max x' 0 + b * max (-x') 0)|
      = |h * (max x 0 - max x' 0) + b * (max (-x) 0 - max (-x') 0)| := by ring_nf
    _ ≤ |h * (max x 0 - max x' 0)| + |b * (max (-x) 0 - max (-x') 0)| := abs_add_le _ _
    _ = h * |max x 0 - max x' 0| + b * |max (-x) 0 - max (-x') 0| := by
        rw [abs_mul, abs_mul, abs_of_pos hh, abs_of_pos hb]
    _ ≤ h * |x - x'| + b * |x - x'| := by gcongr
    _ = (h + b) * |x - x'| := by ring

theorem g69h2_max_convex (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    max (a * x + b * y) 0 ≤ a * max x 0 + b * max y 0 := by
  apply max_le
  · nlinarith [le_max_left x 0, le_max_left y 0]
  · nlinarith [le_max_right x 0, le_max_right y 0]

theorem g69h2_phi_convex (h b : ℝ) (hh : 0 < h) (hb : 0 < b) :
    ConvexOn ℝ Set.univ (g69h2_phi h b) := by
  refine ⟨convex_univ, fun x _ y _ a c ha hc hac => ?_⟩
  simp only [smul_eq_mul, g69h2_phi]
  have e1 := g69h2_max_convex x y a c ha hc hac
  have e2 := g69h2_max_convex (-x) (-y) a c ha hc hac
  rw [show a * -x + c * -y = -(a * x + c * y) by ring] at e2
  have := mul_le_mul_of_nonneg_left e1 hh.le
  have := mul_le_mul_of_nonneg_left e2 hb.le
  nlinarith

theorem g69h2_bs_ge (T : ℕ) (μ : ℕ → Measure ℝ) (h b L : ℕ → ℝ) (k : ℕ) (hk : T ≤ k) (x : ℝ) :
    bsCost T μ h b L k x = 0 := by
  rw [bsCost, dif_neg (by omega)]

theorem g69h2_bs_lt (T : ℕ) (μ : ℕ → Measure ℝ) (h b L : ℕ → ℝ) (k : ℕ) (hk : k < T) (x : ℝ) :
    bsCost T μ h b L k x = shadowU T μ h b L k (max x (L k)) := by
  rw [bsCost, dif_pos hk]; rfl

theorem g69h2_Lip_add {f g : ℝ → ℝ} {K K' : ℝ} (hf : g69h2_Lip f K) (hg : g69h2_Lip g K') :
    g69h2_Lip (fun x => f x + g x) (K + K') := by
  refine ⟨add_nonneg hf.1 hg.1, fun x x' => ?_⟩
  calc |f x + g x - (f x' + g x')| = |(f x - f x') + (g x - g x')| := by ring_nf
    _ ≤ |f x - f x'| + |g x - g x'| := abs_add_le _ _
    _ ≤ K * |x - x'| + K' * |x - x'| := add_le_add (hf.2 x x') (hg.2 x x')
    _ = (K + K') * |x - x'| := by ring

theorem g69h2_shadow_lip (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < b i)
    (L : ℕ → ℝ) (k : ℕ) {K : ℝ} (hK : g69h2_Lip (bsCost T μ h b L (k + 1)) K) :
    g69h2_Lip (shadowU T μ h b L k) (h k + b k + K) := by
  have e : shadowU T μ h b L k = fun y => (∫ d, g69h2_phi (h k) (b k) (y - d) ∂(μ k)) +
      ∫ d, bsCost T μ h b L (k + 1) (y - d) ∂(μ k) := by
    funext y; unfold shadowU; rw [g69h2_nv_eq]
  rw [e]
  exact g69h2_Lip_add (g69h2_int_lip (μ k) (hμ k) (g69h2_phi_lip _ _ (hh k) (hb k)))
    (g69h2_int_lip (μ k) (hμ k) hK)

theorem g69h2_bs_lip (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < b i)
    (L : ℕ → ℝ) : ∀ k, ∃ K, g69h2_Lip (bsCost T μ h b L k) K := by
  have : ∀ m k, T ≤ k + m → ∃ K, g69h2_Lip (bsCost T μ h b L k) K := by
    intro m
    induction m with
    | zero =>
      intro k hk
      refine ⟨0, le_rfl, fun x x' => ?_⟩
      rw [g69h2_bs_ge T μ h b L k (by omega), g69h2_bs_ge T μ h b L k (by omega)]; simp
    | succ m ih =>
      intro k hk
      by_cases hkT : k < T
      · obtain ⟨K, hK⟩ := ih (k + 1) (by omega)
        have hS := g69h2_shadow_lip T μ hμ h b hh hb L k hK
        refine ⟨h k + b k + K, hS.1, fun x x' => ?_⟩
        rw [g69h2_bs_lt T μ h b L k hkT, g69h2_bs_lt T μ h b L k hkT]
        exact (hS.2 _ _).trans (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ _) hS.1)
      · refine ⟨0, le_rfl, fun x x' => ?_⟩
        rw [g69h2_bs_ge T μ h b L k (by omega), g69h2_bs_ge T μ h b L k (by omega)]; simp
  exact fun k => this T k (by omega)

theorem g69h2_phi_nonneg (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (u : ℝ) : 0 ≤ g69h2_phi h b u := by
  unfold g69h2_phi
  have := le_max_right u 0; have := le_max_right (-u) 0
  positivity

theorem g69h2_bs_nonneg (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i)
    (hb : ∀ i, 0 < b i) (L : ℕ → ℝ) : ∀ k x, 0 ≤ bsCost T μ h b L k x := by
  have : ∀ m k, T ≤ k + m → ∀ x, 0 ≤ bsCost T μ h b L k x := by
    intro m
    induction m with
    | zero => intro k hk x; rw [g69h2_bs_ge T μ h b L k (by omega)]
    | succ m ih =>
      intro k hk x
      by_cases hkT : k < T
      · rw [g69h2_bs_lt T μ h b L k hkT]
        unfold shadowU
        rw [g69h2_nv_eq]
        exact add_nonneg (integral_nonneg fun d => g69h2_phi_nonneg _ _ (hh k) (hb k) _)
          (integral_nonneg fun d => ih (k + 1) (by omega) _)
      · rw [g69h2_bs_ge T μ h b L k (by omega)]
  exact fun k => this T k (by omega)
theorem g69h2_minAbove_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (r : ℝ)
    (hr : ∀ y, f r ≤ f y) :
    ConvexOn ℝ Set.univ (minAbove f) ∧
      (∀ x, x ≤ r → minAbove f x = f r) ∧
      (∀ x, r < x → minAbove f x = f x) := by
  have hmono : ∀ x y, r ≤ x → x ≤ y → f x ≤ f y := by
    intro x y hx hxy
    rcases eq_or_lt_of_le hxy with h | h
    · rw [h]
    rcases eq_or_lt_of_le hx with h' | h'
    · rw [← h']; exact hr y
    -- x = θ r + (1-θ) y
    have hθ : 0 < y - r := by linarith
    have := hf.2 (Set.mem_univ r) (Set.mem_univ y)
      (show (0:ℝ) ≤ (y - x) / (y - r) from div_nonneg (by linarith) hθ.le)
      (show (0:ℝ) ≤ (x - r) / (y - r) from div_nonneg (by linarith) hθ.le) (by field_simp [hθ.ne']; ring)
    have e : (y - x) / (y - r) * r + (x - r) / (y - r) * y = x := by
      field_simp [hθ.ne']; ring
    simp only [smul_eq_mul] at this
    rw [e] at this
    have h1 := hr y
    have : f x ≤ (y - x) / (y - r) * f y + (x - r) / (y - r) * f y := by
      have := mul_le_mul_of_nonneg_left h1 (div_nonneg (show (0:ℝ) ≤ y - x by linarith) hθ.le)
      linarith
    rw [← add_mul, show (y - x) / (y - r) + (x - r) / (y - r) = 1 by field_simp [hθ.ne']; ring, one_mul] at this
    exact this
  have hbdd : ∀ x : ℝ, BddBelow (Set.range fun y : ↥(Set.Ici x) => f y.1) :=
    fun x => ⟨f r, by rintro _ ⟨y, rfl⟩; exact hr y.1⟩
  have hw : ∀ x, minAbove f x = f (max x r) := by
    intro x
    unfold minAbove
    apply le_antisymm
    · exact ciInf_le (hbdd x) ⟨max x r, Set.mem_Ici.2 (le_max_left _ _)⟩
    · refine le_ciInf fun ⟨y, hy⟩ => ?_
      simp only
      rcases le_total x r with h | h
      · rw [max_eq_right h]; exact hr y
      · rw [max_eq_left h]; exact hmono x y h hy
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [hw, smul_eq_mul]
    have hm : max (a * x + b * y) r ≤ a * max x r + b * max y r := by
      apply max_le
      · nlinarith [le_max_left x r, le_max_left y r]
      · have := mul_le_mul_of_nonneg_left (le_max_right x r) ha
        have := mul_le_mul_of_nonneg_left (le_max_right y r) hb
        have : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
        linarith
    calc f (max (a * x + b * y) r) ≤ f (a * max x r + b * max y r) :=
          hmono _ _ (le_max_right _ _) hm
      _ ≤ a * f (max x r) + b * f (max y r) := by
          have := hf.2 (Set.mem_univ (max x r)) (Set.mem_univ (max y r)) ha hb hab
          simpa [smul_eq_mul] using this
  · intro x hx; rw [hw, max_eq_right hx]
  · intro x hx; rw [hw, max_eq_left hx.le]



theorem g69h2_mono_right (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (r : ℝ)
    (hr : ∀ y, f r ≤ f y) : ∀ x y, r ≤ x → x ≤ y → f x ≤ f y := by
  intro x y hx hxy
  have h1 := (g69h2_minAbove_convex f hf r hr)
  -- f x ≤ f y: use minAbove characterization
  rcases eq_or_lt_of_le hx with h' | h'
  · rw [← h']; exact hr y
  rcases eq_or_lt_of_le hxy with h'' | h''
  · rw [h'']
  have hθ : 0 < y - r := by linarith
  have := hf.2 (Set.mem_univ r) (Set.mem_univ y)
    (show (0:ℝ) ≤ (y - x) / (y - r) from div_nonneg (by linarith) hθ.le)
    (show (0:ℝ) ≤ (x - r) / (y - r) from div_nonneg (by linarith) hθ.le) (by field_simp [hθ.ne']; ring)
  have e : (y - x) / (y - r) * r + (x - r) / (y - r) * y = x := by
    field_simp [hθ.ne']; ring
  simp only [smul_eq_mul] at this
  rw [e] at this
  have h2 := hr y
  have h3 := mul_le_mul_of_nonneg_left h2 (div_nonneg (show (0:ℝ) ≤ y - x by linarith) hθ.le)
  have h4 : (y - x) / (y - r) + (x - r) / (y - r) = 1 := by field_simp [hθ.ne']; ring
  have h5 : (y - x) / (y - r) * f y + (x - r) / (y - r) * f y = f y := by
    rw [← add_mul, h4, one_mul]
  linarith

theorem g69h2_G_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (r L : ℝ)
    (hr : ∀ y, f r ≤ f y) (hrL : r ≤ L) : ConvexOn ℝ Set.univ (fun x => f (max x L)) := by
  have hmono := g69h2_mono_right f hf r hr
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hm : max (a * x + b * y) L ≤ a * max x L + b * max y L := by
    apply max_le
    · nlinarith [le_max_left x L, le_max_left y L]
    · have := mul_le_mul_of_nonneg_left (le_max_right x L) ha
      have := mul_le_mul_of_nonneg_left (le_max_right y L) hb
      have : a * L + b * L = L := by rw [← add_mul, hab, one_mul]
      linarith
  calc f (max (a * x + b * y) L) ≤ f (a * max x L + b * max y L) :=
        hmono _ _ (hrL.trans (le_max_right _ _)) hm
    _ ≤ a * f (max x L) + b * f (max y L) := by
        have := hf.2 (Set.mem_univ (max x L)) (Set.mem_univ (max y L)) ha hb hab
        simpa [smul_eq_mul] using this

theorem g69h2_smallest_min (f : ℝ → ℝ) (hf : Continuous f) (c C : ℝ) (hc : 0 < c)
    (hlow : ∀ y, c * |y| - C ≤ f y) : ∃ r, IsSmallestMinimizer f r := by
  have hlim : Filter.Tendsto f (Filter.cocompact ℝ) Filter.atTop := by
    have h1 : Filter.Tendsto (fun y : ℝ => c * |y| - C) (Filter.cocompact ℝ) Filter.atTop := by
      have := (tendsto_norm_cocompact_atTop (E := ℝ)).const_mul_atTop hc
      simp only [Real.norm_eq_abs] at this
      exact Filter.tendsto_atTop_add_const_right _ (-C) this
    exact Filter.tendsto_atTop_mono hlow h1
  obtain ⟨x0, hx0⟩ := hf.exists_forall_le hlim
  set S := {y | f y ≤ f x0}
  have hS : ∀ y, y ∈ S ↔ ∀ z, f y ≤ f z := fun y =>
    ⟨fun hy z => hy.trans (hx0 z), fun hy => hy x0⟩
  have hcl : IsClosed S := isClosed_le hf continuous_const
  have hne : S.Nonempty := ⟨x0, show f x0 ≤ f x0 from le_rfl⟩
  have hbdd : BddBelow S := by
    refine ⟨-((f x0 + C) / c), fun y hy => ?_⟩
    have h1 := hlow y
    have h2 : c * |y| ≤ f x0 + C := by have : f y ≤ f x0 := hy; linarith
    have h3 : |y| ≤ (f x0 + C) / c := by rw [le_div_iff₀ hc]; linarith
    have := neg_abs_le y
    linarith
  refine ⟨sInf S, (hS _).1 (hcl.csInf_mem hne hbdd), fun y hy => csInf_le hbdd ((hS y).2 hy)⟩

theorem g69h2_phi_ge (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (u : ℝ) :
    h * u ≤ g69h2_phi h b u ∧ -b * u ≤ g69h2_phi h b u := by
  unfold g69h2_phi
  have := le_max_left u 0; have := le_max_right u 0
  have := le_max_left (-u) 0; have := le_max_right (-u) 0
  constructor <;> nlinarith

theorem g69h2_nv_low (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (y : ℝ) :
    min h b * |y| - (|h * ∫ d, d ∂μ| + |b * ∫ d, d ∂μ|) ≤ ∫ d, g69h2_phi h b (y - d) ∂μ := by
  have hi := g69h2_int μ hμ (g69h2_phi_lip h b hh hb) y
  have hid : Integrable (fun d : ℝ => d) μ := hμ
  have e1 : ∫ d, h * (y - d) ∂μ = h * y - h * ∫ d, d ∂μ := by
    rw [integral_const_mul, integral_sub (integrable_const _) hid, integral_const]; simp; ring
  have e2 : ∫ d, -b * (y - d) ∂μ = -b * y + b * ∫ d, d ∂μ := by
    rw [integral_const_mul, integral_sub (integrable_const _) hid, integral_const]; simp; ring
  have i1 : h * y - h * ∫ d, d ∂μ ≤ ∫ d, g69h2_phi h b (y - d) ∂μ := by
    rw [← e1]
    exact integral_mono ((integrable_const _).sub hid |>.const_mul h) hi
      fun d => (g69h2_phi_ge h b hh hb _).1
  have i2 : -b * y + b * ∫ d, d ∂μ ≤ ∫ d, g69h2_phi h b (y - d) ∂μ := by
    rw [← e2]
    exact integral_mono ((integrable_const _).sub hid |>.const_mul (-b)) hi
      fun d => (g69h2_phi_ge h b hh hb _).2
  set E := ∫ d, d ∂μ
  have a1 := le_abs_self (h * E); have a2 := neg_abs_le (h * E)
  have a3 := le_abs_self (b * E); have a4 := neg_abs_le (b * E)
  have m1 := min_le_left h b; have m2 := min_le_right h b
  have m0 : 0 < min h b := lt_min hh hb
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; nlinarith [mul_le_mul_of_nonneg_right m1 hy]
  · rw [abs_of_nonpos hy]; nlinarith [mul_le_mul_of_nonneg_right m2 (neg_nonneg.mpr hy)]

theorem g69h2_minAbove_lip (f : ℝ → ℝ) {K : ℝ} (hf : g69h2_Lip f K) (h0 : ∀ y, 0 ≤ f y) :
    g69h2_Lip (minAbove f) K := by
  have hbdd : ∀ x : ℝ, BddBelow (Set.range fun y : ↥(Set.Ici x) => f y.1) :=
    fun x => ⟨0, by rintro _ ⟨y, rfl⟩; exact h0 y.1⟩
  have hle : ∀ x y, x ≤ y → minAbove f y ≤ f y := fun x y _ =>
    ciInf_le (hbdd y) ⟨y, Set.mem_Ici.2 le_rfl⟩
  have key : ∀ x x', x ≤ x' → minAbove f x ≤ minAbove f x' ∧
      minAbove f x' ≤ minAbove f x + K * (x' - x) := by
    intro x x' hxx'
    constructor
    · unfold minAbove
      refine le_ciInf fun ⟨y, hy⟩ => ?_
      exact ciInf_le (hbdd x) ⟨y, Set.mem_Ici.2 (hxx'.trans hy)⟩
    · have : minAbove f x' - K * (x' - x) ≤ minAbove f x := by
        unfold minAbove
        refine le_ciInf fun ⟨y, hy⟩ => ?_
        have h1 : (⨅ z : ↥(Set.Ici x'), f z.1) ≤ f (y + (x' - x)) :=
          ciInf_le (hbdd x') ⟨y + (x' - x), Set.mem_Ici.2 (by simp at hy ⊢; linarith)⟩
        have h2 := hf.2 (y + (x' - x)) y
        rw [show y + (x' - x) - y = x' - x by ring, abs_of_nonneg (show (0:ℝ) ≤ x' - x by linarith)] at h2
        have h3 := le_abs_self (f (y + (x' - x)) - f y)
        simp only
        linarith
      linarith
  refine ⟨hf.1, fun x x' => ?_⟩
  rcases le_total x x' with hx | hx
  · obtain ⟨k1, k2⟩ := key x x' hx
    rw [abs_le]; rw [abs_of_nonpos (by linarith)]; constructor <;> nlinarith [hf.1]
  · obtain ⟨k1, k2⟩ := key x' x hx
    rw [abs_le]; rw [abs_of_nonneg (by linarith)]; constructor <;> nlinarith [hf.1]

theorem g69h2_V_ge (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (i : ℕ) (hi : T ≤ i) (x : ℝ) :
    optV T μ h b i x = 0 := by
  rw [optV, dif_neg (by omega)]

theorem g69h2_V_lt (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (i : ℕ) (hi : i < T) (x : ℝ) :
    optV T μ h b i x = minAbove (optU T μ h b i) x := by
  rw [optV, dif_pos hi]; rfl

theorem g69h2_V_props (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < b i) :
    ∀ k, (∃ K, g69h2_Lip (optV T μ h b k) K) ∧ ∀ x, 0 ≤ optV T μ h b k x := by
  have : ∀ m k, T ≤ k + m → (∃ K, g69h2_Lip (optV T μ h b k) K) ∧ ∀ x, 0 ≤ optV T μ h b k x := by
    intro m
    induction m with
    | zero =>
      intro k hk
      refine ⟨⟨0, le_rfl, fun x x' => ?_⟩, fun x => ?_⟩
      · rw [g69h2_V_ge T μ h b k (by omega), g69h2_V_ge T μ h b k (by omega)]; simp
      · rw [g69h2_V_ge T μ h b k (by omega)]
    | succ m ih =>
      intro k hk
      by_cases hkT : k < T
      · obtain ⟨⟨K, hK⟩, h0⟩ := ih (k + 1) (by omega)
        have eU : optU T μ h b k = fun y => (∫ d, g69h2_phi (h k) (b k) (y - d) ∂(μ k)) +
            ∫ d, optV T μ h b (k + 1) (y - d) ∂(μ k) := by
          funext y; unfold optU; rw [g69h2_nv_eq]
        have hUl : g69h2_Lip (optU T μ h b k) (h k + b k + K) := by
          rw [eU]
          exact g69h2_Lip_add (g69h2_int_lip (μ k) (hμ k) (g69h2_phi_lip _ _ (hh k) (hb k)))
            (g69h2_int_lip (μ k) (hμ k) hK)
        have hU0 : ∀ y, 0 ≤ optU T μ h b k y := by
          intro y; rw [eU]
          exact add_nonneg (integral_nonneg fun d => g69h2_phi_nonneg _ _ (hh k) (hb k) _)
            (integral_nonneg fun d => h0 _)
        have e : optV T μ h b k = minAbove (optU T μ h b k) :=
          funext fun x => g69h2_V_lt T μ h b k hkT x
        refine ⟨⟨_, e ▸ g69h2_minAbove_lip _ hUl hU0⟩, fun x => ?_⟩
        rw [e]; unfold minAbove
        exact le_ciInf fun y => hU0 _
      · refine ⟨⟨0, le_rfl, fun x x' => ?_⟩, fun x => ?_⟩
        · rw [g69h2_V_ge T μ h b k (by omega), g69h2_V_ge T μ h b k (by omega)]; simp
        · rw [g69h2_V_ge T μ h b k (by omega)]
  exact fun k => this T k (by omega)

theorem g69h2_U_nonneg (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < b i)
    (k : ℕ) (y : ℝ) : 0 ≤ optU T μ h b k y := by
  unfold optU; rw [g69h2_nv_eq]
  exact add_nonneg (integral_nonneg fun d => g69h2_phi_nonneg _ _ (hh k) (hb k) _)
    (integral_nonneg fun d => (g69h2_V_props T μ hμ h b hh hb (k + 1)).2 _)

theorem g69h2_shadow_nonneg (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (hh : ∀ i, 0 < h i)
    (hb : ∀ i, 0 < b i) (L : ℕ → ℝ) (k : ℕ) (y : ℝ) : 0 ≤ shadowU T μ h b L k y := by
  unfold shadowU; rw [g69h2_nv_eq]
  exact add_nonneg (integral_nonneg fun d => g69h2_phi_nonneg _ _ (hh k) (hb k) _)
    (integral_nonneg fun d => g69h2_bs_nonneg T μ h b hh hb L _ _)

theorem g69h2_prod_ge_one (ε : ℕ → ℝ) (T : ℕ) (hε : ∀ t, t < T → 0 ≤ ε t) (s : ℕ) :
    1 ≤ ∏ j ∈ Finset.Ico s T, (1 + ε j) := by
  calc (1:ℝ) = ∏ j ∈ Finset.Ico s T, (1:ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun j hj => by
        have := hε j (Finset.mem_Ico.1 hj).2; linarith

theorem solution (T : ℕ) (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, Integrable id (μ i)) (h b : ℕ → ℝ)
    (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < b i) (L : ℕ → ℝ) (t : ℕ) (ht : t + 1 < T)
    (hL : IsUpperBaseStock T μ h b L (t + 1))
    (R : ℕ → ℝ) (hR : ∀ j, t ≤ j → j < T → IsSmallestMinimizer (optU T μ h b j) (R j))
    (Rbar : ℝ) (hRbar : IsSmallestMinimizer (shadowU T μ h b L t) Rbar)
    (β : ℕ → ℝ) (hβ1 : ∀ j ∈ Finset.Ioo t T, 1 ≤ β j)
    (hβ : ∀ j ∈ Finset.Ioo t T, shadowU T μ h b L j (L j) ≤ β j * optU T μ h b j (R j)) :
    shadowU T μ h b L t Rbar ≤ (⨆ j : Finset.Ioo t T, β j) * optU T μ h b t (R t) := by
  set B := ⨆ j : Finset.Ioo t T, β j with hB
  have hbdd : BddAbove (Set.range fun j : Finset.Ioo t T => β j) := (Set.finite_range _).bddAbove
  have hjB : ∀ j ∈ Finset.Ioo t T, β j ≤ B := fun j hj => le_ciSup hbdd ⟨j, hj⟩
  have hmem : t + 1 ∈ Finset.Ioo t T := Finset.mem_Ioo.2 ⟨by omega, ht⟩
  have hB1 : 1 ≤ B := (hβ1 _ hmem).trans (hjB _ hmem)
  have hBpos : 0 < B := lt_of_lt_of_le one_pos hB1
  have hbase : ∀ s, s + 1 = T → ∀ y, shadowU T μ h b L s y ≤ B * optU T μ h b s y := by
    intro s hs y
    have e : shadowU T μ h b L s y = optU T μ h b s y := by
      unfold shadowU optU
      simp [g69h2_bs_ge T μ h b L (s + 1) (by omega), g69h2_V_ge T μ h b (s + 1) (by omega)]
    rw [e]
    have := g69h2_U_nonneg T μ hμ h b hh hb s y
    nlinarith
  have Q : ∀ m s, T ≤ s + 1 + m → t ≤ s → s < T →
      ∀ y, shadowU T μ h b L s y ≤ B * optU T μ h b s y := by
    intro m
    induction m with
    | zero => intro s hs _ hsT; exact hbase s (by omega)
    | succ m ih =>
      intro s hs hts hsT
      by_cases hs1 : s + 1 < T
      · have IH := ih (s + 1) (by omega) (by omega) hs1
        obtain ⟨r, ⟨hc, hsm⟩, hrL⟩ := hL (s + 1) (by omega) hs1
        have hjI : s + 1 ∈ Finset.Ioo t T := Finset.mem_Ioo.2 ⟨by omega, hs1⟩
        have hg := hβ (s + 1) hjI
        have hgB := hjB (s + 1) hjI
        have hRs := hR (s + 1) (by omega) hs1
        have hpt : ∀ x, bsCost T μ h b L (s + 1) x ≤ B * optV T μ h b (s + 1) x := by
          intro x
          have claim : ∀ z, x ≤ z → bsCost T μ h b L (s + 1) x ≤ B * optU T μ h b (s + 1) z := by
            intro z hz
            rw [g69h2_bs_lt T μ h b L (s + 1) hs1]
            rcases le_total x (L (s + 1)) with hxL | hxL
            · rw [max_eq_right hxL]
              have h0 := g69h2_U_nonneg T μ hμ h b hh hb (s + 1) (R (s + 1))
              calc _ ≤ β (s + 1) * optU T μ h b (s + 1) (R (s + 1)) := hg
                _ ≤ B * optU T μ h b (s + 1) (R (s + 1)) := mul_le_mul_of_nonneg_right hgB h0
                _ ≤ B * optU T μ h b (s + 1) z := mul_le_mul_of_nonneg_left (hRs.1 z) hBpos.le
            · rw [max_eq_left hxL]
              exact (g69h2_mono_right _ hc r hsm.1 x z (hrL.trans hxL) hz).trans (IH z)
          rw [g69h2_V_lt T μ h b (s + 1) hs1]
          have : bsCost T μ h b L (s + 1) x / B ≤ minAbove (optU T μ h b (s + 1)) x := by
            unfold minAbove
            refine le_ciInf fun ⟨z, hz⟩ => ?_
            rw [div_le_iff₀ hBpos, mul_comm]
            exact claim z hz
          rw [div_le_iff₀ hBpos] at this
          linarith
        intro y
        obtain ⟨K1, hK1⟩ := g69h2_bs_lip T μ hμ h b hh hb L (s + 1)
        obtain ⟨⟨K2, hK2⟩, hV0⟩ := g69h2_V_props T μ hμ h b hh hb (s + 1)
        have i1 := g69h2_int (μ s) (hμ s) hK1 y
        have i2 := g69h2_int (μ s) (hμ s) hK2 y
        have hint : ∫ d, bsCost T μ h b L (s + 1) (y - d) ∂(μ s) ≤
            B * ∫ d, optV T μ h b (s + 1) (y - d) ∂(μ s) := by
          rw [← integral_const_mul]
          exact integral_mono i1 (i2.const_mul _) fun d => hpt _
        have hnv : 0 ≤ nvCost (μ s) (h s) (b s) y := by
          rw [g69h2_nv_eq]; exact integral_nonneg fun d => g69h2_phi_nonneg _ _ (hh s) (hb s) _
        unfold shadowU optU
        nlinarith
      · exact hbase s (by omega)
  have hQ := Q T t (by omega) le_rfl (by omega) (R t)
  exact (hRbar.1 (R t)).trans hQ
