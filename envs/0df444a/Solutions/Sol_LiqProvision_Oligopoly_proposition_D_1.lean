-- Prove2me | solution 1 for LiqProvision.Oligopoly.proposition_D_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:58:55.785405+00:00
-- url     : https://prove2.me/submissions/ef104a2a-50a1-4bf3-a4f0-dd696bc4f5dd

import Mathlib

open Set MeasureTheory Filter Topology

namespace LiqD1Aux

/-- four-point inequality for concave functions -/
theorem four_point {φ : ℝ → ℝ} (hc : ConcaveOn ℝ univ φ) {u x d : ℝ} (hux : u ≤ x)
    (hd : 0 ≤ d) : φ (x + d) + φ u ≤ φ x + φ (u + d) := by
  rcases hux.lt_or_eq with hux | rfl
  · rcases hd.lt_or_eq with hd | rfl
    · have hL : 0 < x + d - u := by linarith
      set w := d / (x + d - u) with hw
      have hw0 : 0 < w := div_pos hd hL
      have hw1 : w < 1 := by rw [hw, div_lt_one hL]; linarith
      have h1 := hc.2 (mem_univ u) (mem_univ (x + d)) hw0.le (by linarith : 0 ≤ 1 - w)
        (by ring)
      have h2 := hc.2 (mem_univ u) (mem_univ (x + d)) (by linarith : 0 ≤ 1 - w) hw0.le
        (by ring)
      simp only [smul_eq_mul] at h1 h2
      have e1 : w * u + (1 - w) * (x + d) = x := by rw [hw]; field_simp; ring
      have e2 : (1 - w) * u + w * (x + d) = u + d := by rw [hw]; field_simp; ring
      rw [e1] at h1; rw [e2] at h2
      linarith
    · simp only [add_zero]; linarith
  · linarith

theorem Iic_shift (g : ℝ → ℝ) (x d : ℝ) :
    ∫ t in Iic (x + d), g t = ∫ u in Iic x, g (u + d) := by
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t => (Iic (x + d)).indicator g t) d
  rw [← this]
  congr 1; funext u
  by_cases h : u ≤ x
  · rw [indicator_of_mem (by simp; linarith), indicator_of_mem (by simpa using h)]
  · rw [indicator_of_notMem (by simp; linarith), indicator_of_notMem (by simpa using h)]

theorem Ioi_shift (g : ℝ → ℝ) (x d : ℝ) :
    ∫ t in Ioi (x + d), g t = ∫ u in Ioi x, g (u + d) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t => (Ioi (x + d)).indicator g t) d
  rw [← this]
  congr 1; funext u
  by_cases h : x < u
  · rw [indicator_of_mem (by simp; linarith), indicator_of_mem (by simpa using h)]
  · rw [indicator_of_notMem (by simp; linarith), indicator_of_notMem (by simpa using h)]

/-- an integrable function cannot be bounded below by a positive constant on a half-line -/
theorem not_bdd_Ici {f : ℝ → ℝ} (hint : Integrable f) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, 0 ≤ x → c ≤ f x) : False := by
  have hI : IntegrableOn (fun _ => c) (Ici (0:ℝ)) := by
    refine Integrable.mono' hint.integrableOn aestronglyMeasurable_const ?_
    refine (ae_restrict_mem measurableSet_Ici).mono fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_pos hc]; exact h x hx
  rw [integrableOn_const_iff] at hI
  rcases hI with h1 | h1
  · simp at h1; linarith
  · simp at h1

theorem not_bdd_Iic {f : ℝ → ℝ} (hint : Integrable f) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≤ 0 → c ≤ f x) : False := by
  have hI : IntegrableOn (fun _ => c) (Iic (0:ℝ)) := by
    refine Integrable.mono' hint.integrableOn aestronglyMeasurable_const ?_
    refine (ae_restrict_mem measurableSet_Iic).mono fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_pos hc]; exact h x hx
  rw [integrableOn_const_iff] at hI
  rcases hI with h1 | h1
  · simp at h1; linarith
  · simp at h1

end LiqD1Aux

open LiqD1Aux in
theorem solution (f : ℝ → ℝ) (hpos : ∀ x, 0 < f x)
    (hint : MeasureTheory.Integrable f) (hmass : ∫ x, f x = 1)
    (hlc : ConcaveOn ℝ Set.univ (fun x => Real.log (f x))) :
    (ConcaveOn ℝ Set.univ (fun x => Real.log (∫ y in Set.Iic x, f y)) ∧
      ConcaveOn ℝ Set.univ (fun x => Real.log (∫ y in Set.Ioi x, f y))) ∧
    (∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ x, f x ≤ C * Real.exp (-ε * |x|)) ∧
    (∃ f' : ℝ → ℝ, (∀ x, HasDerivWithinAt f (f' x) (Set.Ici x) x) ∧
      ∃ xs : ℝ, (∀ x < xs, 0 ≤ f' x) ∧ ∀ x, xs ≤ x → f' x ≤ 0) := by
  set φ : ℝ → ℝ := fun x => Real.log (f x) with hφ
  have hfφ : ∀ x, f x = Real.exp (φ x) := fun x => (Real.exp_log (hpos x)).symm
  have hφc : Continuous φ := by
    rw [← continuousOn_univ]
    exact hlc.continuousOn isOpen_univ
  have hfc : Continuous f := by
    have : f = fun x => Real.exp (φ x) := funext hfφ
    rw [this]; exact hφc.rexp
  -- secants
  obtain ⟨a, b, hab, hφab⟩ : ∃ a b, a < b ∧ φ b < φ a := by
    by_contra hcon
    push Not at hcon
    apply not_bdd_Ici hint (hpos 0)
    intro x hx
    rcases hx.lt_or_eq with hx | rfl
    · rw [hfφ, hfφ]; exact Real.exp_le_exp.2 (hcon 0 x hx)
    · exact le_rfl
  obtain ⟨a', b', hab', hφab'⟩ : ∃ a b, a < b ∧ φ a < φ b := by
    by_contra hcon
    push Not at hcon
    apply not_bdd_Iic hint (hpos 0)
    intro x hx
    rcases hx.lt_or_eq with hx | rfl
    · rw [hfφ, hfφ]; exact Real.exp_le_exp.2 (hcon x 0 hx)
    · exact le_rfl
  set s := (φ b - φ a) / (b - a) with hs
  set s' := (φ b' - φ a') / (b' - a') with hs'
  have hs0 : s < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hs'0 : 0 < s' := div_pos (by linarith) (by linarith)
  -- right tail: φ x ≤ φ b + s (x - b) for x ≥ b
  have hright : ∀ x, b ≤ x → φ x ≤ φ b + s * (x - b) := by
    intro x hx
    rcases hx.lt_or_eq with hx | rfl
    · have := hlc.slope_anti_adjacent (mem_univ a) (mem_univ x) hab hx
      rw [div_le_iff₀ (by linarith)] at this
      linarith
    · simp
  have hleft : ∀ x, x ≤ a' → φ x ≤ φ a' - s' * (a' - x) := by
    intro x hx
    rcases hx.lt_or_eq with hx | rfl
    · have := hlc.slope_anti_adjacent (mem_univ x) (mem_univ b') hx hab'
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    · simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  -- (a) log F concave
  · set F : ℝ → ℝ := fun x => ∫ y in Iic x, f y with hF
    have hFpos : ∀ x, 0 < F x := by
      intro x
      rw [hF]; simp only
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun y => (hpos y).le) hint.integrableOn]
      have : Function.support f = univ := by
        ext y; simp [(hpos y).ne']
      rw [this, univ_inter, Real.volume_Iic]; simp
    have hFeq : ∀ x, F x = F 0 + ∫ t in (0:ℝ)..x, f t := by
      intro x
      rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
      simp only [hF]; ring
    have hFd : ∀ x, HasDerivAt F (f x) x := by
      intro x
      have h := ((hfc.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add (F 0)
      exact h.congr_of_eventuallyEq (Eventually.of_forall fun y => hFeq y)
    have hGd : ∀ x, HasDerivAt (fun x => Real.log (F x)) (f x / F x) x :=
      fun x => (hFd x).log (hFpos x).ne'
    have hderiv : deriv (fun x => Real.log (F x)) = fun x => f x / F x :=
      funext fun x => (hGd x).deriv
    apply AntitoneOn.concaveOn_of_deriv convex_univ
    · exact fun x _ => (hGd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hGd x).differentiableAt.differentiableWithinAt
    · rw [hderiv, interior_univ]
      intro x _ y _ hxy
      simp only
      rcases hxy.lt_or_eq with hxy | rfl
      · set d := y - x
        have hy : y = x + d := by simp [d]
        rw [div_le_div_iff₀ (hFpos y) (hFpos x)]
        have hFy : F y = ∫ u in Iic x, f (u + d) := by
          simp only [hF]; rw [hy]; exact Iic_shift f x d
        have hint2 : Integrable (fun u => f (u + d)) := hint.comp_add_right d
        rw [hFy]
        simp only [hF]
        rw [← integral_const_mul, ← integral_const_mul]
        apply setIntegral_mono_on (hint.integrableOn.const_mul _)
          (hint2.integrableOn.const_mul _) measurableSet_Iic
        intro u hu
        rw [hfφ y, hfφ u, hfφ x, hfφ (u + d), ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have := four_point hlc (u := u) (x := x) (d := d) hu (by simp [d]; linarith)
        rw [← hy] at this
        linarith
      · exact le_rfl
  -- (a) log F̄ concave
  · set F : ℝ → ℝ := fun x => ∫ y in Ioi x, f y with hF
    have hFpos : ∀ x, 0 < F x := by
      intro x
      rw [hF]; simp only
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun y => (hpos y).le) hint.integrableOn]
      have : Function.support f = univ := by
        ext y; simp [(hpos y).ne']
      rw [this, univ_inter, Real.volume_Ioi]; simp
    have hFeq : ∀ x, F x = F 0 - ∫ t in (0:ℝ)..x, f t := by
      intro x
      rw [← intervalIntegral.integral_Ioi_sub_Ioi' hint.integrableOn hint.integrableOn]
      simp only [hF]; ring
    have hFd : ∀ x, HasDerivAt F (-f x) x := by
      intro x
      have h := ((hfc.integral_hasStrictDerivAt 0 x).hasDerivAt).const_sub (F 0)
      exact h.congr_of_eventuallyEq (Eventually.of_forall fun y => hFeq y)
    have hGd : ∀ x, HasDerivAt (fun x => Real.log (F x)) (-f x / F x) x :=
      fun x => (hFd x).log (hFpos x).ne'
    have hderiv : deriv (fun x => Real.log (F x)) = fun x => -f x / F x :=
      funext fun x => (hGd x).deriv
    apply AntitoneOn.concaveOn_of_deriv convex_univ
    · exact fun x _ => (hGd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hGd x).differentiableAt.differentiableWithinAt
    · rw [hderiv, interior_univ]
      intro x _ y _ hxy
      simp only
      rcases hxy.lt_or_eq with hxy | rfl
      · set d := y - x
        have hy : y = x + d := by simp [d]
        rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (hFpos x) (hFpos y)]
        have hFy : F y = ∫ u in Ioi x, f (u + d) := by
          simp only [hF]; rw [hy]; exact Ioi_shift f x d
        have hint2 : Integrable (fun u => f (u + d)) := hint.comp_add_right d
        rw [hFy]
        simp only [hF]
        rw [← integral_const_mul, ← integral_const_mul]
        apply setIntegral_mono_on (hint2.integrableOn.const_mul _)
          (hint.integrableOn.const_mul _) measurableSet_Ioi
        intro u hu
        rw [hfφ y, hfφ u, hfφ x, hfφ (u + d), ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have := four_point hlc (u := x) (x := u) (d := d) (le_of_lt hu) (by simp [d]; linarith)
        rw [← hy] at this
        linarith
      · exact le_rfl
  -- (b) exponential tails
  · set lo := min a' 0
    set hi := max b 0
    obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn
      hφc.continuousOn
    set ε := min (-s) s' with hε
    have hε0 : 0 < ε := lt_min (by linarith) hs'0
    have hεs : ε ≤ -s := min_le_left _ _
    have hεs' : ε ≤ s' := min_le_right _ _
    set K₀ := |φ b - s * b| + |φ a' - s' * a'| + |M₀| + ε * (|a'| + |b|) with hK₀
    refine ⟨Real.exp K₀, ε, Real.exp_pos _, hε0, fun x => ?_⟩
    rw [hfφ x, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have k1 := le_abs_self (φ b - s * b)
    have k2 := le_abs_self (φ a' - s' * a')
    have k3 := abs_nonneg (φ b - s * b)
    have k4 := abs_nonneg (φ a' - s' * a')
    have k5 := abs_nonneg M₀
    have k6 : 0 ≤ ε * (|a'| + |b|) := by positivity
    by_cases hx1 : hi ≤ x
    · have hxb : b ≤ x := (le_max_left _ _).trans hx1
      have hx0 : 0 ≤ x := (le_max_right _ _).trans hx1
      rw [abs_of_nonneg hx0]
      have := hright x hxb
      have : s * x ≤ -ε * x := mul_le_mul_of_nonneg_right (by linarith) hx0
      nlinarith
    by_cases hx2 : x ≤ lo
    · have hxa : x ≤ a' := hx2.trans (min_le_left _ _)
      have hx0 : x ≤ 0 := hx2.trans (min_le_right _ _)
      rw [abs_of_nonpos hx0]
      have := hleft x hxa
      have : s' * x ≤ ε * x := mul_le_mul_of_nonpos_right hεs' hx0
      nlinarith
    push Not at hx1 hx2
    have hb := hM₀ x ⟨hx2.le, hx1.le⟩
    rw [Real.norm_eq_abs] at hb
    have hφx : φ x ≤ |M₀| := (le_abs_self _).trans (hb.trans (le_abs_self _))
    have habs : |x| ≤ |a'| + |b| := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
        have : x < max b 0 := hx1
        rcases le_total b 0 with hb0 | hb0
        · rw [max_eq_right hb0] at this; linarith [abs_nonneg a', abs_nonneg b]
        · rw [max_eq_left hb0] at this; linarith [abs_nonneg a', le_abs_self b]
      · rw [abs_of_nonpos h]
        have : min a' 0 < x := hx2
        rcases le_total a' 0 with ha0 | ha0
        · rw [min_eq_left ha0] at this; linarith [neg_abs_le a', abs_nonneg b]
        · rw [min_eq_right ha0] at this; linarith [abs_nonneg a', abs_nonneg b]
    have : ε * |x| ≤ ε * (|a'| + |b|) := mul_le_mul_of_nonneg_left habs hε0.le
    nlinarith
  -- (c) right derivative and unimodality
  · set g : ℝ → ℝ := fun x => -φ x with hg
    have hgc : ConvexOn ℝ univ g := hlc.neg
    set ψ : ℝ → ℝ := fun x => -derivWithin g (Ioi x) x with hψ
    have hψd : ∀ x, HasDerivWithinAt φ (ψ x) (Ioi x) x := by
      intro x
      have h := (hgc.hasDerivWithinAt_rightDeriv_of_mem_interior
        (by simp : x ∈ interior (univ : Set ℝ))).neg
      have e : (-g) = φ := by funext y; simp [hg]
      rw [e] at h; exact h
    have hψanti : Antitone ψ := by
      intro x y hxy
      have := hgc.monotoneOn_rightDeriv (by simp : x ∈ interior (univ : Set ℝ))
        (by simp : y ∈ interior (univ : Set ℝ)) hxy
      simp only [hψ]; linarith
    have hfd : ∀ x, HasDerivWithinAt f (f x * ψ x) (Ici x) x := by
      intro x
      have h := (hψd x).exp
      have e : (fun y => Real.exp (φ y)) = f := by funext y; rw [hfφ]
      rw [e, ← hfφ] at h
      exact hasDerivWithinAt_Ioi_iff_Ici.1 h
    -- slopes
    have hψ_le : ∀ x y, x < y → ψ y ≤ (φ y - φ x) / (y - x) := by
      intro x y hxy
      have ht := (hasDerivWithinAt_iff_tendsto_slope.1 (hψd y))
      have hset : Ioi y \ {y} = Ioi y := by ext z; simp
      rw [hset] at ht
      apply le_of_tendsto ht
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [slope_def_field]
      exact hlc.slope_anti_adjacent (mem_univ x) (mem_univ z) hxy hz
    have hψ_ge : ∀ x y, x < y → (φ y - φ x) / (y - x) ≤ ψ x := by
      intro x y hxy
      have := hlc.slope_le_rightDeriv (mem_univ x) (mem_univ y) hxy (hψd x).differentiableWithinAt
      rw [slope_def_field] at this
      have e : derivWithin φ (Ioi x) x = ψ x :=
        (hψd x).derivWithin (uniqueDiffWithinAt_Ioi x)
      rw [e] at this; exact this
    set A := {x | ψ x ≤ 0} with hA
    have hbA : b ∈ A := by
      show ψ b ≤ 0
      have := hψ_le a b hab
      have : (φ b - φ a) / (b - a) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
      linarith
    have hAbdd : BddBelow A := by
      refine ⟨a', fun x hx => ?_⟩
      by_contra hlt
      push Not at hlt
      have h1 := hψ_ge x a' hlt
      have h2 := hlc.slope_anti_adjacent (mem_univ x) (mem_univ b') hlt hab'
      have h3 : 0 < (φ b' - φ a') / (b' - a') := hs'0
      have : (0:ℝ) < ψ x := by linarith
      exact absurd (show ψ x ≤ 0 from hx) (not_le.2 this)
    set xs := sInf A with hxs
    refine ⟨fun x => f x * ψ x, hfd, xs, ?_, ?_⟩
    · intro x hx
      have : x ∉ A := notMem_of_lt_csInf hx hAbdd
      have hψx : 0 < ψ x := by simpa [hA] using this
      exact mul_nonneg (hpos x).le hψx.le
    · intro x hx
      apply mul_nonpos_of_nonneg_of_nonpos (hpos x).le
      rcases hx.lt_or_eq with hx | rfl
      · obtain ⟨c, hcA, hc⟩ := exists_lt_of_csInf_lt ⟨b, hbA⟩ hx
        exact (hψanti hc.le).trans hcA
      · -- ψ xs ≤ 0
        have hmono : ∀ z, xs < z → φ z ≤ φ xs := by
          intro z hz
          have hlim : Tendsto φ (𝓝[>] xs) (𝓝 (φ xs)) := hφc.continuousAt.continuousWithinAt
          apply ge_of_tendsto hlim
          filter_upwards [Ioo_mem_nhdsGT hz] with t ht
          obtain ⟨c, hcA, hc⟩ := exists_lt_of_csInf_lt ⟨b, hbA⟩ ht.1
          have hψt : ψ t ≤ 0 := (hψanti hc.le).trans hcA
          have := hψ_ge t z ht.2
          rw [div_le_iff₀ (by linarith [ht.2])] at this
          nlinarith [ht.2]
        have ht := (hasDerivWithinAt_iff_tendsto_slope.1 (hψd xs))
        have hset : Ioi xs \ {xs} = Ioi xs := by ext z; simp
        rw [hset] at ht
        apply le_of_tendsto ht
        filter_upwards [self_mem_nhdsWithin] with z hz
        rw [slope_def_field]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith [hmono z hz]) (by linarith [mem_Ioi.1 hz])
