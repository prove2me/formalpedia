-- Prove2me | solution 1 for K24.Global.metric_admissible_positive_holder_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:45:11.08631+00:00
-- url     : https://prove2.me/submissions/6264f9d1-206f-425d-a504-c04127e91fd6

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Matrix.Norms.Elementwise

namespace K24.Global.PositiveNeighborhoodProof

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem derivative_le_holder (k j : ℕ) (α : ℝ≥0) (s : Set E) (f : E → V)
    (hj : j ≤ k) : derivativeENorm j s f ≤ coordinateHolderENorm k α s f := by
  exact (Finset.single_le_sum (f := fun i => derivativeENorm i s f)
    (fun _ _ => zero_le) (Finset.mem_range.mpr (show j < k + 1 by omega))).trans le_self_add

theorem value_le_holder (k : ℕ) (α : ℝ≥0) (s : Set E) (f : E → V)
    (x : E) (hx : x ∈ s) : (‖f x‖₊ : ℝ≥0∞) ≤ coordinateHolderENorm k α s f := by
  have h := (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ 0 f s y‖₊ : ℝ≥0∞)) ⟨x, hx⟩).trans
    (derivative_le_holder k 0 α s f (Nat.zero_le _))
  have heq : ‖iteratedFDerivWithin ℝ 0 f s x‖₊ = ‖f x‖₊ :=
    Subtype.ext (norm_iteratedFDerivWithin_zero)
  simpa only [heq] using h

theorem derivative_mono (j : ℕ) {s t : Set E} (hs : IsOpen s) (ht : IsOpen t)
    (hst : s ⊆ t) (f : E → V) : derivativeENorm j s f ≤ derivativeENorm j t f := by
  apply iSup_le
  intro x
  have h := le_iSup (fun y : t => (‖iteratedFDerivWithin ℝ j f t y‖₊ : ℝ≥0∞)) ⟨x, hst x.property⟩
  change (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞) ≤ ⨆ y : t, (‖iteratedFDerivWithin ℝ j f t y‖₊ : ℝ≥0∞)
  simpa only [iteratedFDerivWithin_of_isOpen j hs x.property,
    iteratedFDerivWithin_of_isOpen j ht (hst x.property)] using h

theorem holder_mono_domain (k : ℕ) (α : ℝ≥0) {s t : Set E} (hs : IsOpen s)
    (ht : IsOpen t) (hst : s ⊆ t) (f : E → V) :
    coordinateHolderENorm k α s f ≤ coordinateHolderENorm k α t f := by
  apply add_le_add
  · exact Finset.sum_le_sum fun j _ => derivative_mono j hs ht hst f
  · by_cases hfin : eHolderNorm α (fun y : t => iteratedFDerivWithin ℝ k f t y) = ⊤
    · simp [hfin]
    have hh := (eHolderNorm_ne_top.mp hfin).holderWith
    have hi : LipschitzWith 1 (fun x : s => (⟨x, hst x.property⟩ : t)) := by
      intro x y
      change edist (x : E) (y : E) ≤ (1 : ℝ≥0∞) * edist (x : E) (y : E)
      simp
    have hh' := hh.comp hi.holderWith
    simp only [mul_one, NNReal.one_rpow] at hh'
    have heq : (fun x : s => iteratedFDerivWithin ℝ k f s x) =
        (fun y : t => iteratedFDerivWithin ℝ k f t y) ∘ (fun x : s => (⟨x, hst x.property⟩ : t)) := by
      funext x
      simp only [Function.comp_apply, iteratedFDerivWithin_of_isOpen k hs x.property,
        iteratedFDerivWithin_of_isOpen k ht (hst x.property)]
    rw [heq]
    exact hh'.eHolderNorm_le.trans_eq ((eHolderNorm_ne_top.mp hfin).coe_nnHolderNorm_eq_eHolderNorm)

theorem holder_add (k : ℕ) (α : ℝ≥0) {s : Set E} (hs : IsOpen s)
    (f g : E → V) (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) :
    coordinateHolderENorm k α s (f + g) ≤
      coordinateHolderENorm k α s f + coordinateHolderENorm k α s g := by
  have hder (j : ℕ) (hj : j ≤ k) (x : s) :
      iteratedFDerivWithin ℝ j (f + g) s x =
        iteratedFDerivWithin ℝ j f s x + iteratedFDerivWithin ℝ j g s x :=
    iteratedFDerivWithin_add_apply ((hf x x.property).of_le (by exact_mod_cast hj))
      ((hg x x.property).of_le (by exact_mod_cast hj)) hs.uniqueDiffOn x.property
  have hnorm (j : ℕ) (hj : j ≤ k) : derivativeENorm j s (f + g) ≤
      derivativeENorm j s f + derivativeENorm j s g := by
    apply iSup_le
    intro x
    rw [hder j hj x]
    exact (ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)).trans
      (add_le_add (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j f s y‖₊ : ℝ≥0∞)) x)
        (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j g s y‖₊ : ℝ≥0∞)) x))
  have hhold : eHolderNorm α (fun x : s => iteratedFDerivWithin ℝ k (f + g) s x) ≤
      eHolderNorm α (fun x : s => iteratedFDerivWithin ℝ k f s x) +
      eHolderNorm α (fun x : s => iteratedFDerivWithin ℝ k g s x) := by
    simp_rw [hder k le_rfl]
    exact eHolderNorm_add_le
  exact (add_le_add (Finset.sum_le_sum fun j hj => hnorm j (by simpa using Finset.mem_range.mp hj))
    hhold).trans_eq (by rw [Finset.sum_add_distrib]; unfold coordinateHolderENorm; ac_rfl)


theorem derivative_point_bound (k j : ℕ) (α : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f : E → V) (B : ℝ≥0)
    (hB : coordinateHolderENorm k α s f ≤ B) (hj : j ≤ k)
    (x : E) (hx : x ∈ s) : ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  have hb := (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j f s y‖₊ : ℝ≥0∞)) ⟨x, hx⟩).trans
    ((derivative_le_holder k j α s f hj).trans hB)
  rw [iteratedFDerivWithin_of_isOpen j hs hx] at hb
  exact_mod_cast hb

theorem interior_lipschitz (k j : ℕ) (α : ℝ≥0) {s t : Set E}
    (ht : IsOpen t) (f : E → V) (B : ℝ≥0) (r : ℝ) (hr : 0 < r)
    (hshrink : ∀ x ∈ s, Metric.closedBall x r ⊆ t)
    (hf : ContDiffOn ℝ k f t) (hB : coordinateHolderENorm k α t f ≤ B)
    (hj : j + 1 ≤ k) :
    LipschitzOnWith (B + 2 * B / ⟨r, hr.le⟩) (iteratedFDeriv ℝ j f) s := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  have hxt : x ∈ t := hshrink x hx (Metric.mem_closedBall_self hr.le)
  have hyt : y ∈ t := hshrink y hy (Metric.mem_closedBall_self hr.le)
  have hnon : 0 ≤ (2 : ℝ) * B / r := by positivity
  change ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤
    ((B : ℝ) + 2 * B / r) * ‖x - y‖
  by_cases hxy : ‖x - y‖ ≤ r
  · have hlocal := (convex_closedBall y r).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := iteratedFDeriv ℝ j f)
      (fun z hz => ((hf z (hshrink y hy hz)).contDiffAt
        (ht.mem_nhds (hshrink y hy hz))).differentiableAt_iteratedFDeriv
        (by exact_mod_cast (show j < k by omega)))
      (fun z hz => by
        rw [norm_fderiv_iteratedFDeriv]
        exact derivative_point_bound k (j + 1) α ht f B hB hj z (hshrink y hy hz))
      (Metric.mem_closedBall_self hr.le) (show x ∈ Metric.closedBall y r by simpa [dist_eq_norm] using hxy)
    exact hlocal.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hnon) (norm_nonneg _))
  · have hdist : r ≤ ‖x - y‖ := le_of_lt (lt_of_not_ge hxy)
    have hsub := norm_sub_le (iteratedFDeriv ℝ j f x) (iteratedFDeriv ℝ j f y)
    have hxb := derivative_point_bound k j α ht f B hB (by omega) x hxt
    have hyb := derivative_point_bound k j α ht f B hB (by omega) y hyt
    have hfrac : 2 * (B : ℝ) ≤ (2 * B / r) * ‖x - y‖ := by
      calc
        2 * (B : ℝ) = (2 * B / r) * r := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hdist hnon
    nlinarith [mul_nonneg B.coe_nonneg (norm_nonneg (x - y))]

theorem interior_holder_bound (k j : ℕ) (α : ℝ≥0) {s t : Set E}
    (hs : IsOpen s) (ht : IsOpen t) (f : E → V) (B : ℝ≥0) (r R : ℝ)
    (hr : 0 < r) (hR : 0 < R) (hα : α ≤ 1)
    (hshrink : ∀ x ∈ s, Metric.closedBall x r ⊆ t)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 2 * R)
    (hf : ContDiffOn ℝ k f t) (hB : coordinateHolderENorm k α t f ≤ B)
    (hj : j + 1 ≤ k) :
    eHolderNorm α (fun x : s => iteratedFDerivWithin ℝ j f s x) ≤
      ((B + 2 * B / ⟨r, hr.le⟩) * NNReal.rpow (⟨2 * R, by positivity⟩ : ℝ≥0) (1 - (α : ℝ)) : ℝ≥0) := by
  have hL : LipschitzWith (B + 2 * B / ⟨r, hr.le⟩)
      (fun x : s => iteratedFDeriv ℝ j f x) := by
    intro x y
    exact interior_lipschitz k j α ht f B r hr hshrink hf hB hj x.property y.property
  let D : ℝ≥0 := ⟨2 * R, by positivity⟩
  have hd : ∀ x y : s, edist x y ≤ (D : ℝ≥0∞) := by
    intro x y
    rw [edist_dist]
    exact ENNReal.ofReal_le_coe.mpr (show dist x y ≤ (D : ℝ) from hdiam x x.property y y.property)
  have hH := hL.holderWith.of_le hd hα
  have heq : (fun x : s => iteratedFDerivWithin ℝ j f s x) =
      (fun x : s => iteratedFDeriv ℝ j f x) := by
    funext x
    exact iteratedFDerivWithin_of_isOpen j hs x.property
  rw [heq]
  exact hH.eHolderNorm_le

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem holder_section_add (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (f g : RawCov2 M) (hf : C.Cov2Holder k α f) (hg : C.Cov2Holder k α g) :
    C.Cov2Holder k α (f + g) := by
  refine ⟨fun ν => (hf.1 ν).add (hg.1 ν), ?_⟩
  apply lt_of_le_of_lt (b := C.cov2ENorm k α f + C.cov2ENorm k α g)
  · apply iSup_le
    intro ν
    exact (holder_add k α (C.chart ν).innerOpen _ _ (hf.1 ν) (hg.1 ν)).trans
      (add_le_add (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
        ((C.chart μ).liftedCov2 f)) ν) (le_iSup (fun μ => coordinateHolderENorm k α
          (C.chart μ).innerDomain ((C.chart μ).liftedCov2 g)) ν))
  · exact ENNReal.add_lt_top.mpr ⟨hf.2, hg.2⟩


theorem admissible_holder_two (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (z : RawCov2 M) (hz : MetricAdmissible C b z) : C.Cov2Holder 2 b.exponent.value z := by
  have hsub (ν : C.Index) : (C.chart ν).innerDomain ⊆ (C.chart ν).outerDomain :=
    fun _ hx => (C.chart ν).closureInnerSubset (subset_closure hx)
  have hB (ν : C.Index) : coordinateHolderENorm b.order b.exponent.value
      (C.chart ν).outerDomain ((C.chart ν).liftedCov2 z) ≤ b.coefficientBound :=
    le_self_add.trans (hz.coefficientBound ν)
  refine ⟨fun ν => ((hz.regularity ν).1.of_le (by exact_mod_cast b.order_ge_two)).mono (hsub ν), ?_⟩
  by_cases hk : b.order = 2
  · apply lt_of_le_of_lt (b := (b.coefficientBound : ℝ≥0∞))
    · apply iSup_le
      intro ν
      exact (holder_mono_domain 2 b.exponent.value (C.chart ν).innerOpen
        (C.chart ν).outerOpen (hsub ν) _).trans (by simpa only [hk] using hB ν)
    · exact ENNReal.coe_lt_top
  · let r : ℝ≥0 := ⟨C.numerics.shrinkRadius, C.numerics.shrinkRadius_pos.le⟩
    let D : ℝ≥0 := ⟨2 * C.numerics.outerRadius, mul_nonneg (by norm_num) C.numerics.outerRadius_pos.le⟩
    let L : ℝ≥0 := (b.coefficientBound + 2 * b.coefficientBound / r) *
      NNReal.rpow D (1 - (b.exponent.value : ℝ))
    apply lt_of_le_of_lt (b := (3 * (b.coefficientBound : ℝ≥0∞) + (L : ℝ≥0∞)))
    · apply iSup_le
      intro ν
      apply add_le_add
      · calc
          (∑ j ∈ Finset.range (2 + 1), derivativeENorm j (C.chart ν).innerDomain
              ((C.chart ν).liftedCov2 z)) ≤ ∑ _j ∈ Finset.range (2 + 1),
                (b.coefficientBound : ℝ≥0∞) := by
            apply Finset.sum_le_sum
            intro j hj
            exact (derivative_mono j (C.chart ν).innerOpen (C.chart ν).outerOpen (hsub ν) _).trans
              ((derivative_le_holder b.order j b.exponent.value (C.chart ν).outerDomain _
                (by have := Finset.mem_range.mp hj; have := b.order_ge_two; omega)).trans (hB ν))
          _ = 3 * (b.coefficientBound : ℝ≥0∞) := by simp [nsmul_eq_mul]
      · apply interior_holder_bound b.order 2 b.exponent.value (C.chart ν).innerOpen
          (C.chart ν).outerOpen _ b.coefficientBound C.numerics.shrinkRadius C.numerics.outerRadius
          C.numerics.shrinkRadius_pos C.numerics.outerRadius_pos b.exponent.lessThanOne.le
        · intro x hx
          exact C.uniformShrink ν.1 ν.2 x (subset_closure hx)
        · obtain ⟨c, hc⟩ := C.uniformOuterRadius ν.1 ν.2
          intro x hx y hy
          have hx' := hc (hsub ν hx)
          have hy' := hc (hsub ν hy)
          have hd := dist_triangle x c y
          rw [dist_comm c y] at hd
          exact (hd.trans (add_le_add (Metric.mem_ball.mp hx').le (Metric.mem_ball.mp hy').le)).trans_eq (by ring)
        · exact (hz.regularity ν).1
        · exact hB ν
        · have := b.order_ge_two
          omega
    · exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) ENNReal.coe_lt_top, ENNReal.coe_lt_top⟩

theorem matrix_bound (A : Mat4) (v : FourSpace) :
    |matrixToBilinear A v v| ≤ 16 * ‖A‖ * ‖v‖ ^ 2 := by
  have hterm (i j : Fin 4) : |v i * A i j * v j| ≤ ‖A‖ * ‖v‖ ^ 2 := by
    have hi : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
    have hj : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    have ha : |A i j| ≤ ‖A‖ := by
      have h : ‖A i j‖ ≤ ‖A i‖ := norm_le_pi_norm (A i) j
      simpa only [Real.norm_eq_abs] using h.trans (norm_le_pi_norm A i)
    calc
      |v i * A i j * v j| = |v i| * |A i j| * |v j| := by simp [abs_mul]
      _ ≤ ‖v‖ * ‖A‖ * ‖v‖ := mul_le_mul (mul_le_mul hi ha (abs_nonneg _) (norm_nonneg _))
        hj (abs_nonneg _) (by positivity)
      _ = ‖A‖ * ‖v‖ ^ 2 := by ring
  have hexp : matrixToBilinear A v v = ∑ i, ∑ j, v i * A i j * v j := by
    simp [matrixToBilinear, coordProj, mul_assoc]
  rw [hexp]
  calc
    |∑ i, ∑ j, v i * A i j * v j| ≤ ∑ i, ∑ j, |v i * A i j * v j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, ‖A‖ * ‖v‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = 16 * ‖A‖ * ‖v‖ ^ 2 := by simp; ring


theorem pullback_apply {F : LocalFiniteCover M} (c : LocalCoverChart F)
    (u : RawCov2 M) (x : FourSpace) (v w : FourSpace) :
    matrixToBilinear (c.liftedCov2 u x) v w =
      u (c.lift x) (c.tangentMap x v) (c.tangentMap x w) := by
  have h := matrixToBilinear_recover
    (bilinearPullback (u (c.lift x)) (c.tangentMap x).toContinuousLinearMap)
  change matrixToBilinear (c.liftedCov2 u x) = _ at h
  rw [h]
  rfl

theorem small_perturbation_positive (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (z h : RawCov2 M) (hz : MetricAdmissible C b z)
    (hsmall : C.cov2ENorm 2 b.exponent.value h < ENNReal.ofReal (b.lower / 32)) :
    IsPositiveDefiniteCov2 (z + h) := by
  intro p v hv
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  let w : FourSpace := (C.chart ν).tangentMap x |>.symm <| v
  have hw : w ≠ 0 := by
    intro hw0
    have h := congrArg ((C.chart ν).tangentMap x) hw0
    exact hv (by simpa [w] using h)
  have hbound : (‖(C.chart ν).liftedCov2 h x‖₊ : ℝ≥0∞) < ENNReal.ofReal (b.lower / 32) :=
    (value_le_holder 2 b.exponent.value (C.chart ν).innerDomain _ x hx).trans_lt
      ((le_iSup (fun μ => coordinateHolderENorm 2 b.exponent.value (C.chart μ).innerDomain
        ((C.chart μ).liftedCov2 h)) ν).trans_lt hsmall)
  have hnorm : ‖(C.chart ν).liftedCov2 h x‖ < b.lower / 32 := by
    exact_mod_cast (ENNReal.coe_lt_ofReal.mp hbound)
  have hell := hz.ellipticityLower ν x
    ((C.chart ν).closureInnerSubset (subset_closure hx)) w
  have hquad := matrix_bound ((C.chart ν).liftedCov2 h x) w
  have hpos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have heq : (z + h) ((C.chart ν).lift x) v v =
      matrixToBilinear ((C.chart ν).liftedCov2 z x) w w +
      matrixToBilinear ((C.chart ν).liftedCov2 h x) w w := by
    rw [pullback_apply, pullback_apply]
    simp [w]
  rw [heq]
  have hneg := neg_abs_le (matrixToBilinear ((C.chart ν).liftedCov2 h x) w w)
  have hmul := mul_lt_mul_of_pos_right hnorm hpos
  nlinarith [mul_pos b.lower_pos hpos]

theorem positive_neighborhood (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (z : RawCov2 M) (hz : MetricAdmissible C b z) :
    SectionNeighborhood (tensorHolderSpace C 2 b.exponent.value)
      (positiveHolderMetrics C 2 b.exponent.value) (C.cov2ENorm 2 b.exponent.value) z := by
  refine ⟨b.lower / 32, div_pos b.lower_pos (by norm_num), ?_⟩
  intro h hh hsmall
  refine ⟨⟨?_, small_perturbation_positive C b z h hz hsmall⟩,
    holder_section_add C 2 b.exponent.value z h (admissible_holder_two C b z hz) hh.2⟩
  intro p v w
  change z p v w + h p v w = z p w v + h p w v
  rw [hz.metric.1 p v w, hh.1 p v w]

end K24.Global.PositiveNeighborhoodProof

namespace K24.Global
universe u

theorem _root_.solution :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
    ∀ (C : BoundedLocalCover M) (metricBounds : MetricCoefficientNumerics) (z : RawCov2 M),
      MetricAdmissible C metricBounds z →
      SectionNeighborhood (tensorHolderSpace C 2 metricBounds.exponent.value)
        (positiveHolderMetrics C 2 metricBounds.exponent.value)
        (C.cov2ENorm 2 metricBounds.exponent.value) z := by
  intro M _ _ _ _ _ C b z hz
  exact PositiveNeighborhoodProof.positive_neighborhood C b z hz

end K24.Global

