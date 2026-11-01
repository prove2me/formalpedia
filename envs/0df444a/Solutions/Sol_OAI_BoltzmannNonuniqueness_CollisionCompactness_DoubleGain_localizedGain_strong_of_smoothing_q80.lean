-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.localizedGain_strong_of_smoothing_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:03:35.145121+00:00
-- url     : https://prove2.me/submissions/463a0b6e-b748-408b-836f-fdb6d6dc2164

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section
-- module Solutions.OAIQ080_BZ.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PullbackRegularLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Quantitative chart estimates for the finite-gain pullback

A normalized derivative within one half of the identity gives an injective
chart. A positive Jacobian lower bound then controls pullback integrals,
including arbitrary bounded measurable masks in the parameter density.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.GainPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chart_injective {s : Set E} (hs : Convex ℝ s)
    {f : E → E} {f' : E → E →L[ℝ] E} (A : E ≃L[ℝ] E)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hclose : ∀ x ∈ s,
      ‖A.symm.toContinuousLinearMap.comp (f' x) - ContinuousLinearMap.id ℝ E‖ ≤ 1/2) :
    InjOn f s := by
  intro x hx y hy hxy
  have hder (z) (hz : z ∈ s) :
      HasFDerivWithinAt (fun w => A.symm (f w))
        (A.symm.toContinuousLinearMap.comp (f' z)) s z :=
    A.symm.toContinuousLinearMap.hasFDerivAt.comp_hasFDerivWithinAt z (hf z hz)
  have h := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' hder hclose hx hy
  simp only [hxy,sub_self,ContinuousLinearMap.id_apply,zero_sub,norm_neg] at h
  have hn : ‖y-x‖ = 0 := by nlinarith [norm_nonneg (y-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

theorem jacobian_pullback_bound {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hi : InjOn f s)
    {c : ℝ} (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(f' x).det|)
    (g : E → ℝ≥0∞) :
    ∫⁻ x in s, g (f x) ∂μ ≤ (ENNReal.ofReal c)⁻¹ * ∫⁻ y in f '' s, g y ∂μ := by
  have hbound : ENNReal.ofReal c * (∫⁻ x in s, g (f x) ∂μ) ≤
      ∫⁻ y in f '' s, g y ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hf hi g]
    apply setLIntegral_mono' hs
    intro x hx
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hdet x hx)) le_rfl
  calc
    _ = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * ∫⁻ x in s, g (f x) ∂μ) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel
        (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hbound

theorem masked_jacobian_pullback_bound {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hi : InjOn f s)
    {c : ℝ} (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(f' x).det|)
    (g ρ : E → ℝ≥0∞) {B : ℝ≥0∞} (hB : B ≠ ∞) (hρ : ∀ x ∈ s, ρ x ≤ B) :
    ∫⁻ x in s, ρ x * g (f x) ∂μ ≤
      (B * (ENNReal.ofReal c)⁻¹) * ∫⁻ y in f '' s, g y ∂μ := by
  calc
    _ ≤ ∫⁻ x in s, B * g (f x) ∂μ := by
      apply setLIntegral_mono' hs
      intro x hx
      exact mul_le_mul' (hρ x hx) le_rfl
    _ = B * ∫⁻ x in s, g (f x) ∂μ := by rw [lintegral_const_mul' _ _ hB]
    _ ≤ B * ((ENNReal.ofReal c)⁻¹ * ∫⁻ y in f '' s, g y ∂μ) :=
      mul_le_mul' le_rfl (jacobian_pullback_bound hs hf hi hc hdet g)
    _ = _ := by rw [mul_assoc]

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # A regular chart persists under locally uniform convergence of derivatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem regular_derivative_neighborhood (A : E ≃L[ℝ] E)
    (hA : 0 < |A.toContinuousLinearMap.det|) :
    ∃ δ > 0, ∀ B : E →L[ℝ] E, ‖B-A.toContinuousLinearMap‖ < δ →
      ‖A.symm.toContinuousLinearMap.comp B - ContinuousLinearMap.id ℝ E‖ ≤ 1/2 ∧
      |A.toContinuousLinearMap.det|/2 ≤ |B.det| := by
  have hcomp : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by ext x; simp
  have hN : Continuous (fun B : E →L[ℝ] E =>
      ‖A.symm.toContinuousLinearMap.comp B - ContinuousLinearMap.id ℝ E‖) := by fun_prop
  have hD : Continuous (fun B : E →L[ℝ] E => |B.det|) :=
    ContinuousLinearMap.continuous_det.abs
  have hn := hN.continuousAt.eventually (Iio_mem_nhds (show
      ‖A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap -
        ContinuousLinearMap.id ℝ E‖ < 1/2 by rw [hcomp,sub_self,norm_zero]; norm_num))
  have hd := hD.continuousAt.eventually
    (Ioi_mem_nhds (show |A.toContinuousLinearMap.det|/2 < |A.toContinuousLinearMap.det| by linarith))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hn.and hd)
  refine ⟨δ,hδ,fun B hB => ?_⟩
  have h := hball (show B ∈ ball A.toContinuousLinearMap δ by
    simpa only [mem_ball,dist_eq_norm] using hB)
  exact ⟨h.1.le,h.2.le⟩

/-- On a small ball at a regular point, all sufficiently late charts are
injective with one common positive Jacobian lower bound. -/
theorem eventually_regular_ball {O : Set E} (hO : IsOpen O) {x₀ : E} (hx₀ : x₀ ∈ O)
    {f' : E → E →L[ℝ] E} (hcont : ContinuousAt f' x₀)
    (A : E ≃L[ℝ] E) (hAt : f' x₀ = A.toContinuousLinearMap)
    (hA : 0 < |A.toContinuousLinearMap.det|)
    {F : ℕ → E → E} {F' : ℕ → E → E →L[ℝ] E}
    (hF : ∀ n, ∀ x ∈ O, HasFDerivAt (F n) (F' n x) x)
    (hconv : ∀ r > 0, ball x₀ r ⊆ O →
      TendstoUniformlyOn F' f' atTop (ball x₀ r)) :
    ∃ r > 0, ball x₀ r ⊆ O ∧
      ∀ᶠ n in atTop, InjOn (F n) (ball x₀ r) ∧
        ∀ x ∈ ball x₀ r, |A.toContinuousLinearMap.det|/2 ≤ |(F' n x).det| := by
  obtain ⟨δ,hδ,hδspec⟩ := regular_derivative_neighborhood A hA
  have hnear : ∀ᶠ x in 𝓝 x₀, ‖f' x-A.toContinuousLinearMap‖ < δ/2 := by
    have h := hcont.eventually (Metric.ball_mem_nhds (f' x₀) (half_pos hδ))
    simpa only [mem_ball,dist_eq_norm,hAt] using h
  obtain ⟨r,hr,hrspec⟩ := Metric.mem_nhds_iff.mp (hnear.and (hO.mem_nhds hx₀))
  have hsub : ball x₀ r ⊆ O := fun x hx => (hrspec hx).2
  refine ⟨r,hr,hsub,?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hconv r hr hsub)) (δ/2) (half_pos hδ)] with n hn
  have hbound (x) (hx : x ∈ ball x₀ r) : ‖F' n x-A.toContinuousLinearMap‖ < δ := by
    have h₁ : ‖F' n x-f' x‖ < δ/2 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hn x hx
    have h₂ := (hrspec hx).1
    calc
      _ ≤ ‖F' n x-f' x‖+‖f' x-A.toContinuousLinearMap‖ := by
        simpa only [dist_eq_norm] using
          dist_triangle (F' n x) (f' x) A.toContinuousLinearMap
      _ < δ := by linarith
  refine ⟨chart_injective (convex_ball x₀ r) A
    (fun x hx => (hF n x (hsub hx)).hasFDerivWithinAt)
    (fun x hx => (hδspec _ (hbound x hx)).1),?_⟩
  exact fun x hx => (hδspec _ (hbound x hx)).2

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Gluing local pullback convergence outside a null critical set -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

theorem lintegral_finite_union_le {X I : Type*} [MeasurableSpace X]
    {μ : Measure X} (s : Finset I) (U : I → Set X) (f : X → ℝ≥0∞) :
    ∫⁻ x in ⋃ i ∈ s, U i, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in U i, f x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [show (⋃ j ∈ insert i s, U j) = U i ∪ ⋃ j ∈ s, U j by simp,
      Finset.sum_insert hi]
    exact (lintegral_union_le f _ _).trans (add_le_add le_rfl ih)

/-- Local integral convergence on a neighborhood of each noncritical point
suffices on a compact set, provided the integrands have a common bound. -/
theorem compact_integral_zero_of_local {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    {μ : Measure X} [OuterRegular μ] {K Z : Set X} (hK : IsCompact K)
    (hZ : μ Z = 0) {f : ℕ → X → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbound : ∀ n x, x ∈ K → f n x ≤ M)
    (hlocal : ∀ x ∈ K \ Z, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      Tendsto (fun n => ∫⁻ y in U, f n y ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, f n x ∂μ) atTop (𝓝 0) := by
  classical
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hhalf : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨δ,hδ,hδsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hM hhalf.ne'
  obtain ⟨Bad,hZBad,hBad,hBadsmall⟩ := Z.exists_isOpen_lt_of_lt (μ := μ) δ (by
    rw [hZ]; exact ENNReal.coe_pos.mpr hδ)
  let R := {x // x ∈ K \ Z}
  have hchoice (x : R) := hlocal x x.2
  choose U hUopen hUmem hUlim using hchoice
  have hcover : K \ Bad ⊆ ⋃ x : R, U x := by
    intro x hx
    have hxR : x ∈ K \ Z := ⟨hx.1,fun hz => hx.2 (hZBad hz)⟩
    exact mem_iUnion.mpr ⟨⟨x,hxR⟩,hUmem ⟨x,hxR⟩⟩
  obtain ⟨I,hI⟩ := (hK.diff hBad).elim_finite_subcover U hUopen hcover
  have hsum : Tendsto (fun n => ∑ i ∈ I, ∫⁻ x in U i, f n x ∂μ) atTop (𝓝 0) := by
    have h := tendsto_finsetSum I (fun i _ => hUlim i)
    simpa using h
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hsum (ε/2) hhalf] with n hn
  have hKB : (∫⁻ x in K ∩ Bad, f n x ∂μ) ≤ M*μ Bad := by
    apply (show (∫⁻ x in K ∩ Bad, f n x ∂μ) ≤ M*μ (K ∩ Bad) from ?_).trans
      (mul_le_mul' le_rfl (measure_mono inter_subset_right))
    calc
      _ ≤ ∫⁻ _x in K ∩ Bad, M ∂μ := by
        apply setLIntegral_mono' (hK.measurableSet.inter hBad.measurableSet)
        intro x hx
        exact hbound n x hx.1
      _ = _ := by simp
  have hset : K ⊆ (K ∩ Bad) ∪ ⋃ i ∈ I, U i := by
    intro x hx
    by_cases hb : x ∈ Bad
    · exact Or.inl ⟨hx,hb⟩
    · exact Or.inr (hI ⟨hx,hb⟩)
  calc
    _ ≤ ∫⁻ x in (K ∩ Bad) ∪ ⋃ i ∈ I, U i, f n x ∂μ := lintegral_mono_set hset
    _ ≤ (∫⁻ x in K ∩ Bad, f n x ∂μ) + ∫⁻ x in ⋃ i ∈ I, U i, f n x ∂μ :=
      lintegral_union_le _ _ _
    _ ≤ M*μ Bad + ∑ i ∈ I, ∫⁻ x in U i, f n x ∂μ :=
      add_le_add hKB (lintegral_finite_union_le I U (f n))
    _ ≤ ε/2+ε/2 := add_le_add
      ((mul_le_mul' le_rfl hBadsmall.le).trans (by simpa [mul_comm] using hδsmall.le)) hn
    _ = ε := ENNReal.add_halves ε

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Pullback estimates after adjoining the unused parameter coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]

theorem product_chart_bound {s : Set (P × Q)} (hs : MeasurableSet s)
    {F : P × Q → P × Q} {F' : P × Q → (P × Q) →L[ℝ] P × Q}
    (hf : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x) (hi : InjOn F s)
    {c : ℝ} (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(F' x).det|)
    {W : Set Q} (hWfin : volume W ≠ ∞)
    (himage : ∀ x ∈ s, (F x).2 ∈ W)
    (g : P → ℝ≥0∞) (hg : Measurable g) (ρ : P × Q → ℝ≥0∞)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hρ : ∀ x ∈ s, ρ x ≤ B) :
    ∫⁻ x in s, ρ x * g (F x).1 ∂((volume : Measure P).prod volume) ≤
      ((B*(ENNReal.ofReal c)⁻¹)*volume W) * ∫⁻ y, g y := by
  have hmain := masked_jacobian_pullback_bound
    (μ := (volume : Measure P).prod volume) hs hf hi hc hdet
    (fun y => g y.1) ρ hB hρ
  have hsub : F '' s ⊆ (univ : Set P) ×ˢ W := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨mem_univ _,himage x hx⟩
  have hproduct : (∫⁻ y in (univ : Set P) ×ˢ W, g y.1
      ∂((volume : Measure P).prod volume)) = volume W * ∫⁻ y, g y := by
    rw [setLIntegral_prod (fun y : P × Q => g y.1) (by fun_prop)]
    simp only [lintegral_const,Measure.restrict_apply_univ,Measure.restrict_univ]
    rw [lintegral_mul_const' _ _ hWfin,mul_comm]
  calc
    _ ≤ (B*(ENNReal.ofReal c)⁻¹) * (∫⁻ y in F '' s, g y.1
        ∂((volume : Measure P).prod volume)) := hmain
    _ ≤ (B*(ENNReal.ofReal c)⁻¹) * (∫⁻ y in (univ : Set P) ×ˢ W, g y.1
        ∂((volume : Measure P).prod volume)) := mul_le_mul' le_rfl (lintegral_mono_set hsub)
    _ = _ := by rw [hproduct]; ac_rfl

theorem tendsto_product_chart_zero {s : Set (P × Q)} (hs : MeasurableSet s)
    {F : ℕ → P × Q → P × Q} {F' : ℕ → P × Q → (P × Q) →L[ℝ] P × Q}
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → P × Q → ℝ≥0∞}
    {c : ℝ} (hc : 0 < c) {B : ℝ≥0∞} (hB : B ≠ ∞)
    {W : Set Q} (hWfin : volume W ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hchart : ∀ᶠ n in atTop,
      (∀ x ∈ s, HasFDerivWithinAt (F n) (F' n x) s x) ∧
      InjOn (F n) s ∧ (∀ x ∈ s, c ≤ |(F' n x).det|) ∧
      (∀ x ∈ s, (F n x).2 ∈ W) ∧ (∀ x ∈ s, ρ n x ≤ B))
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in s, ρ n x*g n (F n x).1
      ∂((volume : Measure P).prod volume)) atTop (𝓝 0) := by
  have hfinite : (B*(ENNReal.ofReal c)⁻¹)*volume W ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hB
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hc)))) hWfin
  have hscale := ENNReal.Tendsto.const_mul (a := (B*(ENNReal.ofReal c)⁻¹)*volume W)
    hL (Or.inr hfinite)
  simp only [mul_zero] at hscale
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hchart] with n hn
  exact product_chart_bound hs hn.1 hn.2.1 hc hn.2.2.1 hWfin hn.2.2.2.1
    (g n) (hg n) (ρ n) hB hn.2.2.2.2

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Local pullback convergence after adjoining a complementary projection -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

section Derivatives
variable {E P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem augmented_derivative_uniform {s : Set E}
    {F : ℕ → E → E →L[ℝ] P} {f : E → E →L[ℝ] P}
    (h : TendstoUniformlyOn F f atTop s) (π : E →L[ℝ] Q) :
    TendstoUniformlyOn (fun n x => (F n x).prod π) (fun x => (f x).prod π) atTop s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h ε hε] with n hn
  intro x hx
  have he : (f x).prod π-(F n x).prod π = (f x-F n x).prod 0 := by
    ext y <;> simp
  simpa only [dist_eq_norm,he,ContinuousLinearMap.opNorm_prod,Prod.norm_def,norm_zero,
    max_eq_left (norm_nonneg _)] using hn x hx

end Derivatives

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]
local notation "E" => P × Q

theorem local_augmented_pullback_zero {O : Set E} (hO : IsOpen O) {x₀ : E} (hx₀ : x₀ ∈ O)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ContinuousAt φ' x₀) (π : E →L[ℝ] Q) (A : E ≃L[ℝ] E)
    (hA : (φ' x₀).prod π = A.toContinuousLinearMap)
    (hconv : ∀ r > 0, ball x₀ r ⊆ O → TendstoUniformlyOn Φ' φ' atTop (ball x₀ r))
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hg : ∀ n, Measurable (g n)) (hρ : ∀ n x, x ∈ O → ρ n x ≤ B)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    ∃ r > 0, ball x₀ r ⊆ O ∧ Tendsto
      (fun n => ∫⁻ x in ball x₀ r, ρ n x*g n (Φ n x)
        ∂((volume : Measure P).prod volume)) atTop (𝓝 0) := by
  let G (n : ℕ) (x : E) : E := (Φ n x,π x)
  let G' (n : ℕ) (x : E) : E →L[ℝ] E := (Φ' n x).prod π
  have hG (n) (x) (hx : x ∈ O) : HasFDerivAt (G n) (G' n x) x :=
    (hder n x hx).prodMk π.hasFDerivAt
  have hc : ContinuousAt (fun x => (φ' x).prod π) x₀ :=
    (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) ℝ).continuous.continuousAt.comp
      (hcont.prodMk continuousAt_const)
  have ha : 0 < |A.toContinuousLinearMap.det| := abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero
  obtain ⟨r,hr,hrO,hevent⟩ := eventually_regular_ball hO hx₀ hc A hA ha hG
    (fun r hr hrO => augmented_derivative_uniform (hconv r hr hrO) π)
  let W : Set Q := closedBall 0 (‖π‖*(‖x₀‖+r))
  have hWfin : volume W ≠ ∞ := (isCompact_closedBall (0 : Q) _).measure_lt_top.ne
  have hW (x : E) (hx : x ∈ ball x₀ r) : π x ∈ W := by
    have hnorm : ‖x‖ ≤ ‖x₀‖+r := by
      have h := norm_le_norm_add_norm_sub x₀ x
      rw [norm_sub_rev x₀ x] at h
      have hxr : ‖x-x₀‖ < r := by simpa only [mem_ball,dist_eq_norm] using hx
      linarith
    change dist (π x) 0 ≤ ‖π‖*(‖x₀‖+r)
    rw [dist_zero_right]
    exact (π.le_opNorm x).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  refine ⟨r,hr,hrO,?_⟩
  apply tendsto_product_chart_zero (F := G) (F' := G') isOpen_ball.measurableSet
    (half_pos ha) hB hWfin hg ?_ hL
  filter_upwards [hevent] with n hn
  exact ⟨fun x hx => (hG n x (hrO hx)).hasFDerivWithinAt,
    hn.1,hn.2,hW,fun x hx => hρ n x (hrO hx)⟩

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Robust compact pullback convergence for submersions

Regularity is expressed by a complementary linear projection at each point.
The critical set is null. Parameter masks need only have a common bound.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]
local notation "E" => P × Q

theorem compact_submersion_pullback_zero {O K Z : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) (hZ : ((volume : Measure P).prod volume) Z = 0)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ∀ x ∈ O, ContinuousAt φ' x)
    (hreg : ∀ x ∈ K \ Z, ∃ π : E →L[ℝ] Q, ∃ A : E ≃L[ℝ] E,
      (φ' x).prod π = A.toContinuousLinearMap)
    (hconv : ∀ x ∈ O, ∀ r > 0, ball x r ⊆ O →
      TendstoUniformlyOn Φ' φ' atTop (ball x r))
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n x, x ∈ O → ρ n x ≤ B) (hgM : ∀ n y, g n y ≤ M)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, ρ n x*g n (Φ n x)
      ∂((volume : Measure P).prod volume)) atTop (𝓝 0) := by
  apply compact_integral_zero_of_local hK hZ (ENNReal.mul_ne_top hB hM)
    (fun n x hx => mul_le_mul' (hρ n x (hKO hx)) (hgM n _))
  intro x hx
  obtain ⟨π,A,hA⟩ := hreg x hx
  obtain ⟨r,hr,_,hlim⟩ := local_augmented_pullback_zero hO (hKO hx.1)
    hder (hcont x (hKO hx.1)) π A hA (hconv x (hKO hx.1)) hB hg hρ hL
  exact ⟨ball x r,isOpen_ball,mem_ball_self hr,hlim⟩

end BoltzmannNonuniqueness.GainPullback

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SubmersionNullPreimage
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A surjective derivative admits the complementary chart used in the pullback -/

noncomputable section

open Function MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
local notation "E" => P × Q

theorem exists_complementary_chart (L : E →L[ℝ] P) (hL : Surjective L) :
    ∃ π : E →L[ℝ] Q, ∃ A : E ≃L[ℝ] E, L.prod π = A.toContinuousLinearMap := by
  classical
  obtain ⟨R,hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  have hR' (y : P) : L (R y) = y := LinearMap.congr_fun hR y
  let κ : E →ₗ[ℝ] LinearMap.ker L.toLinearMap :=
    (LinearMap.id-R.comp L.toLinearMap).codRestrict _ (fun x => by
      change L (x-R (L x)) = 0
      rw [map_sub,hR',sub_self])
  let A₀ : E ≃ₗ[ℝ] P × LinearMap.ker L.toLinearMap :=
    { L.toLinearMap.prod κ with
      invFun := fun y => R y.1+y.2
      left_inv := by
        intro x
        change R (L x)+(x-R (L x)) = x
        abel
      right_inv := by
        rintro ⟨y,z⟩
        have hz : L (z : E) = 0 := z.property
        apply Prod.ext
        · change L (R y+z) = y
          rw [map_add,hR',hz,add_zero]
        · apply Subtype.ext
          change R y+z-R (L (R y+z)) = z
          rw [map_add,hR',hz,add_zero]
          abel }
  have hdim : Module.finrank ℝ (LinearMap.ker L.toLinearMap) = Module.finrank ℝ Q := by
    have h := L.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hL,finrank_top,Module.finrank_prod] at h
    omega
  let e : LinearMap.ker L.toLinearMap ≃ₗ[ℝ] Q := LinearEquiv.ofFinrankEq _ _ hdim
  let A : E ≃L[ℝ] E :=
    (A₀.trans (LinearEquiv.prodCongr (LinearEquiv.refl ℝ P) e)).toContinuousLinearEquiv
  let π : E →L[ℝ] Q := (ContinuousLinearMap.snd ℝ P Q).comp A.toContinuousLinearMap
  refine ⟨π,A,?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext <;> rfl

variable
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]

/-- The L1 form of the manuscript's uniform pullback estimate. -/
theorem compact_surjective_pullback_zero {O K Z : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) (hZ : ((volume : Measure P).prod volume) Z = 0)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ∀ x ∈ O, ContinuousAt φ' x)
    (hreg : ∀ x ∈ K \ Z, Surjective (φ' x))
    (hconv : ∀ x ∈ O, ∀ r > 0, ball x r ⊆ O →
      TendstoUniformlyOn Φ' φ' atTop (ball x r))
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n x, x ∈ O → ρ n x ≤ B) (hgM : ∀ n y, g n y ≤ M)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, ρ n x*g n (Φ n x)
      ∂((volume : Measure P).prod volume)) atTop (𝓝 0) :=
  compact_submersion_pullback_zero hO hK hKO hZ hder hcont
    (fun x hx => exists_complementary_chart (φ' x) (hreg x hx))
    hconv hB hM hg hρ hgM hL

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Null preimages on compact sets for an almost-everywhere submersion -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]

theorem compact_submersion_null_preimage {O K Z : Set (P × Q)}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hZ : ((volume : Measure P).prod volume) Z = 0)
    {φ : P × Q → P} {φ' : P × Q → (P × Q) →L[ℝ] P}
    (hm : Measurable φ) (hder : ∀ x ∈ O, HasFDerivAt φ (φ' x) x)
    (hcont : ∀ x ∈ O, ContinuousAt φ' x)
    (hreg : ∀ x ∈ K \ Z, Function.Surjective (φ' x))
    {N : Set P} (hN : MeasurableSet N) (hN0 : (volume : Measure P) N = 0) :
    (((volume : Measure P).prod volume).restrict K) (φ ⁻¹' N) = 0 := by
  let g : P → ℝ≥0∞ := N.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hN
  have hg1 : ∀ y, g y ≤ 1 := by
    intro y
    exact Set.indicator_le_self' (fun _ _ => zero_le) y
  have hg0 : ∫⁻ y, g y = 0 := by
    change (∫⁻ y, N.indicator (1 : P → ℝ≥0∞) y) = 0
    rw [lintegral_indicator_one hN,hN0]
  have hconstant : ∀ x ∈ O, ∀ r > 0, Metric.ball x r ⊆ O →
      TendstoUniformlyOn (fun _ : ℕ => φ') φ' atTop (Metric.ball x r) := by
    intro x hx r hr hsub
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Filter.Eventually.of_forall (fun _ _ _ => by simpa using hε)
  have hh := compact_surjective_pullback_zero hO hK hKO hZ
    (Φ := fun _ => φ) (Φ' := fun _ => φ') (φ' := φ')
    (fun _ => hder) hcont hreg
    hconstant
    (g := fun _ => g) (ρ := fun _ _ => 1) (B := 1) (M := 1)
    (by simp) (by simp) (fun _ => hg) (fun _ _ _ => le_rfl)
    (fun _ => hg1) (by simpa only [hg0] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0)))
  have he : (∫⁻ x in K, g (φ x) ∂(volume : Measure P).prod volume) = 0 := by
    exact tendsto_nhds_unique tendsto_const_nhds (by simpa only [one_mul] using hh)
  have hind : (fun x => g (φ x)) = (φ ⁻¹' N).indicator (fun _ => (1:ℝ≥0∞)) := by
    funext x
    classical
    by_cases hx : φ x ∈ N <;> simp [g,hx]
  rw [hind] at he
  change (∫⁻ x, (φ ⁻¹' N).indicator (1 : P × Q → ℝ≥0∞) x
    ∂((volume : Measure P).prod volume).restrict K) = 0 at he
  rw [lintegral_indicator_one (hN.preimage hm)] at he
  exact he

end BoltzmannNonuniqueness.GainPullback

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AngularPairTests
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Angular normalization of the hard-sphere collision kernel

The angular measure is the ordinary area measure `volume.toSphere`. Its mass is
`4 * π`; the absolute normal component integrates to `2 * π * ‖g‖`.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem integrable_abs_inner_sphereArea (g : Velocity) :
    Integrable (fun ω : Sphere => |inner ℝ g (ω : Velocity)|) sphereArea := by
  apply (integrable_const ‖g‖).mono' (by fun_prop)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_abs]
  have hω : ‖(ω : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  simpa only [hω, mul_one] using abs_real_inner_le_norm g (ω : Velocity)

/-- The loss-frequency angular normalization in the manuscript. -/
theorem integral_collisionKernel_sphereArea (v w : Velocity) :
    (∫ ω : Sphere, collisionKernel v w ω ∂sphereArea) = 2 * Real.pi * ‖v - w‖ :=
  integral_abs_inner_sphereArea (v - w)

theorem integrable_collisionKernel_sphereArea (v w : Velocity) :
    Integrable (fun ω : Sphere => collisionKernel v w ω) sphereArea :=
  integrable_abs_inner_sphereArea (v - w)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.UnifIntegrableCompat
attribute [-instance] _root_.OAI.closedSubmoduleNormedAddCommGroup _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val _root_.OAI.vonNeumannToStarSubalgebraIsClosed
/-!
# Uniform integrability compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. The two disagree on uniform integrability:

* `d13f23b`'s `UnifIntegrable f p μ` is `Tendsto (fun ε ↦ ⨆ i s (_ : μ s ≤ ε), eLpNorm (f i) p
  (μ.restrict s)) (𝓝 0) (𝓝 0)` (extended-real `ε`, `δ`, any set `s`); `0df444a`'s is the real
  `ε`-`δ` form over measurable sets with `eLpNorm (s.indicator (f i)) p μ`.
* `d13f23b`'s `UniformIntegrable f p μ` has two components, `UnifIntegrable f p μ` and a uniform
  bound; `0df444a`'s has three, measurability first. In `d13f23b` the bound alone gives
  measurability, since there `eLpNorm` is `∞` on a function that is not a.e. strongly measurable.
* `d13f23b`'s `UnifTight` takes `ε : ℝ≥0∞`; `0df444a`'s takes `ε : ℝ≥0`.

So that ported proofs keep `d13f23b`'s shapes (`obtain ⟨hu, C, hC⟩ := hf`, `intro ε hε` with
`ε : ℝ≥0∞`, `hu.ae_mono`, `hu.comp`), this file declares `OAI.UnifIntegrable`,
`OAI.UniformIntegrable` and `OAI.UnifTight`, which shadow Mathlib's inside `namespace OAI`, with
`d13f23b`'s API under `d13f23b`'s names, proved from `0df444a`'s. `OAI.UnifIntegrable` carries the
measurability of every member (Mathlib's `UnifIntegrable` together with it), so that
`OAI.UniformIntegrable` keeps `d13f23b`'s two components and is equivalent to Mathlib's
`UniformIntegrable` (`OAI.uniformIntegrable_iff_mathlib`).

`d13f23b`'s `unifIntegrable_iff` and `unifIntegrable_iff'` cannot be stated as equivalences here
(the right sides do not give measurability): the port rewrites their `mp` direction to
`OAI.UnifIntegrable.enn_spec` / `enn_spec'` and their `mpr` direction to
`OAI.UnifIntegrable.of_enn` / `of_enn'`, which take the measurability as a second argument.
-/

noncomputable section UnifIntegrableCompat

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace OAI

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
  {p : ℝ≥0∞} {f g : ι → α → β}

theorem uniformIntegrable_iff_mathlib :
    UniformIntegrable f p μ ↔ MeasureTheory.UniformIntegrable f p μ :=
  ⟨fun ⟨⟨u, hm⟩, b⟩ => ⟨hm, u, b⟩, fun ⟨hm, u, b⟩ => ⟨⟨u, hm⟩, b⟩⟩

/-! ### `UnifIntegrable` -/

namespace UnifIntegrable

/-- The `mp` direction of `d13f23b`'s `unifIntegrable_iff`. -/
theorem enn_spec (hf : UnifIntegrable f p μ) :
    ∀ ε > 0, ∃ δ > 0, ∀ i s, μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε := by
  intro ε hε
  rcases eq_top_or_lt_top ε with rfl | hεt
  · exact ⟨1, one_pos, fun _ _ _ => le_top⟩
  obtain ⟨δ, hδ, h⟩ := hf.1 (ENNReal.toReal_pos hε.ne' hεt.ne)
  refine ⟨ENNReal.ofReal δ, ENNReal.ofReal_pos.2 hδ, fun i s hs => ?_⟩
  have ht := measurableSet_toMeasurable μ s
  calc eLpNorm (f i) p (μ.restrict s)
      ≤ eLpNorm (f i) p (μ.restrict (toMeasurable μ s)) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono (subset_toMeasurable μ s) le_rfl)
    _ = eLpNorm ((toMeasurable μ s).indicator (f i)) p μ :=
        (eLpNorm_indicator_eq_eLpNorm_restrict ht).symm
    _ ≤ ENNReal.ofReal ε.toReal := h i _ ht (by rwa [measure_toMeasurable])
    _ = ε := ENNReal.ofReal_toReal hεt.ne

/-- The `mpr` direction of `d13f23b`'s `unifIntegrable_iff'`, with the measurability. -/
theorem of_enn' (h : ∀ ε > 0, ∃ δ > 0, ∀ i s, MeasurableSet s → μ s ≤ δ →
      eLpNorm (f i) p (μ.restrict s) ≤ ε) (hm : ∀ i, AEStronglyMeasurable (f i) μ) :
    UnifIntegrable f p μ := by
  refine ⟨fun ε hε => ?_, hm⟩
  obtain ⟨δ, hδ, hb⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hne : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(min δ 1).toReal, ENNReal.toReal_pos (lt_min hδ one_pos).ne' hne, fun i s hsm hs => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hsm]
  refine hb i s hsm (hs.trans ?_)
  rw [ENNReal.ofReal_toReal hne]
  exact min_le_left _ _

/-- The `mpr` direction of `d13f23b`'s `unifIntegrable_iff`, with the measurability. -/
theorem of_enn (h : ∀ ε > 0, ∃ δ > 0, ∀ i s, μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ) : UnifIntegrable f p μ :=
  of_enn' (fun ε hε => (h ε hε).imp fun _ ⟨hδ, hb⟩ => ⟨hδ, fun i s _ => hb i s⟩) hm

end UnifIntegrable

/-! ### `UniformIntegrable` -/

namespace UniformIntegrable

theorem toMathlib (hf : UniformIntegrable f p μ) : MeasureTheory.UniformIntegrable f p μ :=
  uniformIntegrable_iff_mathlib.1 hf

theorem spec (hp : p ≠ 0) (hp' : p ≠ ∞) (hfu : UniformIntegrable f p μ) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε := by
  rcases eq_top_or_lt_top ε with rfl | hεt
  · exact ⟨0, fun _ => le_top⟩
  obtain ⟨C, hC⟩ := hfu.toMathlib.spec hp hp' (ENNReal.toReal_pos hε.ne' hεt.ne)
  exact ⟨C, fun i => (hC i).trans (ENNReal.ofReal_toReal hεt.ne).le⟩

end UniformIntegrable

theorem uniformIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UniformIntegrable (fun _ : ι => g) p μ :=
  uniformIntegrable_iff_mathlib.2 (MeasureTheory.uniformIntegrable_const hp hp_ne_top hg)


/-! ### `UnifTight` -/

end OAI

end UnifIntegrableCompat
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityFourierMultiplier
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Nonconcentration of Lebesgue velocities on affine transport hyperplanes -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem inner_velocity_surjective {ξ : Velocity} (hξ : ξ ≠ 0) :
    Function.Surjective (innerSL ℝ ξ : Velocity →ₗ[ℝ] ℝ) := by
  intro y
  refine ⟨(y / inner ℝ ξ ξ) • ξ, ?_⟩
  have hn : inner ℝ ξ ξ ≠ 0 := (real_inner_self_pos.mpr hξ).ne'
  change inner ℝ ξ ((y / inner ℝ ξ ξ) • ξ) = y
  rw [real_inner_smul_right]
  exact div_mul_cancel₀ y hn

theorem affine_velocity_hyperplane_null (τ : ℝ) {ξ : Velocity} (hξ : ξ ≠ 0) :
    (volume : Measure Velocity) {v | τ + inner ℝ ξ v = 0} = 0 := by
  have ha : ∀ᵐ y : ℝ ∂volume, y ∈ ({-τ} : Set ℝ)ᶜ := by
    simpa only [mem_compl_iff,mem_singleton_iff] using volume.ae_ne (-τ)
  have h := (ae_comp_linearMap_mem_iff (innerSL ℝ ξ : Velocity →ₗ[ℝ] ℝ)
    (volume : Measure Velocity) (volume : Measure ℝ) (inner_velocity_surjective hξ)
    (measurableSet_singleton (-τ)).compl).mpr ha
  have hz : ∀ᵐ v : Velocity ∂volume, ¬(τ + inner ℝ ξ v = 0) := by
    filter_upwards [h] with v hv he
    apply hv
    change inner ℝ ξ v = -τ
    linarith
  simpa only [not_not] using ae_iff.mp hz

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Nonnegative polar integrals for the physical three-dimensional velocity space -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem lintegral_velocity_polar {F : Velocity → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ n : Sphere, ∫⁻ r : Ioi (0:ℝ), F ((r:ℝ) • n.1)
      ∂Measure.volumeIoiPow 2 ∂sphereArea := by
  let H := homeomorphUnitSphereProd Velocity
  have hp := (volume : Measure Velocity).measurePreserving_homeomorphUnitSphereProd
  have hFm : Measurable (fun p : Sphere × Ioi (0:ℝ) => F ((p.2:ℝ) • p.1.1)) := by
    apply hF.comp
    fun_prop
  calc
    (∫⁻ x, F x) = ∫⁻ x : ({0}ᶜ : Set Velocity), F x ∂((volume : Measure Velocity).comap (↑)) := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl,restrict_compl_singleton]
    _ = ∫⁻ p : Sphere × Ioi (0:ℝ), F ((p.2:ℝ) • p.1.1)
        ∂sphereArea.prod (Measure.volumeIoiPow 2) := by
      have hh := hp.lintegral_comp_emb H.measurableEmbedding
        (fun p => F (H.symm p))
      simpa only [H,sphereArea,Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe,finrank_euclideanSpace,
        Fintype.card_fin,Nat.reduceSub] using hh
    _ = _ := lintegral_prod _ hFm.aemeasurable

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Measure preservation for a hard-sphere collision

For each fixed unit normal, the pre/post-collisional map is an orthogonal
involution on the six-dimensional velocity-pair space. Its Euclidean norm is
implemented with `WithLp 2`; the final measure statement uses the ordinary
product of the two three-dimensional Lebesgue measures.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- Fixed-normal pre/post collision change of variables preserves product Lebesgue measure. -/
theorem scatterPair_measurePreserving (ω : Velocity) (hω : ‖ω‖ = 1) :
    MeasurePreserving (scatterPair ω)
      ((volume : Measure Velocity).prod volume)
      ((volume : Measure Velocity).prod volume) := by
  have h := (WithLp.volume_preserving_ofLp Velocity Velocity).comp
    ((scatterLinearIsometryEquiv ω hω).measurePreserving.comp
      (WithLp.volume_preserving_toLp Velocity Velocity))
  exact h

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MarginalUniformIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-fibre integration preserves uniform integrability -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem eLpNorm_integral_le {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X × Y → ℝ} (hf : Measurable f) :
    eLpNorm (fun x => ∫ y, f (x,y) ∂ν) 1 μ ≤ eLpNorm f 1 (μ.prod ν) := by
  rw [eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_one_eq_lintegral_enorm,lintegral_prod _ hf.enorm.aemeasurable]
  exact lintegral_mono (fun x => enorm_integral_le_lintegral_enorm _)

end BoltzmannNonuniqueness.Compactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_VaryingBoundedMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Multiplication by a varying uniformly bounded function preserves L1 smallness -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

theorem tendsto_L1_bounded_mul_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f a : ℕ → X → ℝ} (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (ham : ∀ n, AEStronglyMeasurable (a n) μ)
    (hf : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |a n x| ≤ C) :
    Tendsto (fun n => eLpNorm (fun x => a n x*f n x) 1 μ) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n => eLpNorm (fun x => C*f n x) 1 μ) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) hf
      (Or.inr (by simp : ‖C‖ₑ ≠ ⊤))
    simpa only [← eLpNorm_const_smul,Pi.smul_def,smul_eq_mul,mul_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
    (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
  filter_upwards [ha] with n hn
  apply eLpNorm_mono_ae
  filter_upwards [hn] with x hx
  change |a n x*f n x| ≤ |C*f n x|
  rw [abs_mul,abs_mul,abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded measurable multipliers preserve uniform integrability -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_bounded_multiplier
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) {a : X → ℝ} (ha : Measurable a)
    (C : ℝ≥0) (hC : ∀ x, |a x| ≤ C) :
    UniformIntegrable (fun n x => a x*f n x) 1 μ := by
  let D : ℝ≥0 := C+1
  have hD : (0 : ℝ≥0∞) < D := by simp [D]
  have hb (n : ℕ) (ν : Measure X) (hν : ν ≤ μ) :
      eLpNorm (fun x => a x*f n x) 1 ν ≤ (D : ℝ≥0∞)*eLpNorm (f n) 1 ν := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    filter_upwards [] with x
    apply NNReal.coe_le_coe.mp
    change ‖a x*f n x‖ ≤ (D:ℝ)*‖f n x‖
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right ((hC x).trans (by dsimp [D] <;> norm_num)) (abs_nonneg _)
  constructor
  · apply OAI.UnifIntegrable.of_enn
    intro ε hε
    obtain ⟨δ,hδ,hδsmall⟩ := OAI.UnifIntegrable.enn_spec hf.1 (ε/(D:ℝ≥0∞))
      (ENNReal.div_pos hε.ne' ENNReal.coe_ne_top)
    refine ⟨δ,hδ,fun n s hs => ?_⟩
    calc
      _ ≤ (D:ℝ≥0∞)*eLpNorm (f n) 1 (μ.restrict s) := hb n _ Measure.restrict_le_self
      _ ≤ (D:ℝ≥0∞)*(ε/(D:ℝ≥0∞)) := mul_le_mul' le_rfl (hδsmall n s hs)
      _ = ε := ENNReal.mul_div_cancel hD.ne' ENNReal.coe_ne_top
    exact fun n => ha.aestronglyMeasurable.mul (hf.aestronglyMeasurable n)
  · obtain ⟨B,hB⟩ := hf.2
    refine ⟨D*B,fun n => ?_⟩
    exact (hb n μ le_rfl).trans (by simpa only [ENNReal.coe_mul] using mul_le_mul' le_rfl (hB n))

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform L¹ approximation preserves uniform integrability

This is the analytic bridge from the fixed outer-annulus majorants and the
vanishing small-annulus collision integrals to full uniform integrability.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_approximation {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ℕ → X → ℝ} {g : ℕ → ℕ → X → ℝ}
    (hg : ∀ j, UniformIntegrable (g j) 1 μ)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ j : ℕ, ∀ n,
      eLpNorm (fun x => f n x-g j n x) 1 μ ≤ ε)
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) :
    UniformIntegrable f 1 μ := by
  have htri (j n : ℕ) (ν : Measure X) (hν : ν ≤ μ) : eLpNorm (f n) 1 ν ≤
      eLpNorm (fun x => f n x-g j n x) 1 ν+eLpNorm (g j n) 1 ν := by
    have he : f n = (fun x => f n x-g j n x)+(g j n) := by funext x; simp
    calc
      _ = eLpNorm ((fun x => f n x-g j n x)+(g j n)) 1 ν :=
        congrArg (fun h : X → ℝ => eLpNorm h 1 ν) he
      _ ≤ _ := eLpNorm_add_le (hf := ((hfm n).sub ((hg j).aestronglyMeasurable n)).mono_measure hν)
          (hg := ((hg j).aestronglyMeasurable n).mono_measure hν) (by norm_num)
  constructor
  · apply OAI.UnifIntegrable.of_enn
    intro ε hε
    obtain ⟨j,hj⟩ := happrox (ε/2) (ε.half_pos hε.ne')
    obtain ⟨δ,hδ,hgδ⟩ := OAI.UnifIntegrable.enn_spec (hg j).1 (ε/2) (ε.half_pos hε.ne')
    refine ⟨δ,hδ,?_⟩
    intro n s hs
    calc
      _ ≤ eLpNorm (fun x => f n x-g j n x) 1 (μ.restrict s)+
          eLpNorm (g j n) 1 (μ.restrict s) := htri j n _ Measure.restrict_le_self
      _ ≤ ε/2+ε/2 := add_le_add
        ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hj n)) (hgδ n s hs)
      _ = ε := ε.add_halves
    exact hfm
  · obtain ⟨j,hj⟩ := happrox 1 (by norm_num)
    obtain ⟨C,hC⟩ := (hg j).2
    refine ⟨1+C,?_⟩
    intro n
    calc
      _ ≤ eLpNorm (fun x => f n x-g j n x) 1 μ+eLpNorm (g j n) 1 μ := htri j n _ le_rfl
      _ ≤ 1+C := add_le_add (hj n) (hC n)
      _ = _ := by simp

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedKernelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Conditional tensor products controlled by a single mass marginal -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem normalizedTensor_measurable {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hf : Measurable f) (hg : Measurable g) :
    Measurable (normalizedTensor d f g) := by
  unfold normalizedTensor
  fun_prop

omit [MeasurableSpace X] in
theorem normalizedTensor_fiber_integral {d : X → ℝ} {f g : X × Y → ℝ} (x : X) :
    (∫ y, normalizedTensor d f g (x,y) ∂ν.prod ν) =
      (∫ v, f (x,v) ∂ν)*(∫ w, g (x,w) ∂ν)/(1+d x) := by
  simp only [normalizedTensor,integral_div]
  rw [integral_prod_mul (fun v => f (x,v)) (fun w => g (x,w))]

theorem normalizedTensor_integrable {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (hfi : Integrable f (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (hfd : ∀ᵐ x ∂μ, (∫ v, f (x,v) ∂ν) ≤ d x) :
    Integrable (normalizedTensor d f g) (μ.prod (ν.prod ν)) := by
  have hnon (z : X × (Y × Y)) : 0 ≤ normalizedTensor d f g z :=
    div_nonneg (mul_nonneg (hf _) (hg _)) (by linarith [hd0 z.1])
  have hnorm x : (∫ y, ‖normalizedTensor d f g (x,y)‖ ∂ν.prod ν) =
      (∫ v, f (x,v) ∂ν)*(∫ w, g (x,w) ∂ν)/(1+d x) := by
    simp only [Real.norm_of_nonneg (hnon _)]
    exact normalizedTensor_fiber_integral x
  apply (integrable_prod_iff (normalizedTensor_measurable hd hfm hgm).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hfi.prod_right_ae,hgi.prod_right_ae] with x hfx hgx
    exact (hfx.mul_prod hgx).div_const (1+d x)
  · apply hgi.integral_prod_left.mono'
      ((normalizedTensor_measurable hd hfm hgm).norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    filter_upwards [hfd] with x hx
    rw [hnorm,Real.norm_of_nonneg (div_nonneg
      (mul_nonneg (integral_nonneg (μ := ν) (f := fun v => f (x,v)) (fun v => hf (x,v))) (integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v))))
      (by linarith [hd0 x]))]
    apply (div_le_iff₀ (by linarith [hd0 x] : 0 < 1+d x)).mpr
    nlinarith [integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v)),
      mul_le_mul_of_nonneg_right hx (integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v)))]

theorem normalizedTensor_L1_le {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (hfi : Integrable f (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (hfd : ∀ᵐ x ∂μ, (∫ v, f (x,v) ∂ν) ≤ d x) :
    eLpNorm (normalizedTensor d f g) 1 (μ.prod (ν.prod ν)) ≤ eLpNorm g 1 (μ.prod ν) := by
  have ht := normalizedTensor_integrable hd hd0 hfm hgm hf hg hfi hgi hfd
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm ht,
    eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hgi]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_prod _ ht.norm,integral_prod _ hgi.norm]
  apply integral_mono_ae ht.integral_norm_prod_left hgi.integral_norm_prod_left
  filter_upwards [hfd] with x hx
  have hgn := integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v))
  have hfn := integral_nonneg (μ := ν) (f := fun v => f (x,v)) (fun v => hf (x,v))
  have hn y : 0 ≤ normalizedTensor d f g (x,y) :=
    div_nonneg (mul_nonneg (hf _) (hg _)) (by linarith [hd0 x])
  simp only [Real.norm_of_nonneg (hn _),Real.norm_of_nonneg (hg _)]
  rw [normalizedTensor_fiber_integral]
  apply (div_le_iff₀ (by linarith [hd0 x] : 0 < 1+d x)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hx hgn]

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Truncating a mass-normalized velocity pair costs only its L1 tail -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem fiberMass_measurable {f : X × Y → ℝ} (hf : Measurable f) :
    Measurable (fiberMass ν f) := hf.stronglyMeasurable.integral_prod_right'.measurable

theorem normalizedTensor_norm_swap {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (normalizedTensor d f g) 1 (μ.prod (ν.prod ν)) =
      eLpNorm (normalizedTensor d g f) 1 (μ.prod (ν.prod ν)) := by
  have hp := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := ν))
  calc
    _ = eLpNorm ((normalizedTensor d g f) ∘ (fun z : X × (Y × Y) => (z.1,z.2.2,z.2.1)))
        1 (μ.prod (ν.prod ν)) := by
      congr 1
      funext z
      dsimp only [normalizedTensor,Function.comp_apply]
      rw [mul_comm]
    _ = _ := eLpNorm_comp_measurePreserving
      (normalizedTensor_measurable hd hg hf).aestronglyMeasurable hp

theorem normalizedPair_integrable {f : X × Y → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) (hfi : Integrable f (μ.prod ν)) :
    Integrable (normalizedPair ν f) (μ.prod (ν.prod ν)) :=
  normalizedTensor_integrable (fiberMass_measurable hfm)
    (fun x => integral_nonneg (fun v => hf (x,v))) hfm hfm hf hf hfi hfi
    (ae_of_all _ (fun _ => le_rfl))

theorem normalizedPair_truncation_error {f u : X × Y → ℝ}
    (hfm : Measurable f) (hum : Measurable u)
    (hf : ∀ z, 0 ≤ f z) (hu : ∀ z, 0 ≤ u z) (huf : ∀ z, u z ≤ f z)
    (hfi : Integrable f (μ.prod ν)) (hui : Integrable u (μ.prod ν)) :
    eLpNorm (fun z => normalizedPair ν f z-
      normalizedTensor (fiberMass ν f) u u z) 1 (μ.prod (ν.prod ν)) ≤
      2*eLpNorm (fun z => f z-u z) 1 (μ.prod ν) := by
  have hm := fiberMass_measurable (ν := ν) hfm
  have hn x : 0 ≤ fiberMass ν f x := integral_nonneg (fun v => hf (x,v))
  have hd : ∀ᵐ x ∂μ, (∫ v, f (x,v) ∂ν) ≤ fiberMass ν f x := ae_of_all _ (fun _ => le_rfl)
  have hud : ∀ᵐ x ∂μ, (∫ v, u (x,v) ∂ν) ≤ fiberMass ν f x := by
    filter_upwards [hfi.prod_right_ae,hui.prod_right_ae] with x hfx hux
    exact integral_mono hux hfx (fun v => huf (x,v))
  have hsub z : 0 ≤ f z-u z := sub_nonneg.mpr (huf z)
  have hA := normalizedTensor_L1_le hm hn hfm (hfm.sub hum) hf hsub hfi (hfi.sub hui) hd
  have hB := normalizedTensor_L1_le hm hn hum (hfm.sub hum) hu hsub hui (hfi.sub hui) hud
  have he : (fun z => normalizedPair ν f z-normalizedTensor (fiberMass ν f) u u z) =
      normalizedTensor (fiberMass ν f) f (f-u)+normalizedTensor (fiberMass ν f) (f-u) u := by
    funext z
    dsimp only [normalizedPair,normalizedTensor,Pi.add_apply,Pi.sub_apply]
    ring
  rw [he]
  calc
    _ ≤ eLpNorm (normalizedTensor (fiberMass ν f) f (f-u)) 1 (μ.prod (ν.prod ν))+
        eLpNorm (normalizedTensor (fiberMass ν f) (f-u) u) 1 (μ.prod (ν.prod ν)) :=
      eLpNorm_add_le (hf := (normalizedTensor_measurable hm hfm (hfm.sub hum)).aestronglyMeasurable)
        (hg := (normalizedTensor_measurable hm (hfm.sub hum) hum).aestronglyMeasurable) (by norm_num)
    _ = eLpNorm (normalizedTensor (fiberMass ν f) f (f-u)) 1 (μ.prod (ν.prod ν))+
        eLpNorm (normalizedTensor (fiberMass ν f) u (f-u)) 1 (μ.prod (ν.prod ν)) := by
      rw [normalizedTensor_norm_swap hm (hfm.sub hum) hum]
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add hA hB

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionWeakMarginals
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measure preservation and integrability for the full hard-sphere collision rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem scatterTriple_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (scatterTriple (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  let ν := μ.prod (volume : Measure (Velocity × Velocity))
  have hf (ω : Sphere) : MeasurePreserving
      (fun p : X × (Velocity × Velocity) => (p.1,scatterPair ω p.2)) ν ν := by
    have hω : ‖(ω : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
    have hh := (MeasurePreserving.id μ).prod (scatterPair_measurePreserving (ω : Velocity) hω)
    have he : (Prod.map id (scatterPair (ω : Velocity))) =
        (fun p : X × (Velocity × Velocity) => (p.1,scatterPair ω p.2)) := by
      funext p
      rfl
    rw [he] at hh
    simpa only [ν,Measure.volume_eq_prod] using hh
  have hm : Measurable (fun z : Sphere × (X × (Velocity × Velocity)) =>
      (z.2.1,scatterPair z.1 z.2.2)) := by
    unfold scatterPair scatterLeft scatterRight normalComponent
    fun_prop
  have hh := (MeasurePreserving.id sphereArea).skew_product (μc := ν) (μd := ν)
    (g := fun (ω : Sphere) (p : X × (Velocity × Velocity)) => (p.1,scatterPair ω p.2)) hm
    (ae_of_all _ (fun ω => (hf ω).map_eq))
  have h₁ : MeasurePreserving Prod.swap (ν.prod sphereArea) (sphereArea.prod ν) :=
    Measure.measurePreserving_swap
  have h₂ : MeasurePreserving Prod.swap (sphereArea.prod ν) (ν.prod sphereArea) :=
    Measure.measurePreserving_swap
  exact h₂.comp (hh.comp h₁)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_ra56ad6_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
theorem collisionGrouping_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (collisionGrouping (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) := by
  have ha := (measurePreserving_prodAssoc μ (volume : Measure Velocity) (volume : Measure Velocity)).symm.prod
    (MeasurePreserving.id sphereArea)
  have hb := measurePreserving_prodAssoc (μ.prod (volume : Measure Velocity))
    (volume : Measure Velocity) sphereArea
  have he : (⇑(collisionGrouping (X := X))) =
      MeasurableEquiv.prodAssoc ∘ Prod.map (MeasurableEquiv.prodAssoc.symm)
        (id : Sphere → Sphere) := by
    funext z
    rfl
  rw [he]
  simpa only [Measure.volume_eq_prod] using hb.comp ha

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Weak convergence of the actual full collision rates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem normalizedKernel_measurable : Measurable (normalizedKernel (X := X)) := by
  unfold normalizedKernel collisionKernel normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem normalizedKernel_bound (z : (X × (Velocity × Velocity)) × Sphere) :
    |normalizedKernel z| ≤ 1 := by
  unfold normalizedKernel
  have hw : 0 < 1+‖z.1.2.1‖+‖z.1.2.2‖ := by positivity
  rw [abs_of_nonneg (div_nonneg (collisionKernel_nonneg _ _ _) hw.le),div_le_one₀ hw]
  exact (collisionKernel_le_norm _ _ _).trans ((norm_sub_le _ _).trans (by linarith))

omit [MeasurableSpace X] in
theorem preRate_eq_normalized (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    preRate f z = normalizedKernel z*pairDensity f z.1 := by
  have hw : 1+‖z.1.2.1‖+‖z.1.2.2‖ ≠ 0 := ne_of_gt (by positivity)
  unfold preRate normalizedKernel pairDensity
  field_simp

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SphereDirectionAbsolute
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A measurable direction map with an arbitrary value at zero -/

noncomputable section
open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem sphereDirection_measurable (e : Sphere) : Measurable (sphereDirection e) := by
  apply Measurable.subtype_mk
  change Measurable (fun x => (sphereDirection e x).1)
  have he : (fun x => (sphereDirection e x).1) =
      fun x : Velocity => if x = 0 then e.1 else ‖x‖⁻¹ • x := by
    funext x
    simp only [sphereDirection,NormedSpace.normalize]
    split <;> rfl
  rw [he]
  exact measurable_const.ite (measurableSet_singleton 0) (measurable_norm.inv.smul measurable_id)

theorem sphereDirection_smul (e n : Sphere) {r : ℝ} (hr : 0 < r) :
    sphereDirection e (r • n.1) = n := by
  have hn : n.1 ≠ 0 := by
    intro h
    have := mem_sphere_zero_iff_norm.mp n.property
    rw [h,norm_zero] at this
    norm_num at this
  have h : r • n.1 ≠ 0 := smul_ne_zero hr.ne' hn
  apply Subtype.ext
  simp only [sphereDirection,dite_eq_right h,NormedSpace.normalize,norm_smul,
    Real.norm_eq_abs,abs_of_pos hr,mem_sphere_zero_iff_norm.mp n.property,mul_one,smul_smul,
    inv_mul_cancel₀ hr.ne',one_smul]

end BoltzmannNonuniqueness

end

end

section

/-! # Lifting sphere tests to the unit velocity ball -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem sphereBallLift_measurable (e : Sphere) {f : Sphere → ℝ≥0∞} (hf : Measurable f) :
    Measurable (sphereBallLift e f) := by
  exact (hf.comp (sphereDirection_measurable e)).ite
    (measurableSet_lt measurable_norm measurable_const) measurable_const

theorem sphereBallLift_radial (e n : Sphere) (f : Sphere → ℝ≥0∞)
    (r : Ioi (0:ℝ)) :
    sphereBallLift e f ((r:ℝ) • n.1) = if (r:ℝ) < 1 then f n else 0 := by
  rw [sphereBallLift,sphereDirection_smul e n r.property,norm_smul,
    Real.norm_eq_abs,abs_of_pos r.property,mem_sphere_zero_iff_norm.mp n.property,mul_one]

theorem sphereBallLift_integral (e : Sphere) {f : Sphere → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, sphereBallLift e f x) = (3:ℝ≥0∞)⁻¹ * ∫⁻ n, f n ∂sphereArea := by
  rw [lintegral_velocity_polar (sphereBallLift_measurable e hf)]
  simp_rw [sphereBallLift_radial]
  have hi (n : Sphere) :
      (∫⁻ r : Ioi (0:ℝ), if (r:ℝ) < 1 then f n else 0 ∂Measure.volumeIoiPow 2) =
        (3:ℝ≥0∞)⁻¹*f n := by
    change (∫⁻ r, (Iio (⟨1,by norm_num⟩ : Ioi (0:ℝ))).indicator (fun _ => f n) r
      ∂Measure.volumeIoiPow 2) = _
    rw [lintegral_indicator measurableSet_Iio,setLIntegral_const,Measure.volumeIoiPow_apply_Iio]
    norm_num only [Nat.reduceAdd,one_pow]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3)]
    norm_num [mul_comm]
  simp_rw [hi]
  exact lintegral_const_mul _ hf

end BoltzmannNonuniqueness

end

end

section

/-! # Surface measure is dominated by directions of Lebesgue points in the unit ball -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness

theorem sphereArea_absolutelyContinuous_directions (e : Sphere) :
    sphereArea ≪ Measure.map (sphereDirection e)
      ((volume : Measure Velocity).restrict (Metric.ball 0 1)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply (sphereDirection_measurable e) hN] at hN0
  have hn : ∀ᵐ x : Velocity ∂volume.restrict (Metric.ball 0 1), sphereDirection e x ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not,Set.preimage] using hN0
  have hall := (ae_restrict_iff' measurableSet_ball).mp hn
  have hz : (∫⁻ x : Velocity, sphereBallLift e (N.indicator (fun _ => (1:ℝ≥0∞))) x) = 0 := by
    calc
      _ = ∫⁻ _x : Velocity, (0:ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [hall] with x hx
        by_cases hb : ‖x‖ < 1
        · have hxb : x ∈ Metric.ball (0 : Velocity) 1 := by
            simpa only [Metric.mem_ball,dist_zero_right] using hb
          simp only [sphereBallLift,ite_eq_left hb,Set.indicator_of_notMem (hx hxb)]
        · simp only [sphereBallLift,ite_eq_right hb]
      _ = 0 := lintegral_zero
  rw [sphereBallLift_integral e (measurable_const.indicator hN)] at hz
  change (3:ℝ≥0∞)⁻¹ * (∫⁻ n, N.indicator (1 : Sphere → ℝ≥0∞) n ∂sphereArea) = 0 at hz
  rw [lintegral_indicator_one hN] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedVelocityIntegral
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Absolute entropy for bounded densities with bounded velocity support -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X]

theorem bounded_velocity_integrable {μ : Measure X} [IsFiniteMeasure μ] {N A : ℝ}
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfb : ∀ p, |f p| ≤ A)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) : Integrable f (μ.prod (volume : Measure Velocity)) := by
  have hi : Integrable ((Metric.closedBall (0 : Velocity) N).indicator (fun _ : Velocity => A)) :=
    (integrableOn_const (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  apply (hi.comp_snd μ).mono' hfm.aestronglyMeasurable
  filter_upwards [] with p
  change ‖f p‖ ≤ (Metric.closedBall (0 : Velocity) N).indicator (fun _ => A) p.2
  by_cases hp : p.2 ∈ Metric.closedBall 0 N
  · rw [indicator_of_mem hp,Real.norm_eq_abs]
    exact hfb p
  · have hv : N < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
    rw [hfs p hv,norm_zero,indicator_of_notMem hp]

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyUniformIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Joint value and velocity truncation controlled by absolute entropy -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem entropyTruncation_measurable (R : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (entropyTruncation R f) :=
  Measurable.ite ((measurableSet_le measurable_snd.norm measurable_const).inter
    (measurableSet_le hf measurable_const)) hf measurable_const

omit [MeasurableSpace X] in
theorem entropyGauge_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ entropyGauge f p := mul_nonneg (hf p) (by positivity)

omit [MeasurableSpace X] in
theorem entropyGauge_ge_density {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    f p ≤ entropyGauge f p := by
  have hs := mul_nonneg (hf p) (sq_nonneg ‖p.2‖)
  have hl := mul_nonneg (hf p) (abs_nonneg (Real.log (f p)))
  unfold entropyGauge
  nlinarith

omit [MeasurableSpace X] in
theorem entropyTruncation_bounds (R : ℝ) {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ entropyTruncation R f p ∧ entropyTruncation R f p ≤ Real.exp R := by
  unfold entropyTruncation
  split_ifs with hp
  · exact ⟨hf p,hp.2⟩
  · exact ⟨le_rfl,(Real.exp_pos R).le⟩

omit [MeasurableSpace X] in
theorem entropyTruncation_support (R : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity)
    (hp : R < ‖p.2‖) : entropyTruncation R f p = 0 := by
  simp only [entropyTruncation,not_le.mpr hp,false_and,ite_false, if_false]

omit [MeasurableSpace X] in
theorem entropyTruncation_error {R : ℝ} (hR : 1 ≤ R) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    |f p-entropyTruncation R f p| ≤ entropyGauge f p/R := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  unfold entropyTruncation
  split_ifs with hp
  · rw [sub_self,abs_zero]
    exact div_nonneg (entropyGauge_nonneg hf p) hR0.le
  · rw [sub_zero,abs_of_nonneg (hf p)]
    apply (le_div_iff₀ hR0).mpr
    have hn := hf p
    have he : 0 ≤ ‖p.2‖^2 := sq_nonneg _
    have hl : 0 ≤ |Real.log (f p)| := abs_nonneg _
    by_cases hv : ‖p.2‖ ≤ R
    · have hbig : Real.exp R < f p := lt_of_not_ge (fun ha => hp ⟨hv,ha⟩)
      have hlog : R ≤ Real.log (f p) := by
        simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos R) hbig.le
      have hh := mul_le_mul_of_nonneg_left (hlog.trans (le_abs_self _)) hn
      unfold entropyGauge
      nlinarith [mul_nonneg hn he]
    · have hvR : R < ‖p.2‖ := lt_of_not_ge hv
      have hs : R ≤ ‖p.2‖^2 := by nlinarith [norm_nonneg p.2]
      have hh := mul_le_mul_of_nonneg_left hs hn
      unfold entropyGauge
      nlinarith [mul_nonneg hn hl]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform L1 approximation by bounded velocity truncations -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem integrable_of_entropyGauge {μ : Measure (X × Velocity)} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyGauge f) μ) : Integrable f μ := by
  apply hi.mono' hfm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_of_nonneg (hf p)]
    exact entropyGauge_ge_density hf p)

theorem entropyTruncation_integrable {μ : Measure X} [IsFiniteMeasure μ]
    (R : ℝ) {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    Integrable (entropyTruncation R f) (μ.prod volume) :=
  bounded_velocity_integrable (entropyTruncation_measurable R hfm)
    (fun p => (abs_of_nonneg (entropyTruncation_bounds R hf p).1).trans_le
      (entropyTruncation_bounds R hf p).2) (entropyTruncation_support R f)

theorem entropyTruncation_L1_bound {μ : Measure X} [IsFiniteMeasure μ]
    {R C : ℝ} (hR : 1 ≤ R) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyGauge f) (μ.prod volume))
    (hb : (∫ p, entropyGauge f p ∂μ.prod volume) ≤ C) :
    eLpNorm (fun p => f p-entropyTruncation R f p) 1 (μ.prod volume) ≤ ENNReal.ofReal (C/R) := by
  have hei := (integrable_of_entropyGauge hfm hf hi).sub (entropyTruncation_integrable R hfm hf)
  change Integrable (fun p => f p-entropyTruncation R f p) (μ.prod volume) at hei
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hei]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ p, entropyGauge f p/R ∂μ.prod volume :=
      integral_mono hei.norm (hi.div_const R) (fun p => by
        simpa only [Real.norm_eq_abs] using entropyTruncation_error hR hf p)
    _ = (∫ p, entropyGauge f p ∂μ.prod volume)/R := integral_div R _
    _ ≤ C/R := div_le_div_of_nonneg_right hb (zero_le_one.trans hR)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform entropy and velocity moments imply L1 compactness hypotheses -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

 theorem exists_entropyTruncation_radius (C : ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ j : ℕ, ENNReal.ofReal (C/((j:ℝ)+1)) ≤ ε := by
  have h : Tendsto (fun j : ℕ => C/((j:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (C/((j:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h
  obtain ⟨j,hj⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨j,hj.le⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityCutoffEntropyError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform integrability of the linear velocity moment from entropy and energy -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem linearMoment_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (linearMoment f) := (measurable_const.add measurable_snd.norm).mul hf

theorem velocityLinearCut_measurable (R : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (velocityLinearCut R f) := (linearMoment_measurable hf).ite
      (measurableSet_le measurable_snd.norm measurable_const) measurable_const

theorem linearMoment_integrable {μ : Measure (X × Velocity)} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyGauge f) μ) :
    Integrable (linearMoment f) μ := by
  apply (hi.const_mul 2).mono' (linearMoment_measurable hfm).aestronglyMeasurable
  filter_upwards [] with p
  change ‖(1+‖p.2‖)*f p‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hf p))]
  have h : 1+‖p.2‖ ≤ 2*(1+‖p.2‖^2+|Real.log (f p)|) := by
    nlinarith [sq_nonneg (‖p.2‖-1),abs_nonneg (Real.log (f p))]
  simpa only [linearMoment,entropyGauge,mul_assoc,mul_left_comm,mul_comm] using
    mul_le_mul_of_nonneg_right h (hf p)

omit [MeasurableSpace X] in
theorem velocityLinearCut_error {R : ℝ} (hR : 0 < R) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    |linearMoment f p-velocityLinearCut R f p| ≤ 2*entropyGauge f p/R := by
  by_cases hp : ‖p.2‖ ≤ R
  · simp only [velocityLinearCut,ite_eq_left hp,sub_self,abs_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (entropyGauge_nonneg hf p)) hR.le
  · have hr : R ≤ ‖p.2‖ := (lt_of_not_ge hp).le
    simp only [velocityLinearCut,ite_eq_right hp,sub_zero,linearMoment]
    rw [abs_of_nonneg (mul_nonneg (by positivity) (hf p))]
    apply (le_div_iff₀ hR).mpr
    have hcoeff : (1+‖p.2‖)*R ≤ 2*(1+‖p.2‖^2+|Real.log (f p)|) := by
      have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1+‖p.2‖ by positivity)
      nlinarith [sq_nonneg (‖p.2‖-1),abs_nonneg (Real.log (f p))]
    simpa only [entropyGauge,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_right hcoeff (hf p)

theorem velocityLinearCut_integrable {μ : Measure (X × Velocity)} (R : ℝ)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) μ) : Integrable (velocityLinearCut R f) μ := by
  apply (linearMoment_integrable hfm hf hi).mono'
    (velocityLinearCut_measurable R hfm).aestronglyMeasurable
  filter_upwards [] with p
  have hn : 0 ≤ linearMoment f p := mul_nonneg (by positivity) (hf p)
  by_cases hp : ‖p.2‖ ≤ R
  · rw [velocityLinearCut,ite_eq_left hp,Real.norm_of_nonneg hn]
  · rw [velocityLinearCut,ite_eq_right hp,norm_zero]
    exact hn

theorem velocityLinearCut_L1_error {μ : Measure (X × Velocity)} {R C : ℝ} (hR : 0 < R)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) μ) (hb : (∫ p, entropyGauge f p ∂μ) ≤ C) :
    eLpNorm (fun p => linearMoment f p-velocityLinearCut R f p) 1 μ ≤ ENNReal.ofReal (2*C/R) := by
  have he := (linearMoment_integrable hfm hf hi).sub (velocityLinearCut_integrable R hfm hf hi)
  change Integrable (fun p => linearMoment f p-velocityLinearCut R f p) μ at he
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm he]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ p, 2*entropyGauge f p/R ∂μ :=
      integral_mono he.norm ((hi.const_mul 2).div_const R) (fun p => by
        simpa only [Real.norm_eq_abs] using velocityLinearCut_error hR hf p)
    _ = 2*(∫ p, entropyGauge f p ∂μ)/R := by rw [integral_div,integral_const_mul]
    _ ≤ 2*C/R := div_le_div_of_nonneg_right (by linarith) hR.le

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Compactly supported unit-mass velocity kernels of arbitrarily small radius -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem exists_velocity_mollifier {δ : ℝ} (hδ : 0 < δ) :
    ∃ χ : C(Velocity,ℝ), HasCompactSupport χ ∧ Integrable χ ∧
      (∀ a, 0 ≤ χ a) ∧ (∫ a, χ a) = 1 ∧ (∀ a, χ a ≠ 0 → ‖a‖ < δ) := by
  let b : ContDiffBump (0 : Velocity) := ⟨δ/2,δ,by linarith,by linarith⟩
  let χ : C(Velocity,ℝ) := ⟨b.normed volume,b.continuous_normed⟩
  refine ⟨χ,b.hasCompactSupport_normed,b.integrable_normed,?_,b.integral_normed,?_⟩
  · exact b.nonneg_normed
  · intro a ha
    have hs : a ∈ Function.support (b.normed (volume : Measure Velocity)) := ha
    rw [b.support_normed_eq] at hs
    simpa only [Metric.mem_ball,dist_zero_right] using hs

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_L1TruncationCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Limits of the truncations and their uniform L¹ distance bounds -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}

theorem integral_abs_le_of_eLpNorm_le {v : X → ℝ} (hv : Integrable v μ)
    {B : ℝ} (hB : 0 ≤ B) (he : eLpNorm v 1 μ ≤ ENNReal.ofReal B) :
    ∫ x, |v x| ∂μ ≤ B := by
  have hh : ENNReal.ofReal (∫ x, |v x| ∂μ) = eLpNorm v 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    simpa only [Real.norm_eq_abs] using ofReal_integral_norm_eq_lintegral_enorm hv
  rw [← hh] at he
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp he

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedCollisionRates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The first-velocity-moment weight of the normalized pair is integrable -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem pairVelocityWeight_measurable : Measurable (pairVelocityWeight (X := X)) := by
  unfold pairVelocityWeight
  fun_prop

theorem weightedNormalizedPair_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (weightedNormalizedPair f) :=
  pairVelocityWeight_measurable.mul
    (normalizedTensor_measurable (fiberMass_measurable (ν := volume) hfm) hfm hfm)

theorem normalizedTensor_integrable_swap {d : X → ℝ} {f g : X × Velocity → ℝ}
    (hd : Measurable d) (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (normalizedTensor d g f) (μ.prod (volume.prod volume))) :
    Integrable (normalizedTensor d f g) (μ.prod (volume.prod volume)) := by
  apply memLp_one_iff_integrable.mp
  refine ⟨(normalizedTensor_measurable hd hf hg).aestronglyMeasurable, ?_⟩
  rw [normalizedTensor_norm_swap hd hf hg]
  exact (memLp_one_iff_integrable.mpr hi).2

theorem weightedNormalizedPair_integrable {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) (μ.prod volume)) :
    Integrable (weightedNormalizedPair f) (μ.prod (volume.prod volume)) := by
  have hfi := integrable_of_entropyGauge hfm hf hi
  have hli := linearMoment_integrable hfm hf hi
  have hdm := fiberMass_measurable (ν := volume) hfm
  have hdn (x : X) : 0 ≤ fiberMass volume f x := integral_nonneg (fun v => hf (x,v))
  have hlm := linearMoment_measurable hfm
  have hln (p : X × Velocity) : 0 ≤ linearMoment f p := mul_nonneg (by positivity) (hf p)
  have hr := normalizedTensor_integrable hdm hdn hfm hlm hf hln hfi hli
    (ae_of_all _ (fun _ => le_rfl))
  have hl := normalizedTensor_integrable_swap hdm hlm hfm hr
  have hp := normalizedPair_integrable hfm hf hfi
  apply ((hl.add hr).sub hp).congr
  filter_upwards [] with z
  dsimp only [Pi.sub_apply,Pi.add_apply,weightedNormalizedPair,pairVelocityWeight,normalizedPair,normalizedTensor,linearMoment]
  ring

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Entropy controls the complete mass-normalized velocity pair -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

private theorem bounded_nonnegative_product_div {a b A B r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hr : 0 ≤ r) :
    |a*b/(1+r)| ≤ A*B := by
  rw [abs_of_nonneg (div_nonneg (mul_nonneg ha hb) (by linarith))]
  apply (div_le_iff₀ (by linarith : 0 < 1+r)).mpr
  exact (mul_le_mul hA hB hb hA0).trans (by nlinarith [mul_nonneg (mul_nonneg hA0 hB0) hr])

theorem normalized_entropyTruncation_uniformIntegrable (R : ℝ)
    {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z) :
    UniformIntegrable (fun n => normalizedTensor (fiberMass volume (f n))
      (entropyTruncation R (f n)) (entropyTruncation R (f n))) 1
      (μ.prod (volume.prod volume)) := by
  let a : Velocity → ℝ := (Metric.closedBall (0:Velocity) R).indicator (fun _ => Real.exp R)
  have hai : Integrable a := (integrableOn_const
    (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne).integrable_indicator
    Metric.isClosed_closedBall.measurableSet
  have ha0 v : 0 ≤ a v := indicator_nonneg (fun _ _ => (Real.exp_pos R).le) v
  have hub (n : ℕ) (p : X × Velocity) : entropyTruncation R (f n) p ≤ a p.2 := by
    by_cases hp : p.2 ∈ Metric.closedBall 0 R
    · rw [show a p.2 = Real.exp R from indicator_of_mem hp _]
      exact (entropyTruncation_bounds R (hf n) p).2
    · have hv : R < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
      rw [entropyTruncation_support R (f n) p hv,show a p.2 = 0 from indicator_of_notMem hp _]
  let b : X × (Velocity × Velocity) → ℝ := fun z => a z.2.1*a z.2.2
  have hbi : Integrable b (μ.prod (volume.prod volume)) := (hai.mul_prod hai).comp_snd μ
  have hbui := uniformIntegrable_const (ι := ℕ) (by norm_num : (1:ℝ≥0∞) ≤ 1)
    (by norm_num) (memLp_one_iff_integrable.mpr hbi)
  have hm n : Measurable (normalizedTensor (fiberMass volume (f n))
      (entropyTruncation R (f n)) (entropyTruncation R (f n))) :=
    normalizedTensor_measurable (fiberMass_measurable (hfm n))
      (entropyTruncation_measurable R (hfm n)) (entropyTruncation_measurable R (hfm n))
  have hdom (n : ℕ) (z : X × (Velocity × Velocity)) :
      ‖normalizedTensor (fiberMass volume (f n))
        (entropyTruncation R (f n)) (entropyTruncation R (f n)) z‖ ≤ b z := by
    change |entropyTruncation R (f n) (z.1,z.2.1)*entropyTruncation R (f n) (z.1,z.2.2)/
      (1+fiberMass volume (f n) z.1)| ≤ a z.2.1*a z.2.2
    exact bounded_nonnegative_product_div (entropyTruncation_bounds R (hf n) _).1
      (entropyTruncation_bounds R (hf n) _).1 (hub n _) (hub n _) (ha0 _) (ha0 _)
      (integral_nonneg (fun v => hf n (z.1,v)))
  have hmono (n : ℕ) (s : Set (X × (Velocity × Velocity))) :
      eLpNorm (normalizedTensor (fiberMass volume (f n))
        (entropyTruncation R (f n)) (entropyTruncation R (f n))) 1
        ((μ.prod (volume.prod volume)).restrict s) ≤ eLpNorm b 1 ((μ.prod (volume.prod volume)).restrict s) :=
    eLpNorm_mono_real (hdom n)
  refine ⟨OAI.UnifIntegrable.of_enn ?_ (fun n => (normalizedTensor_measurable
    (fiberMass_measurable (hfm n)) (entropyTruncation_measurable R (hfm n))
    (entropyTruncation_measurable R (hfm n))).aestronglyMeasurable),?_⟩
  · intro ε hε
    obtain ⟨δ,hδ,hδb⟩ := OAI.UnifIntegrable.enn_spec hbui.1 ε hε
    exact ⟨δ,hδ,fun n s hs => (hmono n s).trans (hδb n s hs)⟩
  · obtain ⟨K,hK⟩ := hbui.2
    refine ⟨K,fun n => ?_⟩
    simpa only [Measure.restrict_univ] using (hmono n univ).trans
      (by simpa only [Measure.restrict_univ] using hK n)

theorem normalizedPair_uniformIntegrable {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ z, entropyGauge (f n) z ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => normalizedPair volume (f n)) 1 (μ.prod (volume.prod volume)) := by
  let u := fun (j n : ℕ) => entropyTruncation ((j:ℝ)+1) (f n)
  apply uniformIntegrable_of_approximation
    (g := fun j n => normalizedTensor (fiberMass volume (f n)) (u j n) (u j n))
  · exact fun j => normalized_entropyTruncation_uniformIntegrable ((j:ℝ)+1) hfm hf
  · intro ε hε
    obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (2*C) hε
    refine ⟨j,fun n => ?_⟩
    have hR : 1 ≤ (j:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    have he := normalizedPair_truncation_error (hfm n)
      (entropyTruncation_measurable ((j:ℝ)+1) (hfm n)) (hf n)
      (fun p => (entropyTruncation_bounds ((j:ℝ)+1) (hf n) p).1)
      (fun p => by
        unfold entropyTruncation
        split_ifs
        · exact le_rfl
        · exact hf n p)
      (integrable_of_entropyGauge (hfm n) (hf n) (hi n))
      (entropyTruncation_integrable ((j:ℝ)+1) (hfm n) (hf n))
    calc
      _ ≤ 2*eLpNorm (fun z => f n z-u j n z) 1 (μ.prod volume) := he
      _ ≤ 2*ENNReal.ofReal (C/((j:ℝ)+1)) := mul_le_mul' le_rfl
        (entropyTruncation_L1_bound hR (hfm n) (hf n) (hi n) (hb n))
      _ = ENNReal.ofReal ((2*C)/((j:ℝ)+1)) := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      _ ≤ ε := hj
  · exact fun n => (normalizedTensor_measurable (fiberMass_measurable (hfm n)) (hfm n) (hfm n)).aestronglyMeasurable

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform velocity-tail control of the moment-weighted normalized pair -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

private theorem tail_coeff_bound {R a b : ℝ} (hR : 0 ≤ R) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    (if a ≤ R ∧ b ≤ R then 0 else 1+a+b) ≤
      2*((if a ≤ R then 0 else 1+a)+(if b ≤ R then 0 else 1+b)) := by
  by_cases har : a ≤ R <;> by_cases hbr : b ≤ R <;>
    simp only [har,hbr,and_self,ite_true, if_true,ite_false, if_false,false_and,and_false,
      zero_add,add_zero] <;> (try linarith)

omit [MeasurableSpace X] in
private theorem tail_density_nonneg (R : ℝ) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ linearMoment f p-velocityLinearCut R f p := by
  dsimp only [velocityLinearCut]
  split_ifs
  · simp only [sub_self,le_refl]
  · simp only [sub_zero,linearMoment]
    exact mul_nonneg (by positivity) (hf p)

omit [MeasurableSpace X] in
theorem pairVelocityCut_pointwise_error {R : ℝ} (hR : 0 ≤ R) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : X × (Velocity × Velocity)) :
    |weightedNormalizedPair f z-pairVelocityCut R f z| ≤
      2*(normalizedTensor (fiberMass volume f)
          (fun p => linearMoment f p-velocityLinearCut R f p) f z+
        normalizedTensor (fiberMass volume f) f
          (fun p => linearMoment f p-velocityLinearCut R f p) z) := by
  have hd : 0 < 1+fiberMass volume f z.1 := by
    have hm : 0 ≤ fiberMass volume f z.1 := integral_nonneg (fun v => hf (z.1,v))
    linarith
  have hprod : 0 ≤ f (z.1,z.2.1)*f (z.1,z.2.2) := mul_nonneg (hf _) (hf _)
  have hc := mul_le_mul_of_nonneg_right (tail_coeff_bound hR (norm_nonneg z.2.1) (norm_nonneg z.2.2)) hprod
  have hdiv := div_le_div_of_nonneg_right hc hd.le
  by_cases hv : ‖z.2.1‖ ≤ R <;> by_cases hw : ‖z.2.2‖ ≤ R
  all_goals
    simp only [weightedNormalizedPair,pairVelocityCut,pairVelocityWeight,normalizedPair,
      normalizedTensor,linearMoment,velocityLinearCut,hv,hw,and_self,
      ite_true, if_true,ite_false, if_false,false_and,and_false,sub_self,sub_zero,zero_mul,mul_zero,zero_div,
      zero_add,add_zero,abs_zero] at hdiv ⊢
  · exact le_refl _
  all_goals
    rw [abs_of_nonneg (mul_nonneg (by positivity) (div_nonneg hprod hd.le))]
    first | (convert hdiv using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hdiv.trans (le_of_eq (by ring)))

theorem pairVelocityCut_L1_error {R C : ℝ} (hR : 0 < R) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) (μ.prod volume))
    (hb : (∫ p, entropyGauge f p ∂μ.prod volume) ≤ C) :
    eLpNorm (fun z => weightedNormalizedPair f z-pairVelocityCut R f z) 1
      (μ.prod (volume.prod volume)) ≤ ENNReal.ofReal (8*C/R) := by
  let d : X × Velocity → ℝ := fun p => linearMoment f p-velocityLinearCut R f p
  have hdm : Measurable d := (linearMoment_measurable hfm).sub (velocityLinearCut_measurable R hfm)
  have hdi : Integrable d (μ.prod volume) :=
    (linearMoment_integrable hfm hf hi).sub (velocityLinearCut_integrable R hfm hf hi)
  have hfi := integrable_of_entropyGauge hfm hf hi
  have hm := fiberMass_measurable (ν := volume) hfm
  have hmn (x : X) : 0 ≤ fiberMass volume f x := integral_nonneg (fun v => hf (x,v))
  have hd0 : ∀ p, 0 ≤ d p := tail_density_nonneg R hf
  have hright := normalizedTensor_L1_le hm hmn hfm hdm hf hd0 hfi hdi (ae_of_all _ (fun _ => le_rfl))
  have hleft : eLpNorm (normalizedTensor (fiberMass volume f) d f) 1 (μ.prod (volume.prod volume)) ≤
      eLpNorm d 1 (μ.prod volume) := by
    rw [normalizedTensor_norm_swap hm hdm hfm]
    exact hright
  have hs_nonneg (z : X × (Velocity × Velocity)) :
      0 ≤ normalizedTensor (fiberMass volume f) d f z+normalizedTensor (fiberMass volume f) f d z := by
    have hden : 0 ≤ 1+fiberMass volume f z.1 := by linarith [hmn z.1]
    exact add_nonneg (div_nonneg (mul_nonneg (hd0 _) (hf _)) hden)
      (div_nonneg (mul_nonneg (hf _) (hd0 _)) hden)
  have hnorm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := μ.prod (volume.prod volume))
    (f := weightedNormalizedPair f-pairVelocityCut R f)
    (g := fun z => normalizedTensor (fiberMass volume f) d f z+normalizedTensor (fiberMass volume f) f d z)
    (c := 2) (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,Real.norm_of_nonneg (hs_nonneg z)]
      exact pairVelocityCut_pointwise_error hR.le hf z)) 1
  calc
    _ ≤ 2*(eLpNorm (normalizedTensor (fiberMass volume f) d f) 1 (μ.prod (volume.prod volume))+
        eLpNorm (normalizedTensor (fiberMass volume f) f d) 1 (μ.prod (volume.prod volume))) := by
      exact hnorm.trans (by norm_num; exact mul_le_mul' le_rfl (eLpNorm_add_le (hf := (normalizedTensor_measurable hm hdm hfm).aestronglyMeasurable)
        (hg := (normalizedTensor_measurable hm hfm hdm).aestronglyMeasurable) (by norm_num)))
    _ ≤ 2*(eLpNorm d 1 (μ.prod volume)+eLpNorm d 1 (μ.prod volume)) :=
      mul_le_mul' le_rfl (add_le_add hleft hright)
    _ ≤ 2*(ENNReal.ofReal (2*C/R)+ENNReal.ofReal (2*C/R)) :=
      mul_le_mul' le_rfl (add_le_add (velocityLinearCut_L1_error hR hfm hf hi hb)
        (velocityLinearCut_L1_error hR hfm hf hi hb))
    _ = ENNReal.ofReal (8*C/R) := by
      have hC : 0 ≤ C := (integral_nonneg (entropyGauge_nonneg hf)).trans hb
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Actual pre- and post-collision rates normalized by the spatial mass -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

omit [MeasurableSpace X] in
theorem massNormalizedPreRate_eq (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    massNormalizedPreRate f z = normalizedKernel z*weightedNormalizedPair f z.1 := by
  rw [massNormalizedPreRate,preRate_eq_normalized]
  dsimp only [pairDensity,weightedNormalizedPair,pairVelocityWeight,normalizedPair,normalizedTensor]
  ring

omit [MeasurableSpace X] in
theorem massNormalizedPreRate_eq_fun (f : X × Velocity → ℝ) :
    massNormalizedPreRate f = fun z => normalizedKernel z*weightedNormalizedPair f z.1 :=
  funext (massNormalizedPreRate_eq f)

omit [SFinite μ] in
theorem massNormalizedPreRate_integrable {f : X × Velocity → ℝ} (_hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (massNormalizedPreRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := (hi.comp_fst sphereArea).bdd_mul normalizedKernel_measurable.aestronglyMeasurable
    (ae_of_all _ normalizedKernel_bound)
  simpa only [massNormalizedPreRate_eq_fun] using h

theorem massNormalizedPostRate_integrable {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (massNormalizedPostRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable (massNormalizedPreRate_integrable hfm hi)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedPairUniformIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Entropy gives uniform integrability of moment-weighted normalized pairs -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weightedNormalizedPair_uniformIntegrable
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => weightedNormalizedPair (f n)) 1
      (μ.prod (volume.prod volume)) := by
  have hui := normalizedPair_uniformIntegrable hfm hf hi hb
  have hcut (j : ℕ) : UniformIntegrable (fun n => pairVelocityCut ((j:ℝ)+1) (f n)) 1
      (μ.prod (volume.prod volume)) := by
    let R : ℝ := (j:ℝ)+1
    let a : X × (Velocity × Velocity) → ℝ := fun z =>
      if ‖z.2.1‖ ≤ R ∧ ‖z.2.2‖ ≤ R then pairVelocityWeight z else 0
    have ham : Measurable a := pairVelocityWeight_measurable.ite
      ((measurableSet_le (measurable_snd.fst.norm) measurable_const).inter
        (measurableSet_le (measurable_snd.snd.norm) measurable_const)) measurable_const
    have hR : 0 ≤ R := by dsimp [R] <;> positivity
    have ha (z) : |a z| ≤ 1+2*R := by
      dsimp only [a]
      split_ifs with hz
      · rw [abs_of_nonneg (show 0 ≤ pairVelocityWeight z by dsimp [pairVelocityWeight] <;> positivity)]
        dsimp only [pairVelocityWeight]
        linarith [hz.1,hz.2]
      · simp only [abs_zero]
        positivity
    have h := uniformIntegrable_of_bounded_multiplier hui ham
      ⟨1+2*R,by positivity⟩ ha
    have he : (fun n z => a z*normalizedPair volume (f n) z) =
        (fun n => pairVelocityCut ((j:ℝ)+1) (f n)) := by
      funext n z
      dsimp only [a,pairVelocityCut,weightedNormalizedPair,R]
      split_ifs <;> simp only [zero_mul]
    rwa [he] at h
  apply uniformIntegrable_of_approximation hcut
  intro ε hε
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (8*C) hε
  exact ⟨j,fun n => (pairVelocityCut_L1_error (by positivity : 0 < (j:ℝ)+1)
    (hfm n) (hf n) (hi n) (hb n)).trans hj⟩
  exact fun n => (weightedNormalizedPair_measurable (hfm n)).aestronglyMeasurable

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PairPatchIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong L1 continuity of translations on the outgoing velocity-pair space -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance pairTranslationHaar : Measure.IsAddHaarMeasure (volume : Measure (Velocity × Velocity)) :=
  Measure.prod.instIsAddHaarMeasure _ _

local instance pairTranslationRegular_ra56ad6_1 : (volume : Measure (Velocity × Velocity)).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
private theorem pairTranslation_continuous : Continuous pairTranslation :=
  ContinuousMap.continuous_of_continuous_uncurry pairTranslation (continuous_snd.add continuous_fst)

private theorem pairTranslation_preserving (a : Velocity × Velocity) :
    MeasurePreserving (pairTranslation a) (volume : Measure (Velocity × Velocity)) volume :=
  measurePreserving_add_right volume a

theorem pair_translation_L1 {f : Velocity × Velocity → ℝ} (hf : Integrable f)
    (a : Velocity × Velocity) :
    Tendsto (fun b => eLpNorm (fun p => f (p+b)-f (p+a)) 1 volume) (𝓝 a) (𝓝 0) := by
  let hf₁ := memLp_one_iff_integrable.mpr hf
  let u : Lp ℝ 1 (volume : Measure (Velocity × Velocity)) := hf₁.toLp f
  have hu : u =ᵐ[volume] f := hf₁.coeFn_toLp
  have hc : Continuous (fun b => Lp.compMeasurePreserving (pairTranslation b)
      (pairTranslation_preserving b) u) :=
    continuous_const.compMeasurePreservingLp pairTranslation_continuous
      pairTranslation_preserving (by norm_num)
  have hrep b : Lp.compMeasurePreserving (pairTranslation b) (pairTranslation_preserving b) u =ᵐ[volume]
      (fun p => f (p+b)) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving u (pairTranslation_preserving b),
      (pairTranslation_preserving b).quasiMeasurePreserving.ae hu] with p hp hpu
    exact hp.trans hpu
  have he b : edist (Lp.compMeasurePreserving (pairTranslation b) (pairTranslation_preserving b) u)
      (Lp.compMeasurePreserving (pairTranslation a) (pairTranslation_preserving a) u) =
      eLpNorm (fun p => f (p+b)-f (p+a)) 1 volume := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hrep b).sub (hrep a))
  simpa only [he] using tendsto_iff_edist_tendsto_0.mp (hc.tendsto a)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DoubleCollisionTests
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Surjectivity of the two-output collision variation away from grazing and parallel normals -/
noncomputable section
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness

private theorem inner_values {n m : Velocity}
    (hn : inner ℝ n n = 1) (hm : inner ℝ m m = 1)
    (hc : 1-(inner ℝ n m)^2 ≠ 0) (u v : ℝ) :
    inner ℝ (normalPlaneLift n m u v) n = u ∧
      inner ℝ (normalPlaneLift n m u v) m = v := by
  let c := inner ℝ n m
  let D := 1-c^2
  change inner ℝ (((u-c*v)/D) • n+((v-c*u)/D) • m) n = u ∧
    inner ℝ (((u-c*v)/D) • n+((v-c*u)/D) • m) m = v
  constructor
  · simp only [inner_add_left,real_inner_smul_left,hn,mul_one]
    rw [real_inner_comm n m]
    dsimp only [c,D] at *
    field_simp
    ring
  · simp only [inner_add_left,real_inner_smul_left,hm,mul_one]
    dsimp only [c,D] at *
    field_simp
    ring

theorem doubleOutgoingVariation_surjective {d n m : Velocity}
    (hn : inner ℝ n n = 1) (hm : inner ℝ m m = 1)
    (hc : 1-(inner ℝ n m)^2 ≠ 0) (hd : inner ℝ d n ≠ 0) :
    Function.Surjective (doubleOutgoingVariation d n m) := by
  rintro ⟨a,b⟩
  let q := b-a
  let z := normalPlaneLift n m (inner ℝ q n) (inner ℝ q m)
  have hzn := (inner_values hn hm hc (inner ℝ q n) (inner ℝ q m)).1
  let k := q-z
  have hkn : inner ℝ k n = 0 := by
    change inner ℝ (q-normalPlaneLift n m (inner ℝ q n) (inner ℝ q m)) n = 0
    rw [inner_sub_left,hzn,sub_self]
  let dn := (inner ℝ d n)⁻¹ • k
  have hdn : inner ℝ n dn = 0 := by
    rw [real_inner_comm]
    simp only [dn,real_inner_smul_left,hkn,mul_zero]
  have hscale : (inner ℝ d n) • dn = k := by
    simp only [dn,smul_smul,mul_inv_cancel₀ hd,one_smul]
  let c := inner ℝ n m
  let D := 1-c^2
  let A := (inner ℝ q n-c*inner ℝ q m)/D
  let B := (inner ℝ q m-c*inner ℝ q n)/D
  have hzrepr : z = A • n+B • m := by
    dsimp only [A,B,c,D]
    rfl
  let dd := normalPlaneLift n m (A-inner ℝ d dn) (-B)
  obtain ⟨hddn,hddm⟩ := inner_values hn hm hc (A-inner ℝ d dn) (-B)
  refine ⟨((b+(inner ℝ dd m) • m,dd),dn),?_⟩
  apply Prod.ext
  · change b+(inner ℝ dd m) • m-
        (inner ℝ dd n+inner ℝ d dn-2*(inner ℝ d n)*inner ℝ n dn) • n-
        (inner ℝ d n) • dn = a
    rw [hdn,hddn,hddm,hscale]
    simp only [mul_zero,sub_zero,sub_add_cancel,neg_smul]
    have hq : q = A • n+B • m+k := by rw [← hzrepr]; dsimp only [k]; module
    change b-a = A • n+B • m+k at hq
    calc
      _ = b-(A • n+B • m+k) := by module
      _ = a := by rw [← hq]; abel
  · change b+(inner ℝ dd m) • m-(inner ℝ dd m) • m = b
    module

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The genuine doubled collision map has the surjective outgoing variation -/
noncomputable section
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness
namespace DoubleGain

theorem differential_apply (d n m : Velocity) (z : Domain) :
    differential d n m z = doubleOutgoingVariation d n m z := by
  apply Prod.ext
  · change z.1.1-((inner ℝ d n) • z.2+
      (inner ℝ n z.1.2+inner ℝ d z.2-2*(inner ℝ d n)*inner ℝ n z.2) • n) = _
    rw [real_inner_comm z.1.2 n]
    dsimp only [doubleOutgoingVariation]
    module
  · change z.1.1-(inner ℝ m z.1.2) • m = _
    rw [real_inner_comm z.1.2 m]
    rfl

theorem numerator_hasFDerivAt (v d n : Velocity) :
    HasFDerivAt (fun z : Domain => inner ℝ z.1.2 z.2)
      (numeratorDifferential d n) ((v,d),n) := by
  have h := (relativeProjection.hasFDerivAt (x := ((v,d),n))).inner ℝ
    (normalProjection.hasFDerivAt (x := ((v,d),n)))
  refine h.congr_fderiv (Eq.symm ?_)
  · apply ContinuousLinearMap.ext
    intro z
    change inner ℝ n z.1.2+inner ℝ d z.2 = inner ℝ d z.2+inner ℝ z.1.2 n
    rw [real_inner_comm z.1.2 n]
    ring

theorem denominator_hasFDerivAt (v d n : Velocity) :
    HasFDerivAt (fun z : Domain => inner ℝ z.2 z.2)
      (denominatorDifferential n) ((v,d),n) := by
  have h := (normalProjection.hasFDerivAt (x := ((v,d),n))).inner ℝ
    (normalProjection.hasFDerivAt (x := ((v,d),n)))
  refine h.congr_fderiv (Eq.symm ?_)
  · apply ContinuousLinearMap.ext
    intro z
    change 2*inner ℝ n z.2 = inner ℝ n z.2+inner ℝ z.2 n
    rw [real_inner_comm z.2 n]
    ring

theorem inverse_denominator_hasFDerivAt (v d n : Velocity) (hn : inner ℝ n n = 1) :
    HasFDerivAt (fun z : Domain => (inner ℝ z.2 z.2)⁻¹)
      (-denominatorDifferential n) ((v,d),n) := by
  have h := (hasDerivAt_inv (show inner ℝ n n ≠ 0 by rw [hn]; norm_num)).comp_hasFDerivAt
    ((v,d),n) (denominator_hasFDerivAt v d n)
  refine h.congr_fderiv (Eq.symm ?_)
  · rw [hn]
    norm_num

theorem coefficient_hasFDerivAt (v d n : Velocity) (hn : inner ℝ n n = 1) :
    HasFDerivAt coefficient (coefficientDifferential d n) ((v,d),n) := by
  have h := (numerator_hasFDerivAt v d n).mul (inverse_denominator_hasFDerivAt v d n hn)
  refine h.congr_fderiv (Eq.symm ?_)
  · apply ContinuousLinearMap.ext
    intro z
    change inner ℝ n z.1.2+inner ℝ d z.2-2*(inner ℝ d n)*inner ℝ n z.2 =
    (inner ℝ d n)*(-(2*inner ℝ n z.2))+(inner ℝ n n)⁻¹*
      (inner ℝ n z.1.2+inner ℝ d z.2)
    rw [hn]
    norm_num only
    ring


theorem outgoing_hasFDerivAt (v d n m : Velocity) (hn : inner ℝ n n = 1) :
    HasFDerivAt (outgoing m) (differential d n m) ((v,d),n) := by
  let x : Domain := ((v,d),n)
  have hv := velocityProjection.hasFDerivAt (x := x)
  have hnorm := normalProjection.hasFDerivAt (x := x)
  have hc : coefficient x = inner ℝ d n := by
    change inner ℝ d n*(inner ℝ n n)⁻¹ = inner ℝ d n
    rw [hn]
    norm_num
  have hmult : HasFDerivAt (fun z : Domain => coefficient z • z.2)
      ((inner ℝ d n) • normalProjection+(coefficientDifferential d n).smulRight n) x := by
    have h := (coefficient_hasFDerivAt v d n hn).smul hnorm
    rwa [hc] at h
  have hm : HasFDerivAt (fun z : Domain => inner ℝ z.1.2 m)
      ((innerSL ℝ m).comp relativeProjection) x := by
    have h := (innerSL ℝ m).hasFDerivAt.comp x (relativeProjection.hasFDerivAt (x := x))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact real_inner_comm m z.1.2
  exact (hv.sub hmult).prodMk (hv.sub (hm.smul_const m))

theorem differential_surjective {d n m : Velocity}
    (hn : inner ℝ n n = 1) (hm : inner ℝ m m = 1)
    (hc : 1-(inner ℝ n m)^2 ≠ 0) (hd : inner ℝ d n ≠ 0) :
    Function.Surjective (differential d n m) := by
  intro y
  obtain ⟨z,hz⟩ := doubleOutgoingVariation_surjective hn hm hc hd y
  exact ⟨z,(differential_apply d n m z).trans hz⟩

end DoubleGain
end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Parallel and grazing normals occupy null sets in the doubled gain parameters -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem velocity_line_null {m : Velocity} (hm : m ≠ 0) :
    (volume : Measure Velocity) (Submodule.span ℝ {m}) = 0 := by
  apply MeasureTheory.Measure.addHaar_submodule
  intro htop
  have hdim := congrArg (fun S : Submodule ℝ Velocity => Module.finrank ℝ S) htop
  rw [finrank_top,finrank_span_singleton hm] at hdim
  norm_num at hdim

theorem normalized_parallel_mem_span {m n : Velocity} (hm : ‖m‖ = 1) (hn : n ≠ 0)
    (h : 1-(inner ℝ (NormedSpace.normalize n) m)^2 = 0) :
    n ∈ Submodule.span ℝ {m} := by
  let N := NormedSpace.normalize n
  let c := inner ℝ N m
  have hN : ‖N‖ = 1 := NormedSpace.norm_normalize hn
  have hc : c^2 = 1 := by dsimp only [c,N] <;> linarith
  have hzero : N-c • m = 0 := by
    apply norm_eq_zero.mp
    have he := norm_sub_sq_real N (c • m)
    rw [hN,norm_smul,hm,real_inner_smul_right] at he
    simp only [one_pow,Real.norm_eq_abs,mul_one,sq_abs] at he
    change ‖N-c • m‖^2 = 1-2*(c*c)+c^2 at he
    nlinarith [norm_nonneg (N-c • m)]
  have hNm : N ∈ Submodule.span ℝ {m} :=
    Submodule.mem_span_singleton.mpr ⟨c,(sub_eq_zero.mp hzero).symm⟩
  have hns := (Submodule.span ℝ {m}).smul_mem ‖n‖ hNm
  simpa only [N,NormedSpace.norm_smul_normalize] using hns

theorem regular_normal_ae {m : Velocity} (hm : ‖m‖ = 1) :
    ∀ᵐ n : Velocity ∂volume, n ≠ 0 ∧
      1-(inner ℝ (NormedSpace.normalize n) m)^2 ≠ 0 := by
  have hm0 : m ≠ 0 := norm_ne_zero_iff.mp (by rw [hm]; norm_num)
  have hout : ∀ᵐ n : Velocity ∂volume, n ∉ Submodule.span ℝ {m} := by
    apply ae_iff.mpr
    have hs : {a : Velocity | ¬a ∉ Submodule.span ℝ {m}} =
        (Submodule.span ℝ {m} : Set Velocity) := by ext a; simp
    rw [hs]
    exact velocity_line_null hm0
  filter_upwards [volume.ae_ne (0:Velocity),hout] with n hn hout
  exact ⟨hn,fun h => hout (normalized_parallel_mem_span hm hn h)⟩

theorem regular_grazing_ae {n : Velocity} (hn : n ≠ 0) :
    ∀ᵐ d : Velocity ∂volume, inner ℝ d (NormedSpace.normalize n) ≠ 0 := by
  have hN : NormedSpace.normalize n ≠ 0 := (NormedSpace.normalize_eq_zero_iff n).not.mpr hn
  have he := Published.affine_velocity_hyperplane_null 0 hN
  have hh : ∀ᵐ d : Velocity ∂volume, inner ℝ (NormedSpace.normalize n) d ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not,zero_add] using he
  filter_upwards [hh] with d hd
  rwa [real_inner_comm (NormedSpace.normalize n) d]

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The two-output submersion for nonzero, unnormalized collision normals -/
noncomputable section
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem outgoing_scale (m v d n : Velocity) {r : ℝ} (hr : r ≠ 0) :
    outgoing m ((v,d),r • n) = outgoing m ((v,d),n) := by
  by_cases hn : n = 0
  · simp [hn,outgoing]
  have hnn : inner ℝ n n ≠ 0 := (real_inner_self_pos.mpr hn).ne'
  apply Prod.ext
  · change v-(inner ℝ d (r • n)*(inner ℝ (r • n) (r • n))⁻¹) • (r • n) =
      v-(inner ℝ d n*(inner ℝ n n)⁻¹) • n
    rw [real_inner_smul_right,real_inner_smul_left,real_inner_smul_right,smul_smul]
    congr 2
    field_simp
  · rfl

theorem outgoing_comp_scale (m : Velocity) {r : ℝ} (hr : r ≠ 0) :
    outgoing m ∘ scaleNormal r = outgoing m := by
  funext z
  exact outgoing_scale m z.1.1 z.1.2 z.2 hr

theorem scaleNormal_surjective {r : ℝ} (hr : r ≠ 0) :
    Function.Surjective (scaleNormal r) := by
  intro z
  refine ⟨(z.1,r⁻¹ • z.2),?_⟩
  change (z.1,r • r⁻¹ • z.2) = z
  rw [smul_smul,mul_inv_cancel₀ hr,one_smul]

theorem raw_outgoing_regular {v d n m : Velocity} (hn : n ≠ 0) (hm : ‖m‖ = 1)
    (hc : 1-(inner ℝ (NormedSpace.normalize n) m)^2 ≠ 0)
    (hd : inner ℝ d (NormedSpace.normalize n) ≠ 0) :
    ∃ A : Domain →L[ℝ] (Velocity × Velocity),
      HasFDerivAt (outgoing m) A ((v,d),n) ∧ Function.Surjective A := by
  let N := NormedSpace.normalize n
  have hN : inner ℝ N N = 1 := by
    rw [real_inner_self_eq_norm_sq,NormedSpace.norm_normalize hn]
    norm_num
  have hM : inner ℝ m m = 1 := by rw [real_inner_self_eq_norm_sq,hm]; norm_num
  have hr : ‖n‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hn)
  let S := scaleNormal ‖n‖⁻¹
  have H := (outgoing_hasFDerivAt v d N m hN).comp ((v,d),n)
    (S.hasFDerivAt (x := ((v,d),n)))
  have H' : HasFDerivAt (outgoing m)
      ((differential d N m).comp S) ((v,d),n) := by
    simpa only [S,outgoing_comp_scale m hr] using H
  refine ⟨(differential d N m).comp S,H',?_⟩
  exact (differential_surjective hN hM hc hd).comp (scaleNormal_surjective hr)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Full rank for almost every doubled outgoing collision parameter -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem good_measurable (m : Velocity) :
    MeasurableSet {p : Velocity × Velocity | good m p.2 p.1} := by
  have hN : Measurable (fun p : Velocity × Velocity => NormedSpace.normalize p.1) := by
    unfold NormedSpace.normalize
    fun_prop
  have hc : Measurable (fun p : Velocity × Velocity =>
      1-(inner ℝ (NormedSpace.normalize p.1) m)^2) := by fun_prop
  have hd : Measurable (fun p : Velocity × Velocity => inner ℝ p.2 (NormedSpace.normalize p.1)) :=
    measurable_snd.inner hN
  exact (measurableSet_eq_fun measurable_fst measurable_const).compl.inter
    ((measurableSet_eq_fun hc measurable_const).compl.inter
      (measurableSet_eq_fun hd measurable_const).compl)

theorem good_ae (m : Velocity) (hm : ‖m‖ = 1) :
    ∀ᵐ p : Velocity × Velocity ∂(volume : Measure Velocity).prod volume, good m p.1 p.2 := by
  have hh : ∀ᵐ n : Velocity ∂volume, ∀ᵐ d : Velocity ∂volume, good m d n := by
    filter_upwards [regular_normal_ae hm] with n hn
    filter_upwards [regular_grazing_ae hn.1] with d hd
    exact ⟨hn.1,hn.2,hd⟩
  have hp := (Measure.ae_prod_iff_ae_ae (good_measurable m)).mpr hh
  exact (Measure.measurePreserving_swap (μ := (volume : Measure Velocity))
    (ν := (volume : Measure Velocity))).quasiMeasurePreserving.ae hp

theorem outgoing_rank_ae (m : Velocity) (hm : ‖m‖ = 1) :
    ∀ᵐ z : Domain ∂(volume : Measure (Velocity × Velocity)).prod volume,
      Function.Surjective (fderiv ℝ (outgoing m) z) := by
  have hp := good_ae m hm
  have htrip : ∀ᵐ z : Velocity × (Velocity × Velocity)
      ∂(volume : Measure Velocity).prod ((volume : Measure Velocity).prod volume),
      good m z.2.1 z.2.2 := Measure.quasiMeasurePreserving_snd.ae hp
  have hassoc := (measurePreserving_prodAssoc (volume : Measure Velocity)
    (volume : Measure Velocity) (volume : Measure Velocity)).quasiMeasurePreserving.ae htrip
  rw [← Measure.volume_eq_prod] at hassoc
  filter_upwards [hassoc] with z hz
  change good m z.1.2 z.2 at hz
  obtain ⟨A,hA,hsur⟩ := raw_outgoing_regular (v := z.1.1) hz.1 hm hz.2.1 hz.2.2
  change HasFDerivAt (outgoing m) A z at hA
  rwa [hA.fderiv]

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Local smoothness of the doubled outgoing map off the zero normal -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem normalDomain_open : IsOpen normalDomain :=
  isClosed_singleton.isOpen_compl.preimage continuous_snd

theorem outgoing_measurable (m : Velocity) : Measurable (outgoing m) := by
  unfold outgoing
  fun_prop

theorem outgoing_contDiffAt (m : Velocity) {z : Domain} (hz : z ∈ normalDomain) :
    ContDiffAt ℝ 1 (outgoing m) z := by
  have hv : ContDiff ℝ 1 (fun x : Domain => x.1.1) := by fun_prop
  have hd : ContDiff ℝ 1 (fun x : Domain => x.1.2) := by fun_prop
  have hn : ContDiff ℝ 1 (fun x : Domain => x.2) := by fun_prop
  have hnum : ContDiff ℝ 1 (fun x : Domain => inner ℝ x.1.2 x.2) := hd.inner ℝ hn
  have hden : ContDiff ℝ 1 (fun x : Domain => inner ℝ x.2 x.2) := hn.inner ℝ hn
  have hne : inner ℝ z.2 z.2 ≠ 0 := (real_inner_self_pos.mpr hz).ne'
  have hfirst := hv.contDiffAt.sub ((hnum.contDiffAt.mul (hden.contDiffAt.inv hne)).smul hn.contDiffAt)
  have hsecond : ContDiff ℝ 1 (fun x : Domain => x.1.1-(inner ℝ x.1.2 m) • m) :=
    hv.sub ((hd.inner ℝ contDiff_const).smul contDiff_const)
  exact hfirst.prodMk hsecond.contDiffAt

theorem outgoing_contDiffOn (m : Velocity) : ContDiffOn ℝ 1 (outgoing m) normalDomain :=
  fun _ hz => (outgoing_contDiffAt m hz).contDiffWithinAt

theorem outgoing_hasFDerivAt_fderiv (m : Velocity) {z : Domain} (hz : z ∈ normalDomain) :
    HasFDerivAt (outgoing m) (fderiv ℝ (outgoing m) z) z :=
  (outgoing_contDiffAt m hz).differentiableAt_one.hasFDerivAt

theorem outgoing_fderiv_continuousAt (m : Velocity) {z : Domain} (hz : z ∈ normalDomain) :
    ContinuousAt (fderiv ℝ (outgoing m)) z :=
  ((outgoing_contDiffOn m).continuousOn_fderiv_of_isOpen normalDomain_open (by norm_num)).continuousAt
    (normalDomain_open.mem_nhds hz)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The joint outgoing law has a density on every compact nonzero-normal parameter set -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem compact_outgoing_law_absolutelyContinuous (m : Velocity) (hm : ‖m‖ = 1)
    {K : Set Domain} (hK : IsCompact K) (hKO : K ⊆ normalDomain) :
    (Measure.map (outgoing m)
      (((volume : Measure (Velocity × Velocity)).prod volume).restrict K)) ≪
        (volume : Measure (Velocity × Velocity)) := by
  have : Measure.IsAddHaarMeasure (volume : Measure (Velocity × Velocity)) := by
    change Measure.IsAddHaarMeasure ((volume : Measure Velocity).prod volume)
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply outgoing_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let Z : Set Domain := {z | ¬Function.Surjective (fderiv ℝ (outgoing m) z)}
  have hZ : ((volume : Measure (Velocity × Velocity)).prod volume) Z = 0 :=
    ae_iff.mp (outgoing_rank_ae m hm)
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply (outgoing_measurable m) hN]
  apply GainPullback.compact_submersion_null_preimage normalDomain_open hK hKO hZ
    (outgoing_measurable m)
    (fun _ hz => outgoing_hasFDerivAt_fderiv m hz)
    (fun _ hz => outgoing_fderiv_continuousAt m hz)
  · intro z hz
    exact not_not.mp hz.2
  · exact hN
  · exact hN0

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Absolute continuity of the full doubled outgoing law -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem outgoing_law_absolutelyContinuous (m : Velocity) (hm : ‖m‖ = 1) :
    (Measure.map (outgoing m) ((volume : Measure (Velocity × Velocity)).prod volume)) ≪
      (volume : Measure (Velocity × Velocity)) := by
  let μ : Measure Domain := (volume : Measure (Velocity × Velocity)).prod volume
  let : LocallyCompactSpace normalDomain := normalDomain_open.locallyCompactSpace
  let K (i : ℕ) : Set Domain := Subtype.val '' compactCovering normalDomain i
  have hK i : IsCompact (K i) := (isCompact_compactCovering normalDomain i).image continuous_subtype_val
  have hKO i : K i ⊆ normalDomain := by
    rintro _ ⟨z,_,rfl⟩
    exact z.property
  have hcover : (⋃ i, K i) = normalDomain := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      exact hKO i hi
    · intro hz
      obtain ⟨i,hi⟩ := exists_mem_compactCovering (⟨z,hz⟩ : normalDomain)
      exact mem_iUnion.mpr ⟨i,⟨⟨z,hz⟩,hi,rfl⟩⟩
  have hout : μ normalDomainᶜ = 0 := by
    have hgood : ∀ᵐ z ∂μ, z ∈ normalDomain :=
      Measure.quasiMeasurePreserving_snd.ae (volume.ae_ne (0 : Velocity))
    exact ae_iff.mp hgood
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply (outgoing_measurable m) hN]
  have hKi i : μ ((outgoing m ⁻¹' N) ∩ K i) = 0 := by
    have h := compact_outgoing_law_absolutelyContinuous m hm (hK i) (hKO i) hN0
    rw [Measure.map_apply (outgoing_measurable m) hN,Measure.restrict_apply (hN.preimage (outgoing_measurable m))] at h
    exact h
  have hinside : μ ((outgoing m ⁻¹' N) ∩ normalDomain) = 0 := by
    rw [← hcover,inter_iUnion]
    exact measure_iUnion_null hKi
  apply measure_mono_null (show outgoing m ⁻¹' N ⊆
    normalDomainᶜ ∪ ((outgoing m ⁻¹' N) ∩ normalDomain) from by
      intro z hz
      by_cases hzo : z ∈ normalDomain
      · exact Or.inr ⟨hz,hzo⟩
      · exact Or.inl hzo)
  exact measure_union_null hout hinside

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The doubled outgoing law with the physical surface-area normal measure -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem angularOutgoing_measurable (m : Velocity) : Measurable (angularOutgoing m) :=
  (outgoing_measurable m).comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

theorem direction_outgoing (e : Sphere) (m : Velocity) (p : Velocity × Velocity)
    {n : Velocity} (hn : n ≠ 0) :
    outgoing m (p,(sphereDirection e n).1) = outgoing m (p,n) := by
  dsimp only [sphereDirection]
  rw [dite_eq_right hn]
  exact outgoing_scale m p.1 p.2 n (inv_ne_zero (norm_ne_zero_iff.mpr hn))

theorem angular_outgoing_law_absolutelyContinuous (m : Velocity) (hm : ‖m‖ = 1) :
    (Measure.map (angularOutgoing m)
      ((volume : Measure (Velocity × Velocity)).prod sphereArea)) ≪
        (volume : Measure (Velocity × Velocity)) := by
  let e : Sphere := ⟨m,mem_sphere_zero_iff_norm.mpr hm⟩
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply (angularOutgoing_measurable m) hN]
  have hraw := outgoing_law_absolutelyContinuous m hm hN0
  rw [Measure.map_apply (outgoing_measurable m) hN] at hraw
  have hrawae : ∀ᵐ z : Domain ∂(volume : Measure (Velocity × Velocity)).prod volume,
      outgoing m z ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not,Set.preimage] using hraw
  have hsections := Measure.ae_ae_of_ae_prod hrawae
  have hsections' : ∀ᵐ p : Velocity × Velocity ∂volume,
      ∀ᵐ n : Sphere ∂sphereArea, angularOutgoing m (p,n) ∉ N := by
    filter_upwards [hsections] with p hp
    let A : Set Sphere := {n | angularOutgoing m (p,n) ∈ N}
    have hA : MeasurableSet A := hN.preimage
      ((angularOutgoing_measurable m).comp (measurable_const.prodMk measurable_id))
    have hdir : ∀ᵐ n : Velocity ∂volume, sphereDirection e n ∉ A := by
      filter_upwards [hp,volume.ae_ne (0 : Velocity)] with n hn hn0
      change outgoing m (p,(sphereDirection e n).1) ∉ N
      rwa [direction_outgoing e m p hn0]
    have hz : (Measure.map (sphereDirection e)
        ((volume : Measure Velocity).restrict (Metric.ball 0 1))) A = 0 := by
      rw [Measure.map_apply (sphereDirection_measurable e) hA]
      have hrestrict := ae_restrict_of_ae hdir (s := Metric.ball (0 : Velocity) 1)
      simpa only [not_not,Set.preimage] using ae_iff.mp hrestrict
    have ha := sphereArea_absolutelyContinuous_directions e hz
    apply ae_iff.mpr
    simpa only [not_not,A] using ha
  have hall : ∀ᵐ z : (Velocity × Velocity) × Sphere
      ∂(volume : Measure (Velocity × Velocity)).prod sphereArea, angularOutgoing m z ∉ N :=
    (Measure.ae_prod_iff_ae_ae (hN.preimage (angularOutgoing_measurable m)).compl).mpr hsections'
  simpa only [not_not,Set.preimage] using ae_iff.mp hall

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Absolute continuity for two physical outgoing velocities with common incoming pair -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance doublePhysicalSFinite :
    SFinite ((volume : Measure (Velocity × Velocity)).prod sphereArea) :=
  Measure.prod.instSFinite

theorem relativePair_measurePreserving : MeasurePreserving relativePair
    (volume : Measure (Velocity × Velocity)) volume := by
  have hneg := (MeasurePreserving.id (volume : Measure Velocity)).prod
    (Measure.measurePreserving_neg (volume : Measure Velocity))
  have hp := hneg.comp (measurePreserving_prod_sub
    (volume : Measure Velocity) (volume : Measure Velocity))
  change MeasurePreserving relativePair ((volume : Measure Velocity).prod volume)
    ((volume : Measure Velocity).prod volume)
  have he : Prod.map id Neg.neg ∘ (fun p : Velocity × Velocity => (p.1,p.2-p.1)) = relativePair := by
    funext p
    exact Prod.ext rfl (neg_sub _ _)
  rw [he] at hp
  exact hp

theorem physicalPairAt_eq (m : Velocity) (z : (Velocity × Velocity) × Sphere) :
    physicalPairAt m z = angularOutgoing m (relativePair z.1,z.2) := by
  have hn := mem_sphere_zero_iff_norm.mp z.2.property
  have hi : inner ℝ z.2.1 z.2.1 = 1 := by rw [real_inner_self_eq_norm_sq,hn]; norm_num
  simp only [physicalPairAt,angularOutgoing,outgoing,relativePair,scatterLeft,normalComponent,hi,inv_one,mul_one]

theorem physicalPairAt_measurable (m : Velocity) : Measurable (physicalPairAt m) := by
  unfold physicalPairAt scatterLeft normalComponent
  fun_prop

theorem physicalPairAt_law_absolutelyContinuous (m : Velocity) (hm : ‖m‖ = 1) :
    (Measure.map (physicalPairAt m) ((volume : Measure (Velocity × Velocity)).prod sphereArea)) ≪
      (volume : Measure (Velocity × Velocity)) := by
  have hp := relativePair_measurePreserving.prod (MeasurePreserving.id sphereArea)
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply (physicalPairAt_measurable m) hN]
  have h := angular_outgoing_law_absolutelyContinuous m hm hN0
  rw [Measure.map_apply (angularOutgoing_measurable m) hN] at h
  have hae : ∀ᵐ z : (Velocity × Velocity) × Sphere
      ∂(volume : Measure (Velocity × Velocity)).prod sphereArea, angularOutgoing m z ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not,Set.preimage] using h
  have hh := hp.quasiMeasurePreserving.ae hae
  have hf : ∀ᵐ z : (Velocity × Velocity) × Sphere
      ∂(volume : Measure (Velocity × Velocity)).prod sphereArea, physicalPairAt m z ∉ N := by
    filter_upwards [hh] with z hz
    rwa [physicalPairAt_eq]
  simpa only [not_not,Set.preimage] using ae_iff.mp hf

theorem physicalDoubleOutgoing_measurable : Measurable physicalDoubleOutgoing := by
  unfold physicalDoubleOutgoing physicalPairAt scatterLeft normalComponent
  fun_prop

theorem physical_double_law_absolutelyContinuous :
    (Measure.map physicalDoubleOutgoing
      (((volume : Measure (Velocity × Velocity)).prod sphereArea).prod sphereArea)) ≪
        (volume : Measure (Velocity × Velocity)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [Measure.map_apply physicalDoubleOutgoing_measurable hN]
  have hsection (m : Sphere) : ∀ᵐ z : (Velocity × Velocity) × Sphere
      ∂(volume : Measure (Velocity × Velocity)).prod sphereArea, physicalPairAt m.1 z ∉ N := by
    have h := physicalPairAt_law_absolutelyContinuous m.1
      (mem_sphere_zero_iff_norm.mp m.property) hN0
    rw [Measure.map_apply (physicalPairAt_measurable m.1) hN] at h
    apply ae_iff.mpr
    simpa only [not_not,Set.preimage] using h
  have hswap : ∀ᵐ z : Sphere × ((Velocity × Velocity) × Sphere)
      ∂sphereArea.prod ((volume : Measure (Velocity × Velocity)).prod sphereArea),
      physicalDoubleOutgoing (z.2,z.1) ∉ N := by
    apply (Measure.ae_prod_iff_ae_ae
      ((hN.preimage physicalDoubleOutgoing_measurable).preimage measurable_swap).compl).mpr
    exact ae_of_all _ hsection
  have hh := (Measure.measurePreserving_swap
    (μ := ((volume : Measure (Velocity × Velocity)).prod sphereArea))
    (ν := sphereArea)).quasiMeasurePreserving.ae hswap
  change ∀ᵐ z : ((Velocity × Velocity) × Sphere) × Sphere
    ∂((volume : Measure (Velocity × Velocity)).prod sphereArea).prod sphereArea,
      physicalDoubleOutgoing z ∉ N at hh
  simpa only [not_not,Set.preimage] using ae_iff.mp hh

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Finite, absolutely continuous physical two-output reference measures -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance doubleReferenceSFinite_ra56ad6_1 :
    SFinite ((volume : Measure (Velocity × Velocity)).prod sphereArea) := Measure.prod.instSFinite
theorem rateProduct_measurable : Measurable rateProduct := by
  unfold rateProduct collisionKernel normalComponent
  fun_prop

theorem rateProduct_integrable (R : ℝ) : Integrable rateProduct (parameterMeasure R) := by
  have hpair : ∀ᵐ p : Velocity × Velocity
      ∂(volume : Measure (Velocity × Velocity)).restrict (incomingBall R), p ∈ incomingBall R :=
    ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
      (isCompact_closedBall (0 : Velocity) R)).measurableSet
  have hfirst : ∀ᵐ z : (Velocity × Velocity) × Sphere
      ∂((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)).prod sphereArea,
      z.1 ∈ incomingBall R := Measure.quasiMeasurePreserving_fst.ae hpair
  have hall : ∀ᵐ z : Parameters ∂parameterMeasure R, z.1.1 ∈ incomingBall R :=
    Measure.quasiMeasurePreserving_fst.ae hfirst
  apply (integrable_const ((2*|R|)^2)).mono' rateProduct_measurable.aestronglyMeasurable
  filter_upwards [hall] with z hz
  have hv : ‖z.1.1.1‖ ≤ |R| := (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1 : ‖z.1.1.1‖ ≤ R).trans (le_abs_self R)
  have hw : ‖z.1.1.2‖ ≤ |R| := (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2 : ‖z.1.1.2‖ ≤ R).trans (le_abs_self R)
  have hb (n : Sphere) : collisionKernel z.1.1.1 z.1.1.2 n ≤ 2*|R| := by
    have hk : collisionKernel z.1.1.1 z.1.1.2 n ≤ ‖z.1.1.1-z.1.1.2‖ := by
      simpa only [collisionKernel,normalComponent,mem_sphere_zero_iff_norm.mp n.property,mul_one] using
        abs_real_inner_le_norm (z.1.1.1-z.1.1.2) (n : Velocity)
    exact hk.trans ((norm_sub_le _ _).trans (by linarith))
  change ‖collisionKernel z.1.1.1 z.1.1.2 z.1.2.1*collisionKernel z.1.1.1 z.1.1.2 z.2.1‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (collisionKernel_nonneg _ _ _) (collisionKernel_nonneg _ _ _))]
  simpa only [pow_two] using mul_le_mul (hb z.1.2) (hb z.2) (collisionKernel_nonneg _ _ _) (by positivity)

instance physicalReferenceMeasureFinite (R : ℝ) : IsFiniteMeasure (physicalReferenceMeasure R) := by
  have := isFiniteMeasure_withDensity_ofReal (rateProduct_integrable R).hasFiniteIntegral
  unfold physicalReferenceMeasure
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply physicalDoubleOutgoing_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem physicalReferenceMeasure_absolutelyContinuous (R : ℝ) :
    physicalReferenceMeasure R ≪ (volume : Measure (Velocity × Velocity)) := by
  have hbase : parameterMeasure R ≪
      ((volume : Measure (Velocity × Velocity)).prod sphereArea).prod sphereArea :=
    (Measure.absolutelyContinuous_restrict.prod Measure.AbsolutelyContinuous.rfl).prod
      Measure.AbsolutelyContinuous.rfl
  have hw := (withDensity_absolutelyContinuous (parameterMeasure R)
    (fun z => ENNReal.ofReal (rateProduct z))).trans hbase
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hN0
  rw [physicalReferenceMeasure,Measure.map_apply physicalDoubleOutgoing_measurable hN]
  apply hw
  have h := physical_double_law_absolutelyContinuous hN0
  rwa [Measure.map_apply physicalDoubleOutgoing_measurable hN] at h

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The integrable physical two-output density and its translation continuity -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem referenceDensity_measurable (R : ℝ) : Measurable (referenceDensity R) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem referenceDensity_integrable (R : ℝ) : Integrable (referenceDensity R) := by
  have h := Measure.integrableOn_toReal_rnDeriv
    (μ := physicalReferenceMeasure R) (ν := (volume : Measure (Velocity × Velocity)))
    (measure_ne_top (physicalReferenceMeasure R) Set.univ)
  rw [IntegrableOn,Measure.restrict_univ] at h
  change Integrable (fun p : Velocity × Velocity =>
    ((physicalReferenceMeasure R).rnDeriv (volume : Measure (Velocity × Velocity)) p).toReal) volume
  exact h

theorem referenceDensity_integral (R : ℝ) (φ : Velocity × Velocity → ℝ) :
    (∫ p, referenceDensity R p*φ p) = ∫ p, φ p ∂physicalReferenceMeasure R :=
  integral_toReal_rnDeriv_mul (physicalReferenceMeasure_absolutelyContinuous R)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Physical two-output tests and the squared angular adjoint -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance doubleTestInnerSFinite (R : ℝ) :
    SFinite (((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)).prod sphereArea) :=
  Measure.prod.instSFinite

theorem referenceDensity_test (R : ℝ) {φ : Velocity × Velocity → ℝ}
    (hφ : Measurable φ) :
    (∫ p, referenceDensity R p*φ p) =
      ∫ z, rateProduct z*φ (physicalDoubleOutgoing z) ∂parameterMeasure R := by
  rw [referenceDensity_integral,physicalReferenceMeasure,
    integral_map physicalDoubleOutgoing_measurable.aemeasurable hφ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul rateProduct_measurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : 0 ≤ rateProduct z :=
    mul_nonneg (collisionKernel_nonneg _ _ _) (collisionKernel_nonneg _ _ _)
  rw [ENNReal.toReal_ofReal hz,smul_eq_mul]

theorem angularAdjoint_measurable {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (angularAdjoint ψ) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  change Measurable (fun z : (Velocity × Velocity) × Sphere =>
    collisionKernel z.1.1 z.1.2 z.2*ψ (scatterLeft z.1.1 z.1.2 z.2))
  apply Measurable.mul
  · unfold collisionKernel normalComponent
    fun_prop
  · apply hψ.comp
    unfold scatterLeft normalComponent
    fun_prop

theorem double_test_integrable (R : ℝ) {ψ : Velocity → ℝ}
    (hψ : Measurable ψ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |ψ v| ≤ C) :
    Integrable (fun z => rateProduct z*
      (ψ (physicalDoubleOutgoing z).1*ψ (physicalDoubleOutgoing z).2)) (parameterMeasure R) := by
  have hm : Measurable (fun z => ψ (physicalDoubleOutgoing z).1*ψ (physicalDoubleOutgoing z).2) :=
    (hψ.comp (measurable_fst.comp physicalDoubleOutgoing_measurable)).mul
      (hψ.comp (measurable_snd.comp physicalDoubleOutgoing_measurable))
  have hb z : |ψ (physicalDoubleOutgoing z).1*ψ (physicalDoubleOutgoing z).2| ≤ C^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0
  apply ((rateProduct_integrable R).bdd_mul hm.aestronglyMeasurable
    (ae_of_all _ hb)).congr
  exact ae_of_all _ (fun _ => mul_comm _ _)

theorem angularAdjoint_square (R : ℝ) {ψ : Velocity → ℝ}
    (hψ : Measurable ψ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |ψ v| ≤ C) :
    (∫ p in incomingBall R, (angularAdjoint ψ p)^2) =
      ∫ p, referenceDensity R p*(ψ p.1*ψ p.2) := by
  have hφ : Measurable (fun p : Velocity × Velocity => ψ p.1*ψ p.2) :=
    (hψ.comp measurable_fst).mul (hψ.comp measurable_snd)
  rw [referenceDensity_test R hφ]
  rw [parameterMeasure,integral_prod _ (double_test_integrable R hψ hC0 hC)]
  have hi := (double_test_integrable R hψ hC0 hC).integral_prod_left
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with p
  have hfactor (n : Sphere) :
      (∫ m : Sphere, rateProduct ((p,n),m)*
        (ψ (physicalDoubleOutgoing ((p,n),m)).1*ψ (physicalDoubleOutgoing ((p,n),m)).2)
        ∂sphereArea) =
      (collisionKernel p.1 p.2 n*ψ (scatterLeft p.1 p.2 n))*angularAdjoint ψ p := by
    change (∫ m : Sphere, (collisionKernel p.1 p.2 n*collisionKernel p.1 p.2 m)*
      (ψ (scatterLeft p.1 p.2 n)*ψ (scatterLeft p.1 p.2 m)) ∂sphereArea) = _
    rw [show (fun m : Sphere => (collisionKernel p.1 p.2 n*collisionKernel p.1 p.2 m)*
      (ψ (scatterLeft p.1 p.2 n)*ψ (scatterLeft p.1 p.2 m))) =
      (fun m : Sphere => (collisionKernel p.1 p.2 n*ψ (scatterLeft p.1 p.2 n))*
        (collisionKernel p.1 p.2 m*ψ (scatterLeft p.1 p.2 m))) by funext m; ring]
    exact integral_const_mul _ _
  simp_rw [hfactor]
  rw [integral_mul_const]
  exact (pow_two _).trans rfl

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SquareIntegralToL1
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing square integrals imply vanishing L1 integrals on finite measures -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness

theorem integral_abs_tendsto_zero_of_square {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : ℕ → X → ℝ}
    (hi : ∀ n, Integrable (f n) μ)
    (hi2 : ∀ n, Integrable (fun x => (f n x)^2) μ)
    (ht : Tendsto (fun n => ∫ x, (f n x)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |f n x| ∂μ) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let M := μ.real Set.univ
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  let δ := ε/(2*(M+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : δ*M < ε/2 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(M+1))).mpr
    nlinarith
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (δ*ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hlim : (∫ x, (f n x)^2 ∂μ) < δ*ε/2 := by
    have h := hN n hn
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun x => sq_nonneg _))] at h
    exact h
  have hb : (∫ x, |f n x| ∂μ) ≤ δ*M+(∫ x, (f n x)^2 ∂μ)/δ := by
    calc
      _ ≤ ∫ x, δ+(f n x)^2/δ ∂μ := by
        apply integral_mono (hi n).abs ((integrable_const δ).add ((hi2 n).div_const δ))
        intro x
        change |f n x| ≤ δ+(f n x)^2/δ
        have hs := sq_nonneg (|f n x|-δ)
        have hs' : |f n x| * δ ≤ δ^2+(f n x)^2 := by nlinarith [sq_abs (f n x)]
        calc
          _ ≤ (δ^2+(f n x)^2)/δ := (le_div_iff₀ hδ).mpr hs'
          _ = _ := by field_simp
      _ = _ := by rw [integral_add (integrable_const δ) ((hi2 n).div_const δ),
        integral_const,smul_eq_mul,integral_div]; dsimp [M] <;> ring
  have hsmall2 : (∫ x, (f n x)^2 ∂μ)/δ < ε/2 := by
    apply (div_lt_iff₀ hδ).mpr
    nlinarith
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun x => abs_nonneg _))]
  linarith

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedTranslationTests
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.physicalReferenceMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly bounded tests against small translations of an L1 pair density -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance weightedTranslationHaar : Measure.IsAddHaarMeasure (volume : Measure (Velocity × Velocity)) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem weighted_translation_identity (ρ φ : Velocity × Velocity → ℝ) (a : Velocity × Velocity) :
    (∫ p, ρ p*φ (p+a)) = ∫ p, ρ (p-a)*φ p := by
  simpa only [add_sub_cancel_right] using
    (integral_add_right_eq_self (fun p => ρ (p-a)*φ p) a)

theorem weighted_translation_difference {ρ φ : Velocity × Velocity → ℝ}
    (hρ : Integrable ρ) (hφ : Measurable φ) {C : ℝ} (hC : ∀ p, |φ p| ≤ C)
    (a : Velocity × Velocity) :
    (∫ p, ρ p*(φ (p+a)-φ p)) = ∫ p, φ p*(ρ (p-a)-ρ p) := by
  have hshift : Integrable (fun p => ρ (p-a)) := hρ.comp_sub_right a
  have hA : Integrable (fun p => ρ p*φ (p+a)) := by
    apply (hρ.bdd_mul (hφ.comp (measurable_id.add_const a)).aestronglyMeasurable
      (ae_of_all _ (fun p => hC (p+a)))).congr
    exact ae_of_all _ (fun _ => mul_comm _ _)
  have hB : Integrable (fun p => ρ p*φ p) := by
    apply (hρ.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ hC)).congr
    exact ae_of_all _ (fun _ => mul_comm _ _)
  have hD : Integrable (fun p => φ p*ρ (p-a)) :=
    hshift.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ hC)
  have hE : Integrable (fun p => φ p*ρ p) :=
    hρ.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ hC)
  calc
    _ = (∫ p, ρ p*φ (p+a))-(∫ p, ρ p*φ p) := by
      simp_rw [mul_sub]
      exact integral_sub hA hB
    _ = (∫ p, φ p*ρ (p-a))-(∫ p, φ p*ρ p) := by
      rw [weighted_translation_identity]
      simp_rw [mul_comm]
    _ = _ := by
      simp_rw [mul_sub]
      exact (integral_sub hD hE).symm

theorem weighted_translation_tests_zero {ρ : Velocity × Velocity → ℝ}
    (hρm : Measurable ρ) (hρ : Integrable ρ) {a : ℕ → Velocity × Velocity}
    (ha : Tendsto a atTop (𝓝 0)) {φ : ℕ → Velocity × Velocity → ℝ}
    (hφ : ∀ n, Measurable (φ n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n p, |φ n p| ≤ C) :
    Tendsto (fun n => ∫ p, ρ p*(φ n (p+a n)-φ n p)) atTop (𝓝 0) := by
  let f : ℕ → Velocity × Velocity → ℝ := fun n p => ρ (p-a n)-ρ p
  have hfm n : Measurable (f n) := (hρm.comp (measurable_id.sub_const (a n))).sub hρm
  have hfi n : Integrable (f n) := (hρ.comp_sub_right (a n)).sub hρ
  have hL : Tendsto (fun n => eLpNorm (f n) 1 volume) atTop (𝓝 0) := by
    have han : Tendsto (fun n => -a n) atTop (𝓝 0) := by simpa only [neg_zero] using ha.neg
    have ht := (pair_translation_L1 hρ 0).comp han
    simpa only [Function.comp_def,sub_eq_add_neg,add_zero,neg_zero,f] using ht
  have hb := Compactness.tendsto_L1_bounded_mul_zero
    (fun n => (hfm n).aestronglyMeasurable) (fun n => (hφ n).aestronglyMeasurable)
    hL hC (Filter.Eventually.of_forall (fun n => ae_of_all _ (hbound n)))
  have hi n : Integrable (fun p => φ n p*f n p) :=
    (hfi n).bdd_mul (hφ n).aestronglyMeasurable (ae_of_all _ (hbound n))
  have ht : Tendsto (fun n => ∫ p, φ n p*f n p) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_L1' (hfi := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (fun _ : Velocity × Velocity => (0:ℝ))
      (Filter.Eventually.of_forall hi) (by
        change Tendsto (fun n => eLpNorm (fun p => φ n p*f n p-0) 1 volume) atTop (𝓝 0)
        simpa only [sub_zero] using hb)
  apply ht.congr'
  exact Filter.Eventually.of_forall (fun n => (weighted_translation_difference hρ (hφ n) (hbound n) (a n)).symm)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PairTranslatedProduct
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.physicalReferenceMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A translated product of arbitrary bounded tests is small against an L1 pair density -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem translated_pair_product_zero {ρ : Velocity × Velocity → ℝ}
    (hρm : Measurable ρ) (hρ : Integrable ρ) {a : ℕ → Velocity}
    (ha : Tendsto a atTop (𝓝 0)) {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ n, Measurable (ψ n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n v, |ψ n v| ≤ C) :
    Tendsto (fun n => ∫ p : Velocity × Velocity,
      ρ p*((ψ n (p.1+a n)-ψ n p.1)*(ψ n (p.2+a n)-ψ n p.2))) atTop (𝓝 0) := by
  let φ : ℕ → Velocity × Velocity → ℝ := fun n p => ψ n p.1*ψ n p.2
  have hφ n : Measurable (φ n) := ((hψ n).comp measurable_fst).mul ((hψ n).comp measurable_snd)
  have hφbound n p : |φ n p| ≤ C^2 := by
    rw [show φ n p = ψ n p.1*ψ n p.2 from rfl,abs_mul,pow_two]
    exact mul_le_mul (hbound n p.1) (hbound n p.2) (abs_nonneg _) hC
  have haa : Tendsto (fun n => (a n,a n)) atTop (𝓝 (0 : Velocity × Velocity)) :=
    ha.prodMk_nhds ha
  have ha0 : Tendsto (fun n => (a n,(0:Velocity))) atTop (𝓝 (0 : Velocity × Velocity)) :=
    ha.prodMk_nhds tendsto_const_nhds
  have h0a : Tendsto (fun n => ((0:Velocity),a n)) atTop (𝓝 (0 : Velocity × Velocity)) :=
    tendsto_const_nhds.prodMk_nhds ha
  have h1 := weighted_translation_tests_zero hρm hρ haa hφ (sq_nonneg C) hφbound
  have h2 := weighted_translation_tests_zero hρm hρ ha0 hφ (sq_nonneg C) hφbound
  have h3 := weighted_translation_tests_zero hρm hρ h0a hφ (sq_nonneg C) hφbound
  have hi n (b : Velocity × Velocity) : Integrable (fun p => ρ p*(φ n (p+b)-φ n p)) := by
    have hm := ((hφ n).comp (measurable_id.add_const b)).sub (hφ n)
    have hb p : |φ n (p+b)-φ n p| ≤ 2*C^2 := by
      calc
        _ ≤ |φ n (p+b)|+|φ n p| := abs_sub _ _
        _ ≤ C^2+C^2 := add_le_add (hφbound n _) (hφbound n _)
        _ = _ := by ring
    apply (hρ.bdd_mul hm.aestronglyMeasurable (ae_of_all _ hb)).congr
    exact ae_of_all _ (fun _ => mul_comm _ _)
  have he n :
      (∫ p : Velocity × Velocity, ρ p*((ψ n (p.1+a n)-ψ n p.1)*(ψ n (p.2+a n)-ψ n p.2))) =
      ((∫ p, ρ p*(φ n (p+(a n,a n))-φ n p))-
        (∫ p, ρ p*(φ n (p+(a n,0))-φ n p)))-
        (∫ p, ρ p*(φ n (p+(0,a n))-φ n p)) := by
    have hfun : (fun p : Velocity × Velocity =>
        ρ p*((ψ n (p.1+a n)-ψ n p.1)*(ψ n (p.2+a n)-ψ n p.2))) =
        ((fun p => ρ p*(φ n (p+(a n,a n))-φ n p))-
          (fun p => ρ p*(φ n (p+(a n,0))-φ n p)))-
          (fun p => ρ p*(φ n (p+(0,a n))-φ n p)) := by
      funext p
      simp only [φ,Pi.sub_apply,Prod.fst_add,Prod.snd_add,add_zero]
      ring
    rw [hfun]
    change (∫ p, (ρ p*(φ n (p+(a n,a n))-φ n p)-
      ρ p*(φ n (p+(a n,0))-φ n p))-ρ p*(φ n (p+(0,a n))-φ n p)) = _
    calc
      _ = (∫ p, ρ p*(φ n (p+(a n,a n))-φ n p)-ρ p*(φ n (p+(a n,0))-φ n p))-
          (∫ p, ρ p*(φ n (p+(0,a n))-φ n p)) :=
        integral_sub ((hi n (a n,a n)).sub (hi n (a n,0))) (hi n (0,a n))
      _ = _ := congrArg (fun x => x-(∫ p, ρ p*(φ n (p+(0,a n))-φ n p)))
        (integral_sub (hi n (a n,a n)) (hi n (a n,0)))
  have ht := (h1.sub h2).sub h3
  simp only [sub_zero] at ht
  exact ht.congr' (Filter.Eventually.of_forall (fun n => (he n).symm))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AngularGainTranslationTests
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compact incoming-velocity bounds for bounded angular tests -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem angularAdjoint_abs_le {ψ : Velocity → ℝ} {C : ℝ}
    (hC : ∀ v, |ψ v| ≤ C) (p : Velocity × Velocity) :
    |angularAdjoint ψ p| ≤ (2*Real.pi*‖p.1-p.2‖)*C := by
  have hi := norm_integral_le_of_norm_le
    ((integrable_collisionKernel_sphereArea p.1 p.2).mul_const C)
    (ae_of_all _ (fun n : Sphere => show
      ‖collisionKernel p.1 p.2 n*ψ (scatterLeft p.1 p.2 n)‖ ≤
        collisionKernel p.1 p.2 n*C by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (collisionKernel_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_left (hC _) (collisionKernel_nonneg _ _ _)))
  simpa only [angularAdjoint,Real.norm_eq_abs,integral_mul_const,
    integral_collisionKernel_sphereArea] using hi

theorem angularAdjoint_bounded_on (R : ℝ) {ψ : Velocity → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ v, |ψ v| ≤ C) {p : Velocity × Velocity}
    (hp : p ∈ incomingBall R) : |angularAdjoint ψ p| ≤ 4*Real.pi*|R| *C := by
  have hv : ‖p.1‖ ≤ |R| := (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1 : ‖p.1‖ ≤ R).trans (le_abs_self R)
  have hw : ‖p.2‖ ≤ |R| := (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp.2 : ‖p.2‖ ≤ R).trans (le_abs_self R)
  apply (angularAdjoint_abs_le hC p).trans
  have hn : ‖p.1-p.2‖ ≤ 2*|R| := (norm_sub_le _ _).trans (by linarith)
  nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_right hn (mul_nonneg Real.pi_pos.le hC0)]

theorem angularAdjoint_integrableOn (R : ℝ) {ψ : Velocity → ℝ}
    (hψ : Measurable ψ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |ψ v| ≤ C) :
    IntegrableOn (angularAdjoint ψ) (incomingBall R) := by
  apply (integrable_const (4*Real.pi*|R| *C)).mono'
    (angularAdjoint_measurable hψ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
    (isCompact_closedBall (0 : Velocity) R)).measurableSet] with p hp
  exact angularAdjoint_bounded_on R hC0 hC hp

theorem angularAdjoint_square_integrableOn (R : ℝ) {ψ : Velocity → ℝ}
    (hψ : Measurable ψ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |ψ v| ≤ C) :
    IntegrableOn (fun p => (angularAdjoint ψ p)^2) (incomingBall R) := by
  apply (integrable_const ((4*Real.pi*|R| *C)^2)).mono'
    ((angularAdjoint_measurable hψ).pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
    (isCompact_closedBall (0 : Velocity) R)).measurableSet] with p hp
  rw [Real.norm_of_nonneg (sq_nonneg _),← sq_abs (angularAdjoint ψ p)]
  exact pow_le_pow_left₀ (abs_nonneg _) (angularAdjoint_bounded_on R hC0 hC hp) 2

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Uniform translation control for the physical angular adjoint -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem angularAdjoint_translation_square (R : ℝ) {a : ℕ → Velocity}
    (ha : Tendsto a atTop (𝓝 0)) {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ n, Measurable (ψ n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n v, |ψ n v| ≤ C) :
    Tendsto (fun n => ∫ p in incomingBall R,
      (angularAdjoint (fun v => ψ n (v+a n)-ψ n v) p)^2) atTop (𝓝 0) := by
  have ht := translated_pair_product_zero (referenceDensity_measurable R)
    (referenceDensity_integrable R) ha hψ hC hbound
  have he n : (∫ p in incomingBall R,
      (angularAdjoint (fun v => ψ n (v+a n)-ψ n v) p)^2) =
      ∫ p, referenceDensity R p*
        ((ψ n (p.1+a n)-ψ n p.1)*(ψ n (p.2+a n)-ψ n p.2)) := by
    apply angularAdjoint_square R
    · exact ((hψ n).comp (measurable_id.add_const (a n))).sub (hψ n)
    · exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC
    · intro v
      exact (abs_sub _ _).trans (by linarith [hbound n (v+a n),hbound n v])
  exact ht.congr' (Filter.Eventually.of_forall (fun n => (he n).symm))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # L1 translation control for bounded measurable angular tests -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem angularAdjoint_translation_L1 (R : ℝ) {a : ℕ → Velocity}
    (ha : Tendsto a atTop (𝓝 0)) {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ n, Measurable (ψ n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n v, |ψ n v| ≤ C) :
    Tendsto (fun n => ∫ p in incomingBall R,
      |angularAdjoint (fun v => ψ n (v+a n)-ψ n v) p|) atTop (𝓝 0) := by
  have hm n : Measurable (fun v => ψ n (v+a n)-ψ n v) :=
    ((hψ n).comp (measurable_id.add_const (a n))).sub (hψ n)
  have hb n v : |ψ n (v+a n)-ψ n v| ≤ 2*C :=
    (abs_sub _ _).trans (by linarith [hbound n (v+a n),hbound n v])
  have h2C : 0 ≤ 2*C := mul_nonneg (by norm_num) hC
  exact integral_abs_tendsto_zero_of_square
    (fun n => angularAdjoint_integrableOn R (hm n) h2C (hb n))
    (fun n => angularAdjoint_square_integrableOn R (hm n) h2C (hb n))
    (angularAdjoint_translation_square R ha hψ hC hbound)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Angular translation control with a measurable spacetime parameter -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

theorem angularFamily_measurable {ψ : X × Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (angularFamily ψ) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  change Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
    collisionKernel z.1.2.1 z.1.2.2 z.2*ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
  apply Measurable.mul
  · unfold collisionKernel normalComponent
    fun_prop
  · apply hψ.comp
    apply Measurable.prodMk
    · fun_prop
    · unfold scatterLeft normalComponent
      fun_prop

theorem angularFamily_integrable (R : ℝ) {μ : Measure X} [IsFiniteMeasure μ]
    {ψ : X × Velocity → ℝ} (hψ : Measurable ψ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ z, |ψ z| ≤ C) :
    Integrable (angularFamily ψ)
      (μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R))) := by
  apply (integrable_const (4*Real.pi*|R| *C)).mono'
    (angularFamily_measurable hψ).aestronglyMeasurable
  have hp : ∀ᵐ p : Velocity × Velocity ∂volume.restrict (incomingBall R), p ∈ incomingBall R :=
    ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
      (isCompact_closedBall (0 : Velocity) R)).measurableSet
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hp] with z hz
  exact angularAdjoint_bounded_on R hC0 (fun v => hC (z.1,v)) hz

theorem angularFamily_translation_L1 (R : ℝ) {μ : Measure X} [IsFiniteMeasure μ]
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0))
    {ψ : ℕ → X × Velocity → ℝ} (hψ : ∀ n, Measurable (ψ n))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ n z, |ψ n z| ≤ C) :
    Tendsto (fun n => ∫ z,
      |angularFamily (fun q => ψ n (q.1,q.2+a n)-ψ n q) z|
        ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)))
      atTop (𝓝 0) := by
  let d : ℕ → X × Velocity → ℝ := fun n q => ψ n (q.1,q.2+a n)-ψ n q
  have hm n : Measurable (d n) :=
    ((hψ n).comp (measurable_fst.prodMk (measurable_snd.add_const (a n)))).sub (hψ n)
  have hb n q : |d n q| ≤ 2*C :=
    (abs_sub _ _).trans (by linarith [hC n (q.1,q.2+a n),hC n q])
  have h2C : 0 ≤ 2*C := mul_nonneg (by norm_num) hC0
  have hi n := (angularFamily_integrable R (μ := μ) (hm n) h2C (hb n)).abs
  let B := (volume : Measure (Velocity × Velocity)).real (incomingBall R)*(4*Real.pi*|R| *(2*C))
  have hl x : Tendsto (fun n => ∫ p in incomingBall R, |angularFamily (d n) (x,p)|)
      atTop (𝓝 0) := by
    exact angularAdjoint_translation_L1 R ha
      (fun n => (hψ n).comp (measurable_const.prodMk measurable_id)) hC0
      (fun n v => hC n (x,v))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n x => ∫ p in incomingBall R, |angularFamily (d n) (x,p)|)
    (f := fun _ => (0:ℝ)) (fun _ => B)
    (fun n => (hi n).integral_prod_left.aestronglyMeasurable) (integrable_const B)
    (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun p => abs_nonneg _))]
      have hix := (angularAdjoint_integrableOn R
        ((hm n).comp (measurable_const.prodMk measurable_id)) h2C (fun v => hb n (x,v))).abs
      calc
        _ ≤ ∫ _p : Velocity × Velocity in incomingBall R, 4*Real.pi*|R| *(2*C) := by
          apply integral_mono_ae hix (integrable_const _)
          filter_upwards [ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
            (isCompact_closedBall (0 : Velocity) R)).measurableSet] with p hp
          exact angularAdjoint_bounded_on R h2C (fun v => hb n (x,v)) hp
        _ = B := by
          rw [integral_const,smul_eq_mul]
          simp only [Measure.real,Measure.restrict_apply_univ,B]))
    (ae_of_all _ hl)
  simp only [integral_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun n => (integral_prod _ (hi n)).symm)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Bounded incoming densities against arbitrary translated outgoing tests -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem bounded_gain_translation_tests {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (R : ℝ)
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0))
    {ψ : ℕ → X × Velocity → ℝ} (hψ : ∀ n, Measurable (ψ n))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ n z, |ψ n z| ≤ C)
    {g : ℕ → X × (Velocity × Velocity) → ℝ} (hg : ∀ n, Measurable (g n))
    {B : ℝ} (hB : ∀ n z, |g n z| ≤ B) :
    Tendsto (fun n => ∫ z, g n z*
      angularFamily (fun q => ψ n (q.1,q.2+a n)-ψ n q) z
      ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)))
      atTop (𝓝 0) := by
  let d : ℕ → X × Velocity → ℝ := fun n q => ψ n (q.1,q.2+a n)-ψ n q
  have hm n : Measurable (d n) :=
    ((hψ n).comp (measurable_fst.prodMk (measurable_snd.add_const (a n)))).sub (hψ n)
  have hb n q : |d n q| ≤ 2*C :=
    (abs_sub _ _).trans (by linarith [hC n (q.1,q.2+a n),hC n q])
  have h2C : 0 ≤ 2*C := mul_nonneg (by norm_num) hC0
  have hi n := angularFamily_integrable R (μ := μ) (hm n) h2C (hb n)
  have hprod n : Integrable (fun z => g n z*angularFamily (d n) z)
      (μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R))) :=
    (hi n).bdd_mul (hg n).aestronglyMeasurable (ae_of_all _ (hB n))
  have ht := angularFamily_translation_L1 R (μ := μ) ha hψ hC0 hC
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using ht.const_mul B)
  apply Eventually.of_forall
  intro n
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∫ z, ‖g n z*angularFamily (d n) z‖
        ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, B*|angularFamily (d n) z|
        ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) := by
      apply integral_mono_ae (hprod n).norm ((hi n).abs.const_mul B)
      filter_upwards [] with z
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_right (hB n z) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionDissipation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.physicalReferenceMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Passing collision tests between rates and the physical gain/loss marginals -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_8 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem collision_test_marginal {μ : Measure X} [SFinite μ]
    (r : (X × (Velocity × Velocity)) × Sphere → ℝ) (ψ : X × Velocity → ℝ)
    (hi : Integrable (fun z => ψ (z.1.1,z.1.2.1)*r z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (fun p => ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
      ∂(volume : Measure Velocity).prod sphereArea)) (μ.prod volume) ∧
    (∫ p, ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
      ∂(volume : Measure Velocity).prod sphereArea) ∂μ.prod volume) =
      ∫ z, ψ (z.1.1,z.1.2.1)*r z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have hg := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hi
  have he : (fun p : X × Velocity => ∫ q : Velocity × Sphere,
      ψ p*r (collisionGrouping.symm (p,q)) ∂(volume : Measure Velocity).prod sphereArea) =
      (fun p => ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
        ∂(volume : Measure Velocity).prod sphereArea)) := by
    funext p
    exact integral_const_mul _ _
  have hgroup : Integrable (fun y : (X × Velocity) × (Velocity × Sphere) =>
      ψ y.1*r (collisionGrouping.symm y))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) := hg
  constructor
  · have h := hgroup.integral_prod_left
    rw [he] at h
    exact h
  · calc
      _ = ∫ p, ∫ q : Velocity × Sphere, ψ p*r (collisionGrouping.symm (p,q))
          ∂(volume : Measure Velocity).prod sphereArea ∂μ.prod volume := by rw [he]
      _ = ∫ y : (X × Velocity) × (Velocity × Sphere), ψ y.1*r (collisionGrouping.symm y)
          ∂(μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea) :=
        (integral_prod _ hgroup).symm
      _ = _ := (collisionGrouping_measurePreserving μ).symm.integral_comp
        collisionGrouping.symm.measurableEmbedding (fun z => ψ (z.1.1,z.1.2.1)*r z)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PairBoundedTruncation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The physical linear gain operator on incoming pair densities -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

local instance pairGainSphereSFinite : SFinite ((volume : Measure Velocity).prod sphereArea) :=
  Measure.prod.instSFinite

omit [MeasurableSpace X] in
theorem pairPostRate_scatter (g : X × (Velocity × Velocity) → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    pairPostRate g (scatterTriple z) = pairPreRate g z := by
  unfold pairPostRate
  rw [scatterTriple_involutive z]

theorem pairPreRate_measurable {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    Measurable (pairPreRate g) := by
  apply Measurable.mul
  · unfold collisionKernel normalComponent
    fun_prop
  · exact hg.comp measurable_fst

theorem pairGain_measurable {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    Measurable (pairGain g) := by
  exact (((pairPreRate_measurable hg).comp scatterTriple_measurable).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

theorem pairGain_integrable {μ : Measure X} [SFinite μ]
    {g : X × (Velocity × Velocity) → ℝ}
    (hi : Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (pairGain g) (μ.prod volume) := by
  have hp := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hi
  change Integrable (pairPostRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) at hp
  have hh := (collision_test_marginal (pairPostRate g) (fun _ => (1:ℝ))
    (by simpa only [one_mul] using hp)).1
  change Integrable (fun p => ∫ q : Velocity × Sphere,
    pairPostRate g (collisionGrouping.symm (p,q)) ∂(volume : Measure Velocity).prod sphereArea)
      (μ.prod volume)
  simpa only [one_mul] using hh

theorem pairGain_test {μ : Measure X} [SFinite μ]
    {g : X × (Velocity × Velocity) → ℝ}
    (hi : Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    {ψ : X × Velocity → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ z, |ψ z| ≤ C) :
    (∫ p, ψ p*pairGain g p ∂μ.prod volume) =
      ∫ z, g z*angularFamily ψ z ∂μ.prod (volume : Measure (Velocity × Velocity)) := by
  have hp := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hi
  have htest : Integrable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ψ (z.1.1,z.1.2.1)*pairPostRate g z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
    hp.bdd_mul (hψ.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).aestronglyMeasurable
      (ae_of_all _ (fun z => hC _))
  unfold pairGain
  rw [(collision_test_marginal (pairPostRate g) ψ htest).2]
  have he := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z : (X × (Velocity × Velocity)) × Sphere => ψ (z.1.1,z.1.2.1)*pairPostRate g z)
  have hfun : (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ψ ((scatterTriple z).1.1,(scatterTriple z).1.2.1)*pairPostRate g (scatterTriple z)) =
      (fun z => ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*pairPreRate g z) := by
    funext z
    rw [pairPostRate_scatter]
    rfl
  change (∫ z, ψ ((scatterTriple z).1.1,(scatterTriple z).1.2.1)*pairPostRate g (scatterTriple z)
    ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) = _ at he
  rw [hfun] at he
  rw [← he]
  have hsi := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable htest
  change Integrable (fun z : (X × (Velocity × Velocity)) × Sphere =>
    ψ ((scatterTriple z).1.1,(scatterTriple z).1.2.1)*pairPostRate g (scatterTriple z))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) at hsi
  rw [hfun] at hsi
  rw [integral_prod _ hsi]
  apply integral_congr_ae
  filter_upwards [] with z
  change (∫ n : Sphere, ψ (z.1,scatterLeft z.2.1 z.2.2 n)*
    (collisionKernel z.2.1 z.2.2 n*g z) ∂sphereArea) = _
  calc
    _ = ∫ n : Sphere, g z*(collisionKernel z.2.1 z.2.2 n*
        ψ (z.1,scatterLeft z.2.1 z.2.2 n)) ∂sphereArea := by
      apply integral_congr_ae
      exact ae_of_all _ (fun _ => by ring)
    _ = _ := integral_const_mul _ _

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # L1 contraction from physical collision rates to gain densities -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

local instance pairGainL1Sphere : SFinite ((volume : Measure Velocity).prod sphereArea) :=
  Measure.prod.instSFinite

theorem pairGain_eLpNorm_le {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    eLpNorm (pairGain g) 1 (μ.prod volume) ≤
      eLpNorm (pairPreRate g) 1 ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hm := ((pairPreRate_measurable hg).comp scatterTriple_measurable).comp
    collisionGrouping.symm.measurable
  have h := Compactness.eLpNorm_integral_le (μ := μ.prod volume)
    (ν := (volume : Measure Velocity).prod sphereArea) hm
  change eLpNorm (pairGain g) 1 (μ.prod volume) ≤ _ at h
  apply h.trans_eq
  rw [eLpNorm_comp_measurePreserving
    ((pairPreRate_measurable hg).comp scatterTriple_measurable).aestronglyMeasurable
    (collisionGrouping_measurePreserving μ).symm]
  exact eLpNorm_comp_measurePreserving (pairPreRate_measurable hg).aestronglyMeasurable
    (scatterTriple_measurePreserving μ)

theorem pairGain_sub_ae {g h : X × (Velocity × Velocity) → ℝ}
    (hi : Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hj : Integrable (pairPreRate h) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    pairGain (fun z => g z-h z) =ᵐ[μ.prod volume] fun p => pairGain g p-pairGain h p := by
  have hgi := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    ((scatterTriple_measurePreserving μ).integrable_comp_of_integrable hi)
  have hhi := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    ((scatterTriple_measurePreserving μ).integrable_comp_of_integrable hj)
  filter_upwards [hgi.prod_right_ae,hhi.prod_right_ae] with p hp hq
  change (∫ q : Velocity × Sphere, pairPostRate (fun z => g z-h z) (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea) = _
  have he q : pairPostRate (fun z => g z-h z) (collisionGrouping.symm (p,q)) =
      pairPostRate g (collisionGrouping.symm (p,q))-pairPostRate h (collisionGrouping.symm (p,q)) := by
    simp only [pairPostRate,pairPreRate,mul_sub]
  simp_rw [he]
  exact integral_sub hp hq

theorem pairGain_difference_eLpNorm_le {g h : X × (Velocity × Velocity) → ℝ}
    (hg : Measurable g) (hh : Measurable h)
    (hi : Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hj : Integrable (pairPreRate h) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    eLpNorm (fun p => pairGain g p-pairGain h p) 1 (μ.prod volume) ≤
      eLpNorm (fun z => pairPreRate g z-pairPreRate h z) 1
        ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  rw [← eLpNorm_congr_ae (pairGain_sub_ae hi hj)]
  have ht := pairGain_eLpNorm_le (μ := μ) (hg.sub hh)
  have he : pairPreRate (g-h) = (fun z => pairPreRate g z-pairPreRate h z) := by
    funext z
    change collisionKernel _ _ _*(g z.1-h z.1) = _
    exact mul_sub _ _ _
  rw [he] at ht
  exact ht

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The linear velocity moment controls the physical pair-to-gain operator -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem momentPair_measurable {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    Measurable (momentPair g) := by
  unfold momentPair
  fun_prop

omit [SFinite μ] in
theorem pair_lift_eLpNorm_one {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    eLpNorm (fun z : (X × (Velocity × Velocity)) × Sphere => g z.1) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      sphereArea univ*eLpNorm g 1 (μ.prod (volume : Measure (Velocity × Velocity))) := by
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => g z.1) :=
    hg.comp measurable_fst
  rw [eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_one_eq_lintegral_enorm,
    lintegral_prod _ hm.enorm.aemeasurable]
  simp only [lintegral_const]
  rw [lintegral_mul_const _ hg.enorm,mul_comm]

omit [SFinite μ] in
theorem pairPreRate_moment_norm_le {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    eLpNorm (pairPreRate g) 1 ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
      sphereArea univ*eLpNorm (momentPair g) 1 (μ.prod (volume : Measure (Velocity × Velocity))) := by
  rw [← pair_lift_eLpNorm_one (momentPair_measurable hg)]
  apply eLpNorm_mono_ae
  filter_upwards [] with z
  change ‖collisionKernel z.1.2.1 z.1.2.2 z.2*g z.1‖ ≤
    ‖(1+‖z.1.2.1‖+‖z.1.2.2‖)*g z.1‖
  rw [norm_mul,norm_mul,Real.norm_of_nonneg (collisionKernel_nonneg _ _ _),
    Real.norm_of_nonneg (by positivity : 0 ≤ 1+‖z.1.2.1‖+‖z.1.2.2‖)]
  exact mul_le_mul_of_nonneg_right
    ((collisionKernel_le_norm _ _ _).trans ((norm_sub_le _ _).trans (by linarith)))
    (norm_nonneg _)

omit [SFinite μ] in
theorem pairPreRate_integrable_of_moment {g : X × (Velocity × Velocity) → ℝ}
    (hg : Measurable g) (hi : Integrable (momentPair g) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  apply memLp_one_iff_integrable.mp
  exact ⟨(pairPreRate_measurable hg).aestronglyMeasurable,
    (pairPreRate_moment_norm_le hg).trans_lt (ENNReal.mul_lt_top (measure_lt_top _ _)
    (memLp_one_iff_integrable.mpr hi).2)⟩

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Bounded compact truncation in the incoming pair moment norm -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

theorem incomingBall_measurable (R : ℝ) : MeasurableSet (incomingBall R) :=
  Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet

theorem boundedPairCut_measurable (R : ℝ) (B : ℝ≥0)
    {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    Measurable (boundedPairCut R B g) := by
  unfold boundedPairCut
  apply hg.ite _ measurable_const
  exact ((incomingBall_measurable R).preimage measurable_snd).inter
    (measurableSet_lt (momentPair_measurable hg).norm measurable_const)

omit [MeasurableSpace X] in
theorem boundedPairCut_bound (R : ℝ) (B : ℝ≥0)
    (g : X × (Velocity × Velocity) → ℝ) (z : X × (Velocity × Velocity)) :
    |boundedPairCut R B g z| ≤ B := by
  unfold boundedPairCut
  split_ifs with h
  · have hw : 1 ≤ 1+‖z.2.1‖+‖z.2.2‖ := by linarith [norm_nonneg z.2.1,norm_nonneg z.2.2]
    have hnorm : ‖g z‖ ≤ ‖momentPair g z‖ := by
      rw [momentPair,norm_mul,Real.norm_of_nonneg (by linarith : 0 ≤ 1+‖z.2.1‖+‖z.2.2‖)]
      nlinarith [norm_nonneg (g z)]
    have hlt : ‖momentPair g z‖ < (B:ℝ) := h.2
    exact hnorm.trans hlt.le
  · simp only [abs_zero,NNReal.coe_nonneg]

omit [MeasurableSpace X] in
theorem boundedPairCut_support (R : ℝ) (B : ℝ≥0)
    (g : X × (Velocity × Velocity) → ℝ) (z : X × (Velocity × Velocity))
    (hz : z.2 ∉ incomingBall R) : boundedPairCut R B g z = 0 := by
  simp only [boundedPairCut,hz,false_and,ite_false, if_false]

theorem boundedPairCut_moment_error {μ : Measure X} (R : ℝ) (B : ℝ≥0)
    {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g) :
    eLpNorm (momentPair (fun z => g z-boundedPairCut R B g z)) 1 (μ.prod volume) ≤
      eLpNorm (fun z => momentPair g z-momentVelocityCut R g z) 1 (μ.prod volume)+
      eLpNorm (({z | (B:ℝ) ≤ ‖momentPair g z‖}).indicator (momentPair g)) 1 (μ.prod volume) := by
  classical
  let A : Set (X × (Velocity × Velocity)) := {z | (B:ℝ) ≤ ‖momentPair g z‖}
  have he : momentPair (fun z => g z-boundedPairCut R B g z) =
      (fun z => momentPair g z-momentVelocityCut R g z)+A.indicator (momentVelocityCut R g) := by
    funext z
    simp only [Pi.add_apply,momentVelocityCut,Set.indicator_apply,mem_prod,mem_univ,true_and,A,mem_ofPred_eq]
    change (1+‖z.2.1‖+‖z.2.2‖)*(g z-
      (if z.2 ∈ incomingBall R ∧ ‖momentPair g z‖ < (B:ℝ) then g z else 0)) =
      (momentPair g z-(if z.2 ∈ incomingBall R then momentPair g z else 0))+
      (if (B:ℝ) ≤ ‖momentPair g z‖ then (if z.2 ∈ incomingBall R then momentPair g z else 0) else 0)
    by_cases hz : z.2 ∈ incomingBall R <;> by_cases ht : ‖momentPair g z‖ < (B:ℝ)
    all_goals
      simp only [← not_lt,hz,ht,not_true_eq_false,not_false_eq_true,ite_true, if_true,ite_false, if_false,
        and_true,and_false,sub_self,sub_zero,mul_zero,zero_add,add_zero] <;> rfl
  rw [he]
  apply (eLpNorm_add_le (hf := ((momentPair_measurable hg).sub
      ((momentPair_measurable hg).indicator (MeasurableSet.univ.prod (incomingBall_measurable R)))).aestronglyMeasurable)
    (hg := (((momentPair_measurable hg).indicator (MeasurableSet.univ.prod (incomingBall_measurable R))).indicator
      (measurableSet_le measurable_const (momentPair_measurable hg).norm)).aestronglyMeasurable) (by norm_num)).trans
  apply add_le_add_right
  have hvm : Measurable (momentVelocityCut R g) :=
    (momentPair_measurable hg).indicator (MeasurableSet.univ.prod (incomingBall_measurable R))
  have hAm : MeasurableSet A := measurableSet_le
    (measurable_const : Measurable (fun _ : X × (Velocity × Velocity) => (B:ℝ)))
    (momentPair_measurable hg).norm
  apply eLpNorm_mono_ae
  filter_upwards [] with z
  change ‖A.indicator (momentVelocityCut R g) z‖ ≤ ‖A.indicator (momentPair g) z‖
  by_cases hA : z ∈ A
  · simp only [indicator_of_mem hA,momentVelocityCut]
    exact norm_indicator_le_norm_self _ _
  · simp only [indicator_of_notMem hA,norm_zero,le_refl]

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocitySmoothingError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Moving velocity translations onto bounded measurable tests -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

theorem velocityShift_preserving (μ : Measure X) [SFinite μ] (a : Velocity) :
    MeasurePreserving (velocityShift (X := X) a) (μ.prod volume) (μ.prod volume) :=
  (MeasurePreserving.id μ).prod (measurePreserving_add_right (volume : Measure Velocity) a)

theorem velocityShift_test (μ : Measure X) [SFinite μ] (F ψ : X × Velocity → ℝ) (a : Velocity) :
    (∫ p, ψ p*F (p.1,p.2+a) ∂μ.prod volume) =
      ∫ p, ψ (p.1,p.2-a)*F p ∂μ.prod volume := by
  have h := (velocityShift_preserving μ a).integral_comp (velocityShift a).measurableEmbedding
    (fun p => ψ (p.1,p.2-a)*F p)
  change (∫ p, ψ (p.1,p.2+a-a)*F (p.1,p.2+a) ∂μ.prod volume) = _ at h
  simpa only [add_sub_cancel_right] using h

theorem velocityShift_difference_test {μ : Measure X} [SFinite μ] {F ψ : X × Velocity → ℝ}
    (hF : Integrable F (μ.prod volume)) (hψ : Measurable ψ)
    {C : ℝ} (hC : ∀ z, |ψ z| ≤ C) (a : Velocity) :
    (∫ p, ψ p*(F (p.1,p.2+a)-F p) ∂μ.prod volume) =
      ∫ p, (ψ (p.1,p.2-a)-ψ p)*F p ∂μ.prod volume := by
  have hshift := (velocityShift_preserving μ a).integrable_comp_of_integrable hF
  have hA : Integrable (fun p => ψ p*F (p.1,p.2+a)) (μ.prod volume) :=
    hshift.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have hB := hF.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have hC' : Integrable (fun p => ψ (p.1,p.2-a)*F p) (μ.prod volume) :=
    hF.bdd_mul (hψ.comp (measurable_fst.prodMk (measurable_snd.sub_const a))).aestronglyMeasurable
      (ae_of_all _ (fun p => hC _))
  calc
    _ = (∫ p, ψ p*F (p.1,p.2+a) ∂μ.prod volume)-(∫ p, ψ p*F p ∂μ.prod volume) := by
      simp_rw [mul_sub]
      exact integral_sub hA hB
    _ = (∫ p, ψ (p.1,p.2-a)*F p ∂μ.prod volume)-(∫ p, ψ p*F p ∂μ.prod volume) := by
      rw [velocityShift_test]
    _ = _ := by
      simp_rw [sub_mul]
      exact (integral_sub hC' hB).symm

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Integration of velocity translations against a finite convolution kernel -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem parameterShift_preserving : MeasurePreserving (parameterShift (X := X))
    ((volume : Measure Velocity).prod (μ.prod volume))
    ((volume : Measure Velocity).prod (μ.prod volume)) := by
  have hmap (a : Velocity) :
      MeasurePreserving (fun p : X × Velocity => (p.1,p.2-a)) (μ.prod volume) (μ.prod volume) := by
    have he : (fun p : X × Velocity => (p.1,p.2-a)) = ⇑(velocityShift (X := X) (-a)) := by
      funext p
      exact Prod.ext rfl (sub_eq_add_neg p.2 a)
    rw [he]
    exact velocityShift_preserving μ (-a)
  exact (MeasurePreserving.id (volume : Measure Velocity)).skew_product
    (g := fun (a : Velocity) (p : X × Velocity) => (p.1,p.2-a))
    (by fun_prop) (ae_of_all _ (fun a => (hmap a).map_eq))

theorem integrable_velocity_kernel {χ : Velocity → ℝ} {F : X × Velocity → ℝ}
    (hχ : Integrable χ) (hF : Integrable F (μ.prod volume)) :
    Integrable (fun z : Velocity × (X × Velocity) => χ z.1*F (z.2.1,z.2.2-z.1))
      ((volume : Measure Velocity).prod (μ.prod volume)) := by
  have hi := parameterShift_preserving.integrable_comp_of_integrable (hχ.mul_prod hF)
  exact hi

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # An L1 error bound for velocity smoothing by a probability kernel -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem velocitySmooth_integrable {χ : Velocity → ℝ} {F : X × Velocity → ℝ}
    (hχ : Integrable χ) (hF : Integrable F (μ.prod volume)) :
    Integrable (velocitySmooth χ F) (μ.prod volume) :=
  (integrable_velocity_kernel hχ hF).integral_prod_right

theorem velocitySmooth_difference {χ : Velocity → ℝ} {F : X × Velocity → ℝ}
    (hχ : Integrable χ) (hF : Integrable F (μ.prod volume)) (hmass : (∫ a, χ a) = 1) :
    (fun p => velocitySmooth χ F p-F p) =ᵐ[μ.prod volume]
      fun p => ∫ a : Velocity, χ a*(F (p.1,p.2-a)-F p) := by
  filter_upwards [(integrable_velocity_kernel hχ hF).prod_left_ae] with p hp
  change (∫ a : Velocity, χ a*F (p.1,p.2-a))-F p = _
  calc
    _ = (∫ a : Velocity, χ a*F (p.1,p.2-a))-(∫ a : Velocity, χ a*F p) := by
      rw [integral_mul_const,hmass,one_mul]
    _ = ∫ a : Velocity, χ a*F (p.1,p.2-a)-χ a*F p := (integral_sub hp (hχ.mul_const (F p))).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun _ => (mul_sub _ _ _).symm)

theorem velocitySmooth_error_le {χ : Velocity → ℝ} {F : X × Velocity → ℝ}
    (hχ : Integrable χ) (hF : Integrable F (μ.prod volume))
    (hχ0 : ∀ a, 0 ≤ χ a) (hmass : (∫ a, χ a) = 1) {ε : ℝ}
    (hsmall : ∀ a, χ a ≠ 0 →
      (∫ p, |F (p.1,p.2-a)-F p| ∂μ.prod volume) ≤ ε) :
    (∫ p, |velocitySmooth χ F p-F p| ∂μ.prod volume) ≤ ε := by
  let A : Velocity × (X × Velocity) → ℝ :=
    fun z => χ z.1*(F (z.2.1,z.2.2-z.1)-F z.2)
  have hAi : Integrable A ((volume : Measure Velocity).prod (μ.prod volume)) := by
    apply ((integrable_velocity_kernel hχ hF).sub (hχ.mul_prod hF)).congr
    exact ae_of_all _ (fun z => (mul_sub _ _ _).symm)
  have hnorm a : (∫ p, ‖A (a,p)‖ ∂μ.prod volume) =
      χ a*(∫ p, |F (p.1,p.2-a)-F p| ∂μ.prod volume) := by
    simp only [A,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hχ0 a)]
    exact integral_const_mul _ _
  calc
    _ = ∫ p, |∫ a : Velocity, A (a,p)| ∂μ.prod volume := by
      apply integral_congr_ae
      filter_upwards [velocitySmooth_difference hχ hF hmass] with p hp
      exact congrArg abs hp
    _ ≤ ∫ p, (∫ a : Velocity, ‖A (a,p)‖) ∂μ.prod volume := by
      apply integral_mono hAi.integral_prod_right.norm hAi.integral_norm_prod_right
      intro p
      exact norm_integral_le_integral_norm _
    _ = ∫ a : Velocity, (∫ p, ‖A (a,p)‖ ∂μ.prod volume) :=
      (integral_integral_swap hAi.norm).symm
    _ ≤ ∫ a : Velocity, χ a*ε := by
      apply integral_mono_ae hAi.norm.integral_prod_left (hχ.mul_const ε)
      filter_upwards [] with a
      rw [hnorm]
      by_cases ha : χ a = 0
      · simp only [ha,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hsmall a ha) (hχ0 a)
    _ = ε := by rw [integral_mul_const,hmass,one_mul]

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedPairRate
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform L1 velocity translations of gains from bounded compact incoming densities -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem pairIntegral_localize {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (R : ℝ) (g φ : X × (Velocity × Velocity) → ℝ)
    (hg : ∀ z, z.2 ∉ incomingBall R → g z = 0) :
    (∫ z, g z*φ z ∂μ.prod (volume : Measure (Velocity × Velocity))) =
      ∫ z, g z*φ z ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) := by
  have he : μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) =
      (μ.prod (volume : Measure (Velocity × Velocity))).restrict (univ ×ˢ incomingBall R) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := μ) (ν := (volume : Measure (Velocity × Velocity))) univ (incomingBall R))
  rw [he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hz' : z.2 ∉ incomingBall R := by simpa only [mem_prod,mem_univ,true_and] using hz
  rw [hg z hz',zero_mul]

theorem bounded_pairGain_translation {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (R : ℝ)
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0))
    {g : ℕ → X × (Velocity × Velocity) → ℝ} (hg : ∀ n, Measurable (g n))
    {B : ℝ} (hB : ∀ n z, |g n z| ≤ B)
    (hs : ∀ n z, z.2 ∉ incomingBall R → g n z = 0)
    (hi : ∀ n, Integrable (pairPreRate (g n))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Tendsto (fun n => ∫ p, |pairGain (g n) (p.1,p.2+a n)-pairGain (g n) p| ∂μ.prod volume)
      atTop (𝓝 0) := by
  let D : ℕ → X × Velocity → ℝ := fun n p => pairGain (g n) (p.1,p.2+a n)-pairGain (g n) p
  let ψ : ℕ → X × Velocity → ℝ := fun n p => if 0 ≤ D n p then 1 else -1
  have hD n : Measurable (D n) :=
    ((pairGain_measurable (hg n)).comp
      (measurable_fst.prodMk (measurable_snd.add_const (a n)))).sub (pairGain_measurable (hg n))
  have hψ n : Measurable (ψ n) :=
    Measurable.ite (measurableSet_le measurable_const (hD n)) measurable_const measurable_const
  have hψB n p : |ψ n p| ≤ 1 := by dsimp only [ψ]; split <;> norm_num
  have hsign n p : ψ n p*D n p = |D n p| := by
    dsimp only [ψ]
    split_ifs with h
    · rw [one_mul,abs_of_nonneg h]
    · rw [neg_one_mul,abs_of_neg (lt_of_not_ge h)]
  have han : Tendsto (fun n => -a n) atTop (𝓝 0) := by simpa only [neg_zero] using ha.neg
  have ht := bounded_gain_translation_tests (μ := μ) R han hψ (by norm_num : (0:ℝ) ≤ 1) hψB hg hB
  have he n : (∫ p, |D n p| ∂μ.prod volume) =
      ∫ z, g n z*angularFamily (fun q => ψ n (q.1,q.2 + -a n)-ψ n q) z
        ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) := by
    have hφ : Measurable (fun q => ψ n (q.1,q.2-a n)-ψ n q) :=
      ((hψ n).comp (measurable_fst.prodMk (measurable_snd.sub_const (a n)))).sub (hψ n)
    have hφB q : |ψ n (q.1,q.2-a n)-ψ n q| ≤ 2 :=
      (abs_sub _ _).trans (by linarith [hψB n (q.1,q.2-a n),hψB n q])
    calc
      _ = ∫ p, ψ n p*(pairGain (g n) (p.1,p.2+a n)-pairGain (g n) p) ∂μ.prod volume := by
        apply integral_congr_ae
        exact ae_of_all _ (fun p => (hsign n p).symm)
      _ = ∫ p, (ψ n (p.1,p.2-a n)-ψ n p)*pairGain (g n) p ∂μ.prod volume :=
        velocityShift_difference_test (pairGain_integrable (hi n)) (hψ n) (hψB n) (a n)
      _ = ∫ z, g n z*angularFamily (fun q => ψ n (q.1,q.2-a n)-ψ n q) z
          ∂μ.prod (volume : Measure (Velocity × Velocity)) := pairGain_test (hi n) hφ hφB
      _ = _ := by
        rw [pairIntegral_localize μ R (g n) _ (hs n)]
        simp only [sub_eq_add_neg]
  exact ht.congr' (Eventually.of_forall (fun n => (he n).symm))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Integrability of the physical rate for bounded compact incoming pair densities -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem bounded_pairPreRate_integrable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (R : ℝ)
    {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B)
    (hs : ∀ z, z.2 ∉ incomingBall R → g z = 0) :
    Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  let S : Set ((X × (Velocity × Velocity)) × Sphere) := (univ ×ˢ incomingBall R) ×ˢ univ
  have he : (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict S) =
      (μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R))).prod sphereArea := by
    dsimp only [S]
    rw [← Measure.prod_restrict,Measure.restrict_univ,← Measure.prod_restrict,Measure.restrict_univ]
  have hi : IntegrableOn (pairPreRate g) S
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    rw [IntegrableOn,he]
    apply (integrable_const (2*|R| * |B|)).mono' (pairPreRate_measurable hg).aestronglyMeasurable
    have hp : ∀ᵐ p : Velocity × Velocity ∂volume.restrict (incomingBall R), p ∈ incomingBall R :=
      ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
        (isCompact_closedBall (0 : Velocity) R)).measurableSet
    have hq : ∀ᵐ z : X × (Velocity × Velocity)
        ∂μ.prod (volume.restrict (incomingBall R)), z.2 ∈ incomingBall R :=
      Measure.quasiMeasurePreserving_snd.ae hp
    have hz : ∀ᵐ z : (X × (Velocity × Velocity)) × Sphere
        ∂(μ.prod (volume.restrict (incomingBall R))).prod sphereArea, z.1.2 ∈ incomingBall R :=
      Measure.quasiMeasurePreserving_fst.ae hq
    filter_upwards [hz] with z hz
    have hv : ‖z.1.2.1‖ ≤ |R| := (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1 : ‖z.1.2.1‖ ≤ R).trans (le_abs_self R)
    have hw : ‖z.1.2.2‖ ≤ |R| := (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2 : ‖z.1.2.2‖ ≤ R).trans (le_abs_self R)
    have hk : collisionKernel z.1.2.1 z.1.2.2 z.2 ≤ 2*|R| :=
      (collisionKernel_le_norm _ _ _).trans ((norm_sub_le _ _).trans (by linarith))
    change ‖collisionKernel z.1.2.1 z.1.2.2 z.2*g z.1‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (collisionKernel_nonneg _ _ _)]
    exact mul_le_mul hk ((hB z.1).trans (le_abs_self B)) (abs_nonneg _) (by positivity)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro z hz
  have hp : z.1.2 ∉ incomingBall R := by
    simpa only [S,mem_prod,mem_univ,true_and,and_true] using hz
  change collisionKernel _ _ _*g z.1 = 0
  rw [hs z.1 hp,mul_zero]

theorem bounded_pairGain_translation_no_rate_assumption {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (R : ℝ)
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0))
    {g : ℕ → X × (Velocity × Velocity) → ℝ} (hg : ∀ n, Measurable (g n))
    {B : ℝ} (hB : ∀ n z, |g n z| ≤ B)
    (hs : ∀ n z, z.2 ∉ incomingBall R → g n z = 0) :
    Tendsto (fun n => ∫ p, |pairGain (g n) (p.1,p.2+a n)-pairGain (g n) p| ∂μ.prod volume)
      atTop (𝓝 0) :=
  bounded_pairGain_translation R ha hg hB hs
    (fun n => bounded_pairPreRate_integrable R (hg n) (hB n) (hs n))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SmoothedPrePostIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.physicalReferenceMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The outgoing smoothing kernel is the actual incoming physical collision rate -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*}

theorem massNormalizedPreRate_eq_pair (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    massNormalizedPreRate f z = collisionKernel z.1.2.1 z.1.2.2 z.2*
      normalizedPair volume f z.1 := by
  unfold massNormalizedPreRate preRate normalizedPair normalizedTensor
  ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_L1VelocityTranslationApproximation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Passing velocity translation continuity through uniform L1 approximation -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem velocityTranslation_compare {F H : X × Velocity → ℝ}
    (hF : Integrable F (μ.prod volume)) (hH : Integrable H (μ.prod volume)) (a : Velocity) :
    (∫ p, |F (p.1,p.2+a)-F p| ∂μ.prod volume) ≤
      2*(∫ p, |F p-H p| ∂μ.prod volume)+
        (∫ p, |H (p.1,p.2+a)-H p| ∂μ.prod volume) := by
  have hFs := (velocityShift_preserving μ a).integrable_comp_of_integrable hF
  have hHs := (velocityShift_preserving μ a).integrable_comp_of_integrable hH
  have hA : Integrable (fun p => |F (p.1,p.2+a)-H (p.1,p.2+a)|) (μ.prod volume) :=
    (hFs.sub hHs).abs
  have hB : Integrable (fun p => |H (p.1,p.2+a)-H p|) (μ.prod volume) := (hHs.sub hH).abs
  have hC : Integrable (fun p => |F p-H p|) (μ.prod volume) := (hF.sub hH).abs
  have hs := (velocityShift_preserving μ a).integral_comp (velocityShift a).measurableEmbedding
    (fun p => |F p-H p|)
  calc
    _ ≤ ∫ p, (|F (p.1,p.2+a)-H (p.1,p.2+a)|+|H (p.1,p.2+a)-H p|)+|F p-H p|
        ∂μ.prod volume := by
      apply integral_mono (hFs.sub hF).abs ((hA.add hB).add hC)
      intro p
      change |F (p.1,p.2+a)-F p| ≤
        (|F (p.1,p.2+a)-H (p.1,p.2+a)|+|H (p.1,p.2+a)-H p|)+|F p-H p|
      have h1 := abs_sub_le (F (p.1,p.2+a)) (H (p.1,p.2+a)) (H p)
      have h2 := abs_sub_le (F (p.1,p.2+a)) (H p) (F p)
      rw [abs_sub_comm (H p) (F p)] at h2
      linarith
    _ = (∫ p, |F (p.1,p.2+a)-H (p.1,p.2+a)|+|H (p.1,p.2+a)-H p| ∂μ.prod volume)+
        (∫ p, |F p-H p| ∂μ.prod volume) := integral_add (hA.add hB) hC
    _ = ((∫ p, |F (p.1,p.2+a)-H (p.1,p.2+a)| ∂μ.prod volume)+
        (∫ p, |H (p.1,p.2+a)-H p| ∂μ.prod volume))+
        (∫ p, |F p-H p| ∂μ.prod volume) :=
      congrArg (fun r => r+(∫ p, |F p-H p| ∂μ.prod volume)) (integral_add hA hB)
    _ = _ := by
      change (∫ p, |F (velocityShift a p)-H (velocityShift a p)| ∂μ.prod volume)+
        (∫ p, |H (p.1,p.2+a)-H p| ∂μ.prod volume)+(∫ p, |F p-H p| ∂μ.prod volume) = _
      rw [hs]
      ring

theorem velocityTranslation_of_uniform_L1_approximation
    {F : ℕ → X × Velocity → ℝ} (hF : ∀ n, Integrable (F n) (μ.prod volume))
    {a : ℕ → Velocity}
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ H : ℕ → X × Velocity → ℝ,
      (∀ n, Integrable (H n) (μ.prod volume)) ∧
      (∀ n, (∫ p, |F n p-H n p| ∂μ.prod volume) ≤ ε) ∧
      Tendsto (fun n => ∫ p, |H n (p.1,p.2+a n)-H n p| ∂μ.prod volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p, |F n (p.1,p.2+a n)-F n p| ∂μ.prod volume) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨H,hHi,hHe,hHt⟩ := happrox (ε/4) (by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hHt (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hnn := hN n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun p => abs_nonneg _))] at hnn ⊢
  have hc := velocityTranslation_compare (hF n) (hHi n) (a n)
  linarith [hHe n]

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedPairCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual entropy-controlled normalized pairs admit bounded compact moment approximations -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

omit [MeasurableSpace X] in
theorem momentPair_normalizedPair (f : X × Velocity → ℝ) :
    momentPair (normalizedPair volume f) = weightedNormalizedPair f := rfl

omit [MeasurableSpace X] in
theorem momentVelocityCut_normalizedPair (R : ℝ) (f : X × Velocity → ℝ) :
    momentVelocityCut R (normalizedPair volume f) = pairVelocityCut R f := by
  funext z
  by_cases hv : ‖z.2.1‖ ≤ R <;> by_cases hw : ‖z.2.2‖ ≤ R <;>
    simp [momentVelocityCut,incomingBall,Metric.mem_closedBall,dist_zero_right,
      hv,hw,pairVelocityCut,momentPair,weightedNormalizedPair,pairVelocityWeight]

theorem normalizedPair_bounded_moment_approximation
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (R : ℝ) (_hR : 0 < R) (B : ℝ≥0) (u : ℕ → X × (Velocity × Velocity) → ℝ),
      (∀ n, Measurable (u n)) ∧ (∀ n z, |u n z| ≤ B) ∧
      (∀ n z, z.2 ∉ incomingBall R → u n z = 0) ∧
      (∀ n, eLpNorm (momentPair (fun z => normalizedPair volume (f n) z-u n z)) 1
        (μ.prod (volume : Measure (Velocity × Velocity))) ≤ ε) := by
  have hhalf : 0 < ε/2 := ENNReal.half_pos hε.ne'
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (8*C) hhalf
  let R : ℝ := (j:ℝ)+1
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hui := weightedNormalizedPair_uniformIntegrable hfm hf hi hb
  rw [← Measure.volume_eq_prod] at hui
  obtain ⟨B,hB⟩ := hui.spec (by norm_num) (by norm_num) hhalf
  let u := fun n => boundedPairCut R B (normalizedPair volume (f n))
  have hgm n : Measurable (normalizedPair volume (f n)) :=
    normalizedTensor_measurable (fiberMass_measurable (hfm n)) (hfm n) (hfm n)
  refine ⟨R,hR,B,u,fun n => boundedPairCut_measurable R B (hgm n),
    fun n z => boundedPairCut_bound R B _ z,
    fun n z hz => boundedPairCut_support R B _ z hz,fun n => ?_⟩
  have hvel : eLpNorm (fun z => momentPair (normalizedPair volume (f n)) z-
      momentVelocityCut R (normalizedPair volume (f n)) z) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) ≤ ε/2 := by
    rw [momentPair_normalizedPair,momentVelocityCut_normalizedPair]
    apply (pairVelocityCut_L1_error hR (hfm n) (hf n) (hi n) (hb n)).trans
    exact hj
  have hamp : eLpNorm (({z | B ≤ ‖momentPair (normalizedPair volume (f n)) z‖₊}).indicator
      (momentPair (normalizedPair volume (f n)))) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) ≤ ε/2 := by
    simpa only [momentPair_normalizedPair] using hB n
  exact ((boundedPairCut_moment_error R B (hgm n)).trans
    (add_le_add hvel hamp)).trans_eq ε.add_halves

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PairPatchCover
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Gain translation control from bounded compact moment approximations -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem pairGain_translation_of_moment_approximation
    {g : ℕ → X × (Velocity × Velocity) → ℝ}
    (hgm : ∀ n, Measurable (g n))
    (hmi : ∀ n, Integrable (momentPair (g n)) (μ.prod (volume : Measure (Velocity × Velocity))))
    (happrox : ∀ δ : ℝ, 0 < δ →
      ∃ (R : ℝ) (_hR : 0 < R) (B : ℝ≥0) (u : ℕ → X × (Velocity × Velocity) → ℝ),
        (∀ n, Measurable (u n)) ∧ (∀ n z, |u n z| ≤ B) ∧
        (∀ n z, z.2 ∉ incomingBall R → u n z = 0) ∧
        (∀ n, eLpNorm (momentPair (fun z => g n z-u n z)) 1
          (μ.prod (volume : Measure (Velocity × Velocity))) ≤ ENNReal.ofReal δ))
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p,
      |pairGain (g n) (p.1,p.2+a n)-pairGain (g n) p| ∂μ.prod volume) atTop (𝓝 0) := by
  have hri n := pairPreRate_integrable_of_moment (hgm n) (hmi n)
  apply velocityTranslation_of_uniform_L1_approximation (fun n => pairGain_integrable (hri n))
  intro ε hε
  let D := sphereArea.real univ
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  let δ := ε/(D+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨R,hR,B,u,hum,huB,hus,herr⟩ := happrox δ hδ
  have hui n := bounded_pairPreRate_integrable (μ := μ) R (hum n) (huB n) (hus n)
  refine ⟨fun n => pairGain (u n),fun n => pairGain_integrable (hui n),?_,
    bounded_pairGain_translation_no_rate_assumption R ha hum huB hus⟩
  intro n
  have he : (fun z => pairPreRate (g n) z-pairPreRate (u n) z) =
      pairPreRate (fun z => g n z-u n z) := by
    funext z
    exact (mul_sub _ _ _).symm
  have hn : eLpNorm (fun p => pairGain (g n) p-pairGain (u n) p) 1 (μ.prod volume) ≤
      sphereArea univ*eLpNorm (momentPair (fun z => g n z-u n z)) 1
        (μ.prod (volume : Measure (Velocity × Velocity))) := by
    apply (pairGain_difference_eLpNorm_le (hgm n) (hum n) (hri n) (hui n)).trans
    rw [he]
    exact pairPreRate_moment_norm_le ((hgm n).sub (hum n))
  have hDreal : ENNReal.ofReal D = sphereArea univ :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  have heps : D*δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < D+1)).mpr
    nlinarith
  have heL : eLpNorm (fun p => pairGain (g n) p-pairGain (u n) p) 1 (μ.prod volume) ≤
      ENNReal.ofReal ε := by
    apply hn.trans
    calc
      _ ≤ sphereArea univ*ENNReal.ofReal δ := mul_le_mul' le_rfl (herr n)
      _ = ENNReal.ofReal (D*δ) := by rw [← hDreal,ENNReal.ofReal_mul hD]
      _ ≤ _ := ENNReal.ofReal_le_ofReal heps
  exact Published.integral_abs_le_of_eLpNorm_le
    ((pairGain_integrable (hri n)).sub (pairGain_integrable (hui n))) hε.le heL


end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedNormalizedGainTranslation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded incoming weights preserve the actual normalized-gain translation estimate -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weighted_normalizedGain_translation
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    {w : X × (Velocity × Velocity) → ℝ} (hw : Measurable w) (K : ℝ≥0)
    (hK : ∀ z, |w z| ≤ K) {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p,
      |pairGain (fun z => w z*normalizedPair volume (f n) z) (p.1,p.2+a n)-
        pairGain (fun z => w z*normalizedPair volume (f n) z) p| ∂μ.prod volume) atTop (𝓝 0) := by
  let g := fun n => normalizedPair volume (f n)
  have hgm n : Measurable (g n) :=
    normalizedTensor_measurable (fiberMass_measurable (hfm n)) (hfm n) (hfm n)
  have hmi n : Integrable (momentPair (g n)) (μ.prod (volume : Measure (Velocity × Velocity))) := by
    have hh := weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
    rw [← Measure.volume_eq_prod] at hh
    exact hh
  have hmul (u : X × (Velocity × Velocity) → ℝ) :
      momentPair (fun z => w z*u z) = fun z => w z*momentPair u z := by
    funext z
    unfold momentPair
    ring
  apply pairGain_translation_of_moment_approximation (fun n => hw.mul (hgm n))
    (fun n => by
      change Integrable (momentPair (fun z => w z*g n z)) (μ.prod volume)
      rw [hmul]
      exact (hmi n).bdd_mul hw.aestronglyMeasurable (ae_of_all _ hK)) _ ha
  intro δ hδ
  let ρ := δ/((K:ℝ)+1)
  have hρ : 0 < ρ := div_pos hδ (by positivity)
  obtain ⟨R,hR,B,u,hum,huB,hus,herr⟩ := normalizedPair_bounded_moment_approximation
    hfm hf hi hb (ENNReal.ofReal_pos.mpr hρ)
  refine ⟨R,hR,K*B,(fun n z => w z*u n z),fun n => hw.mul (hum n),?_,?_,?_⟩
  · intro n z
    rw [abs_mul,NNReal.coe_mul]
    exact mul_le_mul (hK z) (huB n z) (abs_nonneg _) K.coe_nonneg
  · intro n z hz
    change w z*u n z = 0
    rw [hus n z hz,mul_zero]
  · intro n
    change eLpNorm (momentPair (fun z => w z*g n z-w z*u n z)) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) ≤ ENNReal.ofReal δ
    have he : momentPair (fun z => w z*g n z-w z*u n z) =
        fun z => w z*momentPair (fun y => g n y-u n y) z := by
      funext z
      unfold momentPair
      ring
    rw [he]
    have hm := momentPair_measurable ((hgm n).sub (hum n))
    have hn : eLpNorm (fun z => w z*momentPair (fun y => g n y-u n y) z) 1
        (μ.prod (volume : Measure (Velocity × Velocity))) ≤
        ENNReal.ofReal (K:ℝ)*eLpNorm (momentPair (fun y => g n y-u n y)) 1
          (μ.prod (volume : Measure (Velocity × Velocity))) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards [] with z
      change ‖w z*momentPair (fun y => g n y-u n y) z‖ ≤
        (K:ℝ)*‖momentPair (fun y => g n y-u n y) z‖
      rw [norm_mul,Real.norm_eq_abs (w z)]
      exact mul_le_mul_of_nonneg_right (hK z) (norm_nonneg _)
    have hsmall : (K:ℝ)*ρ ≤ δ := by
      dsimp only [ρ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < (K:ℝ)+1)).mpr
      nlinarith [K.coe_nonneg]
    exact hn.trans ((mul_le_mul' le_rfl (herr n)).trans (by
      rw [← ENNReal.ofReal_mul K.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal hsmall))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedGainSmoothingAE
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Incoming-velocity localization of the actual physical gain -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem localizedPostRate_integrable (η : C(Velocity,ℝ)) (hη : HasCompactSupport η)
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (localizedPostRate η f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  obtain ⟨B,hB⟩ := η.continuous.bounded_above_of_compact_support hη
  have hB0 : 0 ≤ B := (abs_nonneg (η 0)).trans (hB 0)
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      η (scatterLeft z.1.2.1 z.1.2.2 z.2)*η (scatterRight z.1.2.1 z.1.2.2 z.2)) := by
    unfold scatterLeft scatterRight normalComponent
    fun_prop
  apply (massNormalizedPostRate_integrable hfm hi).bdd_mul hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0

theorem localizedPhysicalGain_integrable (η : C(Velocity,ℝ)) (hη : HasCompactSupport η)
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (localizedPhysicalGain η f) (μ.prod volume) := by
  have h := collision_test_marginal (localizedPostRate η f) (fun _ => (1:ℝ))
    (by simpa only [one_mul] using localizedPostRate_integrable η hη hfm hi)
  change Integrable (fun p => ∫ q : Velocity × Sphere,
    localizedPostRate η f (collisionGrouping.symm (p,q)) ∂(volume : Measure Velocity).prod sphereArea)
      (μ.prod volume)
  simpa only [one_mul] using h.1

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Identifying the localized physical gain with the linear pair operator -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness
variable {X : Type*}

theorem localizedPair_preRate (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    pairPreRate (localizedPair η f) z =
      (η z.1.2.1*η z.1.2.2)*massNormalizedPreRate f z := by
  rw [massNormalizedPreRate_eq_pair]
  unfold pairPreRate localizedPair
  ring

theorem localizedPair_postRate (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    pairPostRate (localizedPair η f) z = localizedPostRate η f z := by
  rw [pairPostRate,localizedPair_preRate]
  rfl

theorem localizedPhysicalGain_eq_pairGain [MeasurableSpace X] (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ) :
    localizedPhysicalGain η f = pairGain (localizedPair η f) := by
  funext p
  unfold localizedPhysicalGain pairGain
  apply integral_congr_ae
  exact ae_of_all _ (fun q => (localizedPair_postRate η f _).symm)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Velocity translations of the actual localized physical gains -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem localizedGain_translation
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (η : C(Velocity,ℝ)) (hη : HasCompactSupport η)
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p,
      |localizedPhysicalGain η (f n) (p.1,p.2+a n)-localizedPhysicalGain η (f n) p|
      ∂μ.prod volume) atTop (𝓝 0) := by
  obtain ⟨B,hB⟩ := η.continuous.bounded_above_of_compact_support hη
  have hB0 : 0 ≤ B := (abs_nonneg (η 0)).trans (hB 0)
  let K : ℝ≥0 := ⟨B^2,sq_nonneg B⟩
  have hw : Measurable (fun z : X × (Velocity × Velocity) => η z.2.1*η z.2.2) := by fun_prop
  have hK (z : X × (Velocity × Velocity)) : |η z.2.1*η z.2.2| ≤ K := by
    change |η z.2.1*η z.2.2| ≤ B^2
    rw [abs_mul,pow_two]
    exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hB0
  have ht := weighted_normalizedGain_translation (μ := μ) hfm hf hi hb hw K hK ha
  simp_rw [localizedPhysicalGain_eq_pairGain]
  change Tendsto (fun n => ∫ p,
    |pairGain (fun z => η z.2.1*η z.2.2*normalizedPair volume (f n) z) (p.1,p.2+a n)-
      pairGain (fun z => η z.2.1*η z.2.2*normalizedPair volume (f n) z) p|
      ∂μ.prod volume) atTop (𝓝 0)
  exact ht

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformGainTranslation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common velocity translation modulus for the physical gain sequence -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem uniform_zero_of_all_velocity_sequences {F : ℕ → Velocity → ℝ}
    (h : ∀ (i : ℕ → ℕ) (a : ℕ → Velocity), Tendsto a atTop (𝓝 0) →
      Tendsto (fun n => F (i n) (a n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n a, ‖a‖ < δ → |F n a| < ε := by
  classical
  by_contra hh
  push Not at hh
  have hb (k : ℕ) : ∃ n a, ‖a‖ < 1/((k:ℝ)+1) ∧ ε ≤ |F n a| :=
    hh (1/((k:ℝ)+1)) (by positivity)
  choose i a ha hbad using hb
  have ht : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hat : Tendsto a atTop (𝓝 0) :=
    squeeze_zero_norm' (Eventually.of_forall (fun k => (ha k).le)) ht
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (h i a hat) ε hε
  have hn := hN N le_rfl
  rw [Real.dist_eq,sub_zero] at hn
  exact (not_lt_of_ge (hbad N)) hn

open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem localizedGain_uniform_translation
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (η : C(Velocity,ℝ)) (hη : HasCompactSupport η) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n a, ‖a‖ < δ →
      (∫ p, |localizedPhysicalGain η (f n) (p.1,p.2+a)-localizedPhysicalGain η (f n) p|
        ∂μ.prod volume) < ε := by
  obtain ⟨δ,hδ,hsmall⟩ := uniform_zero_of_all_velocity_sequences
    (F := fun n a => ∫ p,
      |localizedPhysicalGain η (f n) (p.1,p.2+a)-localizedPhysicalGain η (f n) p|
      ∂μ.prod volume)
    (fun i a ha => localizedGain_translation (μ := μ) (fun n => hfm (i n))
      (fun n => hf (i n)) (fun n => hi (i n)) (fun n => hb (i n)) η hη ha) ε hε
  refine ⟨δ,hδ,fun n a ha => ?_⟩
  simpa only [abs_of_nonneg (integral_nonneg (fun p => abs_nonneg _))] using hsmall n a ha

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_GainSmoothingError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common L1 smoothing error for the actual localized gain sequence -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem localizedGain_uniform_smoothing
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (η : C(Velocity,ℝ)) (hη : HasCompactSupport η) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ χ : Velocity → ℝ,
      Integrable χ → (∀ a, 0 ≤ χ a) → (∫ a, χ a) = 1 →
      (∀ a, χ a ≠ 0 → ‖a‖ < δ) → ∀ n,
      (∫ p, |velocitySmooth χ (localizedPhysicalGain η (f n)) p-
        localizedPhysicalGain η (f n) p| ∂μ.prod volume) ≤ ε := by
  obtain ⟨δ,hδ,hsmall⟩ := localizedGain_uniform_translation hfm hf hi hb η hη ε hε
  refine ⟨δ,hδ,fun χ hχ hχ0 hmass hs n => ?_⟩
  have hwi : Integrable (weightedNormalizedPair (f n))
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
  apply velocitySmooth_error_le hχ (localizedPhysicalGain_integrable η hη (hfm n) hwi) hχ0 hmass
  intro a ha
  have hs' : ‖-a‖ < δ := by simpa only [norm_neg] using hs a ha
  have ht := (hsmall n (-a) hs').le
  simpa only [sub_eq_add_neg] using ht

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_StrongCompactPairTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong L1 convergence with uniformly small errors on both sides -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strongL1_of_two_sided_approximations
    {f : ℕ → X → ℝ} {g : X → ℝ} {u : ℕ → ℕ → X → ℝ} {v : ℕ → X → ℝ}
    {δ : ℕ → ℝ≥0∞} (hδ : Tendsto δ atTop (𝓝 0))
    (hf : ∀ j n, eLpNorm (f n-u j n) 1 μ ≤ δ j)
    (hg : ∀ j, eLpNorm (v j-g) 1 μ ≤ δ j)
    (hu : ∀ j, Tendsto (fun n => eLpNorm (u j n-v j) 1 μ) atTop (𝓝 0))
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hum : ∀ j n, AEStronglyMeasurable (u j n) μ)
    (hvm : ∀ j, AEStronglyMeasurable (v j) μ) (hgm : AEStronglyMeasurable g μ) :
    Tendsto (fun n => eLpNorm (f n-g) 1 μ) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε4 : 0 < ε/4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨j,hj⟩ := (ENNReal.tendsto_nhds_zero.mp hδ (ε/4) hε4).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hu j) (ε/4) hε4] with n hn
  have htri (a b c : X → ℝ) (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
      (hc : AEStronglyMeasurable c μ) : eLpNorm (a-c) 1 μ ≤ eLpNorm (a-b) 1 μ+eLpNorm (b-c) 1 μ := by
    have he : a-c = (a-b)+(b-c) := by ext x; simp
    rw [he]
    exact eLpNorm_add_le (hf := ha.sub hb) (hg := hb.sub hc) (by norm_num)
  calc
    _ ≤ eLpNorm (f n-u j n) 1 μ+eLpNorm (u j n-g) 1 μ := htri _ _ _ (hfm n) (hum j n) hgm
    _ ≤ δ j+(eLpNorm (u j n-v j) 1 μ+δ j) :=
      add_le_add (hf j n) ((htri _ _ _ (hum j n) (hvm j) hgm).trans (add_le_add le_rfl (hg j)))
    _ ≤ ε/4+(ε/4+ε/4) := add_le_add hj (add_le_add hn hj)
    _ ≤ ε := by
      calc
        ε/4+(ε/4+ε/4) ≤ ε/4+(ε/4+(ε/4+ε/4)) := by gcongr; exact le_self_add
        _ = 4*(ε/4) := by ring
        _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedGainCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing velocity smoothing from entropy-controlled localized gains -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem velocitySmooth_error_eLpNorm_le {χ : Velocity → ℝ} {F : X × Velocity → ℝ}
    (hχ : Integrable χ) (hF : Integrable F (μ.prod volume)) {ε : ℝ}
    (he : (∫ p, |velocitySmooth χ F p-F p| ∂μ.prod volume) ≤ ε) :
    eLpNorm (velocitySmooth χ F-F) 1 (μ.prod volume) ≤ ENNReal.ofReal ε := by
  have hi := (velocitySmooth_integrable hχ hF).sub hF
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using he)

theorem localizedGain_strong_of_smoothing_q80_oai
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
    (hgi : Integrable (entropyGauge g) (μ.prod volume))
    (η : C(Velocity,ℝ)) (hη : HasCompactSupport η)
    {ν : Measure (X × Velocity)} (hν : ν ≤ μ.prod volume)
    (hc : ∀ χ : C(Velocity,ℝ), HasCompactSupport χ →
      Tendsto (fun n => eLpNorm
        (velocitySmooth χ (localizedPhysicalGain η (f n))-
          velocitySmooth χ (localizedPhysicalGain η g)) 1 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (localizedPhysicalGain η (f n)-localizedPhysicalGain η g) 1 ν) atTop (𝓝 0) := by
  let ε : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hε j : 0 < ε j := by dsimp [ε] <;> positivity
  have hchoice j : ∃ χ : C(Velocity,ℝ), HasCompactSupport χ ∧ Integrable χ ∧
      (∀ n, (∫ p, |velocitySmooth χ (localizedPhysicalGain η (f n)) p-
        localizedPhysicalGain η (f n) p| ∂μ.prod volume) ≤ ε j) ∧
      (∫ p, |velocitySmooth χ (localizedPhysicalGain η g) p-
        localizedPhysicalGain η g p| ∂μ.prod volume) ≤ ε j := by
    obtain ⟨d,hd,hds⟩ := localizedGain_uniform_smoothing hfm hf hi hb η hη (ε j) (hε j)
    obtain ⟨e,he,hes⟩ := localizedGain_uniform_smoothing
      (fun _ : ℕ => hgm) (fun _ => hg) (fun _ => hgi)
      (fun _ => le_refl (∫ p, entropyGauge g p ∂μ.prod volume)) η hη (ε j) (hε j)
    obtain ⟨χ,hχc,hχi,hχ0,hχm,hχs⟩ := exists_velocity_mollifier (lt_min hd he)
    refine ⟨χ,hχc,hχi,?_,?_⟩
    · exact hds χ hχi hχ0 hχm (fun a ha => (hχs a ha).trans_le (min_le_left _ _))
    · exact hes χ hχi hχ0 hχm (fun a ha => (hχs a ha).trans_le (min_le_right _ _)) 0
  choose χ hχc hχi hχf hχg using hchoice
  have hδ : Tendsto (fun j => ENNReal.ofReal (ε j)) atTop (𝓝 0) := by
    have he : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.tendsto 0 |>.comp he
  have hFi n : Integrable (localizedPhysicalGain η (f n)) (μ.prod volume) := by
    apply localizedPhysicalGain_integrable η hη (hfm n)
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
  have hGi : Integrable (localizedPhysicalGain η g) (μ.prod volume) := by
    apply localizedPhysicalGain_integrable η hη hgm
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable hgm hg hgi
  apply strongL1_of_two_sided_approximations hδ
    (u := fun j n => velocitySmooth (χ j) (localizedPhysicalGain η (f n)))
    (v := fun j => velocitySmooth (χ j) (localizedPhysicalGain η g))
  · intro j n
    rw [eLpNorm_sub_comm]
    exact (eLpNorm_mono_measure _ hν).trans
      (velocitySmooth_error_eLpNorm_le (hχi j) (hFi n) (hχf j n))
  · intro j
    exact (eLpNorm_mono_measure _ hν).trans
      (velocitySmooth_error_eLpNorm_le (hχi j) hGi (hχg j))
  · exact fun j => hc (χ j) (hχc j)
  · exact fun n => (hFi n).1.mono_measure hν
  · exact fun j n => (velocitySmooth_integrable (hχi j) (hFi n)).1.mono_measure hν
  · exact fun j => (velocitySmooth_integrable (hχi j) hGi).1.mono_measure hν
  · exact hGi.1.mono_measure hν

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.localizedGain_strong_of_smoothing_q80_oai.{u_1} := @OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.localizedGain_strong_of_smoothing_q80_oai.{u_1}
