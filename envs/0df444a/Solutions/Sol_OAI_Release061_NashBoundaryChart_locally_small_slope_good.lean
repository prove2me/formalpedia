-- Prove2me | solution 1 for OAI.Release061.NashBoundaryChart.locally_small_slope_good
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:54:05.613658+00:00
-- url     : https://prove2.me/submissions/2ae7f5ed-486f-415b-8bb8-1bc3234a475a

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S003
import Theorems.Thm_OAI_Release061_semialgebraic_inward_analytic_from_family

section
-- module Solutions.OAIQ025_SD.Compat
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticImplicitScalar
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061


open Set Filter Topology

theorem analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (i : E ≃L[ℂ] F) (hi : HasFDerivAt f (i : E →L[ℂ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℂ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℂ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm
      (i : E →L[ℂ] F) := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

theorem analytic_implicit_scalar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : E × ℂ → ℂ} {a : E} {b : ℂ}
    (hF : AnalyticAt ℂ F (a, b)) (hzero : F (a, b) = 0)
    (L : E × ℂ →L[ℂ] ℂ) (hL : HasFDerivAt F L (a, b))
    (hsimple : L (0, 1) ≠ 0) :
    ∃ g : E → ℂ, AnalyticAt ℂ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, F (y, g y) = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), F p = 0 → p.2 = g p.1) := by
  let G : E × ℂ → E × ℂ := fun p => (p.1, F p)
  have hG : AnalyticAt ℂ G (a, b) :=
    ((ContinuousLinearMap.fst ℂ E ℂ).analyticAt (a, b)).prod hF
  have hdG : HasFDerivAt G (triangularDifferentialEquiv L hsimple : _ →L[ℂ] _) (a, b) :=
    hasFDerivAt_fst.prodMk hL
  obtain ⟨e, he, hmem, hia⟩ := analytic_local_inverse hG
    (triangularDifferentialEquiv L hsimple) hdG
  have hGab : G (a, b) = (a, 0) := by simp [G, hzero]
  rw [hGab] at hia
  let g : E → ℂ := fun y => (e.symm (y, 0)).2
  have hiac : AnalyticAt ℂ (fun y : E => e.symm (y, 0)) a :=
    hia.comp (f := fun y : E => (y, 0))
      ((ContinuousLinearMap.inl ℂ E ℂ).analyticAt a)
  have hg : AnalyticAt ℂ g a :=
    ((ContinuousLinearMap.snd ℂ E ℂ).analyticAt _).comp hiac
  have hsource : e.symm (a, 0) = (a, b) := by
    rw [← hGab, ← he]
    exact e.left_inv hmem
  refine ⟨g, hg, congrArg Prod.snd hsource, ?_, ?_⟩
  · have hright := e.eventually_right_inverse' hmem
    rw [he, hGab] at hright
    have ht : Tendsto (fun y : E => (y, (0 : ℂ))) (𝓝 a) (𝓝 (a, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    filter_upwards [ht.eventually hright] with y hy
    have hfst : (e.symm (y, 0)).1 = y := congrArg Prod.fst hy
    have hsnd : F (e.symm (y, 0)) = 0 := congrArg Prod.snd hy
    change F (y, (e.symm (y, 0)).2) = 0
    have hpair : (y, (e.symm (y, 0)).2) = e.symm (y, 0) :=
      Prod.ext hfst.symm rfl
    rw [hpair]
    exact hsnd
  · have hleft := e.eventually_left_inverse hmem
    rw [he] at hleft
    filter_upwards [hleft] with p hp hz
    have hGp : G p = (p.1, 0) := by simp [G, hz]
    rw [hGp] at hp
    exact (congrArg Prod.snd hp).symm

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DifferentiableCauchyTransform
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology


theorem polynomial_analytic_root {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (a : Fin d → ℂ) (b : ℂ)
    (hroot : Polynomial.eval₂ (MvPolynomial.eval a) b P = 0)
    (hsimple : Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative ≠ 0) :
    ∃ g : (Fin d → ℂ) → ℂ, AnalyticAt ℂ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, Polynomial.eval₂ (MvPolynomial.eval y) (g y) P = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P = 0 →
        p.2 = g p.1) := by
  let F : ((Fin d → ℂ) × ℂ) → ℂ := fun p =>
    Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P
  have hF : AnalyticAt ℂ F (a, b) := by
    have hpoly : ∀ j : ℕ, AnalyticAt ℂ
        (fun p : ((Fin d → ℂ) × ℂ) => MvPolynomial.eval p.1 (P.coeff j)) (a, b) := by
      intro j
      exact (AnalyticOnNhd.eval_mvPolynomial (P.coeff j) _ (Set.mem_univ _)).comp
        ((ContinuousLinearMap.fst ℂ (Fin d → ℂ) ℂ).analyticAt _)
    simp only [F, Polynomial.eval₂_eq_sum_range]
    exact
      Finset.analyticAt_fun_sum (Finset.range (P.natDegree + 1)) (fun j _ =>
        (hpoly j).mul (((ContinuousLinearMap.snd ℂ (Fin d → ℂ) ℂ).analyticAt _).pow j))
  let L := fderiv ℂ F (a,b)
  have hL : HasFDerivAt F L (a,b) := hF.differentiableAt.hasFDerivAt
  have hv : L (0,1) = Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative := by
    have h1 : HasDerivAt (fun z => F (a,z)) (L (0,1)) b :=
      hL.comp_hasDerivAt b ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))
    have h2 := (P.map (MvPolynomial.eval a)).hasDerivAt b
    simp only [Polynomial.derivative_map, Polynomial.eval_map] at h2
    exact h1.unique h2
  exact analytic_implicit_scalar hF hroot L hL (hv ▸ hsimple)

open Set Filter Metric MeasureTheory
open scoped Topology

theorem differentiableAt_intervalIntegral_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {x : E} {r a b : ℝ} (hr : 0 < r)
    (F : E → ℝ → ℂ) (F' : E → ℝ → E →L[ℂ] ℂ)
    (hc : ContinuousOn (Function.uncurry F) (closedBall x r ×ˢ uIcc a b))
    (hc' : ContinuousOn (Function.uncurry F') (closedBall x r ×ˢ uIcc a b))
    (hd : ∀ y ∈ closedBall x r, ∀ t ∈ uIcc a b, HasFDerivAt (F · t) (F' y t) y) :
    DifferentiableAt ℂ (fun y => ∫ t in a..b, F y t) x := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).prod isCompact_uIcc).exists_bound_of_continuousOn hc'
  have hsec : ∀ y ∈ closedBall x r, ContinuousOn (F y) (uIcc a b) := by
    intro y hy
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hy, ht⟩)
  have hsec' : ContinuousOn (F' x) (uIcc a b) :=
    hc'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨mem_closedBall_self hr.le, ht⟩)
  have hfint : IntervalIntegrable (F x) volume a b :=
    (hsec x (mem_closedBall_self hr.le)).intervalIntegrable
  have hfmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (volume.restrict (uIoc a b)) := by
    filter_upwards [closedBall_mem_nhds x hr] with y hy
    exact (hsec y hy).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  have hbound : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc a b →
      ∀ y ∈ closedBall x r, ‖F' y t‖ ≤ C :=
    Filter.Eventually.of_forall fun t ht y hy => hC (y, t) ⟨hy, uIoc_subset_uIcc ht⟩
  have hdiff : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc a b →
      ∀ y ∈ closedBall x r, HasFDerivAt (F · t) (F' y t) y :=
    Filter.Eventually.of_forall fun t ht y hy => hd y hy t (uIoc_subset_uIcc ht)
  have hderiv : HasFDerivAt (fun y => ∫ t in a..b, F y t)
      (∫ t in a..b, F' x t) x :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (closedBall_mem_nhds x hr) hfmeas hfint
      hsec'.intervalIntegrable.aestronglyMeasurable_restrict_uIoc hbound
      (intervalIntegrable_const (c := C)) hdiff
  exact hderiv.differentiableAt

theorem differentiableAt_circleIntegral_of_analyticOnNhd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {x : E} {r R : ℝ} {c : ℂ} (hr : 0 < r) (hR : 0 ≤ R)
    (f : E × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall x r ×ˢ sphere c R)) :
    DifferentiableAt ℂ (fun y => ∮ z in C(c, R), f (y, z)) x := by
  let ι : E →L[ℂ] E × ℂ := ContinuousLinearMap.inl ℂ E ℂ
  let F : E → ℝ → ℂ := fun y t => deriv (circleMap c R) t * f (y, circleMap c R t)
  let F' : E → ℝ → E →L[ℂ] ℂ := fun y t =>
    deriv (circleMap c R) t • (fderiv ℂ f (y, circleMap c R t)).comp ι
  have hcont : ContinuousOn f (closedBall x r ×ˢ sphere c R) := hf.continuousOn
  have hdercont : ContinuousOn (fderiv ℂ f) (closedBall x r ×ˢ sphere c R) := by
    intro p hp
    exact ((hf p hp).contDiffAt (n := 1)).continuousAt_fderiv (by decide) |>.continuousWithinAt
  have hparam : Continuous (fun p : E × ℝ => (p.1, circleMap c R p.2)) :=
    continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)
  have hmap : MapsTo (fun p : E × ℝ => (p.1, circleMap c R p.2))
      (closedBall x r ×ˢ uIcc 0 (2 * Real.pi)) (closedBall x r ×ˢ sphere c R) :=
    fun p hp => ⟨hp.1, circleMap_mem_sphere c hR p.2⟩
  have hdc : Continuous (fun p : E × ℝ => deriv (circleMap c R) p.2) := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
  have hc : ContinuousOn (Function.uncurry F) (closedBall x r ×ˢ uIcc 0 (2 * Real.pi)) :=
    hdc.continuousOn.mul (hcont.comp hparam.continuousOn hmap)
  have hc' : ContinuousOn (Function.uncurry F') (closedBall x r ×ˢ uIcc 0 (2 * Real.pi)) :=
    hdc.continuousOn.smul ((hdercont.comp hparam.continuousOn hmap).clm_comp continuousOn_const)
  have hd : ∀ y ∈ closedBall x r, ∀ t ∈ uIcc 0 (2 * Real.pi),
      HasFDerivAt (F · t) (F' y t) y := by
    intro y hy t _
    have hp := (hf (y, circleMap c R t) ⟨hy, circleMap_mem_sphere c hR t⟩).differentiableAt.hasFDerivAt
    have hi : HasFDerivAt (fun y : E => (y, circleMap c R t)) ι y :=
      (hasFDerivAt_id y).prodMk (hasFDerivAt_const _ _)
    exact (hp.comp y hi).const_mul _
  change DifferentiableAt ℂ (fun y => ∫ t in 0..2 * Real.pi, F y t) x
  exact differentiableAt_intervalIntegral_of_continuousOn hr F F' hc hc' hd

theorem differentiableOn_cauchyTransform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {A : Set E} (hA : IsOpen A) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (f : E × ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (A ×ˢ sphere c R)) :
    DifferentiableOn ℂ (fun p : E × ℂ =>
      (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(c, R), (w - p.2)⁻¹ * f (p.1, w))
      (A ×ˢ ball c R) := by
  intro p hp
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hA.prod isOpen_ball).mem_nhds hp)
  let F : (E × ℂ) × ℂ → ℂ := fun q => (q.2 - q.1.2)⁻¹ * f (q.1.1, q.2)
  have hF : AnalyticOnNhd ℂ F (closedBall p r ×ˢ sphere c R) := by
    intro q hq
    have hqq := hsub hq.1
    have hne : q.2 - q.1.2 ≠ 0 := sub_ne_zero.mpr
      (Metric.sphere_disjoint_ball.ne_of_mem hq.2 hqq.2)
    let π₁ : (E × ℂ) × ℂ →L[ℂ] E :=
      (ContinuousLinearMap.fst ℂ E ℂ).comp (ContinuousLinearMap.fst ℂ (E × ℂ) ℂ)
    let π₂ : (E × ℂ) × ℂ →L[ℂ] ℂ :=
      (ContinuousLinearMap.snd ℂ E ℂ).comp (ContinuousLinearMap.fst ℂ (E × ℂ) ℂ)
    let π₃ : (E × ℂ) × ℂ →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ (E × ℂ) ℂ
    have ha : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => q.2 - q.1.2) q :=
      (π₃.analyticAt q).sub (π₂.analyticAt q)
    have hb : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => f (q.1.1, q.2)) q :=
      (hf (q.1.1, q.2) ⟨hqq.1, hq.2⟩).comp (f := (π₁.prod π₃))
        ((π₁.prod π₃).analyticAt q)
    exact (ha.inv hne).mul hb
  exact ((differentiableAt_circleIntegral_of_analyticOnNhd hr hR.le F hF).const_mul
    (2 * Real.pi * Complex.I)⁻¹).differentiableWithinAt

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialRemovableLocal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology


theorem bounded_removable_finite
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U E : Set ℂ} (hU : IsOpen U) (hE : E.Finite)
    (f : ℂ → F) (hf : DifferentiableOn ℂ f (U \ E))
    {B : ℝ} (hb : ∀ z ∈ U \ E, ‖f z‖ ≤ B) :
    ∃ g : ℂ → F, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U \ E, g z = f z) ∧ (∀ z ∈ U, ‖g z‖ ≤ B) := by
  classical
  let g : ℂ → F := fun z => if z ∈ E then limUnder (𝓝[≠] z) f else f z
  have heq : ∀ z ∈ U \ E, g z = f z := fun z hz => ite_eq_right hz.2
  have hreg : ∀ z ∈ U \ E, AnalyticAt ℂ g z := by
    intro z hz
    have hh : ∀ᶠ w in 𝓝 z, g w = f w := by
      filter_upwards [(hU.sdiff hE.isClosed).mem_nhds hz] with w hw
      exact heq w hw
    exact (hf.analyticAt ((hU.sdiff hE.isClosed).mem_nhds hz)).congr (Filter.EventuallyEq.symm hh)
  have hpunct : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, w ∈ U \ E := by
    intro z hz
    have hv : U \ (E \ {z}) ∈ 𝓝 z :=
      (hU.sdiff (hE.subset (Set.sdiff_subset : E \ {z} ⊆ E)).isClosed).mem_nhds ⟨hz, by simp⟩
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hv] with w hw hw'
    refine ⟨hw'.1, ?_⟩
    intro hwE
    exact hw'.2 ⟨hwE, hw⟩
  have hlim : ∀ z ∈ U, z ∈ E → Tendsto f (𝓝[≠] z) (𝓝 (g z)) := by
    intro z hz hzE
    change Tendsto f (𝓝[≠] z) (𝓝 (if z ∈ E then _ else _))
    rw [ite_eq_left hzE]
    apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    · filter_upwards [hpunct z hz] with w hw
      exact hf.differentiableAt ((hU.sdiff hE.isClosed).mem_nhds hw)
    · refine ⟨B + ‖f z‖, ?_⟩
      change ∀ᶠ w in 𝓝[≠] z, ‖f w - f z‖ ≤ B + ‖f z‖
      filter_upwards [hpunct z hz] with w hw
      exact (norm_sub_le _ _).trans (add_le_add (hb w hw) le_rfl)
  refine ⟨g, ?_, heq, ?_⟩
  · intro z hz
    by_cases hzE : z ∈ E
    · have hc : ContinuousAt g z := by
        rw [← continuousWithinAt_compl_self]
        apply (hlim z hz hzE).congr'
        filter_upwards [hpunct z hz] with w hw
        exact (heq w hw).symm
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
      filter_upwards [hpunct z hz] with w hw
      exact (hreg w hw).differentiableAt
    · exact hreg z ⟨hz, hzE⟩
  · intro z hz
    by_cases hzE : z ∈ E
    · exact le_of_tendsto (hlim z hz hzE).norm
        ((hpunct z hz).mono fun w hw => hb w hw)
    · rw [heq z ⟨hz, hzE⟩]
      exact hb z ⟨hz, hzE⟩

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IntegralPrimitive
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology


open Polynomial

theorem resultant_derivative_ne_zero_of_generic_separable
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (p : R[X])
    (hp : (p.map (algebraMap R K)).Separable) :
    p.resultant p.derivative ≠ 0 := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h := Polynomial.resultant_ne_zero (p.map (algebraMap R K))
    ((p.map (algebraMap R K)).derivative) hp
  rw [Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.resultant_map_map] at h
  exact fun hz => h (by rw [hz, map_zero])

open Polynomial Algebra
open scoped nonZeroDivisors

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialEmptyInterior
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem PolynomialSignSet.exists_regular_polynomial {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧ ∀ x,
      MvPolynomial.eval (c x) P ≠ 0 → S ∈ 𝓝 x ∨ Sᶜ ∈ 𝓝 x := by
  classical
  induction hS with
  | zero p =>
    by_cases hp : p = 0
    · subst p
      refine ⟨1,one_ne_zero,fun x _ => Or.inl ?_⟩
      simp
    · refine ⟨p,hp,fun x hx => Or.inr ?_⟩
      exact ((MvPolynomial.continuous_eval p).comp hc).continuousAt.eventually_ne hx
  | positive p =>
    by_cases hp : p = 0
    · subst p
      refine ⟨1,one_ne_zero,fun x _ => Or.inr ?_⟩
      simp
    · refine ⟨p,hp,fun x hx => ?_⟩
      rcases lt_or_gt_of_ne hx with hneg | hpos
      · right
        filter_upwards [((MvPolynomial.continuous_eval p).comp hc).continuousAt.tendsto.eventually_lt_const hneg]
          with y hy
        exact not_lt_of_ge hy.le
      · exact Or.inl (((MvPolynomial.continuous_eval p).comp hc).continuousAt.tendsto.eventually_const_lt hpos)
  | @compl _ _ ih =>
    obtain ⟨P,hP,hreg⟩ := ih
    refine ⟨P,hP,fun x hx => ?_⟩
    simpa only [compl_compl] using (hreg x hx).symm
  | @union _ _ _ _ ihS ihT =>
    obtain ⟨P,hP,hregP⟩ := ihS
    obtain ⟨Q,hQ,hregQ⟩ := ihT
    refine ⟨P*Q,mul_ne_zero hP hQ,fun x hx => ?_⟩
    have hPQ : MvPolynomial.eval (c x) P ≠ 0 ∧ MvPolynomial.eval (c x) Q ≠ 0 := by
      simpa only [map_mul,mul_ne_zero_iff] using hx
    rcases hregP x hPQ.1 with hs | hs
    · exact Or.inl (Filter.mem_of_superset hs subset_union_left)
    rcases hregQ x hPQ.2 with ht | ht
    · exact Or.inl (Filter.mem_of_superset ht subset_union_right)
    · exact Or.inr (by simpa only [compl_union] using inter_mem hs ht)

theorem PolynomialSignSet.frontier_polynomial {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧
      ∀ x ∈ frontier S, MvPolynomial.eval (c x) P = 0 := by
  obtain ⟨P,hP,hreg⟩ := hS.exists_regular_polynomial hc
  refine ⟨P,hP,fun x hx => ?_⟩
  by_contra hne
  rcases hreg x hne with hs | hs
  · exact hx.2 (mem_interior_iff_mem_nhds.mpr hs)
  · have hx' : x ∈ frontier Sᶜ := by simpa only [frontier_compl] using hx
    exact hx'.2 (mem_interior_iff_mem_nhds.mpr hs)

theorem PolynomialSignSet.polynomial_of_empty_interior {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) (hempty : interior S = ∅) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧ ∀ x ∈ S, MvPolynomial.eval (c x) P = 0 := by
  obtain ⟨P,hP,hzero⟩ := hS.frontier_polynomial hc
  refine ⟨P,hP,fun x hx => hzero x ?_⟩
  exact ⟨subset_closure hx,by simp only [hempty,mem_empty_iff_false,not_false_eq_true]⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetInf
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.PolynomialSignSet
open Set
open scoped Classical

lemma iff_set {X ι : Type*} {c : X → ι → ℝ} {P Q : X → Prop}
    (hP : PolynomialSignSet c {x | P x}) (hQ : PolynomialSignSet c {x | Q x}) :
    PolynomialSignSet c {x | P x ↔ Q x} := by
  convert (hP.inter hQ).union (hP.compl.inter hQ.compl) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq,mem_union,mem_inter_iff,mem_compl_iff]
  tauto

lemma norm_lt_polynomial {X ι κ : Type*} [Fintype κ] {c : X → ι → ℝ}
    (p : κ → MvPolynomial ι ℝ) (q : MvPolynomial ι ℝ) :
    PolynomialSignSet c {x | ‖fun k => MvPolynomial.eval (c x) (p k)‖ <
      MvPolynomial.eval (c x) q} := by
  have h := (PolynomialSignSet.positive (c := c) q).inter
    (PolynomialSignSet.forall_finite (fun k x =>
      0 < MvPolynomial.eval (c x) (q+p k) ∧ 0 < MvPolynomial.eval (c x) (q-p k))
      (fun k => (PolynomialSignSet.positive (q+p k)).inter
        (PolynomialSignSet.positive (q-p k))))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq,MvPolynomial.eval_add,MvPolynomial.eval_sub]
  constructor
  · intro hx
    have hq : 0 < MvPolynomial.eval (c x) q := (norm_nonneg _).trans_lt hx
    refine ⟨hq,fun k => ?_⟩
    have hk := (pi_norm_lt_iff hq).mp hx k
    rw [Real.norm_eq_abs,abs_lt] at hk
    constructor <;> linarith [hk.1,hk.2]
  · rintro ⟨hq,h⟩
    apply (pi_norm_lt_iff hq).mpr
    intro k
    rw [Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [(h k).1,(h k).2]

end Release061.PolynomialSignSet

namespace Release061.SignElimination
open Set Metric
open scoped Classical

lemma polynomialSignSet_forall_one {X ι : Type*} {c : X → ι → ℝ}
    {P : X × ℝ → Prop}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | P z}) : PolynomialSignSet c {x | ∀ t : ℝ, P (x,t)} := by
  convert (polynomialSignSet_projection_one h.compl).compl using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp

lemma polynomialSignSet_graph_of_sublevel {X ι : Type*} {c : X → ι → ℝ}
    {f : X → ℝ}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | f z.1 < z.2}) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = f z.1} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let e := fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2 (d z.1)
  have hh : PolynomialSignSet e {z | f z.1.1 < z.2} :=
    h.coordinate_preimage (fun z : (X × ℝ) × ℝ => (z.1.1,z.2))
      (fun o => Option.elim o none (fun i => some (some i))) (by
        intro z o; cases o <;> rfl)
  have ht : PolynomialSignSet e {z | z.1.2 < z.2} := by
    convert PolynomialSignSet.positive (c := e)
      (MvPolynomial.X none-MvPolynomial.X (some none)) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [e,d]
  have hq := polynomialSignSet_forall_one (hh.iff_set ht)
  convert hq using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_ofPred_eq]
  constructor
  · intro hz t
    rw [hz]
  · intro hz
    exact le_antisymm (le_of_not_gt (fun hlt => (lt_irrefl _) ((hz z.2).mp hlt)))
      (le_of_not_gt (fun hlt => (lt_irrefl _) ((hz (f z.1)).mpr hlt)))

lemma polynomialSignSet_near_fiber {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) (p : κ → MvPolynomial ι ℝ) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | ∃ y ∈ A z.1, dist (fun k => MvPolynomial.eval (c z.1) (p k)) y < z.2} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let e := fun z : (X × ℝ) × (κ → ℝ) => Sum.elim (d z.1) z.2
  have ha : PolynomialSignSet e {z | z.2 ∈ A z.1.1} :=
    hA.coordinate_preimage (fun z : (X × ℝ) × (κ → ℝ) => (z.1.1,z.2)) (Sum.map some id)
      (by intro z i; cases i <;> rfl)
  have hn : PolynomialSignSet e {z | dist
      (fun k => MvPolynomial.eval (c z.1.1) (p k)) z.2 < z.1.2} := by
    convert PolynomialSignSet.norm_lt_polynomial (c := e)
      (fun k => MvPolynomial.rename (fun i => Sum.inl (some i)) (p k)-MvPolynomial.X (Sum.inr k))
      (MvPolynomial.X (Sum.inl none)) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_ofPred_eq,dist_eq_norm,MvPolynomial.eval_sub,MvPolynomial.eval_X,
      MvPolynomial.eval_rename]
    rfl
  exact polynomialSignSet_projection_finite (ha.inter hn)

lemma polynomialSignSet_infDist_graph {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) (p : κ → MvPolynomial ι ℝ) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = infDist (fun k => MvPolynomial.eval (c z.1) (p k)) (A z.1)} := by
  have hne : PolynomialSignSet c {x | (A x).Nonempty} :=
    polynomialSignSet_projection_finite hA
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  have hemp : PolynomialSignSet d {z | ¬ (A z.1).Nonempty} :=
    hne.compl.coordinate_preimage Prod.fst some (by intros; rfl)
  have ht : PolynomialSignSet d {z | 0 < z.2} := by
    simpa only [MvPolynomial.eval_X,d,Option.elim_none] using
      (PolynomialSignSet.positive (c := d) (MvPolynomial.X none))
  have hsub := (hemp.inter ht).union (polynomialSignSet_near_fiber A hA p)
  apply polynomialSignSet_graph_of_sublevel (f := fun x => infDist (fun k => MvPolynomial.eval (c x) (p k)) (A x))
  convert hsub using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_ofPred_eq,mem_union,mem_inter_iff]
  by_cases he : (A z.1).Nonempty
  · simp only [he,not_true_eq_false,false_and,false_or,infDist_lt_iff he]
  · have ha := Set.not_nonempty_iff_eq_empty.mp he
    simp [ha]

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalOffsetFamilyJoint
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter

namespace Release061
open Set Metric Filter Topology Classical SignElimination

lemma normalOffsetFamily_polynomialSignSet {ι κ : Type*} [Fintype κ]
    {U : Set ((ι → ℝ) × (κ → ℝ))} {B : Set (ι → ℝ)}
    {φ : (ι → ℝ) → (κ → ℝ)} (ρ : ℝ)
    (hU : PolynomialSignSet (fun z => Sum.elim z.1 z.2) U)
    (hφ : PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
      {z | z.1 ∈ B ∧ z.2 = φ z.1}) :
    PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ normalOffsetFamily U B φ ρ z.1} := by
  let c := fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2
  let d := fun z : ((ι → ℝ) × (κ → ℝ)) × (κ → ℝ) => Sum.elim (c z.1) z.2
  have hf : PolynomialSignSet d {z | z.1.1 ∈ B ∧ z.2 = φ z.1.1} :=
    hφ.coordinate_preimage (fun z : ((ι → ℝ) × (κ → ℝ)) × (κ → ℝ) => (z.1.1,z.2))
      (Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr) (by intro z i; cases i <;> rfl)
  have hu : PolynomialSignSet d {z | (z.1.1,z.2+z.1.2) ∈ U} :=
    hU.polynomial_preimage (fun z : ((ι → ℝ) × (κ → ℝ)) × (κ → ℝ) => (z.1.1,z.2+z.1.2))
      (Sum.elim (fun i => MvPolynomial.X (Sum.inl (Sum.inl i)))
        (fun k => MvPolynomial.X (Sum.inr k)+MvPolynomial.X (Sum.inl (Sum.inr k))))
      (by intro z i; cases i <;> simp [c,d])
  have hp : PolynomialSignSet c {z | z.1 ∈ B ∧ (z.1,φ z.1+z.2) ∈ U} := by
    convert polynomialSignSet_projection_finite (hf.inter hu) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_ofPred_eq,mem_inter_iff]
    constructor
    · rintro ⟨hs,hu⟩
      exact ⟨φ z.1,⟨hs,rfl⟩,hu⟩
    · rintro ⟨y,⟨hs,rfl⟩,hu⟩
      exact ⟨hs,hu⟩
  have hn : PolynomialSignSet c {z | ‖z.2‖ < ρ} := by
    convert PolynomialSignSet.norm_lt_polynomial (c := c)
      (fun k : κ => MvPolynomial.X (Sum.inr k)) (MvPolynomial.C ρ) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [c]
  convert hp.inter hn using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [normalOffsetFamily,mem_ofPred_eq,mem_inter_iff]
  tauto

lemma normalOffsetFamily_zero_not_mem {ι κ : Type*} [Fintype κ]
    {U : Set ((ι → ℝ) × (κ → ℝ))} {B : Set (ι → ℝ)}
    {φ : (ι → ℝ) → (κ → ℝ)} {ρ : ℝ} {s : ι → ℝ}
    (hs : (s,φ s) ∉ U) : (0 : κ → ℝ) ∉ normalOffsetFamily U B φ ρ s := by
  rintro ⟨_,_,h⟩
  exact hs (by simpa using h)

lemma normalOffsetFamily_joint_closure {ι κ : Type*} [Fintype κ]
    {U : Set ((ι → ℝ) × (κ → ℝ))} {B : Set (ι → ℝ)}
    {φ : (ι → ℝ) → (κ → ℝ)} {ρ : ℝ} {s : ι → ℝ}
    (hB : B ∈ 𝓝 s) (hφ : ContinuousAt φ s) (hρ : 0 < ρ)
    (hs : (s,φ s) ∈ closure U) :
    (s,(0 : κ → ℝ)) ∈ closure
      {z : (ι → ℝ) × (κ → ℝ) | z.2 ∈ normalOffsetFamily U B φ ρ z.1} := by
  let f : ((ι → ℝ) × (κ → ℝ)) → ((ι → ℝ) × (κ → ℝ)) :=
    fun p => (p.1,p.2-φ p.1)
  have hc : ContinuousAt f (s,φ s) :=
    continuousAt_fst.prodMk (continuousAt_snd.sub (hφ.comp continuousAt_fst))
  have he : f (s,φ s) = (s,0) := by simp [f]
  have hb : ∀ᶠ p : (ι → ℝ) × (κ → ℝ) in 𝓝 (s,φ s), p.1 ∈ B :=
    continuousAt_fst.preimage_mem_nhds hB
  have hn : ∀ᶠ p : (ι → ℝ) × (κ → ℝ) in 𝓝 (s,φ s), ‖p.2-φ p.1‖ < ρ := by
    have ht := hc.snd.norm.tendsto
    have hn := ht.eventually (Iio_mem_nhds (by simpa [f] using hρ))
    exact hn
  rw [← he,mem_closure_iff_frequently]
  apply hc.tendsto.frequently
  apply ((mem_closure_iff_frequently.mp hs).and_eventually (hb.and hn)).mono
  intro p hp
  change p.1 ∈ B ∧ ‖p.2-φ p.1‖ < ρ ∧ (p.1,φ p.1+(p.2-φ p.1)) ∈ U
  exact ⟨hp.2.1,hp.2.2,by simpa only [add_sub_cancel,Prod.mk.eta] using hp.1⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Pair
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open SignElimination
open scoped Classical

namespace SemialgebraicOn
variable {ι κ δ : Type*}
variable {B C : Set (ι → ℝ)} {f : (ι → ℝ) → (κ → ℝ)}

lemma restrict (hf : SemialgebraicOn B f) (hC : PolynomialSignSet id C) :
    SemialgebraicOn (B ∩ C) f := by
  have hc := hC.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => z.1) Sum.inl
    (d := fun z => Sum.elim z.1 z.2) (by intro z i; rfl)
  unfold SemialgebraicOn at hf ⊢
  convert hf.inter hc using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_inter_iff,mem_ofPred_eq,mem_preimage]
  tauto

lemma mono (hf : SemialgebraicOn B f) (hC : PolynomialSignSet id C) (hCB : C ⊆ B) :
    SemialgebraicOn C f := by
  simpa only [inter_eq_right.mpr hCB] using hf.restrict hC

end SemialgebraicOn
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EventualOffsetBall
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061
open Set Filter Metric
open scoped Topology

lemma offsetDistance_nonneg {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (v : E) : 0 ≤ offsetDistance A s t v :=
  le_min zero_le_one infDist_nonneg

lemma offsetDistance_le_one {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (v : E) : offsetDistance A s t v ≤ 1 := min_le_left _ _

lemma offsetDistance_lipschitz {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) : LipschitzWith 1 (offsetDistance A s t) := by
  unfold offsetDistance
  convert (LipschitzWith.const (α := E) (1 : ℝ)).min
    (lipschitz_infDist_pt (offsetScaled A s t)ᶜ) using 1; norm_num

lemma offsetDistance_zero {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (h0 : (0 : E) ∉ A s) : offsetDistance A s t 0 = 0 := by
  rw [offsetDistance,infDist_zero_of_mem (show (0 : E) ∈ (offsetScaled A s t)ᶜ by
    simpa [offsetScaled] using h0)]
  norm_num

lemma tendsto_of_truncated_zero {I : Type*} {l : Filter I} {f : I → ℝ}
    (h : Tendsto (fun i => min 1 (f i)) l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  have he : ∀ᶠ i in l, f i < 1 := by
    filter_upwards [(tendsto_order.mp h).2 1 zero_lt_one] with i hi
    rcases min_lt_iff.mp hi with hi | hi
    · exact (lt_irrefl _ hi).elim
    · exact hi
  exact h.congr' (he.mono fun i hi => min_eq_right hi.le)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetVector
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Set Metric
open scoped Classical

lemma polynomialSignSet_sublevel_of_graph {X ι : Type*} {c : X → ι → ℝ}
    {f : X → ℝ}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = f z.1}) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | f z.1 < z.2} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let e := fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2 (d z.1)
  have hh : PolynomialSignSet e {z | z.2 = f z.1.1} :=
    h.coordinate_preimage (fun z : (X × ℝ) × ℝ => (z.1.1,z.2))
      (fun o => Option.elim o none (fun i => some (some i))) (by
        intro z o; cases o <;> rfl)
  have ht : PolynomialSignSet e {z | z.2 < z.1.2} := by
    convert PolynomialSignSet.positive (c := e)
      (MvPolynomial.X (some none)-MvPolynomial.X none) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [e,d]
  convert polynomialSignSet_projection_one (hh.inter ht) using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp

lemma polynomialSignSet_truncated_graph {X ι : Type*} {c : X → ι → ℝ}
    {f : X → ℝ}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = f z.1}) (a : ℝ) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = min a (f z.1)} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  have ht : PolynomialSignSet d {z | a < z.2} := by
    convert PolynomialSignSet.positive (c := d) (MvPolynomial.X none-MvPolynomial.C a) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [d]
  apply polynomialSignSet_graph_of_sublevel (f := fun x => min a (f x))
  convert ht.union (polynomialSignSet_sublevel_of_graph h) using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_ofPred_eq,mem_union,min_lt_iff]

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetOffset
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Set Metric
open scoped Classical

lemma polynomialSignSet_scaled_complement {X ι κ : Type*}
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) :
    PolynomialSignSet
      (fun z : (X × ℝ) × (κ → ℝ) => Sum.elim (fun o => Option.elim o z.1.2 (c z.1.1)) z.2)
      {z | z.2 ∈ (offsetScaled A z.1.1 z.1.2)ᶜ} := by
  exact hA.compl.polynomial_preimage
    (fun z : (X × ℝ) × (κ → ℝ) => (z.1.1,z.1.2 • z.2))
    (Sum.elim (fun i => MvPolynomial.X (Sum.inl (some i)))
      (fun k => MvPolynomial.X (Sum.inl none)*MvPolynomial.X (Sum.inr k))) (by
        intro z i
        cases i <;> simp)

lemma polynomialSignSet_offsetDistance_graph {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) (v : κ → ℝ) :
    PolynomialSignSet (fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2
      (fun o => Option.elim o z.1.2 (c z.1.1)))
      {z | z.2 = offsetDistance A z.1.1 z.1.2 v} := by
  have hh := polynomialSignSet_infDist_graph
    (c := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
    (fun p : X × ℝ => (offsetScaled A p.1 p.2)ᶜ)
    (polynomialSignSet_scaled_complement A hA) (fun k => MvPolynomial.C (v k))
  have hh' : PolynomialSignSet (fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2
      (fun o => Option.elim o z.1.2 (c z.1.1)))
      {z | z.2 = infDist v (offsetScaled A z.1.1 z.1.2)ᶜ} := by
    simpa only [MvPolynomial.eval_C] using hh
  exact polynomialSignSet_truncated_graph
    (c := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
    (f := fun z : X × ℝ => infDist v (offsetScaled A z.1 z.2)ᶜ) hh' 1

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticMulZeroGerm
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Metric
open scoped Topology

theorem meromorphicAt_of_power_bound {f : ℂ → ℂ} {r C : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r \ {0})) (M : ℕ)
    (hbound : ∀ z ∈ ball 0 r \ {0}, ‖z^M * f z‖ ≤ C) :
    MeromorphicAt f 0 := by
  obtain ⟨g,hg,heq,_⟩ := bounded_removable_finite isOpen_ball (finite_singleton 0)
    (fun z => z^M * f z) ((analyticOnNhd_id.pow M).mul hf).differentiableOn hbound
  have hmer := (hg 0 (mem_ball_self hr)).meromorphicAt.div
    ((analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).pow M).meromorphicAt
  apply hmer.congr
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))] with z hz hzball
  change g z / z^M = f z
  rw [heq z ⟨hzball,hz⟩]
  exact mul_div_cancel_left₀ (f z) (pow_ne_zero M hz)

end

open Set Filter Topology

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_MeromorphicPolynomialRoot
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric NNReal
open scoped Topology

theorem scaled_polynomial_root_bound (P : Polynomial ℂ) (hP : P ≠ 0) (a q : ℂ)
    (ha : P.IsRoot a) (C : ℝ≥0)
    (hC : ∀ j ∈ Finset.range P.natDegree,
      ‖q‖₊ * ‖P.coeff j‖₊ ≤ C * ‖P.leadingCoeff‖₊) :
    ‖q * a‖₊ ≤ C + ‖q‖₊ := by
  have hl : ‖P.leadingCoeff‖₊ ≠ 0 := by simpa using hP
  calc
    ‖q * a‖₊ = ‖q‖₊ * ‖a‖₊ := nnnorm_mul _ _
    _ ≤ ‖q‖₊ * P.cauchyBound := mul_le_mul_of_nonneg_left (ha.norm_lt_cauchyBound hP).le (show 0 ≤ ‖q‖₊ from zero_le)
    _ = (‖q‖₊ * (Finset.range P.natDegree).sup (fun j => ‖P.coeff j‖₊)) / ‖P.leadingCoeff‖₊ + ‖q‖₊ := by
      rw [Polynomial.cauchyBound,mul_add,mul_one,mul_div_assoc]
    _ ≤ C + ‖q‖₊ := by
      apply add_le_add _ le_rfl
      apply (div_le_iff₀ (pos_iff_ne_zero.mpr hl)).mpr
      rw [mul_finset_sup]
      exact Finset.sup_le hC

theorem meromorphicAt_polynomial_root {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : ℂ → (Fin d → ℂ))
    (hA : AnalyticAt ℂ A 0) (f : ℂ → ℂ)
    (hf : ∀ᶠ z in 𝓝[≠] 0, AnalyticAt ℂ f z)
    (hroot : ∀ᶠ z in 𝓝[≠] 0, Polynomial.eval₂ (MvPolynomial.eval (A z)) (f z) P = 0)
    (hlead : ¬∀ᶠ z in 𝓝 0, MvPolynomial.eval (A z) P.leadingCoeff = 0) :
    MeromorphicAt f 0 := by
  have hpa (p : MvPolynomial (Fin d) ℂ) :
      AnalyticAt ℂ (fun z => MvPolynomial.eval (A z) p) 0 :=
    (AnalyticOnNhd.eval_mvPolynomial p (A 0) (mem_univ _)).comp hA
  obtain ⟨M,g,hga,hg0,hfac⟩ := (hpa P.leadingCoeff).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hlead
  simp only [sub_zero,smul_eq_mul] at hfac
  have hgne : ∀ᶠ z in 𝓝 (0 : ℂ), g z ≠ 0 :=
    (hga.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg0
  let J := Finset.range P.natDegree
  let B : ℝ := ∑ j : J, (‖MvPolynomial.eval (A 0) (P.coeff j.val) / g 0‖ + 1)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have hbj (j : J) : ‖MvPolynomial.eval (A 0) (P.coeff j.val) / g 0‖ + 1 ≤ B :=
    Finset.single_le_sum (f := fun j : J => (‖MvPolynomial.eval (A 0) (P.coeff j.val) / g 0‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ j)
  have hce : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ j : J,
      ‖MvPolynomial.eval (A z) (P.coeff j.val) / g z‖ ≤ B := by
    apply Filter.eventually_all.mpr
    intro j
    have hc := ((hpa (P.coeff j.val)).continuousAt.div hga.continuousAt hg0).norm
    exact (hc.tendsto.eventually_le_const (by linarith :
      ‖MvPolynomial.eval (A 0) (P.coeff j.val) / g 0‖ <
        ‖MvPolynomial.eval (A 0) (P.coeff j.val) / g 0‖ + 1)).mono (fun _ h => h.trans (hbj j))
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ ≤ 1 := by
    exact continuousAt_id.norm.tendsto.eventually_le_const (by simp)
  have hbound : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z^M * f z‖ ≤ B + 1 := by
    filter_upwards [hroot,self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hfac.and (hgne.and (hce.and hn)))] with z hz hz0 hzz
    rcases hzz with ⟨hfac,hgz,hcz,hnz⟩
    have hz0 : z ≠ 0 := hz0
    have hleadne : MvPolynomial.eval (A z) P.leadingCoeff ≠ 0 := by
      rw [hfac]
      exact mul_ne_zero (pow_ne_zero M hz0) hgz
    let Q := P.map (MvPolynomial.eval (A z))
    have hQl : Q.leadingCoeff = MvPolynomial.eval (A z) P.leadingCoeff :=
      Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hleadne
    have hQ : Q ≠ 0 := by
      intro h
      have hzero : Q.leadingCoeff = 0 := h ▸ Polynomial.leadingCoeff_zero
      exact hleadne (hQl.symm.trans hzero)
    have hQr : Q.IsRoot (f z) := by
      simpa only [Q,Polynomial.IsRoot.def,Polynomial.eval_map] using hz
    have he := scaled_polynomial_root_bound Q hQ (f z) (z^M) hQr ⟨B,hB⟩ (by
      intro j hj
      have hjJ : j ∈ J := Finset.mem_range.mpr
        ((Finset.mem_range.mp hj).trans_le Polynomial.natDegree_map_le)
      have hc : ‖MvPolynomial.eval (A z) (P.coeff j)‖ ≤ B * ‖g z‖ := by
        have hh := hcz ⟨j,hjJ⟩
        rw [norm_div] at hh
        exact (div_le_iff₀ (norm_pos_iff.mpr hgz)).mp hh
      apply NNReal.coe_le_coe.mp
      change ‖z^M‖ * ‖Q.coeff j‖ ≤ B * ‖Q.leadingCoeff‖
      rw [hQl,hfac,norm_mul]
      rw [show Q.coeff j = MvPolynomial.eval (A z) (P.coeff j) from by simp only [Q,Polynomial.coeff_map]]
      nlinarith [mul_le_mul_of_nonneg_left hc (norm_nonneg (z^M))])
    have he' : ‖z^M * f z‖ ≤ B + ‖z^M‖ := by exact_mod_cast he
    apply he'.trans
    gcongr
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hnz
  have hall : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → AnalyticAt ℂ f z ∧ ‖z^M*f z‖ ≤ B+1 := by
    simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using hf.and hbound
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hall
  apply meromorphicAt_of_power_bound hr (fun z hz => (hball hz.1 hz.2).1) M
  intro z hz
  exact (hball hz.1 hz.2).2

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteCoveringRamifiedSection
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly _root_.OAI.Release061.instT2SpacePuncturedUnitDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Function

theorem finite_covering_lift_period
    {A X E : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [TopologicalSpace X] [TopologicalSpace E]
    (p : E → X) (hp : IsCoveringMap p) (f : A → X)
    (σ : A ≃ₜ A) (hσ : ∀ a, f (σ a) = f a)
    (g : A → E) (hg : Continuous g) (hpg : p ∘ g = f)
    (a : A) (hfinite : (p ⁻¹' {f a}).Finite) :
    ∃ l : ℕ, 0 < l ∧ ∀ x, g (σ^[l] x) = g x := by
  classical
  have hfiter (k : ℕ) (x : A) : f (σ^[k] x) = f x := by
    induction k with
    | zero => rfl
    | succ k hk => simpa only [Function.iterate_succ_apply',hσ] using hk
  let v : ℕ → p ⁻¹' {f a} := fun k => ⟨g (σ^[k] a),by
    change p (g (σ^[k] a)) = f a
    rw [show p (g (σ^[k] a)) = f (σ^[k] a) from congrFun hpg _]
    exact hfiter k a⟩
  let : Finite (p ⁻¹' {f a}) := hfinite.to_subtype
  obtain ⟨i,j,hij,hv⟩ : ∃ i j : ℕ, i < j ∧ v i = v j := by
    obtain ⟨i,j,hne,hv⟩ := Finite.exists_ne_map_eq_of_infinite v
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i,j,h,hv⟩
    · exact ⟨j,i,h,hv.symm⟩
  have hbase : g (σ^[i] a) = g (σ^[j] a) := congrArg Subtype.val hv
  have heq : (fun x => g (σ^[i] x)) = (fun x => g (σ^[j] x)) := by
    apply hp.eq_of_comp_eq (hg.comp (σ.continuous.iterate i))
      (hg.comp (σ.continuous.iterate j)) _ a hbase
    funext x
    change p (g (σ^[i] x)) = p (g (σ^[j] x))
    rw [show p (g (σ^[i] x)) = f (σ^[i] x) from congrFun hpg _,
      show p (g (σ^[j] x)) = f (σ^[j] x) from congrFun hpg _,hfiter,hfiter]
  refine ⟨j-i,Nat.sub_pos_of_lt hij,fun x => ?_⟩
  obtain ⟨y,hy⟩ := σ.surjective.iterate i x
  have h := congrFun heq y
  have hj : j = (j-i)+i := by omega
  rw [hj,Function.iterate_add_apply,hy] at h
  exact h.symm

open Complex
open scoped UpperHalfPlane
open Function.Periodic

theorem continuous_halfPlaneQ (h : ℝ) (hh : 0 < h) : Continuous (halfPlaneQ h hh) :=
  ((continuous_qParam (h := h)).comp UpperHalfPlane.continuous_coe).subtype_mk _

theorem halfPlaneQ_right_inv (h : ℝ) (hh : 0 < h) (q : PuncturedUnitDisk) :
    halfPlaneQ h hh (halfPlaneInvQ h hh q) = q := by
  apply Subtype.ext
  exact qParam_right_inv hh.ne' q.property.1

theorem isOpenMap_halfPlaneQ (h : ℝ) (hh : 0 < h) : IsOpenMap (halfPlaneQ h hh) := by
  have hopen : IsOpen {z : ℂ | z ≠ 0 ∧ ‖z‖ < 1} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  apply hopen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
  have ha : 2 * Real.pi * I / (h : ℂ) ≠ 0 :=
    div_ne_zero two_pi_I_ne_zero (ofReal_ne_zero.mpr hh.ne')
  have H := Complex.isOpenMap_exp.comp (Homeomorph.mulLeft₀ _ ha).isOpenMap
  have H' := H.comp UpperHalfPlane.isOpenEmbedding_coe.isOpenMap
  convert H' using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  change exp (2 * ↑Real.pi * I * (z : ℂ) / ↑h) = exp ((2 * ↑Real.pi * I / ↑h) * z)
  congr 1
  ring

theorem isOpenQuotientMap_halfPlaneQ (h : ℝ) (hh : 0 < h) :
    IsOpenQuotientMap (halfPlaneQ h hh) :=
  ⟨fun q => ⟨halfPlaneInvQ h hh q,halfPlaneQ_right_inv h hh q⟩,
    continuous_halfPlaneQ h hh,isOpenMap_halfPlaneQ h hh⟩

theorem halfPlaneQ_shift (h : ℝ) (hh : 0 < h) (z : ℍ) :
    halfPlaneQ h hh (halfPlaneShift h z) = halfPlaneQ h hh z := by
  apply Subtype.ext
  change exp (2 * ↑Real.pi * I * ((h : ℂ) + (z : ℂ)) / ↑h) = exp (2 * ↑Real.pi * I * (z : ℂ) / ↑h)
  rw [show 2 * ↑Real.pi * I * ((h : ℂ) + (z : ℂ)) / ↑h =
    2 * ↑Real.pi * I * (z : ℂ) / ↑h + 2 * ↑Real.pi * I by field_simp [ofReal_ne_zero.mpr hh.ne']; ring]
  exact Complex.exp_periodic _

theorem halfPlaneShift_iterate (a : ℝ) (l : ℕ) (z : ℍ) :
    (halfPlaneShift a)^[l] z = halfPlaneShift (l*a) z := by
  induction l with
  | zero => apply UpperHalfPlane.ext; simp [halfPlaneShift]
  | succ l hl =>
    rw [Function.iterate_succ_apply',hl]
    apply UpperHalfPlane.ext
    change (a : ℂ) + ((((l : ℝ)*a : ℝ) : ℂ) + (z : ℂ)) =
      ((((l+1 : ℕ) : ℝ)*a : ℝ) : ℂ) + (z : ℂ)
    push_cast
    ring

theorem halfPlaneShift_add (a b : ℝ) (z : ℍ) :
    halfPlaneShift (a+b) z = halfPlaneShift a (halfPlaneShift b z) := by
  apply UpperHalfPlane.ext
  change ((a+b : ℝ) : ℂ) + (z : ℂ) = (a : ℂ) + ((b : ℂ) + (z : ℂ))
  push_cast
  ring

theorem halfPlaneShift_zero (z : ℍ) : halfPlaneShift 0 z = z := by
  apply UpperHalfPlane.ext
  change (0 : ℂ) + (z : ℂ) = (z : ℂ)
  simp

theorem halfPlane_period_descent {S E : Type*} [TopologicalSpace S] [TopologicalSpace E]
    (h : ℝ) (hh : 0 < h) (g : S × ℍ → E) (hg : Continuous g)
    (hper : ∀ s z, g (s,halfPlaneShift h z) = g (s,z)) :
    ∃ G : S × PuncturedUnitDisk → E, Continuous G ∧
      ∀ s z, G (s,halfPlaneQ h hh z) = g (s,z) := by
  let G : S × PuncturedUnitDisk → E := fun x => g (x.1,halfPlaneInvQ h hh x.2)
  have hG (s : S) (z : ℍ) : G (s,halfPlaneQ h hh z) = g (s,z) := by
    obtain ⟨m,hm⟩ := qParam_left_inv_mod_period hh.ne' (z : ℂ)
    have he : halfPlaneInvQ h hh (halfPlaneQ h hh z) = halfPlaneShift ((m : ℝ)*h) z := by
      apply UpperHalfPlane.ext
      change invQParam h (qParam h z) = (((m : ℝ)*h : ℝ) : ℂ) + (z : ℂ)
      rw [hm]
      push_cast
      ring
    have hp : Periodic (fun a : ℝ => g (s,halfPlaneShift a z)) h := by
      intro a
      change g (s,halfPlaneShift (a+h) z) = g (s,halfPlaneShift a z)
      rw [add_comm a h,halfPlaneShift_add,hper]
    dsimp only [G]
    rw [he]
    simpa only [halfPlaneShift_zero] using hp.int_mul_eq m
  refine ⟨G,?_,hG⟩
  have hQ : IsOpenQuotientMap (Prod.map (id : S → S) (halfPlaneQ h hh)) :=
    IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_halfPlaneQ h hh)
  apply hQ.isQuotientMap.continuous_iff.mpr
  convert hg using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact hG x.1 x.2

theorem halfPlaneQ_nat (l : ℕ) (hl : 0 < l) (z : ℍ) :
    halfPlaneQ 1 one_pos z = puncturedPower l hl (halfPlaneQ l (by exact_mod_cast hl) z) := by
  apply Subtype.ext
  change exp (2 * ↑Real.pi * I * (z : ℂ) / (1 : ℂ)) =
    exp (2 * ↑Real.pi * I * (z : ℂ) / (l : ℂ))^l
  rw [← exp_nat_mul]
  congr 1
  have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  field_simp

theorem finite_covering_ramified_section {S E : Type*}
    [TopologicalSpace S] [ContractibleSpace S] [LocallyPathConnectedSpace S]
    [TopologicalSpace E]
    (p : E → S × PuncturedUnitDisk) (hp : IsCoveringMap p)
    (s₀ : S) (z₀ : ℍ) (e₀ : E) (he : p e₀ = (s₀,halfPlaneQ 1 one_pos z₀))
    (hfinite : (p ⁻¹' {(s₀,halfPlaneQ 1 one_pos z₀)}).Finite) :
    ∃ l : ℕ, ∃ hl : 0 < l, ∃ G : S × PuncturedUnitDisk → E,
      Continuous G ∧ (∀ s q, p (G (s,q)) = (s,puncturedPower l hl q)) ∧
        G (s₀,halfPlaneQ l (by exact_mod_cast hl) z₀) = e₀ := by
  let f : C(S × ℍ,S × PuncturedUnitDisk) :=
    ⟨Prod.map id (halfPlaneQ 1 one_pos),continuous_id.prodMap (continuous_halfPlaneQ 1 one_pos)⟩
  obtain ⟨g,⟨hbase,hpg⟩,_⟩ := hp.existsUnique_continuousMap_lifts f (s₀,z₀) e₀ he
  let σ : (S × ℍ) ≃ₜ (S × ℍ) := (Homeomorph.refl S).prodCongr (halfPlaneShift 1)
  have hσ : ∀ x, f (σ x) = f x := by
    intro x
    change (x.1,halfPlaneQ 1 one_pos (halfPlaneShift 1 x.2)) = (x.1,halfPlaneQ 1 one_pos x.2)
    rw [halfPlaneQ_shift]
  obtain ⟨l,hl,hper⟩ := finite_covering_lift_period p hp f σ hσ g g.continuous hpg
    (s₀,z₀) hfinite
  have hiter (n : ℕ) (s : S) (z : ℍ) : σ^[n] (s,z) = (s,(halfPlaneShift 1)^[n] z) := by
    induction n with
    | zero => rfl
    | succ n hn => rw [Function.iterate_succ_apply',hn,Function.iterate_succ_apply']; rfl
  have hperiod (s : S) (z : ℍ) : g (s,halfPlaneShift (l : ℝ) z) = g (s,z) := by
    simpa only [hiter,halfPlaneShift_iterate,mul_one] using hper (s,z)
  obtain ⟨G,hGc,hG⟩ := halfPlane_period_descent (l : ℝ) (by exact_mod_cast hl) g g.continuous hperiod
  refine ⟨l,hl,G,hGc,?_,(hG s₀ z₀).trans hbase⟩
  intro s q
  obtain ⟨z,hz⟩ := (isOpenQuotientMap_halfPlaneQ (l : ℝ) (by exact_mod_cast hl)).surjective q
  rw [← hz,hG]
  have hc := congrFun hpg (s,z)
  change p (g (s,z)) = (s,halfPlaneQ 1 one_pos z) at hc
  exact hc.trans (congrArg (s,·) (halfPlaneQ_nat l hl z))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialRootFiberFinite
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Filter Set
open scoped Topology

theorem polynomial_analytic_sheets_nonmonic {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ))
    (a : Fin d → ℂ) (hlead : MvPolynomial.eval a P.leadingCoeff ≠ 0) (ha : (P.map (MvPolynomial.eval a)).Separable) :
    ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → ℂ) (W : Set (Fin d → ℂ)),
      I.card = P.natDegree ∧ IsOpen W ∧ a ∈ W ∧
      (∀ i, AnalyticOnNhd ℂ (g i) W) ∧ (∀ i, g i a = i.val) ∧
      ∀ y ∈ W, Function.Injective (fun i => g i y) ∧
        ∀ z : ℂ, Polynomial.eval₂ (MvPolynomial.eval y) z P = 0 ↔
          ∃ i, g i y = z := by
  classical
  have hne (y : Fin d → ℂ) (hy : MvPolynomial.eval y P.leadingCoeff ≠ 0) :
      P.map (MvPolynomial.eval y) ≠ 0 := by
    intro hz
    have H := congrArg (fun Q : Polynomial ℂ => Q.coeff P.natDegree) hz
    apply hy
    simpa only [Polynomial.coeff_map,Polynomial.coeff_natDegree,Polynomial.coeff_zero] using H
  let I : Finset ℂ := (P.map (MvPolynomial.eval a)).roots.toFinset
  have hcard : I.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots ha),
      IsAlgClosed.card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero hlead]
  have hi (i : I) : Polynomial.eval₂ (MvPolynomial.eval a) i.val P = 0 := by
    have h := Polynomial.mem_roots (hne a hlead) |>.mp
      (Multiset.mem_toFinset.mp i.property)
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using h
  have hs (i : I) : Polynomial.eval₂ (MvPolynomial.eval a) i.val P.derivative ≠ 0 := by
    simpa only [Polynomial.eval₂_id, Polynomial.eval₂_at_apply, Polynomial.derivative_map,
      Polynomial.eval_map] using
      ha.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := i.val)
        (by simpa only [Polynomial.eval₂_id, Polynomial.eval₂_at_apply, Polynomial.eval_map] using hi i)
  choose g hg hga hgr _hgu using fun i : I => polynomial_analytic_root P a i.val (hi i) (hs i)
  have hgi : ∀ᶠ y in 𝓝 a, Function.Injective (fun i => g i y) := by
    have hj : ∀ i j : I, ∀ᶠ y in 𝓝 a, i ≠ j → g i y ≠ g j y := by
      intro i j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
      · have hval : g i a ≠ g j a := by
          rw [hga, hga]
          exact fun h => hij (Subtype.ext h)
        exact ((hg i).continuousAt.ne_iff_eventually_ne (hg j).continuousAt).mp hval |>.mono
          (fun _ hh _ => hh)
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hj i))] with y hy
    intro i j hij
    by_contra h
    exact hy i j h hij
  have hall : ∀ᶠ y in 𝓝 a,
      (∀ i, AnalyticAt ℂ (g i) y) ∧
      (∀ i, Polynomial.eval₂ (MvPolynomial.eval y) (g i y) P = 0) ∧
      Function.Injective (fun i => g i y) := by
    exact (Filter.eventually_all.mpr (fun i => (hg i).eventually_analyticAt)).and
      ((Filter.eventually_all.mpr hgr).and hgi)
  have hle : ∀ᶠ y in 𝓝 a, MvPolynomial.eval y P.leadingCoeff ≠ 0 :=
    ((AnalyticOnNhd.eval_mvPolynomial P.leadingCoeff _ (mem_univ _)).continuousAt.ne_iff_eventually_ne continuousAt_const).mp hlead
  obtain ⟨W, hWsub, hW, haW⟩ := _root_.mem_nhds_iff.mp (hall.and hle)
  have hWlead : ∀ y ∈ W, MvPolynomial.eval y P.leadingCoeff ≠ 0 := fun y hy => (hWsub hy).2
  have hWsub := fun {y} (hy : y ∈ W) => (hWsub hy).1
  refine ⟨I, g, W, hcard, hW, haW, fun i y hy => (hWsub hy).1 i, hga, ?_⟩
  intro y hy
  have hyroot := (hWsub hy).2.1
  have hyinj := (hWsub hy).2.2
  refine ⟨hyinj, ?_⟩
  let J : Finset ℂ := Finset.univ.image (fun i : I => g i y)
  let K : Finset ℂ := (P.map (MvPolynomial.eval y)).roots.toFinset
  have hJK : J ⊆ K := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hne y (hWlead y hy))).mpr
      (by simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hyroot i))
  have hJcard : J.card = I.card := by
    rw [Finset.card_image_of_injective _ hyinj]
    simp
  have hKcard : K.card ≤ P.natDegree := by
    exact (Multiset.toFinset_card_le _).trans (le_of_eq
      (IsAlgClosed.card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero (hWlead y hy)))
  have hJKeq : J = K := Finset.eq_of_subset_of_card_le hJK (by rw [hJcard, hcard]; exact hKcard)
  intro z
  constructor
  · intro hz
    have hzK : z ∈ K := Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (hne y (hWlead y hy))).mpr
        (by simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hz))
    rw [← hJKeq] at hzK
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzK
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact hyroot i

theorem relation_evenlyCovered_of_sheets {X Y J : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace J] [DiscreteTopology J] [Finite J]
    (R : Set (X × Y)) (a : X) (W : Set X) (hW : IsOpen W) (ha : a ∈ W)
    (g : J → X → Y) (hg : ∀ j, ContinuousOn (g j) W)
    (hi : ∀ x ∈ W, Function.Injective (fun j => g j x))
    (he : ∀ x ∈ W, ∀ y, (x,y) ∈ R ↔ ∃ j, g j x = y) :
    IsEvenlyCovered (fun r : R => r.val.1) a J := by
  classical
  let p : R → X := fun r => r.val.1
  let ψ : W × J → p ⁻¹' W := fun x =>
    ⟨⟨(x.1.val,g x.2 x.1.val),(he x.1.val x.1.property _).mpr ⟨x.2,rfl⟩⟩,x.1.property⟩
  have hψc : Continuous ψ := by
    apply continuous_prod_of_discrete_right.mpr
    intro j
    exact (continuous_subtype_val.prodMk (continuousOn_iff_continuous_domRestrict.mp (hg j))).subtype_mk _ |>.subtype_mk _
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hx : x.1 = y.1 := Subtype.ext (congrArg (fun r : p ⁻¹' W => r.val.val.1) hxy)
    have hy : g x.2 x.1.val = g y.2 y.1.val := congrArg (fun r : p ⁻¹' W => r.val.val.2) hxy
    rw [← hx] at hy
    exact Prod.ext hx (hi _ x.1.property hy)
  have hψsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨j,hj⟩ := (he r.val.val.1 r.property r.val.val.2).mp r.val.property
    refine ⟨(⟨r.val.val.1,r.property⟩,j),?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl hj
  let π : p ⁻¹' W → W := fun r => ⟨r.val.val.1,r.property⟩
  have hπ : Continuous π :=
    (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  have hproper : IsProperMap ψ := isProperMap_of_comp_of_t2 hψc hπ isProperMap_fst_of_compactSpace
  let H : W × J ≃ₜ p ⁻¹' W :=
    (Equiv.ofBijective ψ ⟨hψinj,hψsurj⟩).toHomeomorphOfContinuousClosed hψc hproper.isClosedMap
  refine ⟨(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),W,ha,hW,hW.preimage (continuous_fst.comp continuous_subtype_val),H.symm,?_⟩
  intro r
  have h := congrArg (fun t : p ⁻¹' W => t.val.val.1) (H.apply_symm_apply r)
  exact h

theorem polynomial_root_covering {d : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : X → (Fin d → ℂ))
    (hA : Continuous A) (hlead : ∀ x, MvPolynomial.eval (A x) P.leadingCoeff ≠ 0)
    (hsep : ∀ x, (P.map (MvPolynomial.eval (A x))).Separable) :
    IsCoveringMap (fun r : {r : X × ℂ | Polynomial.eval₂ (MvPolynomial.eval (A r.1)) r.2 P = 0} =>
      r.val.1) := by
  intro x
  obtain ⟨J,g,W,_,hWo,hxW,hg,_,hge⟩ := polynomial_analytic_sheets_nonmonic P (A x) (hlead x) (hsep x)
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := J)
  refine relation_evenlyCovered_of_sheets _ x (A ⁻¹' W) (hWo.preimage hA) hxW
    (fun j y => g j (A y)) ?_ ?_ ?_
  · intro j
    exact (hg j).continuousOn.comp hA.continuousOn (fun _ h => h)
  · intro y hy
    exact (hge (A y) hy).1
  · intro y hy z
    exact (hge (A y) hy).2 z

theorem continuous_polynomial_root_analyticAt {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : E → (Fin d → ℂ))
    (g : E → ℂ) (a : E) (hA : AnalyticAt ℂ A a) (hg : ContinuousAt g a)
    (hroot : ∀ᶠ x in 𝓝 a, Polynomial.eval₂ (MvPolynomial.eval (A x)) (g x) P = 0)
    (hsimple : Polynomial.eval₂ (MvPolynomial.eval (A a)) (g a) P.derivative ≠ 0) :
    AnalyticAt ℂ g a := by
  obtain ⟨b,hb,hba,_,hunique⟩ := polynomial_analytic_root P (A a) (g a)
    hroot.self_of_nhds hsimple
  have ht : Tendsto (fun x => (A x,g x)) (𝓝 a) (𝓝 (A a,g a)) := hA.continuousAt.prodMk hg
  have he : g =ᶠ[𝓝 a] fun x => b (A x) := by
    filter_upwards [ht hunique,hroot] with x hx hr
    exact hx hr
  exact (hb.comp hA).congr he.symm

theorem polynomial_root_fiber_finite {d : ℕ} {X : Type*}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : X → (Fin d → ℂ))
    (x : X) (hlead : MvPolynomial.eval (A x) P.leadingCoeff ≠ 0) :
    ((fun r : {r : X × ℂ | Polynomial.eval₂ (MvPolynomial.eval (A r.1)) r.2 P = 0} =>
      r.val.1) ⁻¹' {x}).Finite := by
  have hne : P.map (MvPolynomial.eval (A x)) ≠ 0 := by
    intro hz
    apply hlead
    have H := congrArg (fun Q : Polynomial ℂ => Q.coeff P.natDegree) hz
    simpa only [Polynomial.coeff_map,Polynomial.coeff_natDegree,Polynomial.coeff_zero] using H
  apply Set.Finite.of_injOn (f := fun r => r.val.2) (t := {z | (P.map (MvPolynomial.eval (A x))).IsRoot z})
  · intro r hr
    change r.val.1 = x at hr
    change Polynomial.eval r.val.2 (P.map (MvPolynomial.eval (A x))) = 0
    rw [Polynomial.eval_map,← hr]
    exact r.property
  · intro r hr s hs hval
    apply Subtype.ext
    exact Prod.ext (hr.trans hs.symm) hval
  · exact Polynomial.finite_setOfPred_isRoot hne

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialRamifiedAnalyticRoot
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Filter Set Complex UpperHalfPlane Function
open scoped Topology

theorem polynomial_ramified_continuous_root {d : ℕ} {S : Type*}
    [TopologicalSpace S] [T2Space S] [ContractibleSpace S] [LocallyPathConnectedSpace S]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : S × PuncturedUnitDisk → (Fin d → ℂ))
    (hA : Continuous A)
    (hlead : ∀ x, MvPolynomial.eval (A x) P.leadingCoeff ≠ 0)
    (hsep : ∀ x, (P.map (MvPolynomial.eval (A x))).Separable)
    (s₀ : S) (z₀ : ℍ) (b₀ : ℂ)
    (hb : Polynomial.eval₂ (MvPolynomial.eval (A (s₀,halfPlaneQ 1 one_pos z₀))) b₀ P = 0) :
    ∃ l : ℕ, ∃ hl : 0 < l, ∃ g : S × PuncturedUnitDisk → ℂ,
      Continuous g ∧
      (∀ s q, Polynomial.eval₂ (MvPolynomial.eval (A (s,puncturedPower l hl q))) (g (s,q)) P = 0) ∧
      g (s₀,halfPlaneQ l (by exact_mod_cast hl) z₀) = b₀ := by
  let R := {r : (S × PuncturedUnitDisk) × ℂ | Polynomial.eval₂ (MvPolynomial.eval (A r.1)) r.2 P = 0}
  let p : R → S × PuncturedUnitDisk := fun r => r.val.1
  let e₀ : R := ⟨((s₀,halfPlaneQ 1 one_pos z₀),b₀),hb⟩
  obtain ⟨l,hl,G,hGc,hpG,hG₀⟩ := finite_covering_ramified_section p
    (polynomial_root_covering P A hA hlead hsep) s₀ z₀ e₀ rfl
    (polynomial_root_fiber_finite P A _ (hlead _))
  refine ⟨l,hl,fun x => (G x).val.2,continuous_snd.comp (continuous_subtype_val.comp hGc),?_,?_⟩
  · intro s q
    have h := (G (s,q)).property
    change Polynomial.eval₂ (MvPolynomial.eval (A (p (G (s,q))))) ((G (s,q)).val.2) P = 0 at h
    rwa [hpG] at h
  · exact congrArg (fun r : R => r.val.2) hG₀

theorem simple_root_analytic_extension {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : E → (Fin d → ℂ))
    (Ω : Set E) (hΩ : IsOpen Ω) (hA : AnalyticOnNhd ℂ A Ω)
    (g : Ω → ℂ) (hg : Continuous g)
    (hroot : ∀ x, Polynomial.eval₂ (MvPolynomial.eval (A x.val)) (g x) P = 0)
    (hsimple : ∀ x, Polynomial.eval₂ (MvPolynomial.eval (A x.val)) (g x) P.derivative ≠ 0) :
    ∃ G : E → ℂ, AnalyticOnNhd ℂ G Ω ∧ ∀ x : Ω, G x.val = g x := by
  classical
  let G := Function.extend (Subtype.val : Ω → E) g (fun _ => 0)
  have hG (x : Ω) : G x.val = g x := Subtype.val_injective.extend_apply _ _ _
  have hGc : ContinuousOn G Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hg using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact hG x
  refine ⟨G,?_,hG⟩
  intro x hx
  apply continuous_polynomial_root_analyticAt P A G x (hA x hx) (hGc.continuousAt (hΩ.mem_nhds hx))
  · filter_upwards [hΩ.mem_nhds hx] with y hy
    simpa only [hG ⟨y,hy⟩] using hroot ⟨y,hy⟩
  · simpa only [hG ⟨x,hx⟩] using hsimple ⟨x,hx⟩

theorem polynomial_ramified_analytic_root {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : E × ℂ → (Fin d → ℂ))
    (S : Set E) (hS : IsOpen S) [ContractibleSpace S] [LocallyPathConnectedSpace S]
    (hA : AnalyticOnNhd ℂ A (S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1}))
    (hlead : ∀ x ∈ S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1},
      MvPolynomial.eval (A x) P.leadingCoeff ≠ 0)
    (hsep : ∀ x ∈ S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1},
      (P.map (MvPolynomial.eval (A x))).Separable)
    (s₀ : S) (z₀ : ℍ) (b₀ : ℂ)
    (hb : Polynomial.eval₂ (MvPolynomial.eval (A (s₀.val,(halfPlaneQ 1 one_pos z₀).val))) b₀ P = 0) :
    ∃ l : ℕ, ∃ hl : 0 < l, ∃ G : E × ℂ → ℂ,
      AnalyticOnNhd ℂ G (S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1}) ∧
      (∀ x ∈ S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1},
        Polynomial.eval₂ (MvPolynomial.eval (A (x.1,x.2^l))) (G x) P = 0) ∧
      G (s₀.val,(halfPlaneQ l (by exact_mod_cast hl) z₀).val) = b₀ := by
  let Ω : Set (E × ℂ) := S ×ˢ {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1}
  let α : S × PuncturedUnitDisk → E × ℂ := fun x => (x.1.val,x.2.val)
  have hαc : Continuous α :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have hα : ∀ x, α x ∈ Ω := fun x => ⟨x.1.property,x.2.property⟩
  have hAc : Continuous (A ∘ α) := hA.continuousOn.comp_continuous hαc hα
  obtain ⟨l,hl,g,hgc,hgr,hg₀⟩ := polynomial_ramified_continuous_root P (A ∘ α) hAc
    (fun x => hlead (α x) (hα x)) (fun x => hsep (α x) (hα x)) s₀ z₀ b₀ hb
  let ψ : Ω ≃ₜ S × PuncturedUnitDisk := Homeomorph.Set.prod S _
  let K : E × ℂ → E × ℂ := fun x => (x.1,x.2^l)
  have hK : AnalyticOnNhd ℂ K Set.univ := fun x _ => analyticAt_fst.prod (analyticAt_snd.pow l)
  have hKΩ (x : E × ℂ) (hx : x ∈ Ω) : K x ∈ Ω :=
    ⟨hx.1,pow_ne_zero l hx.2.1,by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hx.2.2 hl.ne'⟩
  have hAK : AnalyticOnNhd ℂ (A ∘ K) Ω := fun x hx =>
    (hA (K x) (hKΩ x hx)).comp (hK x (mem_univ _))
  have hrg (x : Ω) : Polynomial.eval₂ (MvPolynomial.eval ((A ∘ K) x.val)) (g (ψ x)) P = 0 :=
    hgr (ψ x).1 (ψ x).2
  have hsg (x : Ω) : Polynomial.eval₂ (MvPolynomial.eval ((A ∘ K) x.val)) (g (ψ x)) P.derivative ≠ 0 := by
    have hh := (hsep (K x.val) (hKΩ x.val x.property)).eval₂_derivative_ne_zero
      (RingHom.id ℂ) (x := g (ψ x))
    simpa only [Polynomial.eval₂_id,Polynomial.eval₂_at_apply,Polynomial.derivative_map,
      Polynomial.eval_map,Function.comp_def] using hh (by
        simpa only [Polynomial.eval₂_id,Polynomial.eval₂_at_apply,Polynomial.eval_map,Function.comp_def] using hrg x)
  have hΩ : IsOpen Ω := hS.prod (isOpen_ne_fun continuous_id continuous_const |>.inter
    (isOpen_lt (continuous_norm) continuous_const))
  obtain ⟨G,hGa,hGg⟩ := simple_root_analytic_extension P (A ∘ K) Ω hΩ hAK
    (g ∘ ψ) (hgc.comp ψ.continuous) hrg hsg
  refine ⟨l,hl,G,hGa,?_,?_⟩
  · intro x hx
    rw [hGg ⟨x,hx⟩]
    exact hrg ⟨x,hx⟩
  · rw [hGg ⟨(s₀.val,(halfPlaneQ l (by exact_mod_cast hl) z₀).val),s₀.property,
      (halfPlaneQ l (by exact_mod_cast hl) z₀).property⟩]
    exact hg₀

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticZeroRealPolydisc
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem analytic_zero_of_real_interval {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hz : ∀ t : ℝ, |t| < r → f t = 0) : EqOn f 0 (ball 0 r) := by
  apply hf.eqOn_zero_of_preconnected_of_mem_closure (convex_ball (0 : ℂ) r).isPreconnected
    (mem_ball_self hr)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t := min ε r / 2
  have ht : 0 < t := half_pos (lt_min hε hr)
  have htε : t < ε := lt_of_lt_of_le (half_lt_self (lt_min hε hr)) (min_le_left _ _)
  have htr : t < r := lt_of_lt_of_le (half_lt_self (lt_min hε hr)) (min_le_right _ _)
  refine ⟨(t : ℂ),⟨hz t (by simpa [abs_of_pos ht] using htr),?_⟩,?_⟩
  · simpa using ht.ne'
  · simpa [dist_eq_norm,Complex.norm_real,abs_of_pos ht] using htε

theorem analytic_zero_of_real_polydisc {n : ℕ} {f : (Fin n → ℂ) → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hz : ∀ x : Fin n → ℝ, ‖x‖ < r → f (fun i => (x i : ℂ)) = 0) :
    EqOn f 0 (ball 0 r) := by
  classical
  have hgen : ∀ S : Finset (Fin n), ∀ z : Fin n → ℂ, ‖z‖ < r →
      (∀ i ∉ S, (z i).im = 0) → f z = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro z hzr hreal
      have heq : z = fun i => ((z i).re : ℂ) := by
        funext i
        exact Complex.ext rfl (by simpa using hreal i (by simp))
      rw [heq]
      apply hz
      apply (pi_norm_lt_iff hr).mpr
      intro i
      exact (Complex.abs_re_le_norm _).trans_lt ((pi_norm_lt_iff hr).mp hzr i)
    | @insert a S ha ih =>
      intro z hzr hreal
      let g : ℂ → ℂ := fun t => f (Function.update z a t)
      have hupdate : ∀ t : ℂ, ‖t‖ < r → ‖Function.update z a t‖ < r := by
        intro t ht
        apply (pi_norm_lt_iff hr).mpr
        intro i
        by_cases hi : i = a
        · subst i; simpa using ht
        · simpa [Function.update_of_ne hi] using (pi_norm_lt_iff hr).mp hzr i
      have hg : AnalyticOnNhd ℂ g (ball 0 r) := by
        intro t ht
        have haffin : AnalyticAt ℂ (fun t : ℂ => Function.update z a t) t := by
          apply analyticAt_pi_iff.mpr
          intro i
          by_cases hi : i = a
          · subst i
            simp only [Function.update_self]
            exact analyticAt_id
          · simpa only [Function.update_of_ne hi] using (analyticAt_const (𝕜 := ℂ) (v := z i) (x := t))
        have htu : Function.update z a t ∈ ball 0 r := by
          simpa only [mem_ball,dist_zero_right] using
            (hupdate t (by simpa only [mem_ball,dist_zero_right] using ht))
        exact (hf _ htu).comp haffin
      have hgr : ∀ t : ℝ, |t| < r → g t = 0 := by
        intro t ht
        apply ih _ (hupdate t (by simpa using ht))
        intro i hi
        by_cases hia : i = a
        · subst i; simp
        · simpa only [Function.update_of_ne hia] using hreal i (by simp [hia,hi])
      have hzero := analytic_zero_of_real_interval hr hg hgr (by
        simpa only [mem_ball,dist_zero_right] using (pi_norm_lt_iff hr).mp hzr a)
      simpa only [g, Function.update_eq_self, Pi.zero_apply] using hzero
  intro z hzball
  exact hgen Finset.univ z (by simpa only [mem_ball,dist_zero_right] using hzball)
    (by intro i hi; exact (hi (Finset.mem_univ i)).elim)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_MeromorphicRemovablePositiveRay
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem meromorphic_no_pole_of_positive_ray_bound {f : ℂ → ℂ}
    (hf : MeromorphicAt f 0) {r B : ℝ} (hr : 0 < r)
    (hb : ∀ t : ℝ, 0 < t → t < r → ‖f t‖ ≤ B) :
    ∃ c : ℂ, Tendsto f (𝓝[≠] 0) (𝓝 c) := by
  apply tendsto_nhds_of_meromorphicOrderAt_nonneg hf
  by_contra h
  have hp := tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge h)
  let u : ℕ → ℝ := fun n => 1 / (n+1)
  have hu : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have huc : Tendsto (fun n => (u n : ℂ)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall ?_⟩
    · exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hu
    · intro n
      simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
      exact ne_of_gt (by dsimp [u]; positivity)
  have hlarge := ((tendsto_norm_atTop_iff_cobounded.mpr hp).comp huc).eventually
    (eventually_gt_atTop (B+1))
  have hsmall := hu.eventually (gt_mem_nhds hr)
  obtain ⟨n,hn₁,hn₂⟩ := (hlarge.and hsmall).exists
  have hh := hb (u n) (by dsimp [u]; positivity) hn₂
  change B + 1 < ‖f (u n : ℂ)‖ at hn₁
  linarith

theorem meromorphic_removable_of_positive_ray_bound {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hf : AnalyticOnNhd ℂ f (U \ {0})) (hm : MeromorphicAt f 0)
    {r B : ℝ} (hr : 0 < r)
    (hb : ∀ t : ℝ, 0 < t → t < r → ‖f t‖ ≤ B) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ {0}) := by
  classical
  obtain ⟨c,hc⟩ := meromorphic_no_pole_of_positive_ray_bound hm hr hb
  let g := Function.update f 0 c
  have heq : ∀ x : ℂ, x ≠ 0 → g x = f x := by
    intro x hx
    simp [g, Function.update_of_ne hx]
  have hag : ∀ x ∈ U \ {0}, AnalyticAt ℂ g x := by
    intro x hx
    apply (hf x hx).congr
    filter_upwards [isOpen_compl_singleton.mem_nhds hx.2] with y hy
    exact (heq y hy).symm
  refine ⟨g,?_,fun x hx => heq x hx.2⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    have hgc : ContinuousAt g 0 := by
      rw [← continuousWithinAt_compl_self]
      have hg0 : g 0 = c := by simp [g]
      change Tendsto g (𝓝[≠] 0) (𝓝 (g 0))
      rw [hg0]
      apply hc.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (heq y hy).symm
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hgc
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h0)] with y hy hyU
    exact (hag y ⟨hyU,hy⟩).differentiableAt
  · exact hag x ⟨hx,hx0⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RealParameterPolarRemoval
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem analyticOnNhd_of_differentiableOn_finDim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {S : Set E} (hS : IsOpen S) {f : E → ℂ} (hf : DifferentiableOn ℂ f S) :
    AnalyticOnNhd ℂ f S := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) := (Module.finBasis ℂ E).equivFunL
  have ha := analyticOnNhd_of_differentiableOn_finite
    (hS.preimage e.symm.continuous) (hf.comp e.symm.differentiable.differentiableOn (fun _ h => h))
  intro x hx
  have hx' : e x ∈ e.symm ⁻¹' S := by simpa only [mem_preimage,e.symm_apply_apply] using hx
  have hcomp := (ha (e x) hx').comp (e.analyticAt x)
  simpa only [Function.comp_def,e.symm_apply_apply] using hcomp

theorem real_parameter_polar_removal {n : ℕ}
    {r R S : ℝ} (hr : 0 < r) (hR : 0 < R) (hRS : R < S)
    (f : (Fin n → ℂ) × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball 0 r ×ˢ (ball 0 S \ {0})))
    (hm : ∀ s : Fin n → ℝ, ‖s‖ < r →
      MeromorphicAt (fun u => f ((fun i => (s i : ℂ)),u)) 0)
    {B ε : ℝ} (hε : 0 < ε)
    (hb : ∀ s : Fin n → ℝ, ‖s‖ < r → ∀ t : ℝ, 0 < t → t < ε →
      ‖f ((fun i => (s i : ℂ)),t)‖ ≤ B) :
    ∃ g : (Fin n → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball 0 r ×ˢ ball 0 R) ∧
      EqOn g f (ball 0 r ×ˢ (ball 0 R \ {0})) := by
  let g : (Fin n → ℂ) × ℂ → ℂ := fun p =>
    (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(0, R), (w - p.2)⁻¹ * f (p.1,w)
  have hboundary : ∀ u ∈ sphere (0 : ℂ) R, u ∈ ball 0 S \ {0} := by
    intro u hu
    refine ⟨sphere_subset_ball hRS hu,?_⟩
    intro hu0
    have heq : u = 0 := hu0
    subst u
    have hzero : (0 : ℝ) = R := by simpa using hu
    exact hR.ne hzero
  have hg : AnalyticOnNhd ℂ g (ball 0 r ×ˢ ball 0 R) := by
    apply analyticOnNhd_of_differentiableOn_finDim (isOpen_ball.prod isOpen_ball)
    exact differentiableOn_cauchyTransform isOpen_ball hR f
      (fun p hp => hf p ⟨hp.1,hboundary p.2 hp.2⟩)
  have hreal : ∀ s : Fin n → ℝ, ‖s‖ < r → ∀ u ∈ ball 0 R \ {0},
      g ((fun i => (s i : ℂ)),u) = f ((fun i => (s i : ℂ)),u) := by
    intro s hs
    let sc : Fin n → ℂ := fun i => (s i : ℂ)
    have hsc : sc ∈ ball 0 r := by
      rw [mem_ball, dist_zero_right]
      apply (pi_norm_lt_iff hr).mpr
      intro i
      simpa [sc] using (pi_norm_lt_iff hr).mp hs i
    have hsanalytic : AnalyticOnNhd ℂ (fun u => f (sc,u)) (ball 0 S \ {0}) := by
      intro u hu
      exact (hf (sc,u) ⟨hsc,hu⟩).comp
        ((analyticAt_const (v := sc)).prod analyticAt_id)
    obtain ⟨ga,hga,heq⟩ := meromorphic_removable_of_positive_ray_bound
      isOpen_ball (mem_ball_self (hR.trans hRS)) hsanalytic (hm s hs) hε (hb s hs)
    intro u hu
    have hc : (2 * Real.pi * Complex.I)⁻¹ *
        (∮ w in C(0,R), (w-u)⁻¹ * ga w) = ga u := by
      simpa only [smul_eq_mul] using
        Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          (s := ∅) Set.countable_empty hu.1
          (hga.continuousOn.mono (closedBall_subset_ball hRS))
          (fun w hw => (hga w ((ball_subset_ball hRS.le) hw.1)).differentiableAt)
    change (2 * Real.pi * Complex.I)⁻¹ *
      (∮ w in C(0,R), (w-u)⁻¹ * f (sc,w)) = f (sc,u)
    have hequ : ga u = f (sc,u) := heq ⟨ball_subset_ball hRS.le hu.1,hu.2⟩
    rw [← hequ,← hc]
    congr 1
    apply circleIntegral.integral_congr hR.le
    intro w hw
    dsimp only
    have heqw : ga w = f (sc,w) := heq (hboundary w hw)
    rw [heqw]
  refine ⟨g,hg,?_⟩
  intro p hp
  let h : (Fin n → ℂ) → ℂ := fun s => g (s,p.2) - f (s,p.2)
  have hh : AnalyticOnNhd ℂ h (ball 0 r) := by
    intro s hs
    have hin : AnalyticAt ℂ (fun s : Fin n → ℂ => (s,p.2)) s :=
      analyticAt_id.prod analyticAt_const
    exact ((hg (s,p.2) ⟨hs,hp.2.1⟩).comp (f := fun s => (s,p.2)) hin).sub
      ((hf (s,p.2) ⟨hs,ball_subset_ball hRS.le hp.2.1,hp.2.2⟩).comp (f := fun s => (s,p.2)) hin)
  have hhz : ∀ s : Fin n → ℝ, ‖s‖ < r → h (fun i => (s i : ℂ)) = 0 := by
    intro s hs
    exact sub_eq_zero.mpr (hreal s hs p.2 hp.2)
  have hzero := analytic_zero_of_real_polydisc hr hh hhz hp.1
  exact sub_eq_zero.mp hzero

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AlgebraicBranchRamification
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Filter Set Complex UpperHalfPlane Function
open scoped Topology

theorem continuous_polynomial_roots_eq {d : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : X → (Fin d → ℂ))
    (hA : Continuous A)
    (hlead : ∀ x, MvPolynomial.eval (A x) P.leadingCoeff ≠ 0)
    (hsep : ∀ x, (P.map (MvPolynomial.eval (A x))).Separable)
    (g h : X → ℂ) (hg : Continuous g) (hh : Continuous h)
    (hgr : ∀ x, Polynomial.eval₂ (MvPolynomial.eval (A x)) (g x) P = 0)
    (hhr : ∀ x, Polynomial.eval₂ (MvPolynomial.eval (A x)) (h x) P = 0)
    (x₀ : X) (h₀ : g x₀ = h x₀) : g = h := by
  let R := {r : X × ℂ | Polynomial.eval₂ (MvPolynomial.eval (A r.1)) r.2 P = 0}
  let G : X → R := fun x => ⟨(x,g x),hgr x⟩
  let H : X → R := fun x => ⟨(x,h x),hhr x⟩
  have he : G = H := (polynomial_root_covering P A hA hlead hsep).eq_of_comp_eq
    ((continuous_id.prodMk hg).subtype_mk _) ((continuous_id.prodMk hh).subtype_mk _)
    rfl x₀ (Subtype.ext (Prod.ext rfl h₀))
  exact funext fun x => congrArg (fun r : R => r.val.2) (congrFun he x)

theorem halfPlaneQ_unitImaginary (h : ℝ) (hh : 0 < h) :
    (halfPlaneQ h hh unitImaginaryHalfPlane).val =
      (Real.exp (-2 * Real.pi / h) : ℂ) := by
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I * Complex.I / (h : ℂ)) = _
  rw [show 2 * (Real.pi : ℂ) * Complex.I * Complex.I / (h : ℂ) =
    ((-2 * Real.pi / h : ℝ) : ℂ) from by
      push_cast
      rw [mul_assoc (2 * (Real.pi : ℂ)),Complex.I_mul_I]
      ring]
  exact Complex.ofReal_exp _ |>.symm

theorem halfPlaneQ_unitImaginary_real_bounds (h : ℝ) (hh : 0 < h) :
    0 < Real.exp (-2 * Real.pi / h) ∧ Real.exp (-2 * Real.pi / h) < 1 := by
  refine ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr ?_⟩
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos) hh

end

open Filter Set Metric Complex
open scoped Topology

theorem realParameter_zero {n : ℕ} : realParameter (0 : Fin n → ℝ) = 0 := by
  ext i
  exact Complex.ofReal_zero

theorem continuous_realParameter (n : ℕ) : Continuous (realParameter (n := n)) :=
  continuous_pi (fun i => Complex.continuous_ofReal.comp (continuous_apply i))

theorem norm_realParameter {n : ℕ} (s : Fin n → ℝ) : ‖realParameter s‖ = ‖s‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [realParameter,Complex.norm_real] using norm_le_pi_norm s i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [realParameter,Complex.norm_real] using norm_le_pi_norm (realParameter s) i

theorem realParameter_mem_ball {n : ℕ} {s : Fin n → ℝ} {r : ℝ} (hs : s ∈ ball 0 r) :
    realParameter s ∈ ball 0 r := by
  simpa only [mem_ball,dist_zero_right,norm_realParameter] using hs

theorem algebraic_real_parameter_removal {n d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ))
    (A : (Fin n → ℂ) × ℂ → (Fin d → ℂ))
    {r R S : ℝ} (hr : 0 < r) (hR : 0 < R) (hRS : R < S)
    (hA : AnalyticOnNhd ℂ A (ball 0 r ×ˢ ball 0 S))
    (f : (Fin n → ℂ) × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball 0 r ×ˢ (ball 0 S \ {0})))
    (hroot : ∀ p ∈ ball 0 r ×ˢ (ball 0 S \ {0}),
      Polynomial.eval₂ (MvPolynomial.eval (A p)) (f p) P = 0)
    (hlead : ∀ p ∈ ball 0 r ×ˢ (ball 0 S \ {0}),
      MvPolynomial.eval (A p) P.leadingCoeff ≠ 0)
    {B ε : ℝ} (hε : 0 < ε)
    (hb : ∀ s : Fin n → ℝ, ‖s‖ < r → ∀ t : ℝ, 0 < t → t < ε →
      ‖f (realParameter s,t)‖ ≤ B) :
    ∃ g : (Fin n → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball 0 r ×ˢ ball 0 R) ∧
      EqOn g f (ball 0 r ×ˢ (ball 0 R \ {0})) := by
  apply real_parameter_polar_removal hr hR hRS f hf _ hε hb
  intro s hs
  have hsc : realParameter s ∈ ball 0 r := realParameter_mem_ball (by simpa using hs)
  have hAs : AnalyticAt ℂ (fun u => A (realParameter s,u)) 0 :=
    (hA (realParameter s,0) ⟨hsc,mem_ball_self (hR.trans hRS)⟩).comp
      (analyticAt_const.prod analyticAt_id)
  have heu : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∈ ball 0 S \ {0} := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self (hR.trans hRS)))] with u hu huS
    exact ⟨huS,hu⟩
  apply meromorphicAt_polynomial_root P (fun u => A (realParameter s,u)) hAs (fun u => f (realParameter s,u))
  · exact heu.mono fun u hu => (hf (realParameter s,u) ⟨hsc,hu⟩).comp
      (analyticAt_const.prod analyticAt_id)
  · exact heu.mono fun u hu => hroot (realParameter s,u) ⟨hsc,hu⟩
  · intro hz
    obtain ⟨u,hu,huz⟩ := (heu.and (hz.filter_mono nhdsWithin_le_nhds)).exists
    exact hlead (realParameter s,u) ⟨hsc,hu⟩ huz

theorem ramified_real_branch_match {n d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ))
    (A : (Fin n → ℂ) × ℂ → (Fin d → ℂ))
    {r : ℝ} (hA : ContinuousOn A (ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1}))
    (hlead : ∀ p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1},
      MvPolynomial.eval (A p) P.leadingCoeff ≠ 0)
    (hsep : ∀ p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1},
      (P.map (MvPolynomial.eval (A p))).Separable)
    (b : (Fin n → ℝ) × ℝ → ℂ)
    (hb : ContinuousOn b (ball 0 r ×ˢ Ioo 0 1))
    (hbr : ∀ (p : (Fin n → ℝ) × ℝ), p ∈ ball 0 r ×ˢ Ioo 0 1 →
      Polynomial.eval₂ (MvPolynomial.eval (A (realParameter p.1,p.2))) (b p) P = 0)
    (l : ℕ) (hl : 0 < l) (G : (Fin n → ℂ) × ℂ → ℂ)
    (hG : ContinuousOn G (ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1}))
    (hGr : ∀ p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1},
      Polynomial.eval₂ (MvPolynomial.eval (A (p.1,p.2^l))) (G p) P = 0)
    (s₀ : Fin n → ℝ) (hs₀ : s₀ ∈ ball 0 r) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1)
    (h₀ : G (realParameter s₀,t₀) = b (s₀,t₀^l)) :
    ∀ s ∈ ball 0 r, ∀ t ∈ Ioo (0 : ℝ) 1,
      G (realParameter s,t) = b (s,t^l) := by
  let : ContractibleSpace (ball (0 : Fin n → ℝ) r) :=
    (convex_ball (0 : Fin n → ℝ) r).contractibleSpace ⟨s₀,hs₀⟩
  let : ContractibleSpace (Ioo (0 : ℝ) 1) := (convex_Ioo (𝕜 := ℝ) 0 1).contractibleSpace ⟨t₀,ht₀⟩
  let X := (ball (0 : Fin n → ℝ) r) × (Ioo (0 : ℝ) 1)
  let ι : X → (Fin n → ℂ) × ℂ := fun x => (realParameter x.1.val,x.2.val)
  let κ : X → (Fin n → ℂ) × ℂ := fun x => (realParameter x.1.val,(x.2.val : ℂ)^l)
  let β : X → (Fin n → ℝ) × ℝ := fun x => (x.1.val,x.2.val^l)
  have hιc : Continuous ι :=
    ((continuous_realParameter n).comp (continuous_subtype_val.comp continuous_fst)).prodMk
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd))
  have hκc : Continuous κ := hιc.fst.prodMk (hιc.snd.pow l)
  have hβc : Continuous β := (continuous_subtype_val.comp continuous_fst).prodMk
    ((continuous_subtype_val.comp continuous_snd).pow l)
  have hι (x : X) : ι x ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1} := by
    refine ⟨realParameter_mem_ball x.1.property,?_,?_⟩
    · change (x.2.val : ℂ) ≠ 0
      exact_mod_cast x.2.property.1.ne'
    · simpa only [ι,Complex.norm_real,Real.norm_eq_abs,abs_of_pos x.2.property.1] using x.2.property.2
  have hκ (x : X) : κ x ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1} := by
    refine ⟨(hι x).1,pow_ne_zero l (hι x).2.1,?_⟩
    change ‖(x.2.val : ℂ)^l‖ < 1
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (hι x).2.2 hl.ne'
  have hβ (x : X) : β x ∈ ball 0 r ×ˢ Ioo 0 1 :=
    ⟨x.1.property,pow_pos x.2.property.1 l,pow_lt_one₀ x.2.property.1.le x.2.property.2 hl.ne'⟩
  have hgcont : Continuous (G ∘ ι) := hG.comp_continuous hιc hι
  have hbcont : Continuous (b ∘ β) := hb.comp_continuous hβc hβ
  have he := continuous_polynomial_roots_eq P (A ∘ κ) (hA.comp_continuous hκc hκ)
    (fun x => hlead (κ x) (hκ x)) (fun x => hsep (κ x) (hκ x))
    (G ∘ ι) (b ∘ β) hgcont hbcont
    (fun x => hGr (ι x) (hι x))
    (fun x => by simpa only [Function.comp_apply,κ,β,Complex.ofReal_pow] using hbr (β x) (hβ x))
    (⟨s₀,hs₀⟩,⟨t₀,ht₀⟩) h₀
  intro s hs t ht
  exact congrFun he (⟨s,hs⟩,⟨t,ht⟩)

theorem bounded_algebraic_branch_ramification {n d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ))
    (A : (Fin n → ℂ) × ℂ → (Fin d → ℂ))
    {r : ℝ} (hr : 0 < r)
    (hA : AnalyticOnNhd ℂ A (ball 0 r ×ˢ ball 0 1))
    (hlead : ∀ p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1},
      MvPolynomial.eval (A p) P.leadingCoeff ≠ 0)
    (hsep : ∀ p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1},
      (P.map (MvPolynomial.eval (A p))).Separable)
    (b : (Fin n → ℝ) × ℝ → ℂ)
    (hb : ContinuousOn b (ball 0 r ×ˢ Ioo 0 1))
    (hbr : ∀ (p : (Fin n → ℝ) × ℝ), p ∈ ball 0 r ×ˢ Ioo 0 1 →
      Polynomial.eval₂ (MvPolynomial.eval (A (realParameter p.1,p.2))) (b p) P = 0)
    {B : ℝ} (hbound : ∀ p ∈ ball 0 r ×ˢ Ioo 0 1, ‖b p‖ ≤ B) :
    ∃ l : ℕ, 0 < l ∧ ∃ F : (Fin n → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ F (ball 0 r ×ˢ ball 0 (1/2)) ∧
      ∀ s ∈ ball 0 r, ∀ t ∈ Ioo (0 : ℝ) (1/2),
        F (realParameter s,t) = b (s,t^l) := by
  let : ContractibleSpace (ball (0 : Fin n → ℂ) r) :=
    (convex_ball (0 : Fin n → ℂ) r).contractibleSpace ⟨0,mem_ball_self hr⟩
  let : LocallyPathConnectedSpace (ball (0 : Fin n → ℂ) r) :=
    isOpen_ball.locallyPathConnectedSpace
  let t₁ : ℝ := Real.exp (-2 * Real.pi / 1)
  have ht₁ : t₁ ∈ Ioo (0 : ℝ) 1 := halfPlaneQ_unitImaginary_real_bounds 1 one_pos
  have hA' : AnalyticOnNhd ℂ A (ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1}) :=
    hA.mono (fun p hp => ⟨hp.1,by simpa only [mem_ball,dist_zero_right] using hp.2.2⟩)
  have hroot₀ : Polynomial.eval₂
      (MvPolynomial.eval (A (0,(halfPlaneQ 1 one_pos unitImaginaryHalfPlane).val))) (b (0,t₁)) P = 0 := by
    rw [halfPlaneQ_unitImaginary]
    simpa only [t₁,realParameter_zero] using
      hbr (0,t₁) ⟨mem_ball_self hr,ht₁⟩
  obtain ⟨l,hl,G,hGa,hGr,hG₀⟩ := polynomial_ramified_analytic_root P A (ball 0 r) isOpen_ball
    hA' hlead hsep ⟨0,mem_ball_self hr⟩ unitImaginaryHalfPlane (b (0,t₁)) hroot₀
  let t₀ : ℝ := Real.exp (-2 * Real.pi / l)
  have htl : (0 : ℝ) < l := by exact_mod_cast hl
  have ht₀ : t₀ ∈ Ioo (0 : ℝ) 1 := halfPlaneQ_unitImaginary_real_bounds l htl
  have hpow : t₀^l = t₁ := by
    have he := congrArg Subtype.val (halfPlaneQ_nat l hl unitImaginaryHalfPlane)
    change (halfPlaneQ 1 one_pos unitImaginaryHalfPlane).val =
      (halfPlaneQ l htl unitImaginaryHalfPlane).val^l at he
    rw [halfPlaneQ_unitImaginary,halfPlaneQ_unitImaginary] at he
    dsimp only [t₀,t₁]
    exact_mod_cast he.symm
  have hinit : G (realParameter 0,t₀) = b (0,t₀^l) := by
    rw [hpow]
    rw [halfPlaneQ_unitImaginary] at hG₀
    simpa only [realParameter_zero,t₀] using hG₀
  have hmatch := ramified_real_branch_match P A hA'.continuousOn hlead hsep b hb hbr
    l hl G hGa.continuousOn hGr 0 (mem_ball_self hr) t₀ ht₀ hinit
  let K : (Fin n → ℂ) × ℂ → (Fin n → ℂ) × ℂ := fun p => (p.1,p.2^l)
  have hKa (p : (Fin n → ℂ) × ℂ) : AnalyticAt ℂ K p :=
    analyticAt_fst.prod (analyticAt_snd.pow l)
  have hK (p : (Fin n → ℂ) × ℂ) (hp : p ∈ ball 0 r ×ˢ ball 0 1) :
      K p ∈ ball 0 r ×ˢ ball 0 1 := by
    refine ⟨hp.1,?_⟩
    simp only [K,mem_ball,dist_zero_right,norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by simpa only [mem_ball,dist_zero_right] using hp.2) hl.ne'
  have hAK : AnalyticOnNhd ℂ (A ∘ K) (ball 0 r ×ˢ ball 0 1) :=
    fun p hp => (hA (K p) (hK p hp)).comp (hKa p)
  have hpun : ball (0 : ℂ) 1 \ {0} = {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1} := by
    ext u
    simp only [Set.mem_sdiff,mem_ball,dist_zero_right,mem_singleton_iff,mem_ofPred_eq,and_comm]
  obtain ⟨F,hFa,hFG⟩ := algebraic_real_parameter_removal P (A ∘ K) hr (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) < 1) hAK G (by simpa only [hpun] using hGa)
    (by simpa only [hpun,Function.comp_def,K] using hGr)
    (by
      intro p hp
      rw [hpun] at hp
      apply hlead (K p)
      exact ⟨hp.1,pow_ne_zero l hp.2.1,by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hp.2.2 hl.ne'⟩)
    (by norm_num : (0 : ℝ) < 1)
    (by
      intro s hs t ht ht1
      rw [hmatch s (by simpa only [mem_ball,dist_zero_right] using hs) t ⟨ht,ht1⟩]
      exact hbound (s,t^l) ⟨by simpa only [mem_ball,dist_zero_right] using hs,
        pow_pos ht l,pow_lt_one₀ ht.le ht1 hl.ne'⟩)
  refine ⟨l,hl,F,hFa,?_⟩
  intro s hs t ht
  rw [hFG (by
    refine ⟨realParameter_mem_ball hs,?_,?_⟩
    · simpa only [mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1] using ht.2
    · simpa only [mem_singleton_iff,Complex.ofReal_eq_zero] using ht.1.ne')]
  exact hmatch s hs t ⟨ht.1,ht.2.trans (by norm_num)⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticZeroNull
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter MeasureTheory
open scoped Topology

theorem analytic_real_zero_null {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set ℝ} (hU : MeasurableSet U) (hc : IsPreconnected U)
    {f : ℝ → F} (hf : AnalyticOnNhd ℝ f U) {p : ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    volume {x | x ∈ U ∧ f x = 0} = 0 := by
  have ha := hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hc
  rcases ha with ha | ha
  · exact (hne (ha hp)).elim
  · have hb := ae_restrict_le_codiscreteWithin (μ := volume) hU ha
    have hd := (ae_restrict_iff' hU).mp hb
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hd] with x hx
    exact fun h => hx h.1 h.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radialPlane_analytic (p : E × ℝ) (q : E × ℝ) : AnalyticAt ℝ (radialPlane p) q := by
  exact analyticAt_const.add ((analyticAt_snd.smul analyticAt_fst).prod analyticAt_snd)

theorem radialLine_analytic (p : E × ℝ) (y : E) (t : ℝ) : AnalyticAt ℝ (radialLine p y) t := by
  exact (radialPlane_analytic p (y,t)).comp (analyticAt_const.prod analyticAt_id)

theorem analytic_zero_null_convex [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set (E × ℝ)} (hU : IsOpen U) (hc : Convex ℝ U)
    {f : E × ℝ → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E × ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    (μ.prod volume) {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  let Z : Set (E × ℝ) := {x | x ∈ U ∧ f x = 0}
  have hZ : MeasurableSet Z := by
    have hm : Measurable (U.piecewise f (fun _ => 0)) :=
      hf.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
    convert hU.measurableSet.inter ((measurableSet_singleton (0 : F)).preimage hm) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    by_cases hx : x ∈ U <;> simp [Z,hx]
  have hr : Continuous (radialPlane p) := continuous_iff_continuousAt.mpr fun q => (radialPlane_analytic p q).continuousAt
  have hn : (μ.prod volume) (radialPlane p ⁻¹' Z) = 0 := by
    apply Measure.measure_prod_null_of_ae_null (hZ.preimage hr.measurable)
    apply Eventually.of_forall
    intro y
    let I : Set ℝ := radialLine p y ⁻¹' U
    have hI : IsOpen I := hU.preimage (continuous_iff_continuousAt.mpr fun t => (radialLine_analytic p y t).continuousAt)
    have hr0 : radialLine p y 0 = p := by
      change p + ((0 : ℝ) • y,(0 : ℝ)) = p
      rw [zero_smul]
      exact add_zero p
    have h0 : (0 : ℝ) ∈ I := by change radialLine p y 0 ∈ U; simpa only [hr0] using hp
    have hf0 : f (radialLine p y 0) ≠ 0 := by simpa only [hr0] using hne
    exact analytic_real_zero_null hI.measurableSet (hc.affine_preimage (radialLine p y)).isPreconnected
      (fun t ht => (hf _ ht).comp (radialLine_analytic p y t)) h0 hf0
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ.prod volume) (s := radialPlane p ⁻¹' Z)
    (fun q _ => (radialPlane_analytic p q).differentiableAt.differentiableWithinAt) hn
  have hplane : (μ.prod volume) (Set.univ ×ˢ {p.2}) = 0 := by
    rw [Measure.prod_prod,measure_singleton,mul_zero]
  apply measure_mono_null (t := radialPlane p '' (radialPlane p ⁻¹' Z) ∪ (Set.univ ×ˢ {p.2}))
      _ (measure_union_null himg hplane)
  intro x hx
  by_cases ht : x.2 = p.2
  · exact Or.inr ⟨mem_univ _,ht⟩
  · left
    let q : E × ℝ := ((x.2-p.2)⁻¹ • (x.1-p.1),x.2-p.2)
    have hq : radialPlane p q = x := by
      ext
      · simp only [radialPlane,q,Prod.fst_add,smul_smul]
        rw [mul_inv_cancel₀ (sub_ne_zero.mpr ht),one_smul]
        abel
      · simp [radialPlane,q]
    exact ⟨q,by simpa only [mem_preimage,hq] using hx,hq⟩

theorem analytic_zero_null_connected [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set (E × ℝ)} (hU : IsOpen U) (hc : IsPreconnected U)
    {f : E × ℝ → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E × ℝ} (hp : p ∈ U) (hne : f p ≠ 0) :
    (μ.prod volume) {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  have hball : ∀ x ∈ U, ∃ r > 0, Metric.ball x r ⊆ U := fun x hx =>
    Metric.isOpen_iff.mp hU x hx
  choose! r hr hsub using hball
  obtain ⟨T,hTU,hTc,hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := U) (f := fun x => Metric.ball x (r x))
    (fun x hx => mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (hr x hx)))
  have hn : ∀ x ∈ T, (μ.prod volume) {y | y ∈ Metric.ball x (r x) ∧ f y = 0} = 0 := by
    intro x hx
    have hxu := hTU hx
    have he : ∃ y ∈ Metric.ball x (r x), f y ≠ 0 := by
      by_contra! he
      have hz : f =ᶠ[𝓝 x] 0 := by
        filter_upwards [Metric.ball_mem_nhds x (hr x hxu)] with y hy
        exact he y hy
      exact hne (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hxu hz hp)
    obtain ⟨y,hy,hfy⟩ := he
    exact analytic_zero_null_convex μ Metric.isOpen_ball (convex_ball x (r x))
      (hf.mono (hsub x hxu)) hy hfy
  apply measure_mono_null (t := ⋃ x ∈ T, {y | y ∈ Metric.ball x (r x) ∧ f y = 0})
    _ ((measure_biUnion_null_iff hTc).mpr hn)
  intro y hy
  obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp (hcov hy.1)
  exact mem_iUnion₂.mpr ⟨x,hx,hyx,hy.2⟩

theorem analytic_zero_null [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {f : E → F} (hf : AnalyticOnNhd ℝ f U)
    {p : E} (hp : p ∈ U) (hne : f p ≠ 0) : μ {x | x ∈ U ∧ f x = 0} = 0 := by
  classical
  rcases subsingleton_or_nontrivial E with hs | hnt
  · have hz : {x | x ∈ U ∧ f x = 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hne ((congrArg f (Subsingleton.elim p x)).trans hx.2)
    rw [hz,measure_empty]
  · obtain ⟨n,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
    let e : E ≃L[ℝ] ((Fin n → ℝ) × ℝ) := ContinuousLinearEquiv.ofFinrankEq
      (by simpa [Module.finrank_prod,Module.finrank_pi_fintype,Nat.succ_eq_add_one] using hd)
    let U' := e.symm ⁻¹' U
    let f' := f ∘ e.symm
    have hf' : AnalyticOnNhd ℝ f' U' := fun x hx => (hf _ hx).comp (e.symm.analyticAt x)
    have hp' : e p ∈ U' := by simpa only [U',mem_preimage,e.symm_apply_apply] using hp
    have he : f' (e p) ≠ 0 := by simpa only [f',Function.comp_apply,e.symm_apply_apply] using hne
    have hU' : IsOpen U' := hU.preimage e.symm.continuous
    have hc' : IsPreconnected U' := e.symm.toHomeomorph.isPreconnected_preimage.mpr hc
    have hn := analytic_zero_null_connected (volume : Measure (Fin n → ℝ)) hU' hc' hf' hp' he
    let Z' := {x | x ∈ U' ∧ f' x = 0}
    have hZ' : MeasurableSet Z' := by
      have hm : Measurable (U'.piecewise f' (fun _ => 0)) :=
        hf'.continuousOn.measurable_piecewise continuousOn_const hU'.measurableSet
      convert hU'.measurableSet.inter ((measurableSet_singleton (0 : F)).preimage hm) using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      by_cases hx : x ∈ U' <;> simp [Z',hx]
    have hae : ∀ᵐ q ∂(volume : Measure (Fin n → ℝ)).prod volume, q ∈ Z'ᶜ :=
      measure_eq_zero_iff_ae_notMem.mp hn
    have hat := (ae_comp_linearMap_mem_iff e.toLinearMap μ
      ((volume : Measure (Fin n → ℝ)).prod volume) e.surjective hZ'.compl).mpr hae
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hat] with x hx
    have hx' : e x ∈ Z'ᶜ := hx
    simpa [Z',U',f'] using hx'

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericPolynomialParameterFactor
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory

theorem complex_polynomial_real_witness {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    ∃ x : Fin n → ℝ, MvPolynomial.eval (fun i => (x i : ℂ)) P ≠ 0 := by
  classical
  by_contra! hz
  apply hP
  apply MvPolynomial.funext_set (fun _ => Set.range (fun t : ℝ => (t : ℂ)))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz'
  have hc : ∀ i, ∃ t : ℝ, (t : ℂ) = z i := fun i => hz' i (mem_univ i)
  choose x hx using hc
  have he : z = fun i => (x i : ℂ) := (funext hx).symm
  simpa only [he,map_zero] using hz x

theorem complex_polynomial_real_zero_null {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} = 0 := by
  obtain ⟨x,hx⟩ := complex_polynomial_real_witness P hP
  have he (s : Fin n → ℝ) : AnalyticAt ℝ (fun y : Fin n → ℝ => fun i => (y i : ℂ)) s := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact (Complex.ofRealCLM.analyticAt _).comp
      ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt s)
  have ha : AnalyticOnNhd ℝ (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) P) univ := by
    intro s _
    exact (((AnalyticOnNhd.eval_mvPolynomial P) _ (mem_univ _)).restrictScalars (𝕜 := ℝ)).comp (he s)
  simpa only [mem_univ,true_and] using analytic_zero_null volume isOpen_univ
    isPreconnected_univ ha (mem_univ x) hx

theorem analyticAt_parameter_polynomial {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) (a : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ =>
      Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P) a := by
  have hpoly : ∀ j : ℕ, AnalyticAt ℂ
      (fun p : ((Fin n → ℂ) × ℂ) => MvPolynomial.eval p.1 (P.coeff j)) a := by
    intro j
    exact (AnalyticOnNhd.eval_mvPolynomial (P.coeff j) _ (Set.mem_univ _)).comp
      ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).analyticAt _)
  simp only [Polynomial.eval₂_eq_sum_range]
  exact Finset.analyticAt_fun_sum (Finset.range (P.natDegree + 1)) (fun j _ =>
    (hpoly j).mul (((ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).analyticAt _).pow j))

theorem generic_polynomial_parameter_factor {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) (hP : P ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ (k : ℕ) (g : ((Fin n → ℂ) × ℂ) → ℂ),
        AnalyticAt ℂ g ((fun i => (s i : ℂ)),0) ∧
        g ((fun i => (s i : ℂ)),0) ≠ 0 ∧
        (∀ p, Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P = p.2^k * g p) ∧
        ∀ᶠ p in 𝓝 ((fun i => (s i : ℂ)),(0 : ℂ)), g p ≠ 0 := by
  let k := P.natTrailingDegree
  have hc : P.coeff k ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hP
  let E : Set (Fin n → ℝ) := {s | MvPolynomial.eval (fun i => (s i : ℂ)) (P.coeff k) = 0}
  refine ⟨E,complex_polynomial_real_zero_null _ hc,?_⟩
  intro s hs
  obtain ⟨Q,hQ⟩ := Polynomial.X_pow_dvd_iff.mpr
    (fun d (hd : d < k) => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd)
  let g : ((Fin n → ℂ) × ℂ) → ℂ := fun p => Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 Q
  have hg := analyticAt_parameter_polynomial Q ((fun i => (s i : ℂ)),0)
  have hcoeff : Q.coeff 0 = P.coeff k := by
    rw [hQ]
    simpa only [zero_add] using (Polynomial.coeff_X_pow_mul Q k 0).symm
  have hgne : g ((fun i => (s i : ℂ)),0) ≠ 0 := by
    simpa only [g,Polynomial.eval₂_at_zero,hcoeff,E,Set.mem_ofPred_eq] using hs
  refine ⟨k,g,hg,hgne,?_,hg.continuousAt.eventually_ne hgne⟩
  intro p
  rw [hQ,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericFinParameterPolynomial
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory Metric

theorem generic_polynomial_parameter_nonzero {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) (hP : P ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ r > 0, ∀ z ∈ ball (fun i => (s i : ℂ)) r,
        ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 → Polynomial.eval₂ (MvPolynomial.eval z) t P ≠ 0 := by
  obtain ⟨E,hE,hfactor⟩ := generic_polynomial_parameter_factor P hP
  refine ⟨E,hE,?_⟩
  intro s hs
  obtain ⟨k,g,_,_,he,hunit⟩ := hfactor s hs
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hunit
  refine ⟨r,hr,?_⟩
  intro z hz t ht ht0
  have hzt : (z,t) ∈ ball ((fun i => (s i : ℂ)),(0 : ℂ)) r := by
    simpa only [mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hz ht
  rw [he (z,t)]
  exact mul_ne_zero (pow_ne_zero k ht0) (hsub hzt)

theorem separable_map_of_leading_resultant_ne_zero
    {R K : Type*} [CommRing R] [Field K] (P : Polynomial R) (e : R →+* K)
    (hl : e P.leadingCoeff ≠ 0)
    (hd : e (P.resultant P.derivative) ≠ 0) : (P.map e).Separable := by
  by_cases hdeg : P.natDegree = 0
  · have hP : P = Polynomial.C P.leadingCoeff := by
      simpa only [Polynomial.leadingCoeff,hdeg] using Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rw [hP,Polynomial.map_C]
    exact (Polynomial.separable_C _).mpr (isUnit_iff_ne_zero.mpr hl)
  · obtain ⟨a,b,_,_,hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
      P P.derivative le_rfl le_rfl (Or.inl hdeg)
    have hh := congrArg (Polynomial.map e) hab
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C] at hh
    refine ⟨Polynomial.C ((e (P.resultant P.derivative))⁻¹) * a.map e,
      Polynomial.C ((e (P.resultant P.derivative))⁻¹) * b.map e,?_⟩
    rw [Polynomial.derivative_map]
    calc
      _ = Polynomial.C ((e (P.resultant P.derivative))⁻¹) *
          (P.map e * a.map e + P.derivative.map e * b.map e) := by ring
      _ = 1 := by rw [hh,← Polynomial.C_mul,inv_mul_cancel₀ hd,Polynomial.C_1]

theorem generic_fin_polynomial_parameter_nonzero {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℂ) (hP : P ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ r > 0, ∀ z ∈ ball (fun i => (s i : ℂ)) r,
        ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 → MvPolynomial.eval (Fin.cons t z) P ≠ 0 := by
  obtain ⟨E,hE,hn⟩ := generic_polynomial_parameter_nonzero
    (MvPolynomial.finSuccEquiv ℂ n P)
    ((MvPolynomial.finSuccEquiv ℂ n).injective.ne hP)
  refine ⟨E,hE,?_⟩
  intro s hs
  obtain ⟨r,hr,hn⟩ := hn s hs
  refine ⟨r,hr,?_⟩
  intro z hz t ht ht0
  rw [MvPolynomial.eval_eq_eval_mv_eval' z t P,Polynomial.eval_map]
  exact hn z hz t ht ht0

theorem generic_fin_parameter_polynomial_separable {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin (n+1)) ℂ))
    (hP : P ≠ 0) (hres : P.resultant P.derivative ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ r > 0, ∀ z ∈ ball (fun i => (s i : ℂ)) r,
        ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 →
          MvPolynomial.eval (Fin.cons t z) P.leadingCoeff ≠ 0 ∧
          (P.map (MvPolynomial.eval (Fin.cons t z))).Separable := by
  obtain ⟨E₁,hE₁,h₁⟩ := generic_fin_polynomial_parameter_nonzero P.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hP)
  obtain ⟨E₂,hE₂,h₂⟩ := generic_fin_polynomial_parameter_nonzero (P.resultant P.derivative) hres
  refine ⟨E₁ ∪ E₂,measure_union_null hE₁ hE₂,?_⟩
  intro s hs
  have hs₁ : s ∉ E₁ := fun h => hs (Or.inl h)
  have hs₂ : s ∉ E₂ := fun h => hs (Or.inr h)
  obtain ⟨r₁,hr₁,hn₁⟩ := h₁ s hs₁
  obtain ⟨r₂,hr₂,hn₂⟩ := h₂ s hs₂
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,?_⟩
  intro z hz t ht ht0
  have hz₁ := ball_subset_ball (min_le_left r₁ r₂) hz
  have hz₂ := ball_subset_ball (min_le_right r₁ r₂) hz
  have ht₁ := ball_subset_ball (min_le_left r₁ r₂) ht
  have ht₂ := ball_subset_ball (min_le_right r₁ r₂) ht
  have hl := hn₁ z hz₁ t ht₁ ht0
  exact ⟨hl,separable_map_of_leading_resultant_ne_zero P _ hl (hn₂ z hz₂ t ht₂ ht0)⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericAlgebraicBranchRamification2
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory Metric

theorem remove_ramification_scale {n l : ℕ} {s : Fin n → ℝ} {r c : ℝ}
    (hc : 0 < c) (hl : 0 < l)
    (F : (Fin n → ℂ) × ℂ → ℂ)
    (hFa : AnalyticOnNhd ℂ F (ball 0 r ×ˢ ball 0 (1/2)))
    (b : (Fin n → ℝ) × ℝ → ℂ)
    (hF : ∀ x ∈ ball 0 r, ∀ t ∈ Ioo (0 : ℝ) (1/2),
      F (realParameter x,t) = b (s+x,c*t^l)) :
    ∃ ε > 0, ∃ H : (Fin n → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (realParameter s) r ×ˢ ball 0 ε) ∧
      ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) ε,
        H (realParameter x,t) = b (x,t^l) := by
  let a : ℝ := c ^ (l : ℝ)⁻¹
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  have hal : a^l = c := Real.rpow_inv_natCast_pow hc.le hl.ne'
  let T : ((Fin n → ℂ) × ℂ) → ((Fin n → ℂ) × ℂ) :=
    fun p => (p.1-realParameter s,p.2/(a : ℂ))
  have hTa (p : (Fin n → ℂ) × ℂ) : AnalyticAt ℂ T p :=
    (((ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).analyticAt p).sub analyticAt_const).prod
      (((ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).analyticAt p).div_const)
  have hTmem (p : (Fin n → ℂ) × ℂ)
      (hp : p ∈ ball (realParameter s) r ×ˢ ball 0 (a/2)) :
      T p ∈ ball 0 r ×ˢ ball 0 (1/2) := by
    constructor
    · simpa only [T,mem_ball,dist_eq_norm,sub_zero] using hp.1
    · simp only [T,mem_ball,dist_zero_right,norm_div,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos ha]
      apply (div_lt_iff₀ ha).mpr
      have ht := hp.2
      simp only [mem_ball,dist_zero_right] at ht
      linarith
  refine ⟨a/2,by positivity,F ∘ T,?_,?_⟩
  · intro p hp
    exact (hFa _ (hTmem p hp)).comp (hTa p)
  · intro x hx t ht
    have hx' : x-s ∈ ball 0 r := by
      simpa only [mem_ball,dist_eq_norm,sub_zero] using hx
    have ht' : t/a ∈ Ioo (0 : ℝ) (1/2) := by
      refine ⟨div_pos ht.1 ha,(div_lt_iff₀ ha).mpr ?_⟩
      linarith [ht.2]
    have he : T (realParameter x,(t : ℂ)) = (realParameter (x-s),((t/a : ℝ) : ℂ)) := by
      apply Prod.ext
      · ext i
        simp only [T,Pi.sub_apply,realParameter,Complex.ofReal_sub]
      · simp only [T,Complex.ofReal_div]
    change F (T (realParameter x,(t : ℂ))) = _
    rw [he,hF (x-s) hx' (t/a) ht']
    congr 1
    apply Prod.ext
    · abel_nf
    · rw [div_pow,hal]
      exact mul_div_cancel₀ (t^l) hc.ne'

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AlgebraicGraphPolynomial
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem real_graph_empty_interior {ι : Type*} [Fintype ι]
    (B : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) :
    interior {x : Option ι → ℝ | (fun i => x (some i)) ∈ B ∧
      x none = f (fun i => x (some i))} = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxS := interior_subset hx
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let y : Option ι → ℝ := x + Pi.single none (r/2)
  have hdist : dist y x < r := by
    rw [dist_eq_norm]
    change ‖x + Pi.single none (r/2) - x‖ < r
    rw [add_sub_cancel_left,Pi.norm_single]
    rw [Real.norm_eq_abs,abs_of_pos (by positivity : 0 < r/2)]
    linarith
  have hyS := hball hdist
  have hyeq := hyS.2
  change y none = _ at hyeq
  simp only [y,Pi.add_apply,Pi.single_eq_same,Pi.single_eq_of_ne (Option.some_ne_none _),add_zero] at hyeq
  linarith [hxS.2,hyeq]

theorem semialgebraic_graph_polynomial {ι : Type*} [Fintype ι]
    (B : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hgraph : PolynomialSignSet (id : (Option ι → ℝ) → (Option ι → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ P : MvPolynomial (Option ι) ℝ, P ≠ 0 ∧
      ∀ s ∈ B, MvPolynomial.eval (fun a => a.elim (f s) s) P = 0 := by
  obtain ⟨P,hP,hzero⟩ := hgraph.polynomial_of_empty_interior continuous_id
    (real_graph_empty_interior B f)
  exact ⟨P,hP,fun s hs => hzero _ ⟨hs,rfl⟩⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SquarefreeRelationOffDenominator
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Polynomial
open scoped nonZeroDivisors

theorem polynomial_clear_denominators
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p : K[X]) :
    ∃ a : R, a ≠ 0 ∧ ∃ q : R[X],
      q.map (algebraMap R K) = C (algebraMap R K a) * p := by
  obtain ⟨a,ha,hq⟩ := IsLocalization.integerNormalization_spec R⁰ p
  refine ⟨a,mem_nonZeroDivisors_iff_ne_zero.mp ha,
    IsLocalization.integerNormalization R⁰ p,?_⟩
  rw [hq,← algebraMap_smul K a p,Polynomial.smul_eq_C_mul]

theorem squarefree_relation_off_denominator
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K]
    (p : R[X]) (hp : p ≠ 0) :
    ∃ q : R[X], q ≠ 0 ∧ (q.map (algebraMap R K)).Separable ∧
      ∃ D : R, D ≠ 0 ∧
        ∀ {F : Type*} [Field F] (e : R →+* F), e D ≠ 0 →
          ∀ z : F, p.eval₂ e z = 0 ↔ q.eval₂ e z = 0 := by
  classical
  let e := algebraMap R K
  have hei : Function.Injective e := IsFractionRing.injective R K
  have hmap : Function.Injective (Polynomial.map e) := Polynomial.map_injective e hei
  have hp' : p.map e ≠ 0 := fun hz => hp (hmap (by simpa only [Polynomial.map_zero] using hz))
  obtain ⟨v,m,hv,hvp,hpv⟩ := exists_squarefree_dvd_pow_of_ne_zero hp'
  have hv0 : v ≠ 0 := by rintro rfl; exact hp' (by simpa using hvp)
  have hvsep : v.Separable := PerfectField.separable_iff_squarefree.mpr hv
  obtain ⟨w,hw⟩ := hvp
  obtain ⟨j,hj⟩ := hpv
  obtain ⟨a,ha,q,hq⟩ := polynomial_clear_denominators (R := R) v
  obtain ⟨b,hb,W,hW⟩ := polynomial_clear_denominators (R := R) w
  obtain ⟨c,hc,J,hJ⟩ := polynomial_clear_denominators (R := R) j
  have haK : e a ≠ 0 := by simpa only [map_zero] using hei.ne_iff.mpr ha
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz,Polynomial.map_zero] at hq
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr haK) hv0) hq.symm
  have hqs : (q.map e).Separable := by
    rw [hq]
    exact Polynomial.Separable.unit_mul (IsUnit.map C (isUnit_iff_ne_zero.mpr haK)) hvsep
  have h₁ : q*W = C (a*b)*p := by
    apply hmap
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul]
    rw [hq,hW,hw]
    dsimp only [e]
    ring
  have h₂ : C c*q^m = C (a^m)*p*J := by
    apply hmap
    simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,map_pow]
    rw [hq,hJ,mul_pow,← Polynomial.C_pow,hj]
    dsimp only [e]
    ring
  refine ⟨q,hq0,hqs,a*b*c,mul_ne_zero (mul_ne_zero ha hb) hc,?_⟩
  intro F _ f hf z
  have hab : f (a*b) ≠ 0 := fun hz => hf (by simp only [map_mul,hz,zero_mul])
  have hc' : f c ≠ 0 := fun hz => hf (by simp only [map_mul,hz,mul_zero])
  constructor
  · intro hz
    have he := congrArg (Polynomial.eval₂ f z) h₂
    simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,hz,mul_zero,zero_mul] at he
    have hpw : (q.eval₂ f z)^m = 0 := (mul_eq_zero.mp he).resolve_left hc'
    by_contra hn
    exact pow_ne_zero m hn hpw
  · intro hz
    have he := congrArg (Polynomial.eval₂ f z) h₁
    simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,hz,zero_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hab

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RealPolynomialAnalyticRoot
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Polynomial

theorem polynomial_gcd_specialization_data
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p q : R[X]) :
    ∃ a b c : R, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      ∃ A B C' U V : R[X],
        C a*p = A*B ∧ C b*q = A*C' ∧ C c*A = p*U+q*V := by
  classical
  let e := algebraMap R K
  have hi : Function.Injective (Polynomial.map e) :=
    Polynomial.map_injective e (IsFractionRing.injective R K)
  let g := EuclideanDomain.gcd (p.map e) (q.map e)
  obtain ⟨w,hw⟩ := EuclideanDomain.gcd_dvd_left (p.map e) (q.map e)
  obtain ⟨j,hj⟩ := EuclideanDomain.gcd_dvd_right (p.map e) (q.map e)
  change p.map e = g*w at hw
  change q.map e = g*j at hj
  obtain ⟨a,ha,A,hA⟩ := polynomial_clear_denominators (R := R) g
  obtain ⟨b,hb,B,hB⟩ := polynomial_clear_denominators (R := R) w
  obtain ⟨c,hc,C',hC⟩ := polynomial_clear_denominators (R := R) j
  obtain ⟨u,hu,U,hU⟩ := polynomial_clear_denominators (R := R)
    (EuclideanDomain.gcdA (p.map e) (q.map e))
  obtain ⟨v,hv,V,hV⟩ := polynomial_clear_denominators (R := R)
    (EuclideanDomain.gcdB (p.map e) (q.map e))
  refine ⟨a*b,a*c,u*v,mul_ne_zero ha hb,mul_ne_zero ha hc,mul_ne_zero hu hv,
    A,B,C',C (a*v)*U,C (a*u)*V,?_,?_,?_⟩
  · apply hi
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul]
    rw [hA,hB,hw]
    dsimp only [e]
    ring
  · apply hi
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul]
    rw [hA,hC,hj]
    dsimp only [e]
    ring
  · apply hi
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul,Polynomial.map_add]
    rw [hA,hU,hV]
    dsimp only [g,e]
    rw [EuclideanDomain.gcd_eq_gcd_ab]
    ring

end

theorem real_analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℝ f a)
    (i : E ≃L[ℝ] F) (hi : HasFDerivAt f (i : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℝ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℝ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm
      (i : E →L[ℝ] F) := by
    apply (continuousMultilinearCurryFin1 ℝ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

theorem real_analytic_implicit_scalar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E × ℝ → ℝ} {a : E} {b : ℝ}
    (hF : AnalyticAt ℝ F (a, b)) (hzero : F (a, b) = 0)
    (L : E × ℝ →L[ℝ] ℝ) (hL : HasFDerivAt F L (a, b))
    (hsimple : L (0, 1) ≠ 0) :
    ∃ g : E → ℝ, AnalyticAt ℝ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, F (y, g y) = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), F p = 0 → p.2 = g p.1) := by
  let G : E × ℝ → E × ℝ := fun p => (p.1, F p)
  have hG : AnalyticAt ℝ G (a, b) :=
    ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt (a, b)).prod hF
  have hdG : HasFDerivAt G (real_triangularDifferentialEquiv L hsimple : _ →L[ℝ] _) (a, b) :=
    hasFDerivAt_fst.prodMk hL
  obtain ⟨e, he, hmem, hia⟩ := real_analytic_local_inverse hG
    (real_triangularDifferentialEquiv L hsimple) hdG
  have hGab : G (a, b) = (a, 0) := by simp [G, hzero]
  rw [hGab] at hia
  let g : E → ℝ := fun y => (e.symm (y, 0)).2
  have hiac : AnalyticAt ℝ (fun y : E => e.symm (y, 0)) a :=
    hia.comp (f := fun y : E => (y, 0))
      ((ContinuousLinearMap.inl ℝ E ℝ).analyticAt a)
  have hg : AnalyticAt ℝ g a :=
    ((ContinuousLinearMap.snd ℝ E ℝ).analyticAt _).comp hiac
  have hsource : e.symm (a, 0) = (a, b) := by
    rw [← hGab, ← he]
    exact e.left_inv hmem
  refine ⟨g, hg, congrArg Prod.snd hsource, ?_, ?_⟩
  · have hright := e.eventually_right_inverse' hmem
    rw [he, hGab] at hright
    have ht : Tendsto (fun y : E => (y, (0 : ℝ))) (𝓝 a) (𝓝 (a, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    filter_upwards [ht.eventually hright] with y hy
    have hfst : (e.symm (y, 0)).1 = y := congrArg Prod.fst hy
    have hsnd : F (e.symm (y, 0)) = 0 := congrArg Prod.snd hy
    change F (y, (e.symm (y, 0)).2) = 0
    have hpair : (y, (e.symm (y, 0)).2) = e.symm (y, 0) :=
      Prod.ext hfst.symm rfl
    rw [hpair]
    exact hsnd
  · have hleft := e.eventually_left_inverse hmem
    rw [he] at hleft
    filter_upwards [hleft] with p hp hz
    have hGp : G p = (p.1, 0) := by simp [G, hz]
    rw [hGp] at hp
    exact (congrArg Prod.snd hp).symm

theorem real_polynomial_analytic_root {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℝ)) (a : Fin d → ℝ) (b : ℝ)
    (hroot : Polynomial.eval₂ (MvPolynomial.eval a) b P = 0)
    (hsimple : Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative ≠ 0) :
    ∃ g : (Fin d → ℝ) → ℝ, AnalyticAt ℝ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, Polynomial.eval₂ (MvPolynomial.eval y) (g y) P = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P = 0 →
        p.2 = g p.1) := by
  let F : ((Fin d → ℝ) × ℝ) → ℝ := fun p =>
    Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P
  have hF : AnalyticAt ℝ F (a, b) := by
    have hpoly : ∀ j : ℕ, AnalyticAt ℝ
        (fun p : ((Fin d → ℝ) × ℝ) => MvPolynomial.eval p.1 (P.coeff j)) (a, b) := by
      intro j
      exact (AnalyticOnNhd.eval_mvPolynomial (P.coeff j) _ (Set.mem_univ _)).comp
        ((ContinuousLinearMap.fst ℝ (Fin d → ℝ) ℝ).analyticAt _)
    simp only [F, Polynomial.eval₂_eq_sum_range]
    exact
      Finset.analyticAt_fun_sum (Finset.range (P.natDegree + 1)) (fun j _ =>
        (hpoly j).mul (((ContinuousLinearMap.snd ℝ (Fin d → ℝ) ℝ).analyticAt _).pow j))
  let L := fderiv ℝ F (a,b)
  have hL : HasFDerivAt F L (a,b) := hF.differentiableAt.hasFDerivAt
  have hv : L (0,1) = Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative := by
    have h1 : HasDerivAt (fun z => F (a,z)) (L (0,1)) b :=
      hL.comp_hasDerivAt b ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))
    have h2 := (P.map (MvPolynomial.eval a)).hasDerivAt b
    simp only [Polynomial.derivative_map, Polynomial.eval_map] at h2
    exact h1.unique h2
  exact real_analytic_implicit_scalar hF hroot L hL (hv ▸ hsimple)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RegularSimpleSheet
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Polynomial Set Filter Topology

lemma continuousAt_real_parameter_eval {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hg : ContinuousAt g x) :
    ContinuousAt (fun y => P.eval₂ (MvPolynomial.eval y) (g y)) x := by
  simp only [Polynomial.eval₂_eq_sum_range]
  exact tendsto_finsetSum _ (fun j _ =>
    (MvPolynomial.continuous_eval (P.coeff j)).continuousAt.mul (hg.pow j))

theorem polynomial_zero_persists_on_simple_sheet {n : ℕ}
    (P Q : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), ContinuousAt g x →
        (∀ᶠ y in 𝓝 x, P.eval₂ (MvPolynomial.eval y) (g y) = 0) →
        P.derivative.eval₂ (MvPolynomial.eval x) (g x) ≠ 0 →
        MvPolynomial.eval x D ≠ 0 → Q.eval₂ (MvPolynomial.eval x) (g x) = 0 →
        ∀ᶠ y in 𝓝 x, Q.eval₂ (MvPolynomial.eval y) (g y) = 0 := by
  obtain ⟨a,b,c,ha,hb,hc,A,B,C',U,V,h₁,h₂,h₃⟩ :=
    polynomial_gcd_specialization_data (K := FractionRing (MvPolynomial (Fin n) ℝ)) P Q
  refine ⟨a*b*c,mul_ne_zero (mul_ne_zero ha hb) hc,?_⟩
  intro g x hg hP hs hD hQ
  have ha' : MvPolynomial.eval x a ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,zero_mul]
  have hb' : MvPolynomial.eval x b ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hc' : MvPolynomial.eval x c ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero]
  have hPx : P.eval₂ (MvPolynomial.eval x) (g x) = 0 := hP.self_of_nhds
  have hAx : A.eval₂ (MvPolynomial.eval x) (g x) = 0 := by
    have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval x) (g x)) h₃
    simp only [eval₂_mul,eval₂_C,eval₂_add,hPx,hQ,zero_mul,zero_add] at he
    exact (mul_eq_zero.mp he).resolve_left hc'
  have hBx : B.eval₂ (MvPolynomial.eval x) (g x) ≠ 0 := by
    intro hz
    have hd := congrArg Polynomial.derivative h₁
    have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval x) (g x)) hd
    simp only [derivative_mul,derivative_C,zero_mul,zero_add,eval₂_mul,eval₂_C,
      eval₂_add,hAx,hz,zero_mul,mul_zero,zero_add] at he
    exact hs ((mul_eq_zero.mp he).resolve_left ha')
  have hBn := (continuousAt_real_parameter_eval B hg).eventually_ne hBx
  have hbn := (MvPolynomial.continuous_eval b).continuousAt.eventually_ne hb'
  filter_upwards [hP,hBn,hbn] with y hPy hBy hby
  have hAy : A.eval₂ (MvPolynomial.eval y) (g y) = 0 := by
    have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval y) (g y)) h₁
    simp only [eval₂_mul,eval₂_C,hPy,mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hBy
  have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval y) (g y)) h₂
  simp only [eval₂_mul,eval₂_C,hAy,zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left hby

theorem PolynomialSignSet.regular_on_simple_sheet {n : ℕ}
    {S : Set (Option (Fin n) → ℝ)} (hS : PolynomialSignSet id S)
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), ContinuousAt g x →
        (∀ᶠ y in 𝓝 x, P.eval₂ (MvPolynomial.eval y) (g y) = 0) →
        P.derivative.eval₂ (MvPolynomial.eval x) (g x) ≠ 0 →
        MvPolynomial.eval x D ≠ 0 →
        (∀ᶠ y in 𝓝 x, (fun o => Option.elim o (g y) y) ∈ S) ∨
        (∀ᶠ y in 𝓝 x, (fun o => Option.elim o (g y) y) ∉ S) := by
  induction hS with
  | zero q =>
    let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) q
    obtain ⟨D,hD,hzero⟩ := polynomial_zero_persists_on_simple_sheet P Q
    refine ⟨D,hD,?_⟩
    intro g x hg hP hs hDx
    by_cases hz : Q.eval₂ (MvPolynomial.eval x) (g x) = 0
    · left
      simpa only [mem_ofPred,id_eq,MvPolynomial.optionEquivLeft_elim_eval,eval_map,Q] using
        hzero g x hg hP hs hDx hz
    · right
      simpa only [mem_ofPred,id_eq,MvPolynomial.optionEquivLeft_elim_eval,eval_map,Q] using
        (continuousAt_real_parameter_eval Q hg).eventually_ne hz
  | positive q =>
    let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) q
    obtain ⟨D,hD,hzero⟩ := polynomial_zero_persists_on_simple_sheet P Q
    refine ⟨D,hD,?_⟩
    intro g x hg hP hs hDx
    by_cases hz : Q.eval₂ (MvPolynomial.eval x) (g x) = 0
    · right
      filter_upwards [hzero g x hg hP hs hDx hz] with y hy
      change ¬ 0 < MvPolynomial.eval (fun o => Option.elim o (g y) y) q
      rw [MvPolynomial.optionEquivLeft_elim_eval,eval_map]
      change ¬ 0 < Q.eval₂ (MvPolynomial.eval y) (g y)
      simp only [hy,lt_self_iff_false,not_false_eq_true]
    · rcases lt_or_gt_of_ne hz with hneg | hpos
      · right
        filter_upwards [(continuousAt_real_parameter_eval Q hg).eventually_lt_const hneg] with y hy
        change ¬ 0 < MvPolynomial.eval (fun o => Option.elim o (g y) y) q
        rw [MvPolynomial.optionEquivLeft_elim_eval,eval_map]
        exact not_lt_of_ge hy.le
      · left
        simpa only [mem_ofPred,id_eq,MvPolynomial.optionEquivLeft_elim_eval,eval_map,Q] using
          (continuousAt_real_parameter_eval Q hg).eventually_const_lt hpos
  | @compl S hS ih =>
    obtain ⟨D,hD,hreg⟩ := ih
    refine ⟨D,hD,?_⟩
    intro g x hg hP hs hDx
    simpa only [mem_compl_iff,not_not] using (hreg g x hg hP hs hDx).symm
  | @union S T hS hT ihS ihT =>
    obtain ⟨D,hD,hregD⟩ := ihS
    obtain ⟨E,hE,hregE⟩ := ihT
    refine ⟨D*E,mul_ne_zero hD hE,?_⟩
    intro g x hg hP hs hDE
    have hD' : MvPolynomial.eval x D ≠ 0 := fun hz => hDE (by simp only [map_mul,hz,zero_mul])
    have hE' : MvPolynomial.eval x E ≠ 0 := fun hz => hDE (by simp only [map_mul,hz,mul_zero])
    rcases hregD g x hg hP hs hD' with h | h
    · exact Or.inl (h.mono fun y hy => Or.inl hy)
    rcases hregE g x hg hP hs hE' with k | k
    · exact Or.inl (k.mono fun y hy => Or.inr hy)
    · right
      filter_upwards [h,k] with y hy ky
      exact fun h => h.elim hy ky

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericAlgebraicRamificationUniform
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Polynomial Set Filter Topology

theorem semialgebraic_function_analytic_off_polynomial {n : ℕ}
    (B : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin n) → ℝ |
        (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ a ∈ B, MvPolynomial.eval a D ≠ 0 → AnalyticAt ℝ f a := by
  obtain ⟨p,hp,hpr⟩ := semialgebraic_graph_polynomial B f hgraph
  let P := MvPolynomial.optionEquivLeft ℝ (Fin n) p
  have hP : P ≠ 0 := (MvPolynomial.optionEquivLeft ℝ (Fin n)).injective.ne hp
  obtain ⟨q,hq,hqs,D₀,hD₀,hqe⟩ :=
    squarefree_relation_off_denominator (K := FractionRing (MvPolynomial (Fin n) ℝ)) P hP
  have hres : q.resultant q.derivative ≠ 0 :=
    resultant_derivative_ne_zero_of_generic_separable q hqs
  obtain ⟨D₁,hD₁,hreg⟩ := hgraph.regular_on_simple_sheet q
  refine ⟨D₀*D₁*q.leadingCoeff*(q.resultant q.derivative),
    mul_ne_zero (mul_ne_zero (mul_ne_zero hD₀ hD₁)
      (Polynomial.leadingCoeff_ne_zero.mpr hq)) hres,?_⟩
  intro a ha hD
  have hD₀a : MvPolynomial.eval a D₀ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,zero_mul]
  have hD₁a : MvPolynomial.eval a D₁ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hl : MvPolynomial.eval a q.leadingCoeff ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hd : MvPolynomial.eval a (q.resultant q.derivative) ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero]
  have hpr' : P.eval₂ (MvPolynomial.eval a) (f a) = 0 := by
    simpa only [MvPolynomial.optionEquivLeft_elim_eval,eval_map,P] using hpr a ha
  have hqr : q.eval₂ (MvPolynomial.eval a) (f a) = 0 :=
    (hqe (MvPolynomial.eval a) hD₀a (f a)).mp hpr'
  have hsep := separable_map_of_leading_resultant_ne_zero q (MvPolynomial.eval a) hl hd
  have hder : q.derivative.eval₂ (MvPolynomial.eval a) (f a) ≠ 0 := by
    have hh := Polynomial.Separable.eval₂_derivative_ne_zero (RingHom.id ℝ) hsep
      (x := f a) (by simpa only [Polynomial.eval₂_id,Polynomial.eval_map] using hqr)
    simpa only [Polynomial.eval₂_id,Polynomial.derivative_map,Polynomial.eval_map] using hh
  obtain ⟨g,hga,hgf,hgr,_⟩ := real_polynomial_analytic_root q a (f a) hqr hder
  have hder' : q.derivative.eval₂ (MvPolynomial.eval a) (g a) ≠ 0 := by
    simpa only [hgf] using hder
  rcases hreg g a hga.continuousAt hgr hder' hD₁a with hyes | hno
  · have he : g =ᶠ[𝓝 a] f := by
      filter_upwards [hyes] with y hy
      exact hy.2
    exact hga.congr he
  · have hn := hno.self_of_nhds
    exact (hn ⟨ha,hgf⟩).elim

end

open Set Filter Topology MeasureTheory Metric
theorem generic_algebraic_ramification_uniform {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin (n+1)) ℂ))
    (hP : P ≠ 0) (hres : P.resultant P.derivative ≠ 0)
 :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∀ {B : Set (Fin n → ℝ)}, IsOpen B → s ∈ B →
      ∀ {ε : ℝ}, 0 < ε → ∀ (b : (Fin n → ℝ) × ℝ → ℂ),
      ContinuousOn b (B ×ˢ Ioo 0 ε) →
      (∀ p ∈ B ×ˢ Ioo 0 ε,
        Polynomial.eval₂ (MvPolynomial.eval (Fin.cons (p.2 : ℂ) (realParameter p.1))) (b p) P = 0) →
      ∀ {M : ℝ}, (∀ p ∈ B ×ˢ Ioo 0 ε, ‖b p‖ ≤ M) →
      ∃ r > 0, ∃ c > 0, ∃ l : ℕ, 0 < l ∧
        ∃ F : (Fin n → ℂ) × ℂ → ℂ,
          ball s r ⊆ B ∧
          AnalyticOnNhd ℂ F (ball 0 r ×ˢ ball 0 (1/2)) ∧
          ∀ x ∈ ball 0 r, ∀ t ∈ Ioo (0 : ℝ) (1/2),
            F (realParameter x,t) = b (s+x,c*t^l) := by
  obtain ⟨E,hE,hg⟩ := generic_fin_parameter_polynomial_separable P hP hres
  refine ⟨E,hE,?_⟩
  intro s hsE B hB hs ε hε b hb hbr M hbound
  obtain ⟨δ,hδ,hg⟩ := hg s hsE
  obtain ⟨ρ,hρ,hρB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hs)
  let r := min δ ρ
  let c := min δ ε / 2
  have hr : 0 < r := lt_min hδ hρ
  have hc : 0 < c := by dsimp [c]; positivity
  have hcδ : c ≤ δ := by dsimp [c]; linarith [min_le_left δ ε,lt_min hδ hε]
  have hcε : c ≤ ε := by dsimp [c]; linarith [min_le_right δ ε,lt_min hδ hε]
  have hsr : ball s r ⊆ B := (ball_subset_ball (min_le_right δ ρ)).trans hρB
  have hreal (x : Fin n → ℝ) (hx : x ∈ ball 0 r) : s+x ∈ B := by
    apply hsr
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx
  have hcomplex (x : Fin n → ℂ) (hx : x ∈ ball 0 r) :
      realParameter s + x ∈ ball (realParameter s) δ := by
    have hx' := ball_subset_ball (min_le_left δ ρ) hx
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx'
  let A : (Fin n → ℂ) × ℂ → (Fin (n+1) → ℂ) :=
    fun p => Fin.cons ((c : ℂ)*p.2) (realParameter s+p.1)
  have hA : AnalyticOnNhd ℂ A (ball 0 r ×ˢ ball 0 1) := by
    intro p _
    apply analyticAt_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact analyticAt_const.mul ((ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).analyticAt p)
    · exact analyticAt_const.add (((ContinuousLinearMap.proj j :
        (Fin n → ℂ) →L[ℂ] ℂ).analyticAt p.1).comp
          ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).analyticAt p))
  have hroot (p : (Fin n → ℂ) × ℂ)
      (hp : p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1}) :
      MvPolynomial.eval (A p) P.leadingCoeff ≠ 0 ∧
        (P.map (MvPolynomial.eval (A p))).Separable := by
    apply hg (realParameter s+p.1) (hcomplex p.1 hp.1) ((c : ℂ)*p.2)
    · simp only [mem_ball,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc]
      exact (mul_lt_mul_of_pos_left hp.2.2 hc).trans_le (by simpa using hcδ)
    · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') hp.2.1
  let β : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) := fun p => (s+p.1,c*p.2)
  have hβ : Continuous β := (continuous_const.add continuous_fst).prodMk
    (continuous_const.mul continuous_snd)
  have hβmem (p : (Fin n → ℝ) × ℝ) (hp : p ∈ ball 0 r ×ˢ Ioo 0 1) :
      β p ∈ B ×ˢ Ioo 0 ε :=
    ⟨hreal p.1 hp.1,mul_pos hc hp.2.1,
      (mul_lt_mul_of_pos_left hp.2.2 hc).trans_le (by simpa using hcε)⟩
  have hb' : ContinuousOn (b ∘ β) (ball 0 r ×ˢ Ioo 0 1) := hb.comp hβ.continuousOn hβmem
  have hbr' : ∀ (p : (Fin n → ℝ) × ℝ), p ∈ ball 0 r ×ˢ Ioo 0 1 →
      Polynomial.eval₂ (MvPolynomial.eval (A (realParameter p.1,p.2))) ((b ∘ β) p) P = 0 := by
    intro p hp
    have hadd : realParameter (s+p.1) = realParameter s+realParameter p.1 := by
      ext i
      simp only [realParameter,Pi.add_apply,Complex.ofReal_add]
    simpa only [A,β,Function.comp_apply,Complex.ofReal_mul,hadd] using hbr (β p) (hβmem p hp)
  obtain ⟨l,hl,F,hFa,hF⟩ := bounded_algebraic_branch_ramification P A hr hA
    (fun p hp => (hroot p hp).1) (fun p hp => (hroot p hp).2)
    (b ∘ β) hb' hbr' (fun p hp => hbound (β p) (hβmem p hp))
  exact ⟨r,hr,c,hc,l,hl,F,hsr,hFa,hF⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericRealParameterPolynomial
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Polynomial Set Filter Topology Metric MeasureTheory

lemma complexify_mv_eval {n : ℕ} (D : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (realParameter x) (MvPolynomial.map Complex.ofRealHom D) =
      (MvPolynomial.eval x D : ℂ) := by
  rw [MvPolynomial.eval_map]
  change _ = Complex.ofRealHom (MvPolynomial.eval x D)
  rw [MvPolynomial.eval₂_comp]
  rfl

lemma complexify_polynomial_eval {n : ℕ} (q : Polynomial (MvPolynomial (Fin n) ℝ))
    (x : Fin n → ℝ) (y : ℝ) :
    (q.map (MvPolynomial.map Complex.ofRealHom)).eval₂ (MvPolynomial.eval (realParameter x))
      (y : ℂ) = ((q.eval₂ (MvPolynomial.eval x) y : ℝ) : ℂ) := by
  change _ = Complex.ofRealHom (q.eval₂ (MvPolynomial.eval x) y)
  rw [Polynomial.eval₂_map,Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext (fun D => complexify_mv_eval D x)

theorem semialgebraic_function_algebraic_data {n : ℕ}
    (B : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin n) → ℝ |
        (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
        P.resultant P.derivative ≠ 0 ∧
        ∀ a ∈ B, MvPolynomial.eval a D ≠ 0 → AnalyticAt ℝ f a ∧
          P.eval₂ (MvPolynomial.eval (realParameter a)) (f a : ℂ) = 0 := by
  obtain ⟨D₁,hD₁,hfa⟩ := semialgebraic_function_analytic_off_polynomial B f hgraph
  obtain ⟨p,hp,hpr⟩ := semialgebraic_graph_polynomial B f hgraph
  let p' := MvPolynomial.optionEquivLeft ℝ (Fin n) p
  have hp' : p' ≠ 0 := (MvPolynomial.optionEquivLeft ℝ (Fin n)).injective.ne hp
  obtain ⟨q,hq,hqs,D₀,hD₀,hqe⟩ :=
    squarefree_relation_off_denominator (K := FractionRing (MvPolynomial (Fin n) ℝ)) p' hp'
  let e : MvPolynomial (Fin n) ℝ →+* MvPolynomial (Fin n) ℂ :=
    MvPolynomial.map Complex.ofRealHom
  have hei : Function.Injective e := MvPolynomial.map_injective _ Complex.ofReal_injective
  have hQ : q.map e ≠ 0 := by
    simpa only [Polynomial.map_zero] using (Polynomial.map_injective e hei).ne hq
  have hres : (q.map e).resultant (q.map e).derivative ≠ 0 := by
    rw [Polynomial.derivative_map,
      Polynomial.natDegree_map_eq_of_injective hei,
      Polynomial.natDegree_map_eq_of_injective hei,Polynomial.resultant_map_map]
    exact hei.ne (resultant_derivative_ne_zero_of_generic_separable q hqs)
  refine ⟨D₀*D₁,mul_ne_zero hD₀ hD₁,q.map e,hQ,hres,?_⟩
  intro a ha hD
  have hD₀a : MvPolynomial.eval a D₀ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,zero_mul]
  have hD₁a : MvPolynomial.eval a D₁ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero]
  refine ⟨hfa a ha hD₁a,?_⟩
  have hpr' : p'.eval₂ (MvPolynomial.eval a) (f a) = 0 := by
    simpa only [MvPolynomial.optionEquivLeft_elim_eval,eval_map,p'] using hpr a ha
  have hqr := (hqe (MvPolynomial.eval a) hD₀a (f a)).mp hpr'
  change (q.map (MvPolynomial.map Complex.ofRealHom)).eval₂ _ _ = 0
  rw [complexify_polynomial_eval,hqr,Complex.ofReal_zero]

lemma realParameter_dist {n : ℕ} (x y : Fin n → ℝ) :
    dist (realParameter x) (realParameter y) = dist x y := by
  rw [dist_eq_norm,dist_eq_norm]
  have hh : realParameter x-realParameter y = realParameter (x-y) := by
    ext i
    exact (Complex.ofReal_sub _ _).symm
  rw [hh,norm_realParameter]

theorem generic_real_parameter_polynomial_nonzero {n : ℕ}
    (D : MvPolynomial (Fin (n+1)) ℝ) (hD : D ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ r > 0, ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) r,
        MvPolynomial.eval (Fin.cons t x) D ≠ 0 := by
  have hi := MvPolynomial.map_injective (σ := Fin (n+1)) Complex.ofRealHom
    Complex.ofReal_injective
  obtain ⟨E,hE,hn⟩ := generic_fin_polynomial_parameter_nonzero
    (MvPolynomial.map Complex.ofRealHom D) (hi.ne hD)
  refine ⟨E,hE,?_⟩
  intro s hs
  obtain ⟨r,hr,hn⟩ := hn s hs
  refine ⟨r,hr,?_⟩
  intro x hx t ht
  have hx' : realParameter x ∈ ball (realParameter s) r := by
    simpa only [mem_ball,realParameter_dist] using hx
  have ht' : (t : ℂ) ∈ ball 0 r := by
    simpa only [mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1] using ht.2
  have hh := hn (realParameter x) hx' (t : ℂ) ht' (Complex.ofReal_ne_zero.mpr ht.1.ne')
  have he : Fin.cons (t : ℂ) (realParameter x) = realParameter (Fin.cons t x) := by
    ext i
    refine Fin.cases rfl (fun _ => rfl) i
  rw [he,complexify_mv_eval] at hh
  exact fun hz => hh (by rw [hz,Complex.ofReal_zero])

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicRamificationParametersComplex
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory

theorem semialgebraic_ramification_with_parameters_complex {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : (Fin (n+1) → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b (fun i => x (some i))})
    {M : ℝ} (hbound : ∀ x : Fin (n+1) → ℝ, Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b x‖ ≤ M) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ r > 0, ∃ l : ℕ, 0 < l ∧ ∃ η > 0,
        ∃ F : (Fin n → ℂ) × ℂ → ℂ,
          ball s r ⊆ B ∧
          AnalyticOnNhd ℂ F (ball (realParameter s) r ×ˢ ball 0 η) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η,
            F (realParameter x,t) = (b (Fin.cons (t^l) x) : ℂ) := by
  let T : Set (Fin (n+1) → ℝ) := {x | Fin.tail x ∈ B ∧ x 0 ∈ Ioo 0 ε}
  obtain ⟨D,hD,P,hP,hres,hdata⟩ := semialgebraic_function_algebraic_data T b hgraph
  obtain ⟨E₀,hE₀,hDgood⟩ := generic_real_parameter_polynomial_nonzero D hD
  obtain ⟨E₁,hE₁,hgood⟩ := generic_algebraic_ramification_uniform P hP hres
  refine ⟨(E₀ ∪ E₁) ∩ B,inter_subset_right,
    measure_mono_null inter_subset_left (measure_union_null hE₀ hE₁),?_⟩
  intro s hs hsE
  have hs₀ : s ∉ E₀ := fun h => hsE ⟨Or.inl h,hs⟩
  have hs₁ : s ∉ E₁ := fun h => hsE ⟨Or.inr h,hs⟩
  obtain ⟨δ,hδ,hDgood⟩ := hDgood s hs₀
  obtain ⟨ρ,hρ,hρB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hs)
  let r := min δ ρ
  let τ := min δ ε
  have hr : 0 < r := lt_min hδ hρ
  have hτ : 0 < τ := lt_min hδ hε
  have hrB : ball s r ⊆ B := (ball_subset_ball (min_le_right δ ρ)).trans hρB
  have hsub : ball s r ×ˢ Ioo 0 τ ⊆ B ×ˢ Ioo 0 ε := by
    rintro p ⟨hx,ht⟩
    exact ⟨hrB hx,ht.1,ht.2.trans_le (min_le_right δ ε)⟩
  have hDne (p : (Fin n → ℝ) × ℝ) (hp : p ∈ ball s r ×ˢ Ioo 0 τ) :
      MvPolynomial.eval (Fin.cons p.2 p.1) D ≠ 0 :=
    hDgood p.1 (ball_subset_ball (min_le_left δ ρ) hp.1) p.2
      ⟨hp.2.1,hp.2.2.trans_le (min_le_left δ ε)⟩
  let c : (Fin n → ℝ) × ℝ → (Fin (n+1) → ℝ) := fun p => Fin.cons p.2 p.1
  have hc : Continuous c := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_snd
    · exact (continuous_apply j).comp continuous_fst
  let β : (Fin n → ℝ) × ℝ → ℂ := fun p => (b (c p) : ℂ)
  have hT (p : (Fin n → ℝ) × ℝ) (hp : p ∈ ball s r ×ˢ Ioo 0 τ) : c p ∈ T := by
    exact hsub hp
  have hβ : ContinuousOn β (ball s r ×ˢ Ioo 0 τ) := by
    intro p hp
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((hdata (c p) (hT p hp) (hDne p hp)).1.continuousAt.comp hc.continuousAt)).continuousWithinAt
  have hroot (p : (Fin n → ℝ) × ℝ) (hp : p ∈ ball s r ×ˢ Ioo 0 τ) :
      P.eval₂ (MvPolynomial.eval (Fin.cons (p.2 : ℂ) (realParameter p.1))) (β p) = 0 := by
    have hh := (hdata (c p) (hT p hp) (hDne p hp)).2
    have he : realParameter (c p) = Fin.cons (p.2 : ℂ) (realParameter p.1) := by
      ext i
      refine Fin.cases rfl (fun _ => rfl) i
    simpa only [he,β] using hh
  have hβbound (p : (Fin n → ℝ) × ℝ) (hp : p ∈ ball s r ×ˢ Ioo 0 τ) : ‖β p‖ ≤ M := by
    simpa only [β,Complex.norm_real] using hbound (c p) (hT p hp).1 (hT p hp).2
  obtain ⟨r',hr',c',hc',l,hl,F,hr's,hFa,hF⟩ := hgood s hs₁ isOpen_ball (mem_ball_self hr)
    hτ β hβ hroot hβbound
  obtain ⟨η,hη,H,hHa,hH⟩ := remove_ramification_scale hc' hl F hFa β hF
  exact ⟨r',hr',l,hl,η,hη,H,hr's.trans hrB,hHa,hH⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_JointLimitRamification
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Metric
open scoped Topology
lemma analyticAt_real_parameter_product {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    AnalyticAt ℝ (fun q : (Fin n → ℝ) × ℝ => (realParameter q.1,(q.2 : ℂ))) p := by
  have h₁ : AnalyticAt ℝ (fun q : (Fin n → ℝ) × ℝ => realParameter q.1) p := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact (Complex.ofRealCLM.analyticAt _).comp
      (((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt _).comp
        ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ).analyticAt p))
  exact h₁.prod ((Complex.ofRealCLM.analyticAt _).comp
    ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).analyticAt p))

lemma analyticAt_real_part_restriction {n : ℕ} (F : (Fin n → ℂ) × ℂ → ℂ)
    (p : (Fin n → ℝ) × ℝ)
    (hF : AnalyticAt ℂ F (realParameter p.1,(p.2 : ℂ))) :
    AnalyticAt ℝ (fun q : (Fin n → ℝ) × ℝ => (F (realParameter q.1,(q.2 : ℂ))).re) p := by
  have ha := (hF.restrictScalars (𝕜 := ℝ)).comp
    (f := fun q : (Fin n → ℝ) × ℝ => (realParameter q.1,(q.2 : ℂ)))
    (analyticAt_real_parameter_product p)
  exact (Complex.reCLM.analyticAt _).comp ha

end

section
open Set Filter Topology Metric MeasureTheory

theorem semialgebraic_ramification_with_parameters {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : (Fin (n+1) → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b (fun i => x (some i))})
    {M : ℝ} (hbound : ∀ x : Fin (n+1) → ℝ, Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b x‖ ≤ M) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ r > 0, ∃ l : ℕ, 0 < l ∧ ∃ η > 0,
        ∃ F : (Fin n → ℝ) × ℝ → ℝ,
          ball s r ⊆ B ∧
          AnalyticOnNhd ℝ F (ball s r ×ˢ ball 0 η) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η,
            F (x,t) = b (Fin.cons (t^l) x) := by
  obtain ⟨E,hEB,hE,hg⟩ := semialgebraic_ramification_with_parameters_complex hB hε b hgraph hbound
  refine ⟨E,hEB,hE,?_⟩
  intro s hs hsE
  obtain ⟨r,hr,l,hl,η,hη,F,hrB,hFa,hF⟩ := hg s hs hsE
  refine ⟨r,hr,l,hl,η,hη,(fun p => (F (realParameter p.1,(p.2 : ℂ))).re),hrB,?_,?_⟩
  · intro p hp
    apply analyticAt_real_part_restriction
    apply hFa
    refine ⟨?_,?_⟩
    · simpa only [mem_ball,realParameter_dist] using hp.1
    · simpa only [mem_ball,dist_zero_right,Complex.norm_real] using hp.2
  · intro x hx t ht
    change (F (realParameter x,(t : ℂ))).re = _
    rw [hF x hx t ht,Complex.ofReal_re]

end

open Filter Set Metric Topology

theorem joint_limit_of_ramification {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b F : E × ℝ → ℝ) (s : E) {r η : ℝ} (hr : 0 < r) (hη : 0 < η)
    {l : ℕ} (hl : 0 < l) (hFc : ContinuousAt F (s,0))
    (hF : ∀ x ∈ ball s r, ∀ u ∈ Ioo (0 : ℝ) η, F (x,u) = b (x,u^l)) :
    Tendsto b (𝓝[{p : E × ℝ | 0 < p.2}] (s,0)) (𝓝 (F (s,0))) := by
  let a : ℝ := (l : ℝ)⁻¹
  have ha : 0 < a := inv_pos.mpr (Nat.cast_pos.mpr hl)
  let e : E × ℝ → E × ℝ := fun p => (p.1,p.2^a)
  have he : Continuous e :=
    continuous_fst.prodMk ((Real.continuous_rpow_const ha.le).comp continuous_snd)
  have he₀ : e (s,0) = (s,0) := by
    simp only [e,Real.zero_rpow ha.ne']
  have hT : Tendsto e (𝓝 (s,0)) (𝓝 (s,0)) := by
    simpa only [he₀] using he.continuousAt.tendsto (x := (s,0))
  have hN : ball s r ×ˢ ball (0 : ℝ) η ∈ 𝓝 ((s,0) : E × ℝ) :=
    (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr,mem_ball_self hη⟩
  have hen := hT hN
  have heq : b =ᶠ[𝓝[{p : E × ℝ | 0 < p.2}] (s,0)] F ∘ e := by
    filter_upwards [nhdsWithin_le_nhds hen,self_mem_nhdsWithin] with p hp hp0
    have hu : 0 < p.2^a := Real.rpow_pos_of_pos hp0 _
    have hut : p.2^a < η := by
      have hh := hp.2
      change dist (p.2^a) 0 < η at hh
      simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos hu] using hh
    have hpw : (p.2^a)^l = p.2 := Real.rpow_inv_natCast_pow hp0.le hl.ne'
    change b p = F (p.1,p.2^a)
    rw [hF p.1 hp.1 (p.2^a) ⟨hu,hut⟩,hpw]
  exact ((hFc.tendsto.comp hT).mono_left nhdsWithin_le_nhds).congr' heq.symm

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteCommonRamification
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Metric MeasureTheory Topology

theorem semialgebraic_joint_boundary_limit {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : (Fin (n+1) → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b (fun i => x (some i))})
    {M : ℝ} (hbound : ∀ x : Fin (n+1) → ℝ, Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b x‖ ≤ M) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ L : ℝ,
        Tendsto (fun p : (Fin n → ℝ) × ℝ => b (Fin.cons p.2 p.1))
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 L) := by
  obtain ⟨E,hEB,hE,hg⟩ := semialgebraic_ramification_with_parameters hB hε b hgraph hbound
  refine ⟨E,hEB,hE,?_⟩
  intro s hs hsE
  obtain ⟨r,hr,l,hl,η,hη,F,_,hFa,hF⟩ := hg s hs hsE
  exact ⟨F (s,0),joint_limit_of_ramification _ F s hr hη hl
    (hFa (s,0) ⟨mem_ball_self hr,mem_ball_self hη⟩).continuousAt hF⟩

theorem countable_semialgebraic_joint_boundary_limits {n : ℕ} {J : Type*} [Countable J]
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : J → (Fin (n+1) → ℝ) → ℝ)
    (hgraph : ∀ j, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b j (fun i => x (some i))})
    (M : J → ℝ) (hbound : ∀ j (x : Fin (n+1) → ℝ),
      Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b j x‖ ≤ M j) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∀ j, ∃ L : ℝ,
        Tendsto (fun p : (Fin n → ℝ) × ℝ => b j (Fin.cons p.2 p.1))
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 L) := by
  choose E hEB hE hg using fun j =>
    semialgebraic_joint_boundary_limit hB hε (b j) (hgraph j) (hbound j)
  refine ⟨⋃ j, E j,iUnion_subset hEB,measure_iUnion_null hE,?_⟩
  intro s hs hsE j
  exact hg j s hs (fun h => hsE (mem_iUnion.mpr ⟨j,h⟩))

end

open Set Filter Metric Topology

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OffsetLimitClosedCone
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter
open scoped Topology NNReal

theorem dense_lipschitz_test_limits {I E : Type*} [PseudoMetricSpace E]
    (F : I → E → ℝ) {l : Filter I} [l.NeBot] {L : ℝ≥0}
    (hL : ∀ i, LipschitzWith L (F i)) {D : Set E} (hD : Dense D)
    (htest : ∀ x ∈ D, ∃ a : ℝ, Tendsto (fun i => F i x) l (𝓝 a)) :
    ∃ f : E → ℝ, LipschitzWith L f ∧
      (∀ x, Tendsto (fun i => F i x) l (𝓝 (f x))) ∧
      ∀ K : Set E, IsCompact K → TendstoUniformlyOn F f l K := by
  let g : E → ℝ := fun x => limUnder l (fun i => F i x)
  have hpt (x : E) (hx : x ∈ D) : Tendsto (fun i => F i x) l (𝓝 (g x)) := by
    obtain ⟨a,ha⟩ := htest x hx
    have he : g x = a := ha.limUnder_eq
    rwa [he]
  have hg : LipschitzOnWith L g D := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto ((hpt x hx).dist (hpt y hy))
      (Eventually.of_forall fun i => (hL i).dist_le_mul x y)
  obtain ⟨f,hf,he⟩ := hg.extend_real
  have heq : Equicontinuous F := (LipschitzWith.uniformEquicontinuous F L hL).equicontinuous
  have hall (x : E) : Tendsto (fun i => F i x) l (𝓝 (f x)) := by
    exact (heq x).tendsto_of_mem_closure
      (hf.continuous.continuousAt.mono_left nhdsWithin_le_nhds)
      (fun y hy => by simpa only [he hy] using hpt y hy) (hD x)
  refine ⟨f,hf,hall,?_⟩
  intro K hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have hKlip (i : I) : LipschitzWith L (fun x : K => F i x) :=
    by simpa only [mul_one, Function.comp_def] using (hL i).comp (isometry_subtype_coe.lipschitz)
  have hKeq := (LipschitzWith.uniformEquicontinuous
    (fun i : I => fun x : K => F i x) L hKlip).equicontinuous
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (hKeq.tendsto_uniformFun_iff_pi l (fun x : K => f x)).mpr
  exact tendsto_pi_nhds.mpr fun x => hall x

end

open Set Filter Metric
open scoped Topology Pointwise

lemma offset_complement_dilation {S E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) {c : ℝ} (hc : c ≠ 0) :
    (offsetScaled A s t)ᶜ = c • (offsetScaled A s (c*t))ᶜ := by
  ext x
  constructor
  · intro hx
    refine ⟨c⁻¹ • x,?_,smul_inv_smul₀ hc x⟩
    change (c*t) • (c⁻¹ • x) ∉ A s
    have he : (c*t)*c⁻¹ = t := by field_simp
    change t • x ∉ A s at hx
    simpa only [smul_smul,he] using hx
  · rintro ⟨y,hy,rfl⟩
    change t • (c • y) ∉ A s
    simpa only [offsetScaled,mem_ofPred_eq,mem_compl_iff,smul_smul,mul_comm t c] using hy

lemma offset_distance_dilation {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) {c : ℝ} (hc : 0 < c) (v : E) :
    infDist (c • v) (offsetScaled A s t)ᶜ = c * infDist v (offsetScaled A s (c*t))ᶜ := by
  rw [offset_complement_dilation A s t hc.ne',infDist_smul₀ hc.ne',Real.norm_eq_abs,abs_of_pos hc]

theorem offset_limit_zero_cone {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (s : S) {f : E → ℝ}
    (hf : ∀ v, Tendsto (fun t => offsetDistance A s t v) (𝓝[>] (0 : ℝ)) (𝓝 (f v)))
    (v : E) {c : ℝ} (hc : 0 < c) : f v = 0 ↔ f (c • v) = 0 := by
  have step (v : E) {c : ℝ} (hc : 0 < c) (hv : f v = 0) : f (c • v) = 0 := by
    have hct : Tendsto (fun t : ℝ => c*t) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_,?_⟩
      · simpa only [mul_zero] using
          (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
            Tendsto (fun t : ℝ => c*t) (𝓝[>] 0) (𝓝 (c*0)))
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos hc ht
    have hzero : Tendsto (fun t => offsetDistance A s (c*t) v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [Function.comp_def,hv] using (hf v).comp hct
    have hraw : Tendsto (fun t => infDist v (offsetScaled A s (c*t))ᶜ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_of_truncated_zero hzero
    have hraw' : Tendsto (fun t => infDist (c • v) (offsetScaled A s t)ᶜ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [offset_distance_dilation A s _ hc,mul_zero] using hraw.const_mul c
    have htrunc : Tendsto (fun t => offsetDistance A s t (c • v)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [offsetDistance,min_eq_right (zero_le_one : (0:ℝ) ≤ 1)] using (tendsto_const_nhds (x := (1 : ℝ))).min hraw'
    exact tendsto_nhds_unique (hf (c • v)) htrunc
  refine ⟨step v hc,fun h => ?_⟩
  simpa only [inv_smul_smul₀ hc.ne'] using step (c • v) (inv_pos.mpr hc) h

theorem offset_limit_closed_cone {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (s : S) (h0 : (0 : E) ∉ A s) {f : E → ℝ}
    (hfl : LipschitzWith 1 f)
    (hf : ∀ v, Tendsto (fun t => offsetDistance A s t v) (𝓝[>] (0 : ℝ)) (𝓝 (f v))) :
    IsClosed {v | f v = 0} ∧ (0 : E) ∈ {v | f v = 0} ∧
      ∀ c : ℝ, 0 < c → ∀ v : E, v ∈ {v | f v = 0} ↔ c • v ∈ {v | f v = 0} := by
  refine ⟨isClosed_eq hfl.continuous continuous_const,?_,fun c hc v => offset_limit_zero_cone A s hf v hc⟩
  have h : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 (f 0)) := by
    simpa only [offsetDistance_zero A s _ h0] using hf 0
  exact (tendsto_nhds_unique h tendsto_const_nhds).symm.symm

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicOffsetLimits
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric MeasureTheory Topology

lemma tendsto_positive_vertical {E : Type*} [TopologicalSpace E] (s : E) :
    Tendsto (fun t : ℝ => (s,t)) (𝓝[>] (0 : ℝ))
      (𝓝[{p : E × ℝ | 0 < p.2}] (s,0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_const_nhds.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds),self_mem_nhdsWithin⟩

theorem semialgebraic_lipschitz_boundary_limits {n : ℕ} {Y : Type*}
    [PseudoMetricSpace Y] [TopologicalSpace.SeparableSpace Y]
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : (Fin (n+1) → ℝ) → Y → ℝ)
    (hgraph : ∀ y, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b (fun i => x (some i)) y})
    (M : Y → ℝ) (hbound : ∀ y (x : Fin (n+1) → ℝ),
      Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b x y‖ ≤ M y)
    (hLip : ∀ x, LipschitzWith 1 (b x)) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ f : Y → ℝ, LipschitzWith 1 f ∧
        (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ => b (Fin.cons p.2 p.1) y)
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
        ∀ K : Set Y, IsCompact K →
          TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ => b (Fin.cons p.2 p.1)) f
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K := by
  obtain ⟨D,hD,hDense⟩ := TopologicalSpace.exists_countable_dense Y
  let : Countable D := hD.to_subtype
  obtain ⟨E,hEB,hE,hg⟩ := countable_semialgebraic_joint_boundary_limits hB hε
    (fun y : D => fun x => b x y.val) (fun y => hgraph y.val)
    (fun y => M y.val) (fun y => hbound y.val)
  refine ⟨E,hEB,hE,?_⟩
  intro s hs hsE
  have : NeBot (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) :=
    (tendsto_positive_vertical s).neBot
  exact dense_lipschitz_test_limits _ (fun p => hLip (Fin.cons p.2 p.1)) hDense
    (fun y hy => hg s hs hsE ⟨y,hy⟩)

theorem semialgebraic_offset_joint_limits {n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace.SeparableSpace Y]
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (A : (Fin n → ℝ) → Set Y)
    (hgraph : ∀ y, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = offsetDistance A (fun i => x (some i.succ)) (x (some 0)) y}) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ f : Y → ℝ, LipschitzWith 1 f ∧
        (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2 y)
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
        ∀ K : Set Y, IsCompact K →
          TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2) f
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K := by
  have hg : ∀ y, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = (fun a : Fin (n+1) → ℝ => offsetDistance A (Fin.tail a) (a 0) y)
            (fun i => x (some i))} := hgraph
  have H := semialgebraic_lipschitz_boundary_limits hB hε
    (fun a : Fin (n+1) → ℝ => offsetDistance A (Fin.tail a) (a 0)) hg
    (fun _ => (1 : ℝ)) (fun y x _ _ => by
      rw [Real.norm_of_nonneg (offsetDistance_nonneg A _ _ _)]
      exact offsetDistance_le_one A _ _ _) (fun x => offsetDistance_lipschitz A _ _)
  simpa only [Fin.tail_cons,Fin.cons_zero] using H

theorem semialgebraic_offset_limits {n : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace.SeparableSpace Y]
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (A : (Fin n → ℝ) → Set Y) (h0 : ∀ s ∈ B, (0 : Y) ∉ A s)
    (hgraph : ∀ y, PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = offsetDistance A (fun i => x (some i.succ)) (x (some 0)) y}) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ f : Y → ℝ, LipschitzWith 1 f ∧
        (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
        (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2 y)
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
        (∀ K : Set Y, IsCompact K →
          TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2) f
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K) ∧
        IsClosed {y | f y = 0} ∧ (0 : Y) ∈ {y | f y = 0} ∧
        ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0 := by
  obtain ⟨E,hEB,hE,H⟩ := semialgebraic_offset_joint_limits hB hε A hgraph
  refine ⟨E,hEB,hE,?_⟩
  intro s hs hsE
  obtain ⟨f,hf,hpt,hunif⟩ := H s hs hsE
  have : NeBot (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) :=
    (tendsto_positive_vertical s).neBot
  have hvertical (y : Y) : Tendsto (fun t : ℝ => offsetDistance A s t y)
      (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
    have H := (hpt y).comp (tendsto_positive_vertical s)
    exact H
  have hcone : IsClosed {y | f y = 0} ∧ (0 : Y) ∈ {y | f y = 0} ∧
      ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0 :=
    offset_limit_closed_cone A s (h0 s hs) hf hvertical
  refine ⟨f,hf,?_,hpt,hunif,hcone⟩
  intro y
  exact ⟨ge_of_tendsto (hpt y) (Eventually.of_forall fun p => offsetDistance_nonneg A p.1 p.2 y),
    le_of_tendsto (hpt y) (Eventually.of_forall fun p => offsetDistance_le_one A p.1 p.2 y)⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicOffsetLimitsFamily
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter

namespace Release061
open Set Filter Topology Metric MeasureTheory Classical
open SignElimination

lemma PolynomialSignSet.parameter_strip {n : ℕ} {B : Set (Fin n → ℝ)}
    (hB : PolynomialSignSet id B) (ε : ℝ) :
    PolynomialSignSet id {x : Fin (n+1) → ℝ | Fin.tail x ∈ B ∧ x 0 ∈ Ioo 0 ε} := by
  have hb : PolynomialSignSet id {x : Fin (n+1) → ℝ | Fin.tail x ∈ B} :=
    hB.coordinate_preimage (fun x : Fin (n+1) → ℝ => Fin.tail x) Fin.succ
      (d := id) (by intros; rfl)
  have hp : PolynomialSignSet id {x : Fin (n+1) → ℝ | 0 < x 0} := by
    simpa using (PolynomialSignSet.positive (c := id) (MvPolynomial.X 0))
  have he : PolynomialSignSet id {x : Fin (n+1) → ℝ | x 0 < ε} := by
    have heq : {x : Fin (n+1) → ℝ | x 0 < ε} =
        {x : Fin (n+1) → ℝ | 0 < MvPolynomial.eval (id x)
          (MvPolynomial.C ε-MvPolynomial.X 0)} := by
      ext x
      simp
    rw [heq]
    exact PolynomialSignSet.positive _
  exact hb.inter (hp.inter he)

theorem semialgebraic_offset_limits_from_family {n k : ℕ}
    (A : (Fin n → ℝ) → Set (Fin k → ℝ))
    (hA : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ A z.1})
    (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hBs : PolynomialSignSet id B)
    (h0 : ∀ s ∈ B, (0 : Fin k → ℝ) ∉ A s) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ f : (Fin k → ℝ) → ℝ, LipschitzWith 1 f ∧
        (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
        (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2 y)
          (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
        (∀ K : Set (Fin k → ℝ), IsCompact K →
          TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2) f
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K) ∧
        IsClosed {y | f y = 0} ∧ (0 : Fin k → ℝ) ∈ {y | f y = 0} ∧
        ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0 := by
  apply semialgebraic_offset_limits hB (ε := 1) zero_lt_one A h0
  intro y
  have hg := polynomialSignSet_offsetDistance_graph (c := id) A hA y
  have hgo : PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        x none = offsetDistance A (fun i => x (some i.succ)) (x (some 0)) y} :=
    hg.coordinate_preimage
      (fun x : Option (Fin (n+1)) → ℝ => (((fun i => x (some i.succ)),x (some 0)),x none))
      (fun o => Option.elim o none (fun o => Option.elim o (some 0) (fun i => some i.succ)))
      (by intro x o; cases o with | none => rfl | some o => cases o <;> rfl)
  have hs : PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        (fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 1} :=
    (hBs.parameter_strip 1).coordinate_preimage (fun x : Option (Fin (n+1)) → ℝ => fun i => x (some i))
      some (by intros; rfl)
  exact hs.inter hgo

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AffineInverseGermSemialgebraic
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology Metric
open scoped Classical

lemma polynomialSignSet_real_ball {ι : Type*} [Fintype ι] (p : ι → ℝ) (r : ℝ) :
    PolynomialSignSet id {y : ι → ℝ | ‖y-p‖ < r} := by
  convert PolynomialSignSet.norm_lt_polynomial (c := id)
    (fun j => MvPolynomial.X j - MvPolynomial.C (p j)) (MvPolynomial.C r) using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  simp only [mem_ofPred_eq,id_eq,map_sub,MvPolynomial.eval_X,MvPolynomial.eval_C,Pi.sub_def]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NashNormalGraphBoundary
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology MeasureTheory
open scoped Classical

theorem differentiable_image_null_same_dimension {d n : ℕ} (hd : d=n)
    (f : (Fin d → ℝ) → (Fin n → ℝ)) {A : Set (Fin d → ℝ)}
    (hf : DifferentiableOn ℝ f A) (hA : volume A = 0) :
    volume (f '' A) = 0 := by
  subst n
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hf hA

theorem partial_homeomorph_preimage_null {d n : ℕ} (hd : d=n)
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin n → ℝ))
    {B A : Set (Fin n → ℝ)}
    (he : DifferentiableOn ℝ e.symm B) (hAB : A ⊆ B) (hA : volume A = 0) :
    volume (e.source ∩ e ⁻¹' A) = 0 := by
  have him := differentiable_image_null_same_dimension hd.symm e.symm (he.mono hAB) hA
  apply measure_mono_null (t := e.symm '' A) _ him
  intro x hx
  exact ⟨e x,hx.2,e.left_inv hx.1⟩

end

open Set Filter Topology Metric
open scoped Classical

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicChartBoundaryData
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory Classical
open SignElimination

theorem semialgebraic_joint_boundary_data_from_family {n k : ℕ}
    (A : (Fin n → ℝ) → Set (Fin k → ℝ))
    (hA : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.2 ∈ A z.1})
    (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hBs : PolynomialSignSet id B)
    (hb : ∀ s ∈ B, (s,(0 : Fin k → ℝ)) ∈
      closure {p : (Fin n → ℝ) × (Fin k → ℝ) | p.2 ∈ A p.1})
    (h0 : ∀ s ∈ B, (0 : Fin k → ℝ) ∉ A s) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E →
        (∃ r > 0, ∃ η > 0, ∃ ψ : (Fin n → ℝ) × ℝ → (Fin k → ℝ),
          ball s r ⊆ B ∧ AnalyticOnNhd ℝ ψ (ball s r ×ˢ ball 0 η) ∧
          (∀ x ∈ ball s r, ψ (x,0) = 0) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η, ψ (x,t) ∈ A x) ∧
        ∃ f : (Fin k → ℝ) → ℝ, LipschitzWith 1 f ∧
          (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
          (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2 y)
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
          (∀ K : Set (Fin k → ℝ), IsCompact K →
            TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ => offsetDistance A p.1 p.2) f
              (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K) ∧
          IsClosed {y | f y = 0} ∧ (0 : Fin k → ℝ) ∈ {y | f y = 0} ∧
          ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0 := by
  obtain ⟨E₁,hE₁B,hE₁,H₁⟩ := semialgebraic_inward_analytic_from_family A hA B hB hBs hb
  obtain ⟨E₂,hE₂B,hE₂,H₂⟩ := semialgebraic_offset_limits_from_family A hA B hB hBs h0
  refine ⟨E₁ ∪ E₂,union_subset hE₁B hE₂B,measure_union_null hE₁ hE₂,?_⟩
  intro s hs hsE
  exact ⟨H₁ s hs (fun h => hsE (Or.inl h)),H₂ s hs (fun h => hsE (Or.inr h))⟩

theorem semialgebraic_chart_boundary_data {n k : ℕ}
    (U : Set ((Fin n → ℝ) × (Fin k → ℝ)))
    (hU : PolynomialSignSet (fun z => Sum.elim z.1 z.2) U)
    (B : Set (Fin n → ℝ)) (hB : IsOpen B) (hBs : PolynomialSignSet id B)
    (φ : (Fin n → ℝ) → (Fin k → ℝ)) (hφc : ContinuousOn φ B)
    (hφs : PolynomialSignSet (fun z : (Fin n → ℝ) × (Fin k → ℝ) => Sum.elim z.1 z.2)
      {z | z.1 ∈ B ∧ z.2 = φ z.1}) (ρ : ℝ) (hρ : 0 < ρ)
    (hb : ∀ s ∈ B, (s,φ s) ∈ closure U ∧ (s,φ s) ∉ U) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E →
        (∃ r > 0, ∃ η > 0, ∃ ψ : (Fin n → ℝ) × ℝ → (Fin k → ℝ),
          ball s r ⊆ B ∧ AnalyticOnNhd ℝ ψ (ball s r ×ˢ ball 0 η) ∧
          (∀ x ∈ ball s r, ψ (x,0) = 0) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η,
            ψ (x,t) ∈ normalOffsetFamily U B φ ρ x) ∧
        ∃ f : (Fin k → ℝ) → ℝ, LipschitzWith 1 f ∧
          (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
          (∀ y, Tendsto (fun p : (Fin n → ℝ) × ℝ =>
            offsetDistance (normalOffsetFamily U B φ ρ) p.1 p.2 y)
            (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) (𝓝 (f y))) ∧
          (∀ K : Set (Fin k → ℝ), IsCompact K →
            TendstoUniformlyOn (fun p : (Fin n → ℝ) × ℝ =>
              offsetDistance (normalOffsetFamily U B φ ρ) p.1 p.2) f
              (𝓝[{p : (Fin n → ℝ) × ℝ | 0 < p.2}] (s,0)) K) ∧
          IsClosed {y | f y = 0} ∧ (0 : Fin k → ℝ) ∈ {y | f y = 0} ∧
          ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0 := by
  apply semialgebraic_joint_boundary_data_from_family (normalOffsetFamily U B φ ρ)
    (normalOffsetFamily_polynomialSignSet ρ hU hφs) B hB hBs
  · intro s hs
    exact normalOffsetFamily_joint_closure (hB.mem_nhds hs)
      ((hφc s hs).continuousAt (hB.mem_nhds hs)) hρ (hb s hs).1
  · intro s hs
    exact normalOffsetFamily_zero_not_mem (hb s hs).2

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GoodNashBoundary
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
open scoped Classical

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

theorem null_bad_parameters (c : NashBoundaryChart (m := m) U V B q) :
    ∃ W : Set (Fin d → ℝ), IsOpen W ∧ c.center ∈ W ∧
      volume {x | x ∈ W ∧ ¬ c.GoodAt x} = 0 := by
  have hb : PolynomialSignSet id (ball (0 : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) c.graphRadius) := by
    simpa only [ball,dist_eq_norm] using polynomialSignSet_real_ball (0 : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) c.graphRadius
  have hφs := c.normal.graph_semialgebraic.mono hb (ball_subset_ball c.graphRadius_le)
  obtain ⟨E,hEB,hE,hdata⟩ := semialgebraic_chart_boundary_data
    (c.chart.coordinateDomain U c.normal.realCoordinates) c.domain_semialgebraic
    (ball 0 c.graphRadius) isOpen_ball hb c.normal.graph
    ((fun x hx => (c.normal.graph_analytic x (ball_subset_ball c.graphRadius_le hx)).continuousAt.continuousWithinAt) : ContinuousOn c.normal.graph (ball 0 c.graphRadius))
    hφs 1 zero_lt_one (fun s hs => (c.graph_boundary s hs).1)
  let W := c.normal.parameters.source ∩ c.normal.parameters ⁻¹' ball 0 c.graphRadius
  have hWo : IsOpen W := c.normal.parameters.isOpen_inter_preimage isOpen_ball
  have haW : c.center ∈ W := by
    refine ⟨c.normal.source_mem,?_⟩
    change c.normal.parameters c.center ∈ ball 0 c.graphRadius
    rw [c.normal.parameter_eq]
    simpa only [sub_self,map_zero,Prod.fst_zero] using (mem_ball_self (x :=
      (0 : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ)) c.graphRadius_pos)
  have hnull : volume (c.normal.parameters.source ∩ c.normal.parameters ⁻¹' E) = 0 :=
    partial_homeomorph_preimage_null c.normal.real_dimension c.normal.parameters
      c.normal.inverse_analytic.differentiableOn
      (hEB.trans (ball_subset_ball c.graphRadius_le)) hE
  refine ⟨W,hWo,haW,measure_mono_null ?_ hnull⟩
  intro x hx
  refine ⟨hx.1.1,?_⟩
  by_contra hxE
  exact hx.2 ⟨hx.1.1,hx.1.2,hdata _ hx.1.2 hxE⟩
end NashBoundaryChart

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocallySmallSlopeGood
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem NashBoundaryChart.locally_small_slope_good_oai {d m N : ℕ} {U V : Set (Affine N)}
    {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine N}
    (c : NashBoundaryChart (m := m) U V B q) :
    ∃ W : Set (Fin d → ℝ), IsOpen W ∧ c.center ∈ W ∧
      volume {x | x ∈ W ∧ ¬ SmallSlopeGoodNashBoundary m U V B q x} = 0 := by
  obtain ⟨W,hWo,haW,hnull⟩ := c.null_bad_parameters
  have hcd : ContinuousAt (fderiv ℝ c.normal.graph) 0 :=
    ((c.normal.graph_analytic 0 (mem_ball_self c.normal.radius_pos)).contDiffAt (n := 1)).continuousAt_fderiv (by norm_num)
  have hnear : ∀ᶠ s in 𝓝 0, ‖fderiv ℝ c.normal.graph s‖ < 1/2 :=
    hcd.norm (gt_mem_nhds (by simpa only [c.normal.derivative_zero,norm_zero] using (show (0:ℝ) < 1/2 by norm_num)))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnear
  let T := c.normal.parameters.source ∩ c.normal.parameters ⁻¹' ball 0 r
  have hTo : IsOpen T := c.normal.parameters.isOpen_inter_preimage isOpen_ball
  have haT : c.center ∈ T := by
    refine ⟨c.normal.source_mem,?_⟩
    change c.normal.parameters c.center ∈ ball 0 r
    rw [c.normal.parameter_eq]
    simpa only [sub_self,map_zero,Prod.fst_zero] using (mem_ball_self (x :=
      (0 : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ)) hr)
  refine ⟨W ∩ T,hWo.inter hTo,⟨haW,haT⟩,measure_mono_null ?_ hnull⟩
  intro x hx
  exact ⟨hx.1.1,fun hg => hx.2 ⟨c,hg,hrs hx.1.2.2⟩⟩

end Release061

end

end OAI
end

theorem solution : type_of% @OAI.Release061.NashBoundaryChart.locally_small_slope_good_oai := @OAI.Release061.NashBoundaryChart.locally_small_slope_good_oai
