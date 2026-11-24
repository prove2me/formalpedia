-- Prove2me | solution 1 for GlobalTheory.exists_fourier_expansion_tube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:30:35.545829+00:00
-- url     : https://prove2.me/submissions/339714ee-73ef-4dae-b855-4d99f3d2677e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTube
import Theorems.Thm_GlobalTheory_IsSiegel_mk
import Theorems.Thm_GlobalTheory_Koecher_setIntegral_unitCube_tube
import Theorems.Thm_GlobalTheory_Koecher_summable_exp_neg_mul_sum_abs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory
open MeasureTheory
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open MeasureTheory in
private lemma exists_unitAddTorus_lift_of_periodic {ι : Type} [Fintype ι] (F : (ι → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (x : ι → ℝ) (m : ι → ℤ), F (x + fun i ↦ (m i : ℝ)) = F x) :
    ∃ g : C(UnitAddTorus ι, ℂ), ∀ x : ι → ℝ, g (fun i ↦ (x i : UnitAddCircle)) = F x := by
  have hq : IsOpenQuotientMap (Pi.map fun _ : ι ↦ (QuotientAddGroup.mk : ℝ → UnitAddCircle)) :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  have hfac : Function.FactorsThrough F
      (Pi.map fun _ : ι ↦ (QuotientAddGroup.mk : ℝ → UnitAddCircle)) := by
    intro x x' hxx'
    have hi : ∀ i, ∃ k : ℤ, x i = x' i + k := by
      intro i
      have := congrFun hxx' i
      simp only [Pi.map_apply] at this
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 this.symm)
      exact ⟨k, by simp at hk; linarith⟩
    choose m hm using hi
    have : x = x' + fun i ↦ (m i : ℝ) := funext fun i ↦ hm i
    rw [this, hper]
  let q : C(ι → ℝ, UnitAddTorus ι) := ⟨_, hq.continuous⟩
  have hq' : Topology.IsQuotientMap q := hq.isQuotientMap
  refine ⟨hq'.lift ⟨F, hF⟩ hfac, fun x ↦ ?_⟩
  exact congrFun (congrArg DFunLike.coe (hq'.lift_comp ⟨F, hF⟩ hfac)) x
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open MeasureTheory in
private lemma mFourier_apply_coe {ι : Type} [Fintype ι] (ν : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier ν (fun i ↦ (x i : UnitAddCircle)) =
      cexp (2 * π * I * ∑ i, (ν i : ℂ) * x i) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [fourier_coe_apply]
  push_cast
  congr 1
  ring
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open MeasureTheory in
private lemma mFourierCoeff_lift_eq_integral {ι : Type} [Fintype ι] (g : C(UnitAddTorus ι, ℂ))
    (F : (ι → ℝ) → ℂ) (hg : ∀ x : ι → ℝ, g (fun i ↦ (x i : UnitAddCircle)) = F x) (ν : ι → ℤ) :
    UnitAddTorus.mFourierCoeff g ν =
      ∫ x in Set.Icc (0 : ι → ℝ) 1, cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * x i)) * F x := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ 0]
  have hset : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      Set.univ.pi fun _ ↦ Set.Ioc (0 : ℝ) 1 := by
    ext x; simp
  have hae : (Set.univ.pi fun _ : ι ↦ Set.Ioc (0 : ℝ) 1) =ᵐ[volume] Set.Icc (0 : ι → ℝ) 1 := by
    rw [volume_pi]; exact Measure.univ_pi_Ioc_ae_eq_Icc
  rw [hset, setIntegral_congr_set hae]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ ↦ ?_
  simp only [hg, smul_eq_mul, mFourier_apply_coe]
  congr 2
  push_cast
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring
end GlobalTheory
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory
open MeasureTheory
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
open MeasureTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)) (f : (ι → ℂ) → ℂ), IsOpen Ω → Convex ℝ Ω →
      DifferentiableOn ℂ f {z | (fun i => (z i).im) ∈ Ω} →
      (∀ z, (fun i => (z i).im) ∈ Ω → ∀ m : ι → ℤ, f (z + fun i => (m i : ℂ)) = f z) →
      ∃ a : (ι → ℤ) → ℂ, (∀ z, (fun i => (z i).im) ∈ Ω →
        HasSum (fun ν : ι → ℤ => a ν * cexp (2 * π * I * ∑ i, (ν i : ℂ) * z i)) (f z)) ∧
        ∀ y ∈ Ω, ∀ ν : ι → ℤ, a ν = ∫ x in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1),
          f (fun i => (x i : ℂ) + I * y i) *
            cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))) := by
  intro ι _ Ω f hΩo hΩc hf hper
  set T : Set (ι → ℂ) := {z | (fun i => (z i).im) ∈ Ω} with hT
  have him : Continuous fun z : ι → ℂ ↦ fun i ↦ (z i).im :=
    continuous_pi fun i ↦ Complex.continuous_im.comp (continuous_apply i)
  have hTo : IsOpen T := hΩo.preimage him
  have hTc : IsPreconnected T := by
    refine Convex.isPreconnected ?_
    intro z hz w hw s t hs ht hst
    simp only [hT, Set.mem_setOf_eq] at hz hw ⊢
    convert hΩc hz hw hs ht hst using 1
    funext i
    simp
  have hcont : ContinuousOn f T := hf.continuousOn

  have hmemT : ∀ (x y : ι → ℝ), y ∈ Ω → (fun i ↦ (x i : ℂ) + I * y i) ∈ T := by
    intro x y hy
    simpa [hT] using hy
  let c : (ι → ℝ) → (ι → ℤ) → ℂ := fun y ν ↦ ∫ x in Set.Icc (0 : ι → ℝ) 1,
    f (fun i => (x i : ℂ) + I * y i) * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i)))
  have hc_indep : ∀ y ∈ Ω, ∀ y' ∈ Ω, ∀ ν, c y ν = c y' ν := by
    intro y hy y' hy' ν
    let h : (ι → ℂ) → ℂ := fun z ↦ f z * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * z i))
    have hw : ∀ y ∈ Ω, (fun i ↦ I * (y i : ℂ)) ∈ T := fun y hy ↦ by simpa [hT] using hy
    have key := _root_.GlobalTheory.Koecher.setIntegral_unitCube_tube (f := h) (U := T) hTo hTc
      (fun z hz t ↦ by simpa [hT] using hz)
      (hf.mul (Differentiable.differentiableOn (by fun_prop)))
      (fun z hz i ↦ by
        have hm := hper z hz (Pi.single i 1)
        have hs : (fun j ↦ ((Pi.single i (1 : ℤ) : ι → ℤ) j : ℂ)) = Pi.single i 1 := by
          funext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj]
        rw [hs] at hm
        simp only [h]
        rw [hm]
        congr 1
        rw [show ∑ j, (ν j : ℂ) * (z + (Pi.single i (1 : ℂ) : ι → ℂ)) j =
            ∑ j, (ν j : ℂ) * z j + ν i by
          simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply]]
        rw [mul_add, neg_add, Complex.exp_add]
        have h1 : cexp (-(2 * π * I * (ν i : ℂ))) = 1 := by
          rw [show -(2 * π * I * (ν i : ℂ)) = ((-ν i : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
          exact Complex.exp_int_mul_two_pi_mul_I _
        rw [h1, mul_one])
      (hw y hy) (hw y' hy')
    exact key
  have hc_Ico : ∀ y ν, c y ν = ∫ x in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1),
      f (fun i => (x i : ℂ) + I * y i) *
        cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))) := by
    intro y ν
    have hae : (Set.univ.pi fun _ : ι ↦ Set.Ico (0 : ℝ) 1) =ᵐ[volume] Set.Icc (0 : ι → ℝ) 1 := by
      rw [volume_pi]; exact Measure.univ_pi_Ico_ae_eq_Icc
    rw [setIntegral_congr_set hae]
  have hc_bound : ∀ y ∈ Ω, ∀ M : ℝ, (∀ x : ι → ℝ, ‖f (fun i ↦ (x i : ℂ) + I * y i)‖ ≤ M) →
      ∀ ν, ‖c y ν‖ ≤ Real.exp (2 * π * ∑ i, (ν i : ℝ) * y i) * M := by
    intro y hy M hM ν
    have hvol : volume (Set.Icc (0 : ι → ℝ) 1) = 1 := by simp [Real.volume_Icc_pi]
    refine (norm_setIntegral_le_of_norm_le_const
      (C := Real.exp (2 * π * ∑ i, (ν i : ℝ) * y i) * M) (by simp [hvol]) fun x _ ↦ ?_).trans ?_
    · rw [norm_mul, Complex.norm_exp, mul_comm]
      have hre : (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))).re =
          2 * π * ∑ i, (ν i : ℝ) * y i := by
        simp [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Finset.mul_sum]
      rw [hre]
      exact mul_le_mul_of_nonneg_left (hM x) (Real.exp_pos _).le
    · simp [Measure.real, hvol]
  have hc_coef : ∀ y ∈ Ω, ∃ g : C(UnitAddTorus ι, ℂ),
      (∀ x : ι → ℝ, g (fun i ↦ (x i : UnitAddCircle)) = f (fun i ↦ (x i : ℂ) + I * y i)) ∧
      ∀ ν, UnitAddTorus.mFourierCoeff g ν = Real.exp (-(2 * π * ∑ i, (ν i : ℝ) * y i)) * c y ν := by
    intro y hy
    have hFc : Continuous fun x : ι → ℝ ↦ f (fun i ↦ (x i : ℂ) + I * y i) :=
      hcont.comp_continuous (by fun_prop) fun x ↦ hmemT x y hy
    obtain ⟨g, hg⟩ := exists_unitAddTorus_lift_of_periodic _ hFc (fun x m ↦ by
      have := hper (fun i ↦ (x i : ℂ) + I * y i) (by simpa using hy) m
      convert this using 2
      funext i
      simp only [Pi.add_apply]
      push_cast
      ring)
    refine ⟨g, hg, fun ν ↦ ?_⟩
    rw [mFourierCoeff_lift_eq_integral g _ hg ν]
    simp only [c]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun x _ ↦ ?_
    have hs : ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i) =
        ∑ i, (ν i : ℂ) * x i + I * ∑ i, (ν i : ℂ) * y i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have he : cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))) =
        cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * x i)) * cexp (2 * π * ∑ i, (ν i : ℂ) * y i) := by
      rw [← Complex.exp_add, hs]
      congr 1
      ring_nf
      rw [I_sq]
      ring
    rw [he]
    push_cast
    have hB : cexp (-(2 * π * ∑ i, (ν i : ℂ) * (y i : ℂ))) *
        cexp (2 * π * ∑ i, (ν i : ℂ) * y i) = 1 := by
      rw [← Complex.exp_add]; simp
    linear_combination -(cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * x i)) *
      f (fun i ↦ (x i : ℂ) + I * y i)) * hB
  rcases Set.eq_empty_or_nonempty Ω with hΩ | ⟨y₁, hy₁⟩
  · refine ⟨0, fun z hz ↦ ?_, fun y hy ↦ ?_⟩
    · simp [hΩ] at hz
    · simp [hΩ] at hy
  refine ⟨c y₁, fun z hz ↦ ?_, fun y hy ν ↦ by rw [hc_indep y₁ hy₁ y hy, hc_Ico]⟩
  set y₀ : ι → ℝ := fun i ↦ (z i).im with hy₀
  set x₀ : ι → ℝ := fun i ↦ (z i).re with hx₀
  have hz' : z = fun i ↦ (x₀ i : ℂ) + I * y₀ i := by
    funext i; rw [mul_comm]; exact (Complex.re_add_im _).symm
  obtain ⟨g, hg, hgc⟩ := hc_coef y₀ hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩo y₀ hz
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsub : Metric.closedBall y₀ δ ⊆ Ω :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have hK : IsCompact ((fun p : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (p.1 i : ℂ) + I * p.2 i) ''
      (Set.Icc 0 1 ×ˢ Metric.closedBall y₀ δ)) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image (by fun_prop)
  have hKT : ((fun p : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (p.1 i : ℂ) + I * p.2 i) ''
      (Set.Icc 0 1 ×ˢ Metric.closedBall y₀ δ)) ⊆ T := by
    rintro _ ⟨⟨x, y⟩, ⟨-, hy⟩, rfl⟩
    exact hmemT x y (hsub hy)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKT)
  have hMall : ∀ y ∈ Metric.closedBall y₀ δ, ∀ x : ι → ℝ,
      ‖f (fun i ↦ (x i : ℂ) + I * y i)‖ ≤ M := by
    intro y hy x
    have h1 := hper (fun i ↦ ((Int.fract (x i) : ℝ) : ℂ) + I * y i) (by simpa using hsub hy)
      (fun i ↦ ⌊x i⌋)
    have heq : ((fun i ↦ ((Int.fract (x i) : ℝ) : ℂ) + I * y i) + fun i ↦ ((⌊x i⌋ : ℤ) : ℂ)) =
        fun i ↦ (x i : ℂ) + I * y i := by
      funext i; simp only [Pi.add_apply, Int.fract]; push_cast; ring
    rw [heq] at h1
    rw [h1]
    exact hM _ ⟨(fun i ↦ Int.fract (x i), y),
      ⟨⟨fun i ↦ Int.fract_nonneg _, fun i ↦ (Int.fract_lt_one _).le⟩, hy⟩, rfl⟩
  have hsum : Summable (UnitAddTorus.mFourierCoeff g) := by
    refine Summable.of_norm_bounded
      ((_root_.GlobalTheory.Koecher.summable_exp_neg_mul_sum_abs (ι := ι) (ε := 2 * π * δ) (by positivity)).mul_left M)
      fun ν ↦ ?_
    set s : ι → ℝ := fun i ↦ y₀ i - δ * (Int.sign (ν i) : ℝ) with hsdef
    have hs : s ∈ Metric.closedBall y₀ δ := by
      rw [Metric.mem_closedBall, dist_pi_le_iff hδ0.le]
      intro i
      rw [Real.dist_eq, hsdef]
      simp only [sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos hδ0]
      have : |(Int.sign (ν i) : ℝ)| ≤ 1 := by
        rcases Int.sign_trichotomy (ν i) with h | h | h <;> simp [h]
      nlinarith
    rw [hgc ν, hc_indep y₀ hz s (hsub hs), norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(2 * π * ∑ i, (ν i : ℝ) * y₀ i)) * ‖c s ν‖
        ≤ Real.exp (-(2 * π * ∑ i, (ν i : ℝ) * y₀ i)) *
            (Real.exp (2 * π * ∑ i, (ν i : ℝ) * s i) * M) :=
          mul_le_mul_of_nonneg_left (hc_bound s (hsub hs) M (hMall s hs) ν) (Real.exp_pos _).le
      _ = M * Real.exp (-(2 * π * δ * ∑ i, |((ν i : ℤ) : ℝ)|)) := by
          rw [← mul_assoc, ← Real.exp_add, mul_comm]
          congr 2
          have habs : ∀ i, (ν i : ℝ) * (Int.sign (ν i) : ℝ) = |((ν i : ℤ) : ℝ)| := by
            intro i
            rcases Int.sign_trichotomy (ν i) with h | h | h
            · rw [h, Int.cast_one, mul_one,
                abs_of_pos (by exact_mod_cast Int.sign_eq_one_iff_pos.1 h)]
            · rw [h]; simp [Int.sign_eq_zero_iff_zero.1 h]
            · rw [h, Int.cast_neg, Int.cast_one, mul_neg_one,
                abs_of_neg (by exact_mod_cast Int.sign_eq_neg_one_iff_neg.1 h)]
          simp only [hsdef, mul_sub, Finset.sum_sub_distrib]
          rw [show ∑ i, (ν i : ℝ) * (δ * (Int.sign (ν i) : ℝ)) = δ * ∑ i, |((ν i : ℤ) : ℝ)| by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [← habs]; ring]
          ring
  have key := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum
    (fun i ↦ (x₀ i : UnitAddCircle))
  rw [hg] at key
  convert key using 1
  · funext ν
    rw [hgc ν, mFourier_apply_coe, hc_indep y₁ hy₁ y₀ hz, smul_eq_mul]
    conv_lhs => rw [hz']
    have hs : ∑ i, (ν i : ℂ) * ((x₀ i : ℂ) + I * y₀ i) =
        ∑ i, (ν i : ℂ) * x₀ i + I * ∑ i, (ν i : ℂ) * y₀ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have he : cexp (2 * π * I * ∑ i, (ν i : ℂ) * ((x₀ i : ℂ) + I * y₀ i)) =
        cexp (-(2 * π * ∑ i, (ν i : ℂ) * y₀ i)) * cexp (2 * π * I * ∑ i, (ν i : ℂ) * x₀ i) := by
      rw [← Complex.exp_add, hs]
      congr 1
      ring_nf
      rw [I_sq]
      ring
    rw [he]
    push_cast
    ring
  · rw [← hz']
end _root_.GlobalTheory
end GlobalTheory
