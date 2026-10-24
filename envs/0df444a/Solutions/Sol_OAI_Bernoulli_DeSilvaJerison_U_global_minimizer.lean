-- Prove2me | solution 1 for OAI.Bernoulli.DeSilvaJerison.U_global_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:36:17.382069+00:00
-- url     : https://prove2.me/submissions/5049774d-fffa-4ba5-958c-6fa2dd4dc5b7

import Mathlib
import Definitions.Def_BernoulliNonflatInSeven
import Definitions.Def_OAIQWBNS000
import Theorems.Thm_OAI_Bernoulli_DeSilvaJerison_U_upper_lipschitz_comparison

section
-- module Solutions.OAIQW_BernoulliCone.SobolevCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uE uF uK uι

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace Bernoulli
open scoped _root_.Bernoulli

namespace Test

variable {d : ℕ} {D : Set (Space d)} {φ : Space d → ℝ}

theorem continuous_gradient (hφ : Test D φ) : Continuous (gradient φ) := by
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.comp
    (hφ.1.continuous_fderiv (by simp))

theorem compact_gradient (hφ : Test D φ) : HasCompactSupport (gradient φ) := by
  exact (hφ.2.1.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ (Space d)).symm)

theorem memLp (hφ : Test D φ) : MemLp φ 2 (volume.restrict D) := by
  exact MemLp.mono_measure Measure.restrict_le_self
    (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1)

theorem memLp_gradient (hφ : Test D φ) :
    MemLp (gradient φ) 2 (volume.restrict D) := by
  exact MemLp.mono_measure Measure.restrict_le_self
    (hφ.continuous_gradient.memLp_of_hasCompactSupport hφ.compact_gradient)

theorem eq_zero_outside (hφ : Test D φ) {x : Space d} (hx : x ∉ D) : φ x = 0 := by
  by_contra h
  exact hx (hφ.2.2 (subset_tsupport φ (by exact h)))

theorem weakGradient (hφ : Test D φ) : WeakGradient D φ (gradient φ) := by
  intro ψ hψ h
  have hcφ : Continuous (fun x => (fderiv ℝ φ x) h) := (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcψ : Continuous (fun x => (fderiv ℝ ψ x) h) := (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  simp_rw [inner_gradient_left]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hφ.eq_zero_outside hx, zero_mul])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hψ.eq_zero_outside hx, mul_zero])]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hcφ.mul hψ.1.continuous).integrable_of_hasCompactSupport
      hψ.2.1.mul_left
  · exact (hφ.1.continuous.mul hcψ).integrable_of_hasCompactSupport
      hφ.2.1.mul_right
  · exact (hφ.1.continuous.mul hψ.1.continuous).integrable_of_hasCompactSupport
      hψ.2.1.mul_left
  · exact fun x _ => hφ.1.differentiable (by simp) x
  · exact fun x _ => hψ.1.differentiable (by simp) x

theorem h1 (hφ : Test D φ) : H1 D φ (gradient φ) :=
  ⟨hφ.memLp, hφ.memLp_gradient, hφ.weakGradient⟩

theorem h10 (hφ : Test D φ) : H10 D φ (gradient φ) := by
  refine ⟨hφ.h1, fun ε hε => ⟨φ, hφ, ?_, ?_⟩⟩
  · simpa using (ENNReal.ofReal_pos.mpr hε)
  · simpa using (ENNReal.ofReal_pos.mpr hε)

end Test

section SobolevLinear
variable {d : ℕ} {D : Set (Space d)}
variable {u v : Space d → ℝ} {G V : Space d → Space d}

lemma memLp_inner_const (hG : MemLp G 2 (volume.restrict D)) (h : Space d) :
    MemLp (fun x => inner ℝ (G x) h) 2 (volume.restrict D) := by
  apply hG.of_le_mul (c := ‖h‖) (hG.aestronglyMeasurable.inner aestronglyMeasurable_const)
  exact Filter.Eventually.of_forall (fun x => by
    simpa [mul_comm] using (norm_inner_le_norm (𝕜 := ℝ) (G x) h))

lemma Test.memLp_directional {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    MemLp (fun x => (fderiv ℝ φ x) h) 2 (volume.restrict D) := by
  simpa only [inner_gradient_left] using memLp_inner_const hφ.memLp_gradient h

lemma integrable_deriv_product (hu : MemLp u 2 (volume.restrict D))
    {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    Integrable (fun x => u x * (fderiv ℝ φ x) h) (volume.restrict D) := by
  exact hu.integrable_mul (hφ.memLp_directional h)

lemma integrable_inner_test (hG : MemLp G 2 (volume.restrict D))
    {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    Integrable (fun x => inner ℝ (G x) h * φ x) (volume.restrict D) := by
  exact (memLp_inner_const hG h).integrable_mul hφ.memLp

lemma H1.add (hu : H1 D u G) (hv : H1 D v V) :
    H1 D (fun x => u x + v x) (fun x => G x + V x) := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, ?_⟩
  intro φ hφ h
  simp_rw [add_mul, inner_add_left]
  rw [integral_add (integrable_deriv_product hu.1 hφ h)
      (integrable_deriv_product hv.1 hφ h)]
  simp_rw [add_mul]
  rw [integral_add (integrable_inner_test hu.2.1 hφ h)
      (integrable_inner_test hv.2.1 hφ h), hu.2.2 φ hφ h, hv.2.2 φ hφ h]
  ring

lemma H1.const_smul (hu : H1 D u G) (t : ℝ) :
    H1 D (fun x => t * u x) (fun x => t • G x) := by
  refine ⟨hu.1.const_mul t, hu.2.1.const_smul t, ?_⟩
  intro φ hφ h
  simp_rw [real_inner_smul_left, mul_assoc]
  rw [integral_const_mul, integral_const_mul, hu.2.2 φ hφ h]
  ring

end SobolevLinear

section Variations
variable {d : ℕ} {D : Set (Space d)}

lemma Test.const_mul {φ : Space d → ℝ} (hφ : Test D φ) (t : ℝ) :
    Test D (fun x => t * φ x) := by
  exact ⟨contDiff_const.mul hφ.1, hφ.2.1.mul_left,
    tsupport_mul_subset_right.trans hφ.2.2⟩

lemma Test.gradient_const_mul {φ : Space d → ℝ} (hφ : Test D φ) (t : ℝ) :
    gradient (fun x => t * φ x) = fun x => t • gradient φ x := by
  funext x
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left,
    fderiv_const_mul (hφ.1.differentiable (by simp) x)]
  rfl

lemma Test.h10_const_mul {φ : Space d → ℝ} (hφ : Test D φ) (t : ℝ) :
    H10 D (fun x => t * φ x) (fun x => t • gradient φ x) := by
  rw [← hφ.gradient_const_mul t]
  exact (hφ.const_mul t).h10

lemma integrable_phase {μ : Measure (Space d)} [IsFiniteMeasure μ]
    {u : Space d → ℝ} (hu : AEStronglyMeasurable u μ) :
    Integrable (fun x => if 0 < u x then (1 : ℝ) else 0) μ := by
  have hm : Measurable (fun t : ℝ => if 0 < t then (1 : ℝ) else 0) :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  apply (integrable_const (1 : ℝ)).mono'
    (hm.comp_aemeasurable hu.aemeasurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖(if 0 < u x then (1 : ℝ) else 0)‖ ≤ 1
    split_ifs <;> norm_num)

lemma integrable_inner_of_memLp {μ : Measure (Space d)}
    {G V : Space d → Space d} (hG : MemLp G 2 μ) (hV : MemLp V 2 μ) :
    Integrable (fun x => inner ℝ (G x) (V x)) μ := by
  apply (hG.norm.integrable_mul hV.norm).mono'
    (hG.aestronglyMeasurable.inner hV.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => norm_inner_le_norm (G x) (V x))

end Variations

section GradientUniqueness
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ}
    {G V : Space d → Space d}

/-- The explicit gradient witnesses in the Sobolev definition are unique a.e.
This uses Mathlib's fundamental lemma for compact smooth test functions. -/
lemma H1.gradient_unique (hD : IsOpen D) (hG : H1 D u G) (hV : H1 D u V) :
    G =ᵐ[volume.restrict D] V := by
  have hdir : ∀ h : Space d, ∀ᵐ x ∂volume,
      x ∈ D → inner ℝ (G x - V x) h = 0 := by
    intro h
    apply hD.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    · apply locallyIntegrableOn_of_locallyIntegrable_restrict
      exact (memLp_inner_const (hG.2.1.sub hV.2.1) h).locallyIntegrable (by norm_num)
    · intro φ hφc hφs hφD
      have hφ : Test D φ := ⟨hφc, hφs, hφD⟩
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := D) (fun x hx => by rw [hφ.eq_zero_outside hx, zero_smul])]
      simp only [smul_eq_mul, inner_sub_left, mul_sub]
      have hGi : Integrable (fun x => φ x * inner ℝ (G x) h) (volume.restrict D) := by
        simpa only [mul_comm] using integrable_inner_test hG.2.1 hφ h
      have hVi : Integrable (fun x => φ x * inner ℝ (V x) h) (volume.restrict D) := by
        simpa only [mul_comm] using integrable_inner_test hV.2.1 hφ h
      rw [integral_sub hGi hVi]
      have h1 := hG.2.2 φ hφ h
      have h2 := hV.2.2 φ hφ h
      simp only [mul_comm (φ _)]
      linarith
  apply (ae_restrict_iff' hD.measurableSet).mpr
  have hcoord : ∀ i : Fin d, ∀ᵐ x ∂volume, x ∈ D → G x i = V x i := by
    intro i
    filter_upwards [hdir (EuclideanSpace.single i 1)] with x hx hxD
    have hi := hx hxD
    simpa [EuclideanSpace.inner_single_right, sub_eq_zero] using hi
  filter_upwards [ae_all_iff.mpr hcoord] with x hx hxD
  apply PiLp.ext; intro i
  exact hx i hxD

end GradientUniqueness

section SobolevClosure
variable {d : ℕ} {D : Set (Space d)}

lemma integral_inner_bound {α : Type uα} {E : Type uE} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, inner ℝ (f x) (g x) ∂μ| ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have he : (∫ x, inner ℝ (f x) (g x) ∂μ) =
      inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
  rw [he, ← Lp.norm_toLp f hf, ← Lp.norm_toLp g hg]
  exact abs_real_inner_le_norm _ _

lemma Test.memLp_smul_const {φ : Space d → ℝ} (hφ : Test D φ) (h : Space d) :
    MemLp (fun x => φ x • h) 2 (volume.restrict D) := by
  refine hφ.memLp.of_le_mul (c := ‖h‖)
    (hφ.memLp.aestronglyMeasurable.smul aestronglyMeasurable_const) ?_
  exact ae_of_all _ (fun x => by simp [norm_smul, mul_comm])

/-- Weak H¹ is closed for the actual L² norm on both components. This is
used to zero-extend arbitrary H¹₀ competitors, not just smooth competitors. -/
lemma eq_zero_of_abs_lt {z : ℝ} (h : ∀ ε : ℝ, 0 < ε → |z| < ε) : z = 0 := by
  by_contra hz
  exact lt_irrefl _ (h |z| (abs_pos.mpr hz))

lemma weakGradient_of_approx {u : Space d → ℝ} {G : Space d → Space d}
    (hu : MemLp u 2 (volume.restrict D)) (hG : MemLp G 2 (volume.restrict D))
    (hap : ∀ ε : ℝ, 0 < ε → ∃ v V, H1 D v V ∧
      eLpNorm (fun x => u x-v x) 2 (volume.restrict D) < ENNReal.ofReal ε ∧
      eLpNorm (fun x => G x-V x) 2 (volume.restrict D) < ENNReal.ofReal ε) :
    WeakGradient D u G := by
  intro φ hφ h
  let μ := volume.restrict D
  let ψ := fun x => (fderiv ℝ φ x) h
  let Ψ := fun x => φ x • h
  have hψ : MemLp ψ 2 μ := hφ.memLp_directional h
  have hΨ : MemLp Ψ 2 μ := hφ.memLp_smul_const h
  let C := (eLpNorm ψ 2 μ).toReal + (eLpNorm Ψ 2 μ).toReal + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hz : (∫ x in D, u x * ψ x) + (∫ x in D, inner ℝ (G x) h * φ x) = 0 := by
    apply eq_zero_of_abs_lt
    intro ε hε
    let δ := ε / C
    have hδ : 0 < δ := div_pos hε hC
    obtain ⟨v, V, hv, heu, heG⟩ := hap δ hδ
    have heuto : (eLpNorm (fun x => u x-v x) 2 μ).toReal < δ := by
      exact (ENNReal.toReal_lt_toReal (hu.sub hv.1).eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr
        heu |>.trans_eq (ENNReal.toReal_ofReal hδ.le)
    have heGto : (eLpNorm (fun x => G x-V x) 2 μ).toReal < δ := by
      exact (ENNReal.toReal_lt_toReal (hG.sub hv.2.1).eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr
        heG |>.trans_eq (ENNReal.toReal_ofReal hδ.le)
    have h1 := integral_inner_bound (hu.sub hv.1) hψ
    have h2 := integral_inner_bound (hG.sub hv.2.1) hΨ
    simp only [Real.inner_apply] at h1
    simp only [Ψ, inner_smul_right, mul_comm (φ _)] at h2
    have heq : (∫ x in D, u x * ψ x) + (∫ x in D, inner ℝ (G x) h * φ x) =
        (∫ x in D, (u x-v x)*ψ x) +
          (∫ x in D, inner ℝ (G x-V x) h * φ x) := by
      simp only [sub_mul, inner_sub_left]
      rw [integral_sub (f := fun x => u x * ψ x) (g := fun x => v x * ψ x)
        (hu.integrable_mul hψ) (hv.1.integrable_mul hψ),
        integral_sub (integrable_inner_test hG hφ h) (integrable_inner_test hv.2.1 hφ h)]
      have ht := hv.2.2 φ hφ h
      change (∫ x in D, v x * ψ x) = _ at ht
      linarith
    rw [heq]
    calc
      _ ≤ |∫ x in D, (u x-v x)*ψ x| + |∫ x in D, inner ℝ (G x-V x) h * φ x| := abs_add_le _ _
      _ ≤ (eLpNorm (fun x => u x-v x) 2 μ).toReal * (eLpNorm ψ 2 μ).toReal +
          (eLpNorm (fun x => G x-V x) 2 μ).toReal * (eLpNorm Ψ 2 μ).toReal := add_le_add h1 h2
      _ ≤ δ * (eLpNorm ψ 2 μ).toReal + δ * (eLpNorm Ψ 2 μ).toReal := by
        gcongr
      _ < ε := by
        have hem : δ*C = ε := div_mul_cancel₀ ε hC.ne'
        dsimp [C] at hem
        nlinarith
  linarith

end SobolevClosure

section Localization
variable {d : ℕ} {D E : Set (Space d)}
variable {u v : Space d → ℝ} {G V : Space d → Space d}

lemma WeakGradient.congr (hu : WeakGradient D u G)
    (huv : u =ᵐ[volume.restrict D] v) (hGV : G =ᵐ[volume.restrict D] V) :
    WeakGradient D v V := by
  intro φ hφ h
  have hleft : (∫ x in D, v x * (fderiv ℝ φ x) h) =
      ∫ x in D, u x * (fderiv ℝ φ x) h := by
    apply integral_congr_ae
    filter_upwards [huv] with x hx
    rw [hx]
  have hright : (∫ x in D, inner ℝ (V x) h * φ x) =
      ∫ x in D, inner ℝ (G x) h * φ x := by
    apply integral_congr_ae
    filter_upwards [hGV] with x hx
    rw [hx]
  rw [hleft, hright, hu φ hφ h]

lemma H1.congr (hu : H1 D u G)
    (huv : u =ᵐ[volume.restrict D] v) (hGV : G =ᵐ[volume.restrict D] V) :
    H1 D v V :=
  ⟨hu.1.ae_eq huv, hu.2.1.ae_eq hGV, hu.2.2.congr huv hGV⟩

lemma H10.congr (hu : H10 D u G)
    (huv : u =ᵐ[volume.restrict D] v) (hGV : G =ᵐ[volume.restrict D] V) :
    H10 D v V := by
  refine ⟨hu.1.congr huv hGV, ?_⟩
  intro ε hε
  obtain ⟨φ, hφ, he, heG⟩ := hu.2 ε hε
  refine ⟨φ, hφ, ?_, ?_⟩
  · have heq : (fun x => u x - φ x) =ᵐ[volume.restrict D] (fun x => v x - φ x) :=
      huv.fun_comp (fun z => z) |>.sub (Filter.EventuallyEq.refl _ φ)
    rwa [← eLpNorm_congr_ae heq]
  · have heq : (fun x => G x - gradient φ x) =ᵐ[volume.restrict D]
        (fun x => V x - gradient φ x) := hGV.sub (Filter.EventuallyEq.refl _ (gradient φ))
    rwa [← eLpNorm_congr_ae heq]

lemma Test.fderiv_eq_zero_outside {φ : Space d → ℝ} (hφ : Test D φ)
    {x : Space d} (hx : x ∉ D) : fderiv ℝ φ x = 0 :=
  fderiv_of_notMem_tsupport ℝ (fun h => hx (hφ.2.2 h))

lemma Test.mono {φ : Space d → ℝ} (hφ : Test D φ) (hDE : D ⊆ E) : Test E φ :=
  ⟨hφ.1, hφ.2.1, hφ.2.2.trans hDE⟩

lemma H1.mono (hu : H1 E u G) (hDE : D ⊆ E) : H1 D u G := by
  refine ⟨hu.1.mono_measure (Measure.restrict_mono hDE le_rfl),
    hu.2.1.mono_measure (Measure.restrict_mono hDE le_rfl), ?_⟩
  intro φ hφ h
  have hh := hu.2.2 φ (hφ.mono hDE) h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [(hφ.mono hDE).fderiv_eq_zero_outside hx]; simp),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [(hφ.mono hDE).eq_zero_outside hx, mul_zero])] at hh
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hφ.fderiv_eq_zero_outside hx]; simp),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hφ.eq_zero_outside hx, mul_zero])]
  exact hh

lemma Test.mul {φ ψ : Space d → ℝ} (hφ : Test D φ) (hψ : Test D ψ) :
    Test D (fun x => φ x * ψ x) :=
  ⟨hφ.1.mul hψ.1, hφ.2.1.mul_right, (tsupport_mul_subset_left (f := φ) (g := ψ)).trans hφ.2.2⟩

lemma Test.memLp_top {φ : Space d → ℝ} (hφ : Test D φ) :
    MemLp φ ∞ (volume.restrict D) :=
  (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).mono_measure Measure.restrict_le_self

lemma Test.memLp_gradient_top {φ : Space d → ℝ} (hφ : Test D φ) :
    MemLp (gradient φ) ∞ (volume.restrict D) :=
  (hφ.continuous_gradient.memLp_of_hasCompactSupport hφ.compact_gradient).mono_measure
    Measure.restrict_le_self

lemma Test.gradient_mul {φ ψ : Space d → ℝ} (hφ : Test D φ) (hψ : Test D ψ)
    (x : Space d) : gradient (fun y => φ y * ψ y) x =
      φ x • gradient ψ x + ψ x • gradient φ x := by
  apply (InnerProductSpace.toDual ℝ (Space d)).injective
  ext h
  change inner ℝ (gradient (fun y => φ y * ψ y) x) h =
    inner ℝ (φ x • gradient ψ x + ψ x • gradient φ x) h
  simp only [inner_add_left, real_inner_smul_left, inner_gradient_left]
  have hh := ((hφ.1.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt.mul
    ((hψ.1.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt
  have hh' := hh.fderiv
  change fderiv ℝ (fun y => φ y * ψ y) x = _ at hh'
  rw [hh']
  simp only [add_apply, smul_apply, smul_eq_mul]

lemma energy_congr (huv : u =ᵐ[volume.restrict D] v)
    (hGV : G =ᵐ[volume.restrict D] V) : energy D u G = energy D v V := by
  apply integral_congr_ae
  filter_upwards [huv, hGV] with x hx hGx
  rw [hx, hGx]

lemma Test.gradient_eq_zero_outside {φ : Space d → ℝ} (hφ : Test D φ)
    {x : Space d} (hx : x ∉ D) : gradient φ x = 0 := by
  simp [gradient, hφ.fderiv_eq_zero_outside hx]

/-- Zero extension preserves the exact Sobolev norm of a zero-trace
approximation; neither a smooth representative nor a boundary trace theorem
is assumed. -/
lemma H10.zero_extension (hu : H10 D u G) (hD : MeasurableSet D) (hDE : D ⊆ E) :
    H10 E (D.indicator u) (D.indicator G) := by
  have hres : (volume.restrict E).restrict D = volume.restrict D :=
    Measure.restrict_restrict_of_subset hDE
  have hU : MemLp (D.indicator u) 2 (volume.restrict E) := by
    apply (memLp_indicator_iff_restrict hD).mpr
    rw [hres]
    exact hu.1.1
  have hW : MemLp (D.indicator G) 2 (volume.restrict E) := by
    apply (memLp_indicator_iff_restrict hD).mpr
    rw [hres]
    exact hu.1.2.1
  have hap (ε : ℝ) (hε : 0 < ε) : ∃ φ : Space d → ℝ, Test E φ ∧
      eLpNorm (fun x => D.indicator u x - φ x) 2 (volume.restrict E) < ENNReal.ofReal ε ∧
      eLpNorm (fun x => D.indicator G x - gradient φ x) 2 (volume.restrict E) < ENNReal.ofReal ε := by
    obtain ⟨φ, hφ, hUφ, hGφ⟩ := hu.2 ε hε
    refine ⟨φ, hφ.mono hDE, ?_, ?_⟩
    · have heq : (fun x => D.indicator u x - φ x) = D.indicator (fun x => u x - φ x) := by
        funext x
        by_cases hx : x ∈ D
        · simp [hx]
        · simp [hx, hφ.eq_zero_outside hx]
      rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict hD, hres]
      exact hUφ
    · have heq : (fun x => D.indicator G x - gradient φ x) =
          D.indicator (fun x => G x - gradient φ x) := by
        funext x
        by_cases hx : x ∈ D
        · simp [hx]
        · simp [hx, hφ.gradient_eq_zero_outside hx]
      rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict hD, hres]
      exact hGφ
  refine ⟨⟨hU, hW, weakGradient_of_approx hU hW ?_⟩, hap⟩
  intro ε hε
  obtain ⟨φ, hφ, hUφ, hGφ⟩ := hap ε hε
  exact ⟨φ, gradient φ, hφ.h1, hUφ, hGφ⟩

lemma eLpNorm_sub_lt_of_two {α : Type uα} {F : Type uF} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f g h : α → F}
    (_hf : MemLp f 2 μ) (_hg : MemLp g 2 μ) (_hh : MemLp h 2 μ)
    {ε : ℝ} (hε : 0 < ε)
    (hfg : eLpNorm (fun x => f x - g x) 2 μ < ENNReal.ofReal (ε / 2))
    (hgh : eLpNorm (fun x => g x - h x) 2 μ < ENNReal.ofReal (ε / 2)) :
    eLpNorm (fun x => f x - h x) 2 μ < ENNReal.ofReal ε := by
  have heq : (fun x => f x - h x) =
      (fun x => f x - g x) + (fun x => g x - h x) := by
    funext x
    simp
  rw [heq]
  calc
    _ ≤ eLpNorm (fun x => f x - g x) 2 μ +
        eLpNorm (fun x => g x - h x) 2 μ :=
      eLpNorm_add_le (_hf.sub _hg).aestronglyMeasurable (_hg.sub _hh).aestronglyMeasurable (by norm_num)
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hfg hgh
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

lemma H10.of_approx (hu : MemLp u 2 (volume.restrict D))
    (hG : MemLp G 2 (volume.restrict D))
    (hap : ∀ ε : ℝ, 0 < ε → ∃ v V, H10 D v V ∧
      eLpNorm (fun x => u x - v x) 2 (volume.restrict D) < ENNReal.ofReal ε ∧
      eLpNorm (fun x => G x - V x) 2 (volume.restrict D) < ENNReal.ofReal ε) :
    H10 D u G := by
  refine ⟨⟨hu, hG, weakGradient_of_approx hu hG ?_⟩, ?_⟩
  · intro ε hε
    obtain ⟨v, V, hv, hvu, hVG⟩ := hap ε hε
    exact ⟨v, V, hv.1, hvu, hVG⟩
  · intro ε hε
    obtain ⟨v, V, hv, hvu, hVG⟩ := hap (ε / 2) (by positivity)
    obtain ⟨φ, hφ, hvφ, hVφ⟩ := hv.2 (ε / 2) (by positivity)
    exact ⟨φ, hφ, eLpNorm_sub_lt_of_two hu hv.1.1 hφ.memLp hε hvu hvφ,
      eLpNorm_sub_lt_of_two hG hv.1.2.1 hφ.memLp_gradient hε hVG hVφ⟩

lemma eLpNorm_two_eq_eLpNorm' {α : Type uα} {F : Type uF} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F}
    (hf : AEStronglyMeasurable f μ) : eLpNorm f 2 μ = eLpNorm' f 2 μ := by
  simpa using eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num)

end Localization
end Bernoulli

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Convolution

namespace Bernoulli.Mollification
open scoped _root_.Bernoulli

variable {d : ℕ}
variable {F : Type uF} [NormedAddCommGroup F]

lemma continuous_translate (f : Lp F 2 (volume : Measure (Space d))) :
    Continuous (translate f) := by
  let shifts : Space d → C(Space d, Space d) :=
    fun y => ⟨fun x => x - y, continuous_id.sub continuous_const⟩
  have hc : Continuous shifts := ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hc
    (fun y => measurePreserving_sub_right volume y) (by norm_num)

lemma coeFn_translate (f : Lp F 2 (volume : Measure (Space d))) (y : Space d) :
    translate f y =ᵐ[volume] fun x => f (x - y) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume y)

@[simp] lemma translate_zero (f : Lp F 2 (volume : Measure (Space d))) :
    translate f 0 = f := by
  apply Lp.ext
  simpa using coeFn_translate f 0

section Inner
variable [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma integrable_inner_of_memLp {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {f g : α → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  exact (hf.norm.integrable_mul hg.norm).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (ae_of_all _ fun x => norm_inner_le_norm (f x) (g x))

lemma integral_inner_bound {α : Type uα} {K : Type uK} [MeasurableSpace α]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    {μ : Measure α} {f g : α → K} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, inner ℝ (f x) (g x) ∂μ| ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have he : (∫ x, inner ℝ (f x) (g x) ∂μ) =
      inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
  rw [he, ← Lp.norm_toLp f hf, ← Lp.norm_toLp g hg]
  exact abs_real_inner_le_norm _ _

omit [CompleteSpace F] in
lemma integral_norm_inner_bound {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {f g : α → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖inner ℝ (f x) (g x)‖ ∂μ) ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  calc
    _ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ :=
      integral_mono (integrable_inner_of_memLp hf hg).norm (hf.norm.integrable_mul hg.norm)
        (fun x => norm_inner_le_norm (f x) (g x))
    _ ≤ |∫ x, ‖f x‖ * ‖g x‖ ∂μ| := le_abs_self _
    _ ≤ _ := by
      simpa only [Real.inner_apply, eLpNorm_norm _,
        eLpNorm_norm _] using integral_inner_bound hf.norm hg.norm

omit [CompleteSpace F] in
/-- The Fubini integrability needed to compare a pointwise convolution with
its Bochner integral in L². The testing function is arbitrary L². -/
lemma integrable_convolution_inner {κ : Space d → ℝ} {f g : Space d → F}
    (hκ : Integrable κ volume) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun p : Space d × Space d =>
      inner ℝ (κ p.2 • f (p.1 - p.2)) (g p.1)) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : Space d × Space d =>
      inner ℝ (κ p.2 • f (p.1 - p.2)) (g p.1)) (volume.prod volume) :=
    (hκ.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
      hf.aestronglyMeasurable).inner
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  rw [integrable_prod_iff' hmeas]
  have hft (y : Space d) : MemLp (fun x => f (x - y)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_sub_right volume y)
  refine ⟨ae_of_all _ fun y => ?_, ?_⟩
  · simpa only [real_inner_smul_left] using
      (integrable_inner_of_memLp (hft y) hg).const_mul (κ y)
  · have hm : AEStronglyMeasurable (fun y : Space d =>
        ∫ x : Space d, ‖inner ℝ (κ y • f (x - y)) (g x)‖) volume :=
      hmeas.prod_swap.norm.integral_prod_right'
    apply Integrable.mono' (hκ.norm.mul_const
      ((eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal)) hm
    apply ae_of_all
    intro y
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    simp_rw [real_inner_smul_left, norm_mul, integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hi := integral_norm_inner_bound (hft y) hg
    have heq : eLpNorm (fun x => f (x - y)) 2 volume = eLpNorm f 2 volume :=
      eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (measurePreserving_sub_right volume y)
    rwa [heq] at hi

/-- A pointwise mollification is the same element of L² as the Bochner
average of translates. This proof includes the Fubini and representative bridge. -/
lemma convolution_toLp_eq_integral_translate {κ : Space d → ℝ} {f : Space d → F}
    (hκ : Continuous κ) (hcκ : HasCompactSupport κ)
    (hf : MemLp f 2 volume) (hcf : HasCompactSupport f) :
    (memLp_convolution hκ hcκ hf hcf).toLp
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) =
      ∫ y, κ y • translate (hf.toLp f) y := by
  have hiκ : Integrable κ volume := hκ.integrable_of_hasCompactSupport hcκ
  have hLpInt : Integrable (fun y => κ y • translate (hf.toLp f) y) volume :=
    (hκ.smul (continuous_translate (hf.toLp f))).integrable_of_hasCompactSupport hcκ.smul_right
  have hce := hcκ.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ
    (hf.locallyIntegrable (by norm_num))
  apply ext_inner_left ℝ
  intro g
  rw [← integral_inner hLpInt g]
  have htrans (y : Space d) : inner ℝ g (translate (hf.toLp f) y) =
      ∫ x, inner ℝ (g x) (f (x - y)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_translate (hf.toLp f) y,
      (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp]
      with x hx hy
    rw [hx]
    exact congrArg (inner ℝ (g x)) hy
  have hFubini : Integrable (fun p : Space d × Space d =>
      inner ℝ (g p.1) (κ p.2 • f (p.1 - p.2))) (volume.prod volume) := by
    simpa only [real_inner_comm] using integrable_convolution_inner hiκ hf (Lp.memLp g)
  calc
    _ = ∫ x, inner ℝ (g x) ((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(memLp_convolution hκ hcκ hf hcf).coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, ∫ y, inner ℝ (g x) (κ y • f (x - y)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => (integral_inner (hce x) (g x)).symm
    _ = ∫ y, ∫ x, inner ℝ (g x) (κ y • f (x - y)) :=
      integral_integral_swap hFubini
    _ = ∫ y, inner ℝ g (κ y • translate (hf.toLp f) y) := by
      apply integral_congr_ae
      apply ae_of_all
      intro y
      simp_rw [real_inner_smul_right, integral_const_mul, htrans]

/-- L² convergence of compactly supported mollifications. It applies at
once to the function and its weak gradient, once the weak derivative identity
has been proved. -/
lemma convolution_toLp_tendsto {ι : Type uι} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : Space d)} {f : Space d → F}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hf : MemLp f 2 volume) (hcf : HasCompactSupport f) :
    Tendsto (fun i => (memLp_convolution (φ i).continuous_normed
      (φ i).hasCompactSupport_normed hf hcf).toLp
        ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)) l
      (𝓝 (hf.toLp f)) := by
  have hc : Continuous (fun y : Space d => translate (hf.toLp f) (-y)) :=
    (continuous_translate (hf.toLp f)).comp continuous_neg
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hc 0
  have heq (i : ι) :
      (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => translate (hf.toLp f) (-y))) 0) =
        (memLp_convolution (φ i).continuous_normed (φ i).hasCompactSupport_normed hf hcf).toLp
          ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
    rw [convolution_toLp_eq_integral_translate (φ i).continuous_normed
      (φ i).hasCompactSupport_normed hf hcf]
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub, neg_neg]
  simpa only [heq, neg_zero, translate_zero] using ht

lemma eLpNorm_convolution_sub_tendsto {ι : Type uι} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : Space d)} {f : Space d → F}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hf : MemLp f 2 volume) (hcf : HasCompactSupport f) :
    Tendsto (fun i => eLpNorm
      (fun x => ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x)
      2 volume) l (𝓝 0) := by
  have ht := ((convolution_toLp_tendsto hφ hf hcf).sub
    (tendsto_const_nhds (x := hf.toLp f))).enorm
  have heq (i : ι) :
      ‖(memLp_convolution (φ i).continuous_normed (φ i).hasCompactSupport_normed hf hcf).toLp
        ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - hf.toLp f‖ₑ =
      eLpNorm
        (fun x => ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x)
        2 volume := by
    rw [← MemLp.toLp_sub, Lp.enorm_toLp]
    rfl
  simpa only [heq, sub_self, enorm_zero] using ht

end Inner

end Bernoulli.Mollification

namespace Bernoulli.SobolevDensity
open scoped _root_.Bernoulli
open scoped Convolution
variable {d : ℕ}

lemma test_reflected {κ : Space d → ℝ} (hκ : Test univ κ) (x : Space d) :
    Test univ (fun y => κ (x - y)) := by
  refine ⟨hκ.1.comp (contDiff_const.sub contDiff_id), ?_, subset_univ _⟩
  exact hκ.2.1.comp_homeomorph (Homeomorph.subLeft x)

lemma fderiv_reflected {κ : Space d → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (x y h : Space d) :
    fderiv ℝ (fun z => κ (x - z)) y h = -(fderiv ℝ κ (x - y) h) := by
  have hd := (hκ.differentiable (by simp) (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_sub x)
  change HasFDerivAt (fun z => κ (x - z)) _ y at hd
  rw [hd.fderiv]
  simp

lemma gradient_convolution {κ u : Space d → ℝ} {G : Space d → Space d}
    (hκ : Test univ κ) (hu : H1 univ u G) (x : Space d) :
    gradient (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x := by
  have hfu : MemLp u 2 volume := by simpa using hu.1
  have hfG : MemLp G 2 volume := by simpa using hu.2.1
  have hlocu : LocallyIntegrable u volume := hfu.locallyIntegrable (by norm_num)
  have hlocG : LocallyIntegrable G volume := hfG.locallyIntegrable (by norm_num)
  have hκ₁ : ContDiff ℝ 1 κ := hκ.1.of_le (by simp)
  have hder := hκ.2.1.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hlocu hκ₁ x
  have heq : u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] κ =
      κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := convolution_flip _
  rw [heq] at hder
  apply ext_inner_right ℝ
  intro h
  rw [inner_gradient_left, hder.fderiv,
    convolution_precompR_apply _ hlocu (hκ.2.1.fderiv ℝ)
      (hκ.1.continuous_fderiv (by simp))]
  have hw := hu.2.2 _ (test_reflected hκ x) h
  simp only [Measure.restrict_univ, fderiv_reflected hκ.1, mul_neg,
    integral_neg] at hw
  have hw' := neg_injective hw
  rw [convolution_lsmul_swap, real_inner_comm]
  have hi := hκ.2.1.convolutionExists_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hlocG hκ.1.continuous x
  have hi' : Integrable (fun y => κ (x - y) • G y) volume := hi
  rw [← integral_inner hi']
  simp only [convolution_def, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  calc
    _ = ∫ y, u y * fderiv ℝ κ (x - y) h := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => mul_comm _ _
    _ = ∫ y, inner ℝ (G y) h * κ (x - y) := hw'
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        dsimp only
        rw [real_inner_smul_right, real_inner_comm]
        ring

open scoped Pointwise

lemma tsupport_convolution_subset {κ : Space d → ℝ} {u : Space d → ℝ}
    (hκ : HasCompactSupport κ) (hu : HasCompactSupport u) :
    tsupport (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) ⊆ tsupport κ + tsupport u := by
  apply closure_minimal
  · exact (support_convolution_subset _).trans
      (Set.add_subset_add (subset_tsupport κ) (subset_tsupport u))
  · exact (hκ.isCompact.add hu.isCompact).isClosed

lemma tsupport_mollification_subset {u : Space d → ℝ} (hu : HasCompactSupport u)
    (φ : ContDiffBump (0 : Space d)) {δ : ℝ} (hδ : φ.rOut < δ) :
    tsupport (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) ⊆
      Metric.thickening δ (tsupport u) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := tsupport_convolution_subset φ.hasCompactSupport_normed hu hx
  rw [φ.tsupport_normed_eq, mem_closedBall_zero_iff] at ha
  apply Metric.mem_thickening_iff.mpr
  refine ⟨b, hb, ?_⟩
  simpa [dist_eq_norm] using ha.trans_lt hδ

lemma bumps_tendsto (d : ℕ) : Tendsto (fun n => (bumps d n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Simultaneous weak-H¹ mollification, including support inside the open
set. The gradient convergence is proved, not demanded of the approximants. -/
lemma h10_of_compact_support {D : Set (Space d)} (hD : IsOpen D)
    {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 univ u G) (hcu : HasCompactSupport u) (hcG : HasCompactSupport G)
    (hsu : tsupport u ⊆ D) : H10 D u G := by
  have huD : H1 D u G := hu.mono (subset_univ D)
  refine ⟨huD, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδD⟩ := hcu.isCompact.exists_thickening_subset_open hD hsu
  have hfu : MemLp u 2 volume := by simpa using hu.1
  have hfG : MemLp G 2 volume := by simpa using hu.2.1
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have htu := Mollification.eLpNorm_convolution_sub_tendsto (bumps_tendsto d) hfu hcu
  have htG := Mollification.eLpNorm_convolution_sub_tendsto (bumps_tendsto d) hfG hcG
  have hst : ∀ᶠ n : ℕ in atTop,
      (bumps d n).rOut < δ ∧
      eLpNorm (fun x => ((bumps d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x)
        2 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun x => ((bumps d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x - G x)
        2 volume < ENNReal.ofReal ε := by
    exact ((bumps_tendsto d).eventually_lt_const hδ).and
      ((htu.eventually_lt_const hε').and (htG.eventually_lt_const hε'))
  obtain ⟨n, hnδ, hnu, hnG⟩ := hst.exists
  let κ := (bumps d n).normed volume
  have hκ : Test univ κ :=
    ⟨(bumps d n).contDiff_normed, (bumps d n).hasCompactSupport_normed, subset_univ _⟩
  have hφ : Test D (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) := by
    refine ⟨hκ.2.1.contDiff_convolution_left _ hκ.1 (hfu.locallyIntegrable (by norm_num)),
      hκ.2.1.convolution _ hcu, ?_⟩
    exact (tsupport_mollification_subset hcu (bumps d n) hnδ).trans hδD
  refine ⟨_, hφ, ?_, ?_⟩
  · apply lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self)
    change eLpNorm (u - (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)) 2 volume < _
    rw [eLpNorm_sub_comm]
    exact hnu
  · simp_rw [gradient_convolution hκ hu]
    apply lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self)
    change eLpNorm (G - (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G)) 2 volume < _
    rw [eLpNorm_sub_comm]
    exact hnG

end Bernoulli.SobolevDensity

namespace Bernoulli.SobolevDensity
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}

lemma memLp_global_of_zero_outside {F : Type uF} [NormedAddCommGroup F]
    {f : Space d → F} (hD : MeasurableSet D) (hf : MemLp f 2 (volume.restrict D))
    (hz : ∀ x ∉ D, f x = 0) : MemLp f 2 volume := by
  have heq : D.indicator f = f := by
    funext x
    by_cases hx : x ∈ D
    · simp [hx]
    · simp [hx, hz x hx]
  rw [← heq]
  exact (memLp_indicator_iff_restrict hD).mpr hf

/-- A compactly supported smooth cutoff of a local weak H¹ function is a
whole-space weak H¹ function, with the actual product-rule gradient. -/
lemma h1_mul_test_global {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 D u G) (hD : MeasurableSet D)
    {φ : Space d → ℝ} (hφ : Test D φ) :
    H1 univ (fun x => φ x * u x)
      (fun x => φ x • G x + u x • gradient φ x) := by
  have hφU := hφ.mono (subset_univ D)
  have hzφ (x : Space d) (hx : x ∉ D) : φ x = 0 := hφ.eq_zero_outside hx
  have hzg (x : Space d) (hx : x ∉ D) : gradient φ x = 0 := hφ.gradient_eq_zero_outside hx
  have hum : MemLp (fun x => φ x * u x) 2 volume :=
    memLp_global_of_zero_outside hD (hu.1.mul' hφ.memLp_top)
      (fun x hx => by rw [hzφ x hx, zero_mul])
  have hGm : MemLp (fun x => φ x • G x) 2 volume :=
    memLp_global_of_zero_outside hD (hu.2.1.smul hφ.memLp_top)
      (fun x hx => by rw [hzφ x hx, zero_smul])
  have hgm : MemLp (fun x => u x • gradient φ x) 2 volume :=
    memLp_global_of_zero_outside hD (hφ.memLp_gradient_top.smul hu.1)
      (fun x hx => by rw [hzg x hx, smul_zero])
  refine ⟨by simpa using hum, by rw [Measure.restrict_univ]; exact hGm.add hgm, ?_⟩
  intro ψ hψ h
  have hφψ : Test D (fun x => φ x * ψ x) :=
    ⟨hφ.1.mul hψ.1, hφ.2.1.mul_right,
      (tsupport_mul_subset_left (f := φ) (g := ψ)).trans hφ.2.2⟩
  have hi := integrable_deriv_product (D := univ) (by simpa using hum) hψ h
  have hij := integrable_inner_test (D := univ) (by simpa using hgm) hψ h
  have hik := integrable_inner_test (D := univ) (by simpa using hGm) hψ h
  simp only [Measure.restrict_univ, real_inner_smul_left, inner_gradient_left] at hi hij hik
  have hderiv (x : Space d) :
      u x * (fderiv ℝ (fun y => φ y * ψ y) x) h =
        (φ x * u x) * (fderiv ℝ ψ x) h + (u x * (fderiv ℝ φ x) h) * ψ x := by
    rw [← inner_gradient_left, hφU.gradient_mul hψ,
      inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_gradient_left, inner_gradient_left]
    ring
  have hweak := hu.2.2 _ hφψ h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hφψ.fderiv_eq_zero_outside hx]; simp),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hφψ.eq_zero_outside hx, mul_zero])] at hweak
  simp_rw [hderiv] at hweak
  rw [integral_add hi hij] at hweak
  have hright (x : Space d) : inner ℝ (G x) h * (φ x * ψ x) =
      (φ x * inner ℝ (G x) h) * ψ x := by ring
  simp_rw [hright] at hweak
  simp only [Measure.restrict_univ, inner_add_left, real_inner_smul_left,
    inner_gradient_left, add_mul]
  rw [integral_add hik hij]
  linarith

lemma h10_mul_test {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 D u G) (hD : IsOpen D) {φ : Space d → ℝ} (hφ : Test D φ) :
    H10 D (fun x => φ x * u x)
      (fun x => φ x • G x + u x • gradient φ x) := by
  have hcu : HasCompactSupport (fun x => φ x * u x) := hφ.2.1.mul_right
  have hφs : Test (tsupport φ) φ := ⟨hφ.1, hφ.2.1, subset_rfl⟩
  have hcG : HasCompactSupport (fun x => φ x • G x + u x • gradient φ x) := by
    apply HasCompactSupport.intro hφ.2.1.isCompact
    intro x hx
    rw [hφs.eq_zero_outside hx, hφs.gradient_eq_zero_outside hx]
    simp
  have hsu : tsupport (fun x => φ x * u x) ⊆ D :=
    (tsupport_mul_subset_left (f := φ) (g := u)).trans hφ.2.2
  exact h10_of_compact_support hD (h1_mul_test_global hu hD.measurableSet hφ) hcu hcG hsu

end Bernoulli.SobolevDensity

namespace Bernoulli
open scoped _root_.Bernoulli
namespace LipschitzSobolev
variable {d : ℕ} {u : Space d → ℝ} {K : NNReal}

lemma measurable_gradient : Measurable (gradient u) := by
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ u)

lemma norm_gradient_le (hu : LipschitzWith K u) (x : Space d) :
    ‖gradient u x‖ ≤ K := by
  simpa only [gradient, LinearIsometryEquiv.norm_map] using
    norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hu

lemma weakGradient (hu : LipschitzWith K u) (D : Set (Space d)) :
    WeakGradient D u (gradient u) := by
  intro φ hφ h
  have hφdiff := hφ.1.differentiable (by simp)
  obtain ⟨C, hφlip⟩ := hφ.1.lipschitzWith_of_hasCompactSupport hφ.2.1 (by simp)
  have heq := hu.integral_lineDeriv_mul_eq (μ := volume) hφlip hφ.2.1 h
  have hleft : (fun x => lineDeriv ℝ u x h * φ x) =ᵐ[volume]
      (fun x => inner ℝ (gradient u x) h * φ x) := by
    filter_upwards [hu.ae_differentiableAt] with x hx
    rw [hx.lineDeriv_eq_fderiv, inner_gradient_left]
  have hright : (fun x => lineDeriv ℝ φ x (-h) * u x) =
      (fun x => -(u x * (fderiv ℝ φ x) h)) := by
    funext x
    rw [(hφdiff x).lineDeriv_eq_fderiv, map_neg]
    ring
  rw [integral_congr_ae hleft, hright, integral_neg] at heq
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hne : x ∉ tsupport φ := fun hx' => hx (hφ.2.2 hx')
      rw [fderiv_of_notMem_tsupport ℝ hne, zero_apply, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [hφ.eq_zero_outside hx, mul_zero])]
  linarith

lemma h1_ball (hu : LipschitzWith K u) (c : Space d) (r : ℝ) :
    H1 (Metric.ball c r) u (gradient u) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  refine ⟨?_, ?_, weakGradient hu _⟩
  · apply MemLp.of_bound hu.continuous.aestronglyMeasurable (‖u c‖ + K * max r 0)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    calc ‖u x‖ ≤ ‖u c‖ + ‖u x - u c‖ := norm_le_insert' _ _
      _ ≤ ‖u c‖ + K * dist x c := by
        gcongr
        simpa only [dist_eq_norm] using hu.norm_sub_le x c
      _ ≤ ‖u c‖ + K * max r 0 := by
        gcongr
        exact (Metric.mem_ball.mp hx).le.trans (le_max_left _ _)
  · exact MemLp.of_bound measurable_gradient.aestronglyMeasurable K
      (Filter.Eventually.of_forall (norm_gradient_le hu))

lemma compact_gradient (hc : HasCompactSupport u) : HasCompactSupport (gradient u) := by
  exact (hc.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ (Space d)).symm)

lemma h1_compact (hu : LipschitzWith K u) (hc : HasCompactSupport u) :
    H1 univ u (gradient u) := by
  refine ⟨by simpa using hu.continuous.memLp_of_hasCompactSupport (p := 2) hc, ?_,
    weakGradient hu _⟩
  rw [Measure.restrict_univ]
  have hzero (x : Space d) (hx : x ∉ tsupport u) : gradient u x = 0 := by
    rw [gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero]
  let : IsFiniteMeasure (volume.restrict (tsupport u)) :=
    isFiniteMeasure_restrict.mpr hc.isCompact.measure_lt_top.ne
  have hmem : MemLp (gradient u) 2 (volume.restrict (tsupport u)) :=
    MemLp.of_bound measurable_gradient.aestronglyMeasurable K
      (Filter.Eventually.of_forall (norm_gradient_le hu))
  have heq : (tsupport u).indicator (gradient u) = gradient u := by
    funext x
    by_cases hx : x ∈ tsupport u
    · simp [hx]
    · simp [hx, hzero x hx]
  rw [← heq]
  exact (memLp_indicator_iff_restrict (isClosed_tsupport u).measurableSet).mpr hmem

end LipschitzSobolev
end Bernoulli

namespace Bernoulli
open scoped _root_.Bernoulli

lemma H1.sub {d : ℕ} {D : Set (Space d)} {u v : Space d → ℝ}
    {G V : Space d → Space d} (hu : H1 D u G) (hv : H1 D v V) :
    H1 D (fun x => u x - v x) (fun x => G x - V x) := by
  simpa only [neg_one_mul, neg_one_smul, sub_eq_add_neg] using hu.add (hv.const_smul (-1))

lemma LipschitzSobolev.h10 {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ}
    {K : NNReal} (hu : LipschitzWith K u) (hc : HasCompactSupport u)
    (hD : IsOpen D) (hs : tsupport u ⊆ D) : H10 D u (gradient u) :=
  SobolevDensity.h10_of_compact_support hD (LipschitzSobolev.h1_compact hu hc) hc
    (LipschitzSobolev.compact_gradient hc) hs

end Bernoulli

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}

/-- The closure definition itself provides smooth approximants converging
  simultaneously in both L² seminorms. -/
lemma H10_sequence (hu : H10 D u G) :
    ∃ f : ℕ → Space d → ℝ, (∀ n, Test D (f n)) ∧
      Tendsto (fun n => eLpNorm (f n - u) 2 (volume.restrict D)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (gradient (f n) - G) 2 (volume.restrict D)) atTop (𝓝 0) := by
  choose f hf hfu hfG using fun n : ℕ => hu.2 (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨f, hf, ?_, ?_⟩
  · have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [ENNReal.ofReal_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
    intro n
    dsimp only [Function.comp_apply]
    rw [eLpNorm_sub_comm]
    exact (hfu n).le
  · have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [ENNReal.ofReal_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
    intro n
    dsimp only [Function.comp_apply]
    rw [eLpNorm_sub_comm]
    exact (hfG n).le

lemma gradient_comp {F : ℝ → ℝ} {f : Space d → ℝ} {x : Space d}
    (hF : DifferentiableAt ℝ F (f x)) (hf : DifferentiableAt ℝ f x) :
    gradient (F ∘ f) x = deriv F (f x) • gradient f x := by
  apply ext_inner_right ℝ
  intro h
  rw [inner_gradient_left, fderiv_comp x hF hf, ContinuousLinearMap.comp_apply,
    fderiv_eq_deriv_mul, real_inner_smul_left, inner_gradient_left]

section Dominated
variable {α : Type uα} {E : Type uE} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E]

/-- L² dominated convergence, expressed in the same seminorms as `H10`. -/
lemma tendsto_eLpNorm_zero_of_dominated {f : ℕ → α → E} {b : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hb : MemLp b 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖b x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : MemLp (f n) 2 μ := hb.mono (hf n) (hbound n)
  have hi : Tendsto (fun n => ∫ x, ‖f n x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
      (fun x => ‖b x‖ ^ 2)
      (fun n => (hf n).norm.pow 2) (hb.integrable_norm_pow (by norm_num)) ?_ ?_
    · simpa using ht
    · intro n
      filter_upwards [hbound n] with x hx
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) hx 2
    · filter_upwards [hlim] with x hx
      simpa using hx.norm.pow 2
  have heq (n : ℕ) : eLpNorm (f n) 2 μ =
      ENNReal.ofReal ((∫ x, ‖f n x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
    simpa using (hm n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  simp_rw [heq]
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hi.rpow_const (Or.inr (by norm_num : 0 ≤ (1 / 2 : ℝ))))
  convert! ht using 1
  simp

end Dominated
end Bernoulli.SobolevCalculus

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}

lemma test_comp_h10 (hD : IsOpen D) {F : ℝ → ℝ} {K : NNReal} {f : Space d → ℝ}
    (hF : ContDiff ℝ 1 F) (hlip : LipschitzWith K F) (hz : F 0 = 0)
    (hf : Test D f) : H10 D (F ∘ f) (fun x => deriv F (f x) • gradient f x) := by
  obtain ⟨L, hL⟩ := hf.1.lipschitzWith_of_hasCompactSupport hf.2.1 (by simp)
  have hm := LipschitzSobolev.h10 (hlip.comp hL) (hf.2.1.comp_left hz) hD
    ((tsupport_comp_subset hz f).trans hf.2.2)
  have heq : gradient (F ∘ f) = fun x => deriv F (f x) • gradient f x := by
    funext x
    exact gradient_comp (hF.differentiable (by simp) _) (hf.1.differentiable (by simp) _)
  rwa [heq] at hm

lemma h10_of_strong {f : ℕ → Space d → ℝ} {V : ℕ → Space d → Space d}
    (hu : MemLp u 2 (volume.restrict D)) (hG : MemLp G 2 (volume.restrict D))
    (hf : ∀ n, H10 D (f n) (V n))
    (hfu : Tendsto (fun n => eLpNorm (f n - u) 2 (volume.restrict D)) atTop (𝓝 0))
    (hfG : Tendsto (fun n => eLpNorm (V n - G) 2 (volume.restrict D)) atTop (𝓝 0)) :
    H10 D u G := by
  apply H10.of_approx hu hG
  intro ε hε
  have hp : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  obtain ⟨n, hn, hn'⟩ := ((hfu.eventually_lt_const hp).and (hfG.eventually_lt_const hp)).exists
  refine ⟨f n, V n, hf n, ?_, ?_⟩
  · change eLpNorm (u - f n) 2 (volume.restrict D) < ENNReal.ofReal ε
    rwa [eLpNorm_sub_comm]
  · change eLpNorm (G - V n) 2 (volume.restrict D) < ENNReal.ofReal ε
    rwa [eLpNorm_sub_comm]

section Nemytskii
variable {α : Type uα} {E : Type uE} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma lipschitz_tendsto_eLpNorm {f : ℕ → α → ℝ} {u : α → ℝ}
    {F : ℝ → ℝ} {K : NNReal} (hF : LipschitzWith K F)
    (hu : Tendsto (fun n => eLpNorm' (f n - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm' (F ∘ f n - F ∘ u) 2 μ) atTop (𝓝 0) := by
  have ht := ENNReal.Tendsto.const_mul (a := (K : ℝ≥0∞)) hu (Or.inr ENNReal.coe_ne_top)
  simp only [mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have hbound := eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul
    (μ := μ) (f := F ∘ f n - F ∘ u) (g := f n - u) (c := K) (p := 2)
    (Filter.Eventually.of_forall fun x => by exact_mod_cast hF.norm_sub_le (f n x) (u x))
    (by norm_num)
  exact hbound

lemma lipschitz_tendsto_eLpNorm_of_aestronglyMeasurable {f : ℕ → α → ℝ} {u : α → ℝ}
    {F : ℝ → ℝ} {K : NNReal} (hF : LipschitzWith K F)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hu_meas : AEStronglyMeasurable u μ)
    (hu : Tendsto (fun n => eLpNorm (f n - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F ∘ f n - F ∘ u) 2 μ) atTop (𝓝 0) := by
  have hu_raw : Tendsto (fun n => eLpNorm' (f n - u) 2 μ) atTop (𝓝 0) :=
    hu.congr' (Eventually.of_forall fun n => eLpNorm_two_eq_eLpNorm' ((hf n).sub hu_meas))
  apply (lipschitz_tendsto_eLpNorm hF hu_raw).congr'
  exact Eventually.of_forall fun n => (eLpNorm_two_eq_eLpNorm'
    ((hF.continuous.comp_aestronglyMeasurable (hf n)).sub
      (hF.continuous.comp_aestronglyMeasurable hu_meas))).symm

lemma bounded_smul_tendsto {a : ℕ → α → ℝ} {b : α → ℝ} {G : α → E} {C : ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    (hG : MemLp G 2 μ) (hC : 0 ≤ C)
    (hab : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C) (hbb : ∀ᵐ x ∂μ, ‖b x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x))) :
    Tendsto (fun n => eLpNorm (fun x => (a n x-b x) • G x) 2 μ) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_zero_of_dominated (f := fun n x => (a n x - b x) • G x)
    (fun n => ((ha n).sub hb).smul hG.aestronglyMeasurable)
    (hG.norm.const_smul (2*C))
  · intro n
    filter_upwards [hab n, hbb] with x hx hy
    simp only [Pi.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : 0 ≤ 2*C)]
    have hab' : ‖a n x - b x‖ ≤ 2*C := (norm_sub_le _ _).trans (by linarith)
    exact mul_le_mul_of_nonneg_right hab' (norm_nonneg _)
  · filter_upwards [ht] with x hx
    simpa using (hx.sub_const (b x)).smul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => G x) atTop (𝓝 (G x)))

end Nemytskii
end Bernoulli.SobolevCalculus

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
section Nemytskii
variable {α : Type uα} {E : Type uE} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bounded_smul_strong {a : ℕ → α → ℝ} {b : α → ℝ}
    {V : ℕ → α → E} {G : α → E} {C : ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    (hV : ∀ n, MemLp (V n) 2 μ) (hG : MemLp G 2 μ) (hC : 0 ≤ C)
    (hab : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C) (hbb : ∀ᵐ x ∂μ, ‖b x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (hVG : Tendsto (fun n => eLpNorm (V n - G) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x • V n x - b x • G x) 2 μ)
      atTop (𝓝 0) := by
  have hres := bounded_smul_tendsto ha hb hG hC hab hbb ht
  have hfst := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hVG (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hfst
  have hsum := hfst.add hres
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
  intro n
  have heq : (fun x => a n x • V n x - b x • G x) =
      (fun x => a n x • (V n x-G x)) + (fun x => (a n x-b x) • G x) := by
    funext x
    simp only [Pi.add_apply, smul_sub, sub_smul]
    abel
  dsimp only
  rw [heq]
  apply (eLpNorm_add_le ((ha n).smul ((hV n).sub hG).aestronglyMeasurable) (((ha n).sub hb).smul hG.aestronglyMeasurable) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
  apply add_le_add _ le_rfl
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (f := fun x => a n x • (V n x - G x)) (g := fun x => V n x - G x)
    ?_ 2
  filter_upwards [hab n] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg (V n x - G x))

end Nemytskii
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}

lemma h10_comp_C1 (hD : IsOpen D) (hu : H10 D u G)
    {F : ℝ → ℝ} {K : NNReal} (hF : ContDiff ℝ 1 F)
    (hlip : LipschitzWith K F) (hz : F 0 = 0) :
    H10 D (F ∘ u) (fun x => deriv F (u x) • G x) := by
  obtain ⟨f, hf, hfu, hfG⟩ := H10_sequence hu
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (fun n => (hf n).memLp.aestronglyMeasurable) hu.1.1.aestronglyMeasurable hfu).exists_seq_tendsto_ae
  have hdc := hF.continuous_deriv (by simp)
  have hdermem : MemLp (fun x => deriv F (u x)) ∞ (volume.restrict D) :=
    memLp_top_of_bound (hdc.comp_aestronglyMeasurable hu.1.1.aestronglyMeasurable) K
      (Filter.Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hlip)
  apply h10_of_strong (hlip.comp_memLp hz hu.1.1) (hu.1.2.1.smul hdermem)
    (fun n => test_comp_h10 hD hF hlip hz (hf (ns n)))
  · exact lipschitz_tendsto_eLpNorm_of_aestronglyMeasurable hlip
      (fun n => (hf (ns n)).memLp.aestronglyMeasurable) hu.1.1.aestronglyMeasurable
      (hfu.comp hns.tendsto_atTop)
  · apply bounded_smul_strong
      (fun n => hdc.comp_aestronglyMeasurable (hf (ns n)).memLp.aestronglyMeasurable)
      (hdc.comp_aestronglyMeasurable hu.1.1.aestronglyMeasurable)
      (fun n => (hf (ns n)).memLp_gradient) hu.1.2.1 K.coe_nonneg
      (fun _ => Filter.Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hlip)
      (Filter.Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hlip)
      ?_ (hfG.comp hns.tendsto_atTop)
    filter_upwards [hpoint] with x hx
    exact hdc.continuousAt.tendsto.comp hx

end Bernoulli.SobolevCalculus

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli

lemma cutSlope_continuous (n : ℕ) : Continuous (cutSlope n) := by
  unfold cutSlope
  fun_prop

lemma cutSlope_nonneg (n : ℕ) (t : ℝ) : 0 ≤ cutSlope n t :=
  le_min (le_max_right _ _) (by norm_num)

lemma cutSlope_le_one (n : ℕ) (t : ℝ) : cutSlope n t ≤ 1 := min_le_right _ _

lemma cutSlope_norm_le (n : ℕ) (t : ℝ) : ‖cutSlope n t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (cutSlope_nonneg n t)]
  exact cutSlope_le_one n t

lemma cutPrimitive_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (cutPrimitive n) (cutSlope n t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((cutSlope_continuous n).intervalIntegrable _ _)
    (cutSlope_continuous n).aestronglyMeasurable.stronglyMeasurableAtFilter
    (cutSlope_continuous n).continuousAt

lemma cutPrimitive_contDiff (n : ℕ) : ContDiff ℝ 1 (cutPrimitive n) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (cutPrimitive_deriv n t).differentiableAt, ?_⟩
  have heq : deriv (cutPrimitive n) = cutSlope n := funext fun t =>
    (cutPrimitive_deriv n t).deriv
  rw [heq]
  exact cutSlope_continuous n

lemma cutPrimitive_lipschitz (n : ℕ) : LipschitzWith 1 (cutPrimitive n) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (cutPrimitive_deriv n t).differentiableAt)
  intro t
  rw [(cutPrimitive_deriv n t).deriv, ← NNReal.coe_le_coe]
  exact cutSlope_norm_le n t

lemma cutSlope_tendsto (t : ℝ) :
    Tendsto (fun n => cutSlope n t) atTop (𝓝 (if 0 < t then 1 else 0)) := by
  by_cases ht : 0 < t
  · simp only [ite_eq_left ht]
    have hg : Tendsto (fun n : ℕ => ((n : ℝ)+1)*t) atTop atTop :=
      (tendsto_atTop_mono (fun n : ℕ => (show (n : ℝ) ≤ (n : ℝ)+1 by linarith))
        tendsto_natCast_atTop_atTop).atTop_mul_const ht
    apply tendsto_const_nhds.congr'
    filter_upwards [hg.eventually_ge_atTop 1] with n hn
    dsimp only [cutSlope]
    exact (min_eq_right (hn.trans (le_max_left _ _))).symm
  · simp only [ite_eq_right ht]
    have hf (n : ℕ) : cutSlope n t = 0 := by
      have hm : ((n : ℝ)+1)*t ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt ht)
      simp [cutSlope, max_eq_right hm]
    simp_rw [hf]
    exact tendsto_const_nhds

lemma integral_step (t : ℝ) :
    (∫ s in (0 : ℝ)..t, if 0 < s then (1 : ℝ) else 0) = max t 0 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht]
    calc
      _ = ∫ _s in (0 : ℝ)..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall fun s hs => by
          simp only [uIoc_of_le ht, mem_Ioc] at hs
          simp [hs.1]
      _ = t := by simp
  · rw [max_eq_right ht.le, intervalIntegral.integral_symm]
    have hz : (∫ s in t..(0 : ℝ), if 0 < s then (1 : ℝ) else 0) = 0 := by
      apply intervalIntegral.integral_zero_ae
      exact Filter.Eventually.of_forall fun s hs => by
        simp only [uIoc_of_le ht.le, mem_Ioc] at hs
        simp [not_lt.mpr hs.2]
    simp [hz]

lemma cutPrimitive_tendsto (t : ℝ) :
    Tendsto (fun n => cutPrimitive n t) atTop (𝓝 (max t 0)) := by
  rw [← integral_step t]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Filter.Eventually.of_forall fun n => (cutSlope_continuous n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun s _ => cutSlope_norm_le n s
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun s _ => cutSlope_tendsto s

end Bernoulli.SobolevCalculus

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}

lemma norm_positivePart (t : ℝ) : ‖max t 0‖ ≤ ‖t‖ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
  exact max_le (le_abs_self _) (abs_nonneg _)

lemma step_memLp_top (hu : AEStronglyMeasurable u (volume.restrict D)) :
    MemLp (fun x => if 0 < u x then (1 : ℝ) else 0) ∞ (volume.restrict D) := by
  have hs : Measurable (fun t : ℝ => if 0 < t then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const
  apply memLp_top_of_bound (hs.comp_aemeasurable hu.aemeasurable).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply]
    split_ifs <;> norm_num

lemma h10_positivePart (hD : IsOpen D) (hu : H10 D u G) :
    H10 D (fun x => max (u x) 0)
      (fun x => (if 0 < u x then (1 : ℝ) else 0) • G x) := by
  have hum : MemLp (fun x => max (u x) 0) 2 (volume.restrict D) := by
    apply hu.1.1.mono ((continuous_id.max continuous_const).comp_aestronglyMeasurable hu.1.1.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => norm_positivePart (u x)
  have hg : MemLp (fun x => (if 0 < u x then (1 : ℝ) else 0) • G x)
      2 (volume.restrict D) := hu.1.2.1.smul (step_memLp_top hu.1.1.aestronglyMeasurable)
  have hcomp (n : ℕ) : H10 D (cutPrimitive n ∘ u) (fun x => cutSlope n (u x) • G x) := by
    have hh := h10_comp_C1 hD hu (cutPrimitive_contDiff n) (cutPrimitive_lipschitz n)
      (cutPrimitive_zero n)
    have heq : deriv (cutPrimitive n) = cutSlope n :=
      funext fun t => (cutPrimitive_deriv n t).deriv
    rwa [heq] at hh
  apply h10_of_strong hum hg hcomp
  · apply tendsto_eLpNorm_zero_of_dominated
      (f := fun n x => cutPrimitive n (u x) - max (u x) 0)
      (fun n => ((cutPrimitive_lipschitz n).continuous.comp_aestronglyMeasurable
        hu.1.1.aestronglyMeasurable).sub hum.aestronglyMeasurable)
      (hu.1.1.norm.const_smul (2 : ℝ))
    · intro n
      exact Filter.Eventually.of_forall fun x => by
        have hn : ‖cutPrimitive n (u x)‖ ≤ ‖u x‖ := by
          simpa using (cutPrimitive_lipschitz n).norm_sub_le (u x) 0
        calc
          ‖cutPrimitive n (u x)-max (u x) 0‖ ≤ ‖cutPrimitive n (u x)‖ + ‖max (u x) 0‖ := norm_sub_le _ _
          _ ≤ 2*‖u x‖ := by linarith [norm_positivePart (u x)]
          _ = ‖((2 : ℝ) • fun y => ‖u y‖) x‖ := by simp
    · exact Filter.Eventually.of_forall fun x => by
        simpa using (cutPrimitive_tendsto (u x)).sub_const (max (u x) 0)
  · have ht := bounded_smul_tendsto
      (fun n => (cutSlope_continuous n).comp_aestronglyMeasurable hu.1.1.aestronglyMeasurable)
      (step_memLp_top hu.1.1.aestronglyMeasurable).aestronglyMeasurable
      hu.1.2.1 (by norm_num : (0 : ℝ) ≤ 1)
      (fun n => Filter.Eventually.of_forall fun x => cutSlope_norm_le n (u x))
      (Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num)
      (Filter.Eventually.of_forall fun x => cutSlope_tendsto (u x))
    simp only [sub_smul] at ht
    convert! ht using 1

end Bernoulli.SobolevCalculus

open scoped Manifold
namespace Bernoulli
open scoped _root_.Bernoulli
lemma exists_cutoff {d : ℕ} {K D : Set (Space d)} (hK : IsCompact K)
    (hD : IsOpen D) (hKD : K ⊆ D) :
    ∃ φ : Space d → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D ∧
      (∀ᶠ x in 𝓝ˢ K, φ x = 1) ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) := by
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_thickening_subset_open hD hKD
  have hki : K ⊆ interior (Metric.cthickening (δ/2) K) := by
    exact (Metric.self_subset_thickening (half_pos hδ) _).trans
      (Metric.thickening_subset_interior_cthickening _ _)
  obtain ⟨φ, hφ1, hφ0, hφb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, Space d)) (n := ⊤) hK.isClosed hki
  refine ⟨φ, φ.contMDiff.contDiff, HasCompactSupport.intro (hK.cthickening) hφ0, ?_, hφ1, hφb⟩
  have hs : tsupport (φ : Space d → ℝ) ⊆ Metric.cthickening (δ/2) K := by
    apply closure_minimal _ Metric.isClosed_cthickening
    intro x hx
    by_contra hn
    exact hx (hφ0 x hn)
  exact hs.trans ((Metric.cthickening_subset_thickening' hδ (by linarith) _).trans hδD)
end Bernoulli

namespace Bernoulli
open scoped _root_.Bernoulli
lemma H1.neg {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 D u G) : H1 D (fun x => -u x) (fun x => -G x) := by
  simpa using hu.const_smul (-1)
end Bernoulli

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)} {u : Space d → ℝ} {G : Space d → Space d}

lemma h1_positivePart (hD : IsOpen D) (hu : H1 D u G) :
    H1 D (fun x => max (u x) 0)
      (fun x => (if 0 < u x then (1 : ℝ) else 0) • G x) := by
  have hum : MemLp (fun x => max (u x) 0) 2 (volume.restrict D) := by
    apply hu.1.mono ((continuous_id.max continuous_const).comp_aestronglyMeasurable
      hu.1.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => norm_positivePart (u x)
  refine ⟨hum, hu.2.1.smul (step_memLp_top hu.1.aestronglyMeasurable), ?_⟩
  intro φ hφ h
  obtain ⟨χ, hχd, hχc, hχs, hχ1, _⟩ := exists_cutoff hφ.2.1.isCompact hD hφ.2.2
  have hχ : Test D χ := ⟨hχd, hχc, hχs⟩
  have hh := h10_positivePart hD (SobolevDensity.h10_mul_test hu hD hχ)
  have hc1 (x) (hx : x ∈ tsupport φ) : χ x = 1 := hχ1.self_of_nhdsSet x hx
  have hcG (x) (hx : x ∈ tsupport φ) : gradient χ x = 0 := by
    have heq : χ =ᶠ[𝓝 x] fun _ => 1 := hχ1.filter_mono (nhds_le_nhdsSet hx)
    rw [heq.gradient_eq]
    exact gradient_const x 1
  have hφK : Test (tsupport φ) φ := ⟨hφ.1, hφ.2.1, subset_rfl⟩
  calc
    _ = ∫ x in D, max (χ x*u x) 0 * (fderiv ℝ φ x) h := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        by_cases hx : x ∈ tsupport φ
        · rw [hc1 x hx, one_mul]
        · rw [hφK.fderiv_eq_zero_outside hx]
          simp
    _ = -(∫ x in D, inner ℝ ((if 0 < χ x*u x then (1 : ℝ) else 0) •
        (χ x • G x + u x • gradient χ x)) h * φ x) := hh.1.2.2 φ hφ h
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        by_cases hx : x ∈ tsupport φ
        · rw [hc1 x hx, hcG x hx]
          simp
        · rw [hφK.eq_zero_outside hx]
          simp

/-- A compactly supported H¹ function in the open set has zero trace. No
support or regularity condition is imposed on its given weak gradient. -/
lemma h10_of_local_compact_support (hD : IsOpen D) (hu : H1 D u G)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ D) : H10 D u G := by
  obtain ⟨χ, hχd, hχc, hχs, hχ1, _⟩ := exists_cutoff hc.isCompact hD hs
  have heq : (fun x => χ x*u x) = u := by
    funext x
    by_cases hx : x ∈ tsupport u
    · rw [hχ1.self_of_nhdsSet x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hh := SobolevDensity.h10_mul_test hu hD ⟨hχd, hχc, hχs⟩
  rw [heq] at hh
  have hgrad := H1.gradient_unique hD hh.1 hu
  exact hh.congr (Filter.EventuallyEq.refl _ _) hgrad

/-- Stampacchia's zero-level-set property, obtained from the two truncations
and distributional uniqueness. -/
lemma gradient_zero_on_zero_set (hD : IsOpen D) (hu : H1 D u G) :
    ∀ᵐ x ∂volume.restrict D, u x = 0 → G x = 0 := by
  have hp := h1_positivePart hD hu
  have hn := h1_positivePart hD hu.neg
  have hh := hp.sub hn
  have heq : (fun x => max (u x) 0 - max (-u x) 0) = u := by
    funext x
    exact max_zero_sub_max_neg_zero_eq_self (u x)
  change H1 D (fun x => max (u x) 0 - max (-u x) 0) _ at hh
  rw [heq] at hh
  have hg := H1.gradient_unique hD hu hh
  filter_upwards [hg] with x hx hzero
  simpa [hzero] using hx

end Bernoulli.SobolevCalculus

namespace Bernoulli.SobolevCalculus
open scoped _root_.Bernoulli
section Products
variable {α : Type uα} {E : Type uE} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bounded_smul_strong_of_fixed {a : ℕ → α → ℝ} {b : α → ℝ}
    {V : ℕ → α → E} {G : α → E} {C : ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (_hb : AEStronglyMeasurable b μ)
    (hV : ∀ n, MemLp (V n) 2 μ) (hG : MemLp G 2 μ)
    (hab : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C)
    (hres : Tendsto (fun n => eLpNorm (fun x => (a n x-b x) • G x) 2 μ) atTop (𝓝 0))
    (hVG : Tendsto (fun n => eLpNorm (V n - G) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x • V n x - b x • G x) 2 μ)
      atTop (𝓝 0) := by
  have hfst := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hVG (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hfst
  have hsum := hfst.add hres
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
  intro n
  have heq : (fun x => a n x • V n x - b x • G x) =
      (fun x => a n x • (V n x-G x)) + (fun x => (a n x-b x) • G x) := by
    funext x
    simp only [Pi.add_apply, smul_sub, sub_smul]
    abel
  dsimp only
  rw [heq]
  apply (eLpNorm_add_le ((ha n).smul ((hV n).sub hG).aestronglyMeasurable) (((ha n).sub _hb).smul hG.aestronglyMeasurable) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
  apply add_le_add _ le_rfl
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (f := fun x => a n x • (V n x - G x)) (g := fun x => V n x - G x)
    ?_ 2
  filter_upwards [hab n] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg (V n x - G x))

end Products
variable {d : ℕ} {D : Set (Space d)} {u v : Space d → ℝ} {G V : Space d → Space d}

lemma positivePart_gradient_strong_of_ae (hD : IsOpen D) (hu : H1 D u G)
    {f : ℕ → Space d → ℝ} {F : ℕ → Space d → Space d}
    (hf : ∀ n, H1 D (f n) (F n))
    (hpoint : ∀ᵐ x ∂volume.restrict D, Tendsto (fun n => f n x) atTop (𝓝 (u x)))
    (hFG : Tendsto (fun n => eLpNorm (F n - G) 2 (volume.restrict D)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x =>
      (if 0 < f n x then (1 : ℝ) else 0) • F n x -
      (if 0 < u x then (1 : ℝ) else 0) • G x) 2 (volume.restrict D)) atTop (𝓝 0) := by
  have hfp (n : ℕ) := step_memLp_top (hf n).1.aestronglyMeasurable
  have hup := step_memLp_top hu.1.aestronglyMeasurable
  apply bounded_smul_strong_of_fixed
    (fun n => (hfp n).aestronglyMeasurable) hup.aestronglyMeasurable
    (fun n => (hf n).2.1) hu.2.1
    (C := 1) (fun _ => Filter.Eventually.of_forall fun _ => by split_ifs <;> norm_num) ?_ hFG
  apply tendsto_eLpNorm_zero_of_dominated
    (f := fun n x => ((if 0 < f n x then (1 : ℝ) else 0) -
      (if 0 < u x then (1 : ℝ) else 0)) • G x)
    (fun n => ((hfp n).aestronglyMeasurable.sub hup.aestronglyMeasurable).smul
      hu.2.1.aestronglyMeasurable) (hu.2.1.norm.const_smul (2 : ℝ))
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      have hb : ‖(if 0 < f n x then (1 : ℝ) else 0) -
          (if 0 < u x then (1 : ℝ) else 0)‖ ≤ 2 := by split_ifs <;> norm_num
      simpa only [norm_smul, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (norm_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
        mul_le_mul_of_nonneg_right hb (norm_nonneg (G x))
  · filter_upwards [hpoint, gradient_zero_on_zero_set hD hu] with x hx hz
    by_cases hzero : u x = 0
    · simp only [hz hzero, smul_zero]
      exact tendsto_const_nhds
    · by_cases hpos : 0 < u x
      · apply tendsto_const_nhds.congr'
        filter_upwards [hx.eventually_const_lt hpos] with n hn
        simp [hpos, hn]
      · have hneg : u x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzero
        apply tendsto_const_nhds.congr'
        filter_upwards [hx.eventually_lt_const hneg] with n hn
        simp [hpos, not_lt.mpr hn.le]

end Bernoulli.SobolevCalculus

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.LowerSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

noncomputable section
open Set Filter Finset
open scoped Topology
namespace Bernoulli.DeSilvaJerison

lemma fp_t7 : fp t7 = -1 / (t7 * (1-t7^2)^3) := by
  have h := f_relation ⟨by linarith [t7_pos],t7_lt_one⟩
  rw [f_t7,sub_zero] at h
  calc
    fp t7 = (-1 / (1-t7^2)^3) / t7 :=
      (eq_div_iff (ne_of_gt t7_pos)).mpr (by rw [mul_comm]; exact h)
    _ = _ := by rw [div_div, mul_comm]

lemma c7_eq : c7 = 1 / (t7^2 * (1-t7^2)^5) := by
  have ht : t7≠0 := ne_of_gt t7_pos
  have hd : 1-t7^2≠0 := ne_of_gt (show 0<1-t7^2 by nlinarith [t7_pos,t7_lt_one])
  rw [c7,fp_t7]
  field_simp

lemma p_le_one (t : ℝ) : p t ≤ 1 := by
  rw [p, ← f_zero]
  apply f_strictAnti.antitoneOn ⟨le_rfl,by norm_num⟩
    ⟨le_min (abs_nonneg _) t7_pos.le, (min_le_right _ _).trans_lt t7_lt_one⟩
  exact le_min (abs_nonneg _) t7_pos.le

lemma exists_lipschitz_p : ∃ K : NNReal, LipschitzWith K p := by
  have hc : ContDiffOn ℝ 1 f (Icc 0 t7) := by
    intro t ht
    exact (contDiffAt_f ⟨by linarith [ht.1],ht.2.trans_lt t7_lt_one⟩).contDiffWithinAt
  obtain ⟨K,hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 t7) isCompact_Icc
  have hclip : LipschitzWith 1 (fun t : ℝ => min |t| t7) := by
    simpa only [Real.norm_eq_abs] using ((lipschitzWith_one_norm : LipschitzWith 1 (fun t : ℝ => ‖t‖)).min_const t7)
  refine ⟨K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  have hm (t : ℝ) : min |t| t7 ∈ Icc 0 t7 :=
    ⟨le_min (abs_nonneg _) t7_pos.le, min_le_right _ _⟩
  exact (hK.dist_le_mul _ (hm x) _ (hm y)).trans (by
    have hh := hclip.dist_le_mul x y
    norm_num at hh
    exact mul_le_mul_of_nonneg_left hh K.coe_nonneg)

lemma κ_sq : κ^2 * c7 = 1 := by
  rw [κ, inv_pow, Real.sq_sqrt c7_pos.le]
  exact inv_mul_cancel₀ (ne_of_gt c7_pos)

end Bernoulli.DeSilvaJerison

/-! The concrete seven-dimensional cone belonging to the De Silva–Jerison profile.
These are actual function/Sobolev constructions, not an assumption of minimality. -/
namespace Bernoulli.DeSilvaJerison

lemma Z_le_norm (x : Space 7) : Z x ≤ ‖x‖ := by
  calc Z x ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left (p_le_one _) (norm_nonneg x)
    _ = _ := mul_one _

lemma coordinate_le_norm (x : Space 7) : |x 6| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (6 : Fin 7)

lemma angular_estimate {x y : Space 7} (hx : x≠0) (hy : y≠0) :
    ‖y‖ * |x 6/‖x‖ - y 6/‖y‖| ≤ 2*‖x-y‖ := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hs : 0<‖y‖ := norm_pos_iff.mpr hy
  have hq : |x 6/‖x‖| ≤ 1 := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_one hr).mpr (coordinate_le_norm x)
  have hxy : |x 6-y 6| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply] using coordinate_le_norm (x-y)
  calc
    ‖y‖ * |x 6/‖x‖ - y 6/‖y‖| =
        |(‖y‖-‖x‖)*(x 6/‖x‖) + (x 6-y 6)| := by
      rw [← abs_of_pos hs, ← abs_mul]
      congr 1
      rw [abs_of_pos hs]
      field_simp
      ring
    _ ≤ |‖y‖-‖x‖| * |x 6/‖x‖| + |x 6-y 6| := by
      simpa only [abs_mul] using abs_add_le ((‖y‖-‖x‖)*(x 6/‖x‖)) (x 6-y 6)
    _ ≤ |‖y‖-‖x‖| * 1 + ‖x-y‖ := by gcongr
    _ ≤ ‖x-y‖ + ‖x-y‖ := by
      rw [mul_one]
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = _ := by ring

lemma exists_lipschitz_Z : ∃ K : NNReal, LipschitzWith K Z := by
  obtain ⟨K,hK⟩ := exists_lipschitz_p
  refine ⟨1+2*K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_one, NNReal.coe_ofNat]
  by_cases hx : x=0
  · subst x
    rw [Z_zero,zero_sub,abs_neg,abs_of_nonneg (Z_nonneg y),zero_sub,norm_neg]
    exact (Z_le_norm y).trans (by nlinarith [K.coe_nonneg,norm_nonneg y])
  by_cases hy : y=0
  · subst y
    rw [Z_zero,sub_zero,abs_of_nonneg (Z_nonneg x),sub_zero]
    exact (Z_le_norm x).trans (by nlinarith [K.coe_nonneg,norm_nonneg x])
  have hpd : |p (x 6/‖x‖)-p (y 6/‖y‖)| ≤ K * |x 6/‖x‖- y 6/‖y‖| := by
    simpa only [Real.dist_eq] using hK.dist_le_mul (x 6/‖x‖) (y 6/‖y‖)
  have hpb : |p (x 6/‖x‖)| ≤ 1 := by
    rw [abs_of_nonneg (p_nonneg _)]
    exact p_le_one _
  calc
    |Z x-Z y| = |(‖x‖-‖y‖)*p (x 6/‖x‖) + ‖y‖*(p (x 6/‖x‖)-p (y 6/‖y‖))| := by
      unfold Z
      congr 1
      ring
    _ ≤ |‖x‖-‖y‖| * |p (x 6/‖x‖)| + ‖y‖* |p (x 6/‖x‖)-p (y 6/‖y‖)| := by
      simpa only [abs_mul, abs_of_nonneg (norm_nonneg y)] using
        abs_add_le ((‖x‖-‖y‖)*p (x 6/‖x‖)) (‖y‖*(p (x 6/‖x‖)-p (y 6/‖y‖)))
    _ ≤ |‖x‖-‖y‖| * 1 + ‖y‖*(K* |x 6/‖x‖-y 6/‖y‖|) := by gcongr
    _ = |‖x‖-‖y‖| + K*(‖y‖* |x 6/‖x‖-y 6/‖y‖|) := by ring
    _ ≤ ‖x-y‖ + K*(2*‖x-y‖) := by
      exact add_le_add (abs_norm_sub_norm_le x y)
        (mul_le_mul_of_nonneg_left (angular_estimate hx hy) K.coe_nonneg)
    _ = _ := by ring

lemma exists_lipschitz_U : ∃ K : NNReal, LipschitzWith K U := by
  obtain ⟨K,hK⟩ := exists_lipschitz_Z
  exact ⟨‖κ‖₊*K, (lipschitzWith_smul κ).comp hK⟩

lemma U_continuous : Continuous U := exists_lipschitz_U.choose_spec.continuous

theorem U_h1loc : H1Loc univ U (gradient U) := by
  obtain ⟨K,hK⟩ := exists_lipschitz_U
  intro c r _ _
  exact LipschitzSobolev.h1_ball hK c r

end Bernoulli.DeSilvaJerison

/-! Euclidean calculus for the actual De Silva–Jerison axisymmetric construction.
No free-boundary or variational conclusion is built into these definitions. -/
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Axisymmetric
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasDerivAt_lineFirst {φ φ₁ : ℝ → ℝ} {φ₂ : ℝ} (e x v : E) (α t : ℝ)
    (hx : x+t • v≠0)
    (hφ : HasDerivAt φ (φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖))
      (inner ℝ (x+t • v) e / ‖x+t • v‖))
    (hφ₁ : HasDerivAt φ₁ φ₂ (inner ℝ (x+t • v) e / ‖x+t • v‖)) :
    HasDerivAt (lineFirst e x v α φ φ₁)
      (‖x+t • v‖^α / ‖x+t • v‖^2 *
        (α * φ (inner ℝ (x+t • v) e / ‖x+t • v‖) * ‖v‖^2 +
         α * (α-2) * φ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
           (inner ℝ (x+t • v) v / ‖x+t • v‖)^2 +
         2*(α-1) * φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
           (inner ℝ (x+t • v) v / ‖x+t • v‖) *
           (inner ℝ v e - inner ℝ (x+t • v) e / ‖x+t • v‖ *
             (inner ℝ (x+t • v) v / ‖x+t • v‖)) -
         inner ℝ (x+t • v) e / ‖x+t • v‖ *
           φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
           (‖v‖^2-(inner ℝ (x+t • v) v / ‖x+t • v‖)^2) +
         φ₂ * (inner ℝ v e - inner ℝ (x+t • v) e / ‖x+t • v‖ *
           (inner ℝ (x+t • v) v / ‖x+t • v‖))^2)) t := by
  have hn := norm_ne_zero_iff.mpr hx
  have hr := hasDerivAt_radius x v t hx
  have ha := hasDerivAt_axis x v e t
  have hq : HasDerivAt (fun a:ℝ=>inner ℝ (x+a • v) v) (‖v‖^2) t := by
    simpa only [real_inner_self_eq_norm_sq] using hasDerivAt_axis x v v t
  have hs := hasDerivAt_angular x v e t hx
  have hp := hφ.comp t hs
  have hp₁ := hφ₁.comp t hs
  have hQ := ((hq.const_mul α).div (hr.pow 2) (pow_ne_zero _ hn)).mul hp
  have hS := (((hr.pow 2).const_mul (inner ℝ v e)).sub (ha.mul hq)).div
    (hr.pow 3) (pow_ne_zero _ hn)
  apply (((hr.rpow_const (p:=α) (Or.inl hn)).mul
    (hQ.add (hp₁.mul hS)))).congr_deriv
  simp only [Function.comp_def, Pi.pow_apply, Pi.div_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  rw [Real.rpow_sub_one hn]
  field_simp
  ring

lemma secondCoeff_sum {ι : Type uι} [Fintype ι]
    (α F F₁ F₂ s : ℝ) (p b : ι → ℝ)
    (hp : ∑ i, (p i)^2 = 1) (hb : ∑ i, (b i)^2 = 1)
    (hpb : ∑ i, p i*b i = s) :
    ∑ i, secondCoeff α F F₁ F₂ s (p i) (b i) 1 =
      α*(α+(Fintype.card ι : ℝ)-2)*F - ((Fintype.card ι : ℝ)-1)*s*F₁ + (1-s^2)*F₂ := by
  have he (i:ι) : secondCoeff α F F₁ F₂ s (p i) (b i) 1 =
      (α*F-s*F₁) + (α*(α-2)*F-(2*α-3)*s*F₁+s^2*F₂)*(p i)^2 +
        (2*(α-1)*F₁-2*s*F₂)*(p i*b i) + F₂*(b i)^2 := by
    unfold secondCoeff
    ring
  simp_rw [he, Finset.sum_add_distrib, ←Finset.mul_sum]
  rw [hp,hb,hpb]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma lift_line_second {φ φ₁ : ℝ → ℝ} {φ₂ : ℝ} (e x v : E) (α : ℝ)
    (hx : x≠0)
    (hφ : ∀ᶠ s in 𝓝 (inner ℝ x e / ‖x‖), HasDerivAt φ (φ₁ s) s)
    (hφ₁ : HasDerivAt φ₁ φ₂ (inner ℝ x e / ‖x‖)) :
    deriv (deriv (fun t:ℝ=>lift e α φ (x+t • v))) 0 =
      ‖x‖^α / ‖x‖^2 * secondCoeff α (φ (inner ℝ x e / ‖x‖))
        (φ₁ (inner ℝ x e / ‖x‖)) φ₂ (inner ℝ x e / ‖x‖)
        (inner ℝ x v / ‖x‖) (inner ℝ v e) (‖v‖^2) := by
  have hx0 : x+(0:ℝ) • v≠0 := by simpa
  have hc : ContinuousAt (fun t:ℝ=>x+t • v) 0 := by fun_prop
  have hnear : ∀ᶠ t:ℝ in 𝓝 0, x+t • v≠0 :=
    hc.eventually_ne hx0
  have hs := (hasDerivAt_angular x v e 0 hx0).continuousAt
  have hp : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt φ (φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖))
      (inner ℝ (x+t • v) e / ‖x+t • v‖) := by
    exact hs.tendsto.eventually (p:=fun s=>HasDerivAt φ (φ₁ s) s) (by simpa using hφ)
  have he : deriv (fun t:ℝ=>lift e α φ (x+t • v)) =ᶠ[𝓝 0] lineFirst e x v α φ φ₁ := by
    filter_upwards [hnear,hp] with t ht hpt
    exact (hasDerivAt_lift_line e x v α t ht hpt).deriv
  rw [he.deriv_eq]
  have hh := hasDerivAt_lineFirst e x v α 0 hx0 (by simpa using hφ.self_of_nhds)
    (by simpa using hφ₁)
  simpa only [zero_smul, add_zero, secondCoeff] using hh.deriv

lemma line_second_derivative {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t:ℝ=>f (x+t • v))) 0=(fderiv ℝ (fderiv ℝ f) x v) v := by
  let c := fun t:ℝ=>x+t • v
  let q := fun t:ℝ=>(fderiv ℝ f (c t)) v
  have hc (t:ℝ) : HasDerivAt c v t := by
    simpa only [one_smul,id_eq,c] using ((hasDerivAt_id t).smul_const v).const_add x
  have hc0 : c 0=x := by simp [c]
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), ContDiffAt ℝ 2 f (c t) :=
    (hc 0).continuousAt.tendsto.eventually (hc0 ▸ hf.eventually (by norm_num))
  have hq : deriv (fun t:ℝ=>f (x+t • v)) =ᶠ[𝓝 0] q := by
    filter_upwards [hnear] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hc t)).deriv
  have hff := (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hff' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (c 0) := hc0.symm ▸ hff.hasFDerivAt
  have hh := (hff'.comp_hasDerivAt 0 (hc 0)).clm_apply (hasDerivAt_const 0 v)
  have hqq : HasDerivAt q ((fderiv ℝ (fderiv ℝ f) x v) v) 0 := by
    simpa only [Function.comp_def,ContinuousLinearMap.map_zero,add_zero,q] using hh
  rw [hq.deriv_eq,hqq.deriv]

lemma laplacian_lift [FiniteDimensional ℝ E] {φ φ₁ : ℝ → ℝ} {φ₂ : ℝ}
    (e x : E) (α : ℝ) (he : ‖e‖=1) (hx : x≠0)
    (hc : ContDiffAt ℝ 2 φ (inner ℝ x e / ‖x‖))
    (hφ : ∀ᶠ s in 𝓝 (inner ℝ x e / ‖x‖), HasDerivAt φ (φ₁ s) s)
    (hφ₁ : HasDerivAt φ₁ φ₂ (inner ℝ x e / ‖x‖)) :
    Δ (lift e α φ) x = ‖x‖^α / ‖x‖^2 *
      (α*(α+(Module.finrank ℝ E : ℝ)-2)*φ (inner ℝ x e / ‖x‖) -
        ((Module.finrank ℝ E : ℝ)-1)*(inner ℝ x e / ‖x‖)*φ₁ (inner ℝ x e / ‖x‖) +
        (1-(inner ℝ x e / ‖x‖)^2)*φ₂) := by
  let b := stdOrthonormalBasis ℝ E
  have hn := norm_ne_zero_iff.mpr hx
  have hp : ∑ i, (inner ℝ x (b i) / ‖x‖)^2 = 1 := by
    simp_rw [div_pow, ←Finset.sum_div]
    rw [b.sum_sq_inner_left]
    exact div_self (pow_ne_zero _ hn)
  have hb : ∑ i, (inner ℝ (b i) e)^2 = 1 := by
    rw [b.sum_sq_inner_right,he]
    norm_num
  have hpb : ∑ i, (inner ℝ x (b i) / ‖x‖) * inner ℝ (b i) e = inner ℝ x e / ‖x‖ := by
    simp_rw [div_mul_eq_mul_div, ←Finset.sum_div]
    rw [b.sum_inner_mul_inner]
  have hs := secondCoeff_sum α (φ (inner ℝ x e / ‖x‖)) (φ₁ (inner ℝ x e / ‖x‖)) φ₂
    (inner ℝ x e / ‖x‖) (fun i=>inner ℝ x (b i) / ‖x‖) (fun i=>inner ℝ (b i) e) hp hb hpb
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_two_apply]
  simp only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hcc := contDiffAt_lift (α:=α) hx hc
  simp_rw [←line_second_derivative hcc, lift_line_second e x _ α hx hφ hφ₁]
  have hbunit (i:Fin (Module.finrank ℝ E)) : ‖b i‖^2 = (1:ℝ) := by simp
  change (∑ i, ‖x‖^α / ‖x‖^2 * secondCoeff α (φ (inner ℝ x e / ‖x‖))
    (φ₁ (inner ℝ x e / ‖x‖)) φ₂ (inner ℝ x e / ‖x‖)
    (inner ℝ x (b i) / ‖x‖) (inner ℝ (b i) e) (‖b i‖^2)) = _
  simp_rw [hbunit, ←Finset.mul_sum]
  rw [hs]
  simp

lemma radial_norm {x : E} (hx : x≠0) : ‖radial x‖=1 := by
  rw [radial,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma radial_inner (x e : E) : inner ℝ (radial x) e = inner ℝ x e / ‖x‖ := by
  simp only [radial,real_inner_smul_left,div_eq_mul_inv,mul_comm]

lemma norm_sq_polarGradient {e x : E} (he : ‖e‖=1) (hx : x≠0) (a b : ℝ) :
    ‖polarGradient e x a b‖^2 = a^2 + (1-(inner ℝ x e / ‖x‖)^2)*b^2 := by
  have hn : inner ℝ (radial x) (radial x)=1 := by
    rw [real_inner_self_eq_norm_sq,radial_norm hx]; norm_num
  have het : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  have hrev : inner ℝ e (radial x) = inner ℝ x e / ‖x‖ :=
    (real_inner_comm e (radial x)).symm.trans (radial_inner x e)
  rw [←real_inner_self_eq_norm_sq]
  simp only [polarGradient,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,hn,het,hrev,radial_inner]
  ring

end Bernoulli.Axisymmetric

namespace Bernoulli.DeSilvaJerison
open Axisymmetric InnerProductSpace
open scoped Laplacian ContDiff

lemma angle_contDiffAt {x : Space 7} {n : WithTop ℕ∞} (hx : x≠0) :
    ContDiffAt ℝ n angle x := by
  have hn : ContDiffAt ℝ n (fun y:Space 7=>‖y‖) x := contDiffAt_id.norm ℝ hx
  have hi : ContDiffAt ℝ n (fun y:Space 7=>inner ℝ y axis) x :=
    contDiffAt_id.inner ℝ contDiffAt_const
  unfold angle
  simpa only [inner_axis] using hi.fun_div hn (norm_ne_zero_iff.mpr hx)

lemma Z_eq_Zsigned {x : Space 7} (ht : |angle x|≤t7) : Z x=Zsigned x := by
  rw [Zsigned_eq,Z,p_eq_f (show |x 6 / ‖x‖|≤t7 from ht)]
  rfl

lemma U_eq_Usigned {x : Space 7} (ht : |angle x|≤t7) : U x=Usigned x := by
  unfold U Usigned
  rw [Z_eq_Zsigned ht]

lemma signed_laplacian {x : Space 7} (hx : x≠0) (ha : |angle x|<1) : Δ Zsigned x=0 := by
  have ht : angle x ∈ Ioo (-1:ℝ) 1 := abs_lt.mp ha
  have hp : ∀ᶠ s in 𝓝 (inner ℝ x axis/‖x‖), HasDerivAt f (fp s) s := by
    simp only [inner_axis]
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hasDerivAt_f hs
  have ht' : inner ℝ x axis / ‖x‖ ∈ Ioo (-1:ℝ) 1 := by simpa only [inner_axis,angle] using ht
  have hl := laplacian_lift axis x 1 axis_norm hx (contDiffAt_f ht') hp (hasDerivAt_fp ht')
  have hd : 1-(angle x)^2≠0 := by nlinarith [sq_nonneg (angle x),ht.1,ht.2]
  have hr := f_relation ht
  have he : 6*f (angle x)-6*angle x*fp (angle x)+(1-(angle x)^2)*(-6/(1-(angle x)^2)^4)=0 := by
    field_simp at hr ⊢
    nlinarith [hr]
  change Δ (lift axis 1 f) x=0
  simp only [inner_axis,Space,finrank_euclideanSpace_fin, Nat.cast_ofNat] at hl
  norm_num only at hl
  change Δ (lift axis 1 f) x = ‖x‖^ (1:ℝ) / ‖x‖^2 *
    (6*f (angle x)-6*angle x*fp (angle x)+(1-(angle x)^2)*(-6/(1-(angle x)^2)^4)) at hl
  simpa only [he,mul_zero] using hl

lemma signed_harmonicAt {x : Space 7} (hx : x≠0) (ha : |angle x|<1) :
    HarmonicAt Zsigned x := by
  refine ⟨signed_contDiffAt hx ha,?_⟩
  have hN : ∀ᶠ y in 𝓝 x, y≠0 := isOpen_compl_singleton.mem_nhds hx
  have hA : ∀ᶠ y in 𝓝 x, |angle y|<1 :=
    (angle_contDiffAt (n:=1) hx).continuousAt.abs.eventually (gt_mem_nhds ha)
  filter_upwards [hN,hA] with y hy hya
  exact signed_laplacian hy hya

lemma U_eventuallyEq_Usigned {x : Space 7} (hu : 0<U x) : U =ᶠ[𝓝 x] Usigned := by
  obtain ⟨hx,ht⟩ := (U_pos_iff x).mp hu
  have hA : ∀ᶠ y in 𝓝 x, |angle y|<t7 :=
    (angle_contDiffAt (n:=1) hx).continuousAt.abs.eventually (gt_mem_nhds ht)
  exact hA.mono (fun y hy=>U_eq_Usigned hy.le)

/-- Positive-phase harmonicity is proved for the actual Sobolev candidate. -/
theorem U_harmonic : HarmonicOnNhd U {x|0<U x} := by
  intro x hu
  obtain ⟨hx,ht⟩ := (U_pos_iff x).mp hu
  apply (harmonicAt_congr_nhds (U_eventuallyEq_Usigned hu)).mpr
  exact (signed_harmonicAt hx (ht.trans t7_lt_one)).const_smul (c:=κ)

lemma fp_neg_arg (t : ℝ) : fp (-t)= -fp t := by
  simp only [fp,neg_sq,A_neg]
  ring

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison
open scoped BigOperators

lemma B_nonneg (n:ℕ) {u:ℝ} (hu:0≤u) : 0≤B n u := by
  apply Finset.sum_nonneg
  intro i hi
  positivity

lemma f_series_lower (n:ℕ) {t:ℝ} (ht:0≤t) (ht1:t<1) :
    (8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)
      -15/8*t^2*(B n (t^2)+(t^2)^n/(1-t^2)) ≤ f t := by
  have ha := (A_series_bounds n ht ht1).2
  have hp := mul_le_mul_of_nonneg_left ha (show (0:ℝ)≤15/8*t from by positivity)
  unfold f
  convert! sub_le_sub_left hp ((8-25*t^2+15*t^4)/(8*(1-t^2)^2)) using 1
  ring

lemma fp_series_upper (n:ℕ) {t:ℝ} (ht:0≤t) (ht1:t<1) :
    fp t ≤ -t*(1/(1-t^2)^3+5/4/(1-t^2)^2+15/8/(1-t^2)+15/8*B n (t^2)) := by
  have ha := (A_series_bounds n ht ht1).1
  unfold fp
  have hp := mul_le_mul_of_nonneg_left ha (show (0:ℝ)≤15/8 from by norm_num)
  convert! sub_le_sub_left hp (-t/(1-t^2)^3-5/4*t/(1-t^2)^2-15/8*t/(1-t^2)) using 1
  ring

end Bernoulli.DeSilvaJerison

noncomputable section
open scoped BigOperators
namespace Bernoulli.DeSilvaJerison.Algebra

lemma identity (x:ℝ) : H ((1/5:ℝ)*x)=bern x := by
  unfold H FlowNum JlowNum g g1 bern
  ring

lemma bern_nonneg {x:ℝ} (hx:0≤x) (hx1:x≤1) : 0≤bern x := by
  have hy : 0≤1-x := sub_nonneg.mpr hx1
  unfold bern
  positivity

lemma H_nonneg {u:ℝ} (hu:0≤u) (hu1:u≤1/5) : 0≤H u := by
  have he : u=(1/5:ℝ)*(u/(1/5)) := by ring
  rw [he,identity]
  apply bern_nonneg
  · positivity
  · rw [div_le_one (by norm_num : (0:ℝ)<1/5)]
    exact hu1

lemma hasDerivAt_g (u:ℝ) : HasDerivAt g (g1 u) u := by
  have hh := ((hasDerivAt_const u 1).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (2869387/1000000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (589981/125000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (6566689/1000000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (4206127/500000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (10257227/1000000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (6050939/500000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (2789267/200000:ℝ)).add ((hasDerivAt_id u).mul (hasDerivAt_const u (7895333/500000:ℝ))))))))))))))))))
  convert! hh using 1
  simp only [g1, Pi.add_apply, Pi.mul_apply, id_eq]
  ring

lemma hasDerivAt_g1 (u:ℝ) : HasDerivAt g1 (g2 u) u := by
  have hh := ((hasDerivAt_const u (2869387/1000000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (589981/62500:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (19700067/1000000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (4206127/125000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (10257227/200000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (18152817/250000:ℝ)).add ((hasDerivAt_id u).mul ((hasDerivAt_const u (19524869/200000:ℝ)).add ((hasDerivAt_id u).mul (hasDerivAt_const u (7895333/62500:ℝ))))))))))))))))
  convert! hh using 1
  simp only [g2, Pi.add_apply, Pi.mul_apply, id_eq]
  ring

lemma g_ge_one {u:ℝ} (hu:0≤u) : 1≤g u := by
  unfold g
  have : 0≤u*((2869387/1000000:ℝ)+u*((589981/125000:ℝ)+u*((6566689/1000000:ℝ)+u*((4206127/500000:ℝ)+u*((10257227/1000000:ℝ)+u*((6050939/500000:ℝ)+u*((2789267/200000:ℝ)+u*(7895333/500000:ℝ)))))))) := by positivity
  linarith

lemma g1_nonneg {u:ℝ} (hu:0≤u) : 0≤g1 u := by unfold g1; positivity

lemma g_residual_nonpos {u:ℝ} (hu:0≤u) :
    (1-u)*(2*g1 u+4*u*g2 u)-12*u*g1 u+(-643/200:ℝ)*(-643/200+5)*g u ≤0 := by
  have he : -((1-u)*(2*g1 u+4*u*g2 u)-12*u*g1 u+(-643/200:ℝ)*(-643/200+5)*g u) =
      ((1/1000000:ℝ)+u*((335237/40000000000:ℝ)+u*((18531/5000000000:ℝ)+u*((26639/40000000000:ℝ)+u*((378977/20000000000:ℝ)+u*((2875077/40000000000:ℝ)+u*((1938389/20000000000:ℝ)+u*((1189117/8000000000:ℝ)+u*(107925657105483/20000000000:ℝ))))))))) := by unfold g g1 g2; ring
  have hz : 0≤ -((1-u)*(2*g1 u+4*u*g2 u)-12*u*g1 u+(-643/200:ℝ)*(-643/200+5)*g u) := by
    rw [he]
    positivity
  linarith

lemma lower_logder {u:ℝ} (hu:0≤u) (hub:u≤(27/100:ℝ)) : 0≤2*(1-u)*g1 u-5*g u := by
  let x:=u/(27/100:ℝ)
  have hx:0≤x := by dsimp [x]; positivity
  have hy:0≤1-x := by dsimp [x]; linarith
  have he : 2*(1-u)*g1 u-5*g u =
      (369387/500000:ℝ)*x^0*(1-x)^8 + (558448641/100000000:ℝ)*x^1*(1-x)^7 + (90906551829/5000000000:ℝ)*x^2*(1-x)^6 + (33087845213199/1000000000000:ℝ)*x^3*(1-x)^5 + (910658646456597/25000000000000:ℝ)*x^4*(1-x)^4 + (243550667389510017/10000000000000000:ℝ)*x^5*(1-x)^3 + (1156300362730287837/125000000000000000:ℝ)*x^6*(1-x)^2 + (160712254758181821273/100000000000000000000:ℝ)*x^7*(1-x)^1 + (141611539097570077017/5000000000000000000000:ℝ)*x^8*(1-x)^0 := by
    dsimp [x]
    unfold g g1
    ring
  rw [he]
  positivity

lemma upper_logder {u:ℝ} (hu:0≤u) (hub:u≤(27/100:ℝ)) : 0≤2*g u-(13/25)*g1 u := by
  let x:=u/(27/100:ℝ)
  have hx:0≤x := by dsimp [x]; positivity
  have hy:0≤1-x := by dsimp [x]; linarith
  have he : 2*g u-(13/25)*g1 u =
      (12697969/25000000:ℝ)*x^0*(1-x)^8 + (5359357177/1250000000:ℝ)*x^1*(1-x)^7 + (3933009652441/250000000000:ℝ)*x^2*(1-x)^6 + (408907285769443/12500000000000:ℝ)*x^3*(1-x)^5 + (21018853182775349/500000000000000:ℝ)*x^4*(1-x)^4 + (4252809530492624731/125000000000000000:ℝ)*x^5*(1-x)^3 + (83958125315148478907/5000000000000000000:ℝ)*x^6*(1-x)^2 + (5678700560736300182329/1250000000000000000000:ℝ)*x^7*(1-x)^1 + (1242771118592263674331/2500000000000000000000:ℝ)*x^8*(1-x)^0 := by
    dsimp [x]
    unfold g g1
    ring
  rw [he]
  positivity

lemma FlowNum_nonneg {u:ℝ} (hu:0≤u) (hub:u≤(1/5:ℝ)) : 0≤FlowNum u := by
  let x:=u/(1/5:ℝ)
  have hx:0≤x := by dsimp [x]; positivity
  have hy:0≤1-x := by dsimp [x]; linarith
  have he : FlowNum u =
      8*x^0*(1-x)^8 + 56*x^1*(1-x)^7 + (848/5:ℝ)*x^2*(1-x)^6 + (36192/125:ℝ)*x^3*(1-x)^5 + (1328592/4375:ℝ)*x^4*(1-x)^4 + (13082512/65625:ℝ)*x^5*(1-x)^3 + (57279808/721875:ℝ)*x^6*(1-x)^2 + (62341556/3609375:ℝ)*x^7*(1-x)^1 + (5536402/3609375:ℝ)*x^8*(1-x)^0 := by
    dsimp [x]
    unfold FlowNum
    ring
  rw [he]
  positivity

end Bernoulli.DeSilvaJerison.Algebra

namespace Bernoulli.DeSilvaJerison

lemma gSub_pos (t:ℝ) : 0<gSub t := by
  have h:=Algebra.g_ge_one (sq_nonneg t)
  unfold gSub
  linarith

lemma hasDerivAt_gSub (t:ℝ) : HasDerivAt gSub (gSub1 t) t := by
  have hh:=(Algebra.hasDerivAt_g (t^2)).comp t (hasDerivAt_pow 2 t)
  convert! hh using 1
  dsimp only [gSub1,Function.comp_apply,id_eq]
  norm_num only
  ring

lemma hasDerivAt_gSub1 (t:ℝ) : HasDerivAt gSub1 (gSub2 t) t := by
  have hh:=((hasDerivAt_id t).const_mul 2).mul
    ((Algebra.hasDerivAt_g1 (t^2)).comp t (hasDerivAt_pow 2 t))
  convert! hh using 1
  dsimp only [gSub2,Function.comp_apply,id_eq]
  norm_num only
  ring

lemma gSub_residual (t:ℝ) :
    (1-t^2)*gSub2 t-6*t*gSub1 t+(-643/200:ℝ)*(-643/200+5)*gSub t ≤0 := by
  convert! Algebra.g_residual_nonpos (sq_nonneg t) using 1
  unfold gSub gSub1 gSub2
  ring

lemma qSub_nonneg {t:ℝ} (ht:0≤t) : 0≤qSub t := by
  unfold qSub gSub1
  exact div_nonneg (by have:=Algebra.g1_nonneg (sq_nonneg t); positivity) (gSub_pos t).le

lemma qSub_bounds {t:ℝ} (ht:0≤t) (hT:t≤t7) :
    5*t≤(1-t^2)*qSub t ∧ qSub t≤4 := by
  have htl:t≤517331/1000000 := hT.trans t7_bounds.2
  have hu:t^2≤27/100 := by nlinarith
  have hd:=Algebra.lower_logder (sq_nonneg t) hu
  have hm:=Algebra.upper_logder (sq_nonneg t) hu
  have hp:=Algebra.g1_nonneg (sq_nonneg t)
  have hg:=gSub_pos t
  unfold qSub gSub1 gSub at *
  constructor
  · rw [←mul_div_assoc]
    apply (le_div_iff₀ hg).mpr
    have hh:=mul_nonneg ht hd
    nlinarith
  · apply (div_le_iff₀ hg).mpr
    have hh:=mul_le_mul_of_nonneg_right (show 2*t≤26/25 by linarith) hp
    linarith

lemma c7_upper : c7≤177344/10000 := by
  have hl:t7^2≥(517330/1000000:ℝ)^2 := by nlinarith [t7_bounds.1,t7_pos]
  have hu:1-t7^2≥1-(517331/1000000:ℝ)^2 := by nlinarith [t7_bounds.2,t7_pos]
  have hp:=pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1-(517331/1000000:ℝ)^2) hu 5
  have hm:=mul_le_mul hl hp (by norm_num : (0:ℝ)≤(1-(517331/1000000:ℝ)^2)^5) (sq_nonneg t7)
  have ht : 0<1-t7^2 := by nlinarith [t7_pos,t7_lt_one]
  have hT:=t7_pos
  rw [c7_eq]
  apply (div_le_iff₀ (by positivity : 0<t7^2*(1-t7^2)^5)).mpr
  norm_num at hm
  linarith

lemma fp_strictAnti : StrictAntiOn fp (Ico (0:ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 1)
  · intro t ht
    exact (hasDerivAt_fp ⟨by linarith [ht.1],ht.2⟩).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    rw [(hasDerivAt_fp ⟨by linarith [ht.1],ht.2⟩).deriv]
    have hp : 0<1-t^2 := by nlinarith [ht.1,ht.2]
    exact div_neg_of_neg_of_pos (by norm_num) (pow_pos hp 4)

lemma sub_endpoint_bounds : f (11/25)≤1/3 ∧ fp (11/25)≤-7/2 := by
  have ha : 4722/10000 ≤ A (11/25) := by
    rw [A_eq_half_log (by norm_num)]
    refine le_trans ?_ (Real.sum_range_le_log_div (by norm_num) (by norm_num) 6)
    norm_num [Finset.sum_range_succ]
  constructor <;> dsimp only [f,fp] <;> norm_num at ha ⊢ <;> linarith

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison

lemma FLo_le {t:ℝ} (ht:0≤t) (ht1:t<1) : FLo t≤f t := by
  have hd:1-t^2≠0 := by nlinarith
  convert! f_series_lower 6 ht ht1 using 1
  unfold FLo Algebra.FlowNum B
  norm_num [Finset.sum_range_succ]
  field_simp [hd]
  ring

lemma fp_le_JLo {t:ℝ} (ht:0≤t) (ht1:t<1) : fp t≤-t*JLo t := by
  have hd:1-t^2≠0 := by nlinarith
  convert! fp_series_upper 6 ht ht1 using 1
  unfold JLo Algebra.JlowNum B
  norm_num [Finset.sum_range_succ]
  field_simp [hd]
  ring_nf
  simp

lemma JLo_nonneg {t:ℝ} (ht:0≤t) (ht1:t<1) : 0≤JLo t := by
  have hd:0<1-t^2 := by nlinarith
  have he : JLo t=1/(1-t^2)^3+5/4/(1-t^2)^2+15/8/(1-t^2)+15/8*B 6 (t^2) := by
    unfold JLo Algebra.JlowNum B
    norm_num [Finset.sum_range_succ]
    field_simp
    ring
  rw [he]
  have hh:=B_nonneg 6 (sq_nonneg t)
  positivity

lemma GSub_low {t:ℝ} (ht:0≤t) (htb:t≤11/25) : c7≤GSub t := by
  have ht1:t<1 := by linarith
  have hd:0<1-t^2 := by nlinarith
  have hu:t^2≤1/5 := by nlinarith
  have hg:=gSub_pos t
  have hF:0≤FLo t := div_nonneg (Algebra.FlowNum_nonneg (sq_nonneg t) hu) (by positivity)
  have hL:=FLo_le ht ht1
  have hp:=fp_le_JLo ht ht1
  have hJ:=JLo_nonneg ht ht1
  have hq:=qSub_nonneg ht
  have hB: t*JLo t+FLo t*qSub t ≤ -(fp t-f t*qSub t) := by
    have hh:=mul_le_mul_of_nonneg_right hL hq
    linarith
  have hB0:0≤t*JLo t+FLo t*qSub t := by positivity
  have hs1 := sq_le_sq₀ hF (hF.trans hL) |>.mpr hL
  have hs2 := sq_le_sq₀ hB0 (hB0.trans hB) |>.mpr hB
  have hH:=Algebra.H_nonneg (sq_nonneg t) hu
  have he : Algebra.H (t^2) =
      64*(1-t^2)^6*(gSub t)^2 *
        ((1-(-643/200:ℝ))^2*(FLo t)^2+(1-t^2)*(t*JLo t+FLo t*qSub t)^2-177344/10000) := by
    unfold Algebra.H FLo JLo qSub gSub gSub1
    have hgn : Algebra.g (t^2) ≠ 0 := ne_of_gt hg
    field_simp [ne_of_gt hd,hgn]
    ring
  rw [he] at hH
  have hn := (mul_nonneg_iff_of_pos_left (by positivity : 0<64*(1-t^2)^6*(gSub t)^2)).mp hH
  have hu1:=mul_le_mul_of_nonneg_left hs1 (show (0:ℝ)≤(1-(-643/200:ℝ))^2 by positivity)
  have hu2:=mul_le_mul_of_nonneg_left hs2 hd.le
  dsimp [GSub]
  nlinarith [c7_upper]

lemma hasDerivAt_qSub (t:ℝ) :
    HasDerivAt qSub (gSub2 t/gSub t-(qSub t)^2) t := by
  have hh := (hasDerivAt_gSub1 t).div (hasDerivAt_gSub t) (ne_of_gt (gSub_pos t))
  convert! hh using 1
  unfold qSub
  field_simp

lemma qSub_deriv_bound {t:ℝ} (_ht:0≤t) (_ht1:t<1) :
    (1-t^2)*(gSub2 t/gSub t-(qSub t)^2) ≤
      6*t*qSub t-(-643/200:ℝ)*(-643/200+5)-(1-t^2)*(qSub t)^2 := by
  have hg:=gSub_pos t
  have hh:=gSub_residual t
  have he : (1-t^2)*(gSub2 t/gSub t-(qSub t)^2)-
      (6*t*qSub t-(-643/200:ℝ)*(-643/200+5)-(1-t^2)*(qSub t)^2) =
      ((1-t^2)*gSub2 t-6*t*gSub1 t+(-643/200:ℝ)*(-643/200+5)*gSub t)/gSub t := by
    unfold qSub
    field_simp
    ring
  have hz:=div_nonpos_of_nonpos_of_nonneg hh hg.le
  linarith

lemma hasDerivAt_GSub {t:ℝ} (ht:t∈Ioo (-1:ℝ) 1) :
    HasDerivAt GSub
      (2*((1-(-643/200:ℝ))^2*f t*fp t-t*(fp t-f t*qSub t)^2+
        (1-t^2)*(fp t-f t*qSub t)*(-6/(1-t^2)^4-fp t*qSub t-f t*(gSub2 t/gSub t-(qSub t)^2)))) t := by
  have hh:=(((hasDerivAt_f ht).pow 2).const_mul ((1-(-643/200:ℝ))^2)).add
    (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).mul
      (((hasDerivAt_fp ht).sub ((hasDerivAt_f ht).mul (hasDerivAt_qSub t))).pow 2))
  convert! hh using 1
  norm_num only [id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
  ring

lemma GSub_nonpos_deriv {t:ℝ} (ht:11/25≤t) (ht7:t≤t7) : deriv GSub t ≤0 := by
  have ht0:0≤t := by linarith
  have ht1:t<1:=ht7.trans_lt t7_lt_one
  have hI:t∈Ioo (-1:ℝ) 1:=⟨by linarith,ht1⟩
  have hd:0<1-t^2 := by nlinarith
  have hf0:0≤f t := by
    have hh:=f_strictAnti.antitoneOn ⟨ht0,ht1⟩ ⟨t7_pos.le,t7_lt_one⟩ ht7
    simpa only [f_t7] using hh
  have hfall : f t ≤ f (11/25) := f_strictAnti.antitoneOn ⟨by norm_num,by norm_num⟩ ⟨ht0,ht1⟩ ht
  have hfp : fp t ≤ fp (11/25) := fp_strictAnti.antitoneOn ⟨by norm_num,by norm_num⟩ ⟨ht0,ht1⟩ ht
  have hf:f t≤1/3:=hfall.trans sub_endpoint_bounds.1
  have hp:fp t≤-7/2:=hfp.trans sub_endpoint_bounds.2
  have hq:=qSub_nonneg ht0
  obtain ⟨hqL,hqU⟩:=qSub_bounds ht0 ht7
  have hb:fp t-f t*qSub t≤0 := by nlinarith [mul_nonneg hf0 hq]
  have hres:=qSub_deriv_bound ht0 ht1
  have hODE: (1-t^2)*(-6/(1-t^2)^4)=6*t*fp t-6*f t := by
    have hh:=f_relation hI
    field_simp at hh ⊢
    nlinarith
  have hbd : (1-t^2)*(-6/(1-t^2)^4-fp t*qSub t-f t*(gSub2 t/gSub t-(qSub t)^2)) ≥
      6*t*fp t-6*f t-(1-t^2)*fp t*qSub t-
        f t*(6*t*qSub t-(-643/200:ℝ)*(-643/200+5)-(1-t^2)*(qSub t)^2) := by
    have hh:=mul_le_mul_of_nonneg_left hres hf0
    nlinarith only [hh,hODE]
  have hmul:=mul_le_mul_of_nonpos_left hbd hb
  rw [(hasDerivAt_GSub hI).deriv]
  have hfirst : (5*t-(1-t^2)*qSub t)*(fp t-f t*qSub t)^2 ≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have hlast : (6.02745:ℝ)*fp t+(11.738775:ℝ)*f t*qSub t≤0 := by
    have hmul:=mul_le_mul hf hqU hq (by norm_num : (0:ℝ)≤1/3)
    linarith
  have hlast2:=mul_nonpos_of_nonneg_of_nonpos hf0 hlast
  nlinarith only [hmul,hfirst,hlast2]

lemma GSub_high {t:ℝ} (ht:11/25≤t) (ht7:t≤t7) : c7≤GSub t := by
  have hcont:ContinuousOn GSub (Icc (11/25) t7) := by
    intro x hx
    exact (hasDerivAt_GSub ⟨by linarith [hx.1],hx.2.trans_lt t7_lt_one⟩).continuousAt.continuousWithinAt
  have hanti:AntitoneOn GSub (Icc (11/25) t7) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_GSub ⟨by linarith [hx.1],hx.2.trans t7_lt_one⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact GSub_nonpos_deriv hx.1.le hx.2.le
  have he:GSub t7=c7 := by simp [GSub,f_t7,c7]
  rw [←he]
  exact hanti ⟨ht,ht7⟩ ⟨by linarith [t7_bounds.1],le_rfl⟩ ht7

/-- Exact substitute for DSJ's numerical lower-barrier plot in dimension seven. -/
theorem GSub_ge_c7 {t:ℝ} (ht:0≤t) (ht7:t≤t7) : c7≤GSub t := by
  by_cases h:t≤11/25
  · exact GSub_low ht h
  · exact GSub_high (le_of_lt (lt_of_not_ge h)) ht7

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison
open Axisymmetric InnerProductSpace
open scoped Laplacian ContDiff

lemma qSub_neg (t:ℝ) : qSub (-t)= -qSub t := by
  simp only [qSub,gSub,gSub1,neg_sq]
  ring

lemma GSub_neg (t:ℝ) : GSub (-t)=GSub t := by
  rw [GSub,GSub,f_neg,fp_neg_arg,qSub_neg,neg_sq]
  ring

lemma GSub_ge_c7_abs {t:ℝ} (ht:|t|≤t7) : c7≤GSub t := by
  have hh:=GSub_ge_c7 (abs_nonneg t) ht
  rcases le_total 0 t with hp|hn
  · simpa only [abs_of_nonneg hp] using hh
  · simpa only [abs_of_nonpos hn,GSub_neg] using hh

lemma gSub_contDiff {n:WithTop ℕ∞} : ContDiff ℝ n gSub := by
  unfold gSub Algebra.g
  fun_prop

lemma YSub_pos {x:Space 7} (hx:x≠0) : 0<YSub x := by
  unfold YSub lift
  exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _) (gSub_pos _)

lemma YSub_contDiffAt {x:Space 7} {n:WithTop ℕ∞} (hx:x≠0) :
    ContDiffAt ℝ n YSub x := contDiffAt_lift hx gSub_contDiff.contDiffAt

/-- An actual sign of the Euclidean Laplacian, not a barrier hypothesis. -/
theorem YSub_superharmonic {x:Space 7} (hx:x≠0) : Δ YSub x≤0 := by
  have hp : ∀ᶠ s in 𝓝 (inner ℝ x axis/‖x‖), HasDerivAt gSub (gSub1 s) s :=
    Filter.Eventually.of_forall hasDerivAt_gSub
  have hh:=laplacian_lift axis x (-643/200) axis_norm hx
    (gSub_contDiff (n:=2)).contDiffAt hp (hasDerivAt_gSub1 _)
  rw [YSub,hh]
  have hR:=gSub_residual (inner ℝ x axis/‖x‖)
  have he : (-643/200:ℝ)*(-643/200+(Module.finrank ℝ (Space 7):ℝ)-2)*
      gSub (inner ℝ x axis/‖x‖)-((Module.finrank ℝ (Space 7):ℝ)-1)*
      (inner ℝ x axis/‖x‖)*gSub1 (inner ℝ x axis/‖x‖)+
      (1-(inner ℝ x axis/‖x‖)^2)*gSub2 (inner ℝ x axis/‖x‖)≤0 := by
    simp only [Space,finrank_euclideanSpace_fin,Nat.cast_ofNat]
    nlinarith [hR]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) he

lemma Usigned_gradient {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    gradient Usigned x=κ • polarGradient axis x (f (angle x)) (fp (angle x)) := by
  have hi : inner ℝ x axis/‖x‖∈Ioo (-1:ℝ) 1 := by
    simpa only [inner_axis,angle,Set.mem_Ioo] using abs_lt.mp ha
  rw [show gradient Usigned x=κ • gradient Zsigned x from
    gradient_const_mul κ ((signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num))]
  rw [Zsigned,(hasGradientAt_lift axis x 1 hx (hasDerivAt_f hi)).gradient]
  simp only [Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_smul,one_mul,inner_axis,angle]

lemma YSub_gradient {x:Space 7} (hx:x≠0) :
    gradient YSub x=(‖x‖^(-643/200:ℝ)/‖x‖) •
      polarGradient axis x ((-643/200:ℝ)*gSub (angle x)) (gSub1 (angle x)) := by
  simpa only [YSub,inner_axis,angle] using
    (hasGradientAt_lift axis x (-643/200) hx (hasDerivAt_gSub _)).gradient

lemma U_gradient {x:Space 7} (hu:0<U x) :
    gradient U x=κ • polarGradient axis x (f (angle x)) (fp (angle x)) := by
  obtain ⟨hx,ha⟩:=(U_pos_iff x).mp hu
  have he:gradient U x=gradient Usigned x := by
    rw [gradient,(U_eventuallyEq_Usigned hu).fderiv_eq]
    rfl
  rw [he,Usigned_gradient hx (ha.trans t7_lt_one)]

/-- The square-completion vector of the lower comparison has norm at least one
throughout the entire positive phase of the concrete seven-dimensional cone. -/
theorem lower_groundstate_slope {x:Space 7} (hu:0<U x) :
    1≤‖gradient U x-(U x/YSub x) • gradient YSub x‖^2 := by
  obtain ⟨hx,ha⟩:=(U_pos_iff x).mp hu
  have hn:=norm_ne_zero_iff.mpr hx
  have hg:=ne_of_gt (gSub_pos (angle x))
  have hr:=ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) (-643/200:ℝ))
  have hU : U x=κ*‖x‖*f (angle x) := by
    rw [U_eq_Usigned ha.le,Usigned,Zsigned_eq]
    ring
  have he : gradient U x-(U x/YSub x) • gradient YSub x=
      κ • polarGradient axis x ((1-(-643/200:ℝ))*f (angle x))
        (fp (angle x)-f (angle x)*qSub (angle x)) := by
    rw [U_gradient hu,YSub_gradient hx,hU]
    have hy : YSub x = ‖x‖^(-643/200:ℝ)*gSub (angle x) := by
      simp only [YSub,lift,inner_axis,angle]
    rw [hy]
    unfold polarGradient qSub
    simp only [inner_axis]
    ext i
    simp only [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    unfold angle at *
    field_simp [hn,hg,hr]
    ring
  rw [he,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,norm_sq_polarGradient axis_norm hx]
  have hG:=mul_le_mul_of_nonneg_left (GSub_ge_c7_abs ha.le) (sq_nonneg κ)
  rw [κ_sq] at hG
  simpa only [GSub,inner_axis,angle,mul_pow] using hG

end Bernoulli.DeSilvaJerison

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.HarmonicReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uE

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}

lemma Test.add {f g : Space d → ℝ} (hf : Test D f) (hg : Test D g) :
    Test D (f + g) := by
  exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩

lemma Test.sub {f g : Space d → ℝ} (hf : Test D f) (hg : Test D g) :
    Test D (f - g) := by
  convert hf.add (hg.const_mul (-1)) using 1
  ext x
  simp [sub_eq_add_neg]

lemma H10.const_smul {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H10 D u G) (t : ℝ) :
    H10 D (fun x => t * u x) (fun x => t • G x) := by
  obtain ⟨f, hf, hfu, hfG⟩ := SobolevCalculus.H10_sequence hu
  refine SobolevCalculus.h10_of_strong (hu.1.const_smul t).1 (hu.1.const_smul t).2.1
    (fun n => (hf n).h10_const_mul t) ?_ ?_
  · have heq (n : ℕ) : (fun x => t * f n x) - (fun x => t * u x) = t • (f n - u) := by
      ext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    simp_rw [heq, eLpNorm_const_smul]
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul hfu (a := ‖t‖ₑ) (Or.inr (by simp)))
  · have heq (n : ℕ) : (fun x => t • gradient (f n) x) - (fun x => t • G x) =
        t • (gradient (f n) - G) := by
      ext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_sub]
    simp_rw [heq, eLpNorm_const_smul]
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul hfG (a := ‖t‖ₑ) (Or.inr (by simp)))

lemma H10.neg {u : Space d → ℝ} {G : Space d → Space d} (hu : H10 D u G) :
    H10 D (fun x => -u x) (fun x => -G x) := by
  simpa using hu.const_smul (-1)

end Bernoulli

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.HarmonicWeakLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff BigOperators
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}
namespace Test
lemma directional {φ : Space d → ℝ} (hφ : Test D φ) (e : Space d) :
    Test D (fun x => fderiv ℝ φ x e) := by
  refine ⟨(hφ.1.fderiv_right (by simp)).clm_apply contDiff_const,
    hφ.2.1.fderiv_apply ℝ e, (tsupport_fderiv_apply_subset ℝ e).trans hφ.2.2⟩
end Test

/-- Distributional integration by parts against the Euclidean Laplacian;
no second derivatives of the Sobolev function occur in this statement. -/
lemma H1.laplacian_ibp {u : Space d → ℝ} {G : Space d → Space d}
    (hu : H1 D u G) {φ : Space d → ℝ} (hφ : Test D φ) :
    (∫ x in D, u x * Laplacian.laplacian φ x) =
      -(∫ x in D, inner ℝ (G x) (gradient φ x)) := by
  let b := stdOrthonormalBasis ℝ (Space d)
  have hi (i : Fin (Module.finrank ℝ (Space d))) :=
    hu.2.2 _ (hφ.directional (b i)) (b i)
  have hs (x : Space d) : Laplacian.laplacian φ x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ φ y (b i)) x (b i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ b]
    apply Finset.sum_congr rfl
    intro i _
    rw [iteratedFDeriv_two_apply]
    -- evaluation of a continuously differentiable map into continuous linear maps
    have hd := (hφ.1.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    rw [fderiv_clm_apply hd (differentiableAt_const (b i))]
    simp
  simp_rw [hs,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_deriv_product hu.1 (hφ.directional (b i)) (b i))]
  simp_rw [hi]
  rw [Finset.sum_neg_distrib,← integral_finsetSum _ (fun i _ =>
    integrable_inner_test hu.2.1 (hφ.directional (b i)) (b i))]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    calc
      _ = ∑ i, inner ℝ (G x) (b i) * inner ℝ (b i) (gradient φ x) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm (gradient φ x) (b i),inner_gradient_left]
      _ = _ := b.sum_inner_mul_inner (G x) (gradient φ x)

end Bernoulli

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PositiveQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Halfspace
variable {d : ℕ}

lemma positiveSquareRatio_nonneg {v u : Space d → ℝ} (x : Space d) :
    0 ≤ positiveSquareRatio v u x := by
  by_cases h : 0<u x
  · simp only [positiveSquareRatio,ite_eq_left h]; positivity
  · simp [positiveSquareRatio,h]

end Bernoulli.Halfspace

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ConePicone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Halfspace
variable {d : ℕ}

lemma positiveSquareRatio_hasFDerivAt {u v : Space d → ℝ} {x : Space d}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (hu0 : 0<u x) :
    HasFDerivAt (positiveSquareRatio v u)
      ((2*v x/u x) • fderiv ℝ v x-(v x/u x)^2 • fderiv ℝ u x) x := by
  have hh := (hv.hasFDerivAt.pow 2).mul ((hasDerivAt_inv hu0.ne').comp_hasFDerivAt x hu.hasFDerivAt)
  have he : positiveSquareRatio v u =ᶠ[𝓝 x] (fun y=>v y^2/u y) := by
    filter_upwards [hu.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hu0)] with y hy
    change 0<u y at hy
    simp only [positiveSquareRatio,ite_eq_left hy]
  simp only [Function.comp_apply] at hh
  convert! hh.congr_of_eventuallyEq he using 1
  ext z
  simp only [sub_apply,smul_apply,smul_eq_mul,add_apply,pow_one,Nat.reduceSub]
  field_simp
  ring

lemma positiveSquareRatio_gradient {u v : Space d → ℝ} {x : Space d}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (hu0 : 0<u x) :
    gradient (positiveSquareRatio v u) x=
      (2*v x/u x) • gradient v x-(v x/u x)^2 • gradient u x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,(positiveSquareRatio_hasFDerivAt hu hv hu0).fderiv]
  simp only [sub_apply,smul_apply,smul_eq_mul,inner_sub_left,real_inner_smul_left,inner_gradient_left]

end Bernoulli.Halfspace

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.GroundState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uF

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Laplacian
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}
namespace GroundState

lemma compact_extension_near_test (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hφ : Test D φ) :
    ∃ F : Space d → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      ∀x∈tsupport φ, F =ᶠ[𝓝 x] Y := by
  obtain ⟨χ,hχ,hχc,hχD,hχ1,_⟩ := exists_cutoff hφ.2.1 hD hφ.2.2
  refine ⟨fun x=>χ x*Y x,?_,hχc.mul_right,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x∈tsupport χ
    · exact hχ.contDiffAt.mul (hY.contDiffAt (hD.mem_nhds (hχD hx)))
    · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
  · intro x hx
    filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp [hy]

lemma compact_green {F φ : Space d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hφ : Test univ φ) :
    (∫x, inner ℝ (gradient F x) (gradient φ x)) = -(∫x, Δ F x*φ x) := by
  have hi := (show Test univ F from ⟨hF,hc,subset_univ _⟩).h1.laplacian_ibp hφ
  simp only [Measure.restrict_univ] at hi
  have hs := SchwartzMap.integral_mul_laplacian_right_eq_left
    (hc.toSchwartzMap hF) (hφ.2.1.toSchwartzMap hφ.1) (μ:=volume)
  simp only [SchwartzMap.laplacian_apply] at hs
  change (∫x, F x*Δ φ x)=(∫x, Δ F x*φ x) at hs
  linarith

lemma local_green (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hφ : Test D φ) :
    (∫x, inner ℝ (gradient Y x) (gradient φ x)) = -(∫x, Δ Y x*φ x) := by
  obtain ⟨F,hF,hFc,hFY⟩ := compact_extension_near_test hD hY hφ
  have hi := compact_green hF hFc (show Test univ φ from ⟨hφ.1,hφ.2.1,subset_univ _⟩)
  convert! hi using 1
  · apply integral_congr_ae
    exact ae_of_all _ fun x=>by
      by_cases hx : x∈tsupport φ
      · dsimp only
        simp only [gradient,(hFY x hx).fderiv_eq]
      · have hz : gradient φ x=0 := by rw [gradient,fderiv_of_notMem_tsupport ℝ hx,map_zero]
        simp [hz]
  · congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x=>by
      by_cases hx : x∈tsupport φ
      · dsimp only
        rw [(InnerProductSpace.laplacian_congr_nhds (hFY x hx)).eq_of_nhds]
      · simp [image_eq_zero_of_notMem_tsupport hx]

lemma local_green_integrable (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hφ : Test D φ) :
    Integrable (fun x=>inner ℝ (gradient Y x) (gradient φ x)) ∧
    Integrable (fun x=>Δ Y x*φ x) := by
  obtain ⟨F,hF,hFc,hFY⟩ := compact_extension_near_test hD hY hφ
  have hFtest : Test univ F := ⟨hF,hFc,subset_univ _⟩
  have hφtest : Test univ φ := ⟨hφ.1,hφ.2.1,subset_univ _⟩
  have hgrad := integrable_inner_of_memLp hFtest.memLp_gradient hφtest.memLp_gradient
  simp only [Measure.restrict_univ] at hgrad
  have hLap : Continuous (Δ F) := by
    let S := hFc.toSchwartzMap hF
    have he : (Laplacian.laplacian S : Space d → ℝ)=Δ F := funext fun x=>SchwartzMap.laplacian_apply S x
    exact he ▸ (Laplacian.laplacian S).continuous
  have hi : Integrable (fun x=>Δ F x*φ x) volume :=
    (hLap.mul hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.1.mul_left
  constructor
  · apply hgrad.congr
    exact ae_of_all _ fun x=>by
      by_cases hx : x∈tsupport φ
      · dsimp only
        simp only [gradient,(hFY x hx).fderiv_eq]
      · have hz : gradient φ x=0 := by rw [gradient,fderiv_of_notMem_tsupport ℝ hx,map_zero]
        simp [hz]
  · apply hi.congr
    exact ae_of_all _ fun x=>by
      by_cases hx : x∈tsupport φ
      · dsimp only
        rw [(InnerProductSpace.laplacian_congr_nhds (hFY x hx)).eq_of_nhds]
      · simp [image_eq_zero_of_notMem_tsupport hx]

open Halfspace

lemma square_ratio_test (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x) (hφ : Test D φ) :
    Test D (positiveSquareRatio φ Y) := by
  have hs : tsupport (positiveSquareRatio φ Y)⊆tsupport φ := by
    apply closure_mono
    intro x hx
    by_contra hn
    have hz : φ x=0 := Function.notMem_support.mp hn
    change positiveSquareRatio φ Y x ≠ 0 at hx
    exact hx (by simp [positiveSquareRatio,hz])
  refine ⟨?_,hφ.2.1.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans hφ.2.2⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x∈tsupport φ
  · have hy := hY.contDiffAt (hD.mem_nhds (hφ.2.2 hx))
    have hp := hYp x (hφ.2.2 hx)
    have he : positiveSquareRatio φ Y =ᶠ[𝓝 x] (fun y=>φ y^2/Y y) := by
      filter_upwards [hy.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp)] with y hh
      change 0 < Y y at hh
      simp only [positiveSquareRatio,ite_eq_left hh]
    exact ((hφ.1.contDiffAt.pow 2).div hy hp.ne').congr_of_eventuallyEq he
  · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change φ y = 0 at hy
    simp [positiveSquareRatio,hy]

lemma picone_identity (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x) (hφ : Test D φ) (x : Space d) :
    ‖gradient φ x-(φ x/Y x) • gradient Y x‖^2 = ‖gradient φ x‖^2-
      inner ℝ (gradient Y x) (gradient (positiveSquareRatio φ Y) x) := by
  by_cases hx : x∈D
  · rw [positiveSquareRatio_gradient
      ((hY.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp))
      (hφ.1.differentiable (by simp) x) (hYp x hx)]
    rw [norm_sub_sq_real]
    simp only [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
      norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_comm (gradient φ x) (gradient Y x)]
    ring
  · rw [hφ.eq_zero_outside hx,hφ.gradient_eq_zero_outside hx,
      (square_ratio_test hD hY hYp hφ).gradient_eq_zero_outside hx]
    simp

/-- Ground-state square completion for arbitrary compact smooth tests in a
positive superharmonic domain. It is proved by the weak integration-by-parts
identity, not inserted as an assumption about the explicit barrier. -/
theorem picone_test (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x)
    (hLap : ∀x∈D, Δ Y x≤0) (hφ : Test D φ) :
    (∫x, ‖gradient φ x-(φ x/Y x) • gradient Y x‖^2) ≤
      (∫x, ‖gradient φ x‖^2) := by
  have hq := square_ratio_test hD hY hYp hφ
  have hqi := local_green_integrable hD hY hq
  have hgr := local_green hD hY hq
  have hn : (∫x, Δ Y x*positiveSquareRatio φ Y x)≤0 := by
    apply integral_nonpos
    intro x
    by_cases hx : x∈D
    · exact mul_nonpos_of_nonpos_of_nonneg (hLap x hx) (positiveSquareRatio_nonneg x)
    · simp [hq.eq_zero_outside hx]
  have hφtest : Test univ φ := ⟨hφ.1,hφ.2.1,subset_univ _⟩
  have hi := hφtest.memLp_gradient.integrable_norm_pow (show (2:ℕ)≠0 by simp)
  simp only [Measure.restrict_univ] at hi
  simp_rw [picone_identity hD hY hYp hφ]
  rw [integral_sub hi hqi.1]
  linarith

lemma drift_test_memLp (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x) (hφ : Test D φ) :
    MemLp (fun x=>gradient φ x-(φ x/Y x) • gradient Y x) 2 volume := by
  have hc : Continuous (fun x=>(φ x/Y x) • gradient Y x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x∈tsupport φ
    · have hy := hY.contDiffAt (hD.mem_nhds (hφ.2.2 hx))
      exact (hφ.1.continuous.continuousAt.div hy.continuousAt (hYp x (hφ.2.2 hx)).ne').smul
        ((InnerProductSpace.toDual ℝ (Space d)).symm.continuous.continuousAt.comp
          (hy.continuousAt_fderiv (by simp)))
    · apply (continuousAt_const (y:=(0:Space d))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change φ y=0 at hy
      simp [hy]
  have hs : HasCompactSupport (fun x=>(φ x/Y x) • gradient Y x) := by
    apply hφ.2.1.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro x hx
    change (φ x/Y x) • gradient Y x ≠ 0 at hx
    change φ x ≠ 0
    intro hz
    exact hx (by simp [hz])
  have hφt : Test univ φ := ⟨hφ.1,hφ.2.1,subset_univ _⟩
  have hg := hφt.memLp_gradient
  simp only [Measure.restrict_univ] at hg
  exact hg.sub (hc.memLp_of_hasCompactSupport hs)

lemma integral_norm_sq_eq {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure (Space d)} {f : Space d → F} (hf : MemLp f 2 μ) :
    (∫x, ‖f x‖^2 ∂μ)=‖hf.toLp f‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx,real_inner_self_eq_norm_sq]

lemma picone_test_eLpNorm (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x)
    (hLap : ∀x∈D, Δ Y x≤0) (hφ : Test D φ) :
    eLpNorm (fun x=>gradient φ x-(φ x/Y x) • gradient Y x) 2 (volume.restrict D) ≤
      eLpNorm (gradient φ) 2 (volume.restrict D) := by
  have hφt : Test univ φ := ⟨hφ.1,hφ.2.1,subset_univ _⟩
  have hg := hφt.memLp_gradient
  simp only [Measure.restrict_univ] at hg
  have hl := drift_test_memLp hD hY hYp hφ
  have hi := picone_test hD hY hYp hLap hφ
  rw [integral_norm_sq_eq hl,integral_norm_sq_eq hg] at hi
  have hn : ‖hl.toLp _‖ ≤ ‖hg.toLp _‖ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hi
  have hh : eLpNorm (fun x=>gradient φ x-(φ x/Y x) • gradient Y x) 2 volume ≤
      eLpNorm (gradient φ) 2 volume := by
    rw [← Lp.enorm_toLp hl,← Lp.enorm_toLp hg,← ofReal_norm,← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hn
  have he : eLpNorm (gradient φ) 2 (volume.restrict D)=eLpNorm (gradient φ) 2 volume := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hD.measurableSet]
    congr 1
    ext x
    by_cases hx : x∈D
    · simp [hx]
    · simp [hx,hφ.gradient_eq_zero_outside hx]
  rw [he]
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hh

/-- The full H¹₀ ground-state inequality. Fatou's lemma handles the singular
coefficient at the boundary or cone vertex; no bounded-drift or Hardy hypothesis
is imposed. -/
theorem picone_h10_eLpNorm (hD : IsOpen D) {Y w : Space d → ℝ} {G : Space d → Space d}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x)
    (hLap : ∀x∈D, Δ Y x≤0) (hw : H10 D w G) :
    MemLp (fun x=>G x-(w x/Y x) • gradient Y x) 2 (volume.restrict D) ∧
    eLpNorm (fun x=>G x-(w x/Y x) • gradient Y x) 2 (volume.restrict D) ≤
      eLpNorm G 2 (volume.restrict D) := by
  obtain ⟨φ,hφ,hφw,hφG⟩ := SobolevCalculus.H10_sequence hw
  have htψ := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2:ENNReal)≠0)
    (fun n => (hφ n).memLp.aestronglyMeasurable) hw.1.1.aestronglyMeasurable hφw
  have htG := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2:ENNReal)≠0)
    (fun n => (hφ n).memLp_gradient.aestronglyMeasurable) hw.1.2.1.aestronglyMeasurable hφG
  obtain ⟨a,ha,haw⟩ := htψ.exists_seq_tendsto_ae
  obtain ⟨b,hb,hbG⟩ := (htG.comp ha.tendsto_atTop).exists_seq_tendsto_ae
  let ψ := fun n=>φ (a (b n))
  have hψ : ∀n, Test D (ψ n) := fun n=>hφ (a (b n))
  let T := fun n x=>gradient (ψ n) x-(ψ n x/Y x) • gradient Y x
  let L := fun x=>G x-(w x/Y x) • gradient Y x
  have hT : ∀n, MemLp (T n) 2 (volume.restrict D) := fun n=>
    (drift_test_memLp hD hY hYp (hψ n)).mono_measure Measure.restrict_le_self
  have hTL : ∀ᵐ x ∂volume.restrict D, Tendsto (fun n=>T n x) atTop (𝓝 (L x)) := by
    filter_upwards [haw,hbG] with x hx hy
    exact hy.sub (((hx.comp hb.tendsto_atTop).div_const (Y x)).smul tendsto_const_nhds)
  have hLm := aestronglyMeasurable_of_tendsto_ae _
    (fun n=>(hT n).aestronglyMeasurable) hTL
  have hl := Lp.eLpNorm_lim_le_liminf_eLpNorm (p:=2)
    (fun n=>(hT n).aestronglyMeasurable) L hTL
  have hGnorm : Tendsto (fun n=>eLpNorm (gradient (ψ n)) 2 (volume.restrict D)) atTop
      (𝓝 (eLpNorm G 2 (volume.restrict D))) := by
    have hLp : Tendsto (fun n=>(hφ n).memLp_gradient.toLp (gradient (φ n))) atTop
        (𝓝 (hw.1.2.1.toLp G)) := by
      apply tendsto_iff_enorm_sub_tendsto_zero.mpr
      simpa only [← MemLp.toLp_sub,Lp.enorm_toLp] using hφG
    have hh := hLp.enorm.comp (ha.tendsto_atTop.comp hb.tendsto_atTop)
    simpa only [Lp.enorm_toLp,Function.comp_def,ψ] using hh
  have hbound : eLpNorm L 2 (volume.restrict D) ≤ eLpNorm G 2 (volume.restrict D) := by
    refine hl.trans ?_
    rw [← hGnorm.liminf_eq]
    apply Filter.liminf_le_liminf
    · exact Eventually.of_forall fun n=>picone_test_eLpNorm hD hY hYp hLap (hψ n)
    all_goals isBoundedDefault
  exact ⟨⟨hLm, hbound.trans_lt hw.1.2.1.2⟩,hbound⟩

theorem picone_h10 (hD : IsOpen D) {Y w : Space d → ℝ} {G : Space d → Space d}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x)
    (hLap : ∀x∈D, Δ Y x≤0) (hw : H10 D w G) :
    (∫x in D, ‖G x-(w x/Y x) • gradient Y x‖^2) ≤
      (∫x in D, ‖G x‖^2) := by
  obtain ⟨hl,hb⟩ := picone_h10_eLpNorm hD hY hYp hLap hw
  have ht := ENNReal.toReal_mono hw.1.2.1.eLpNorm_ne_top hb
  rw [integral_norm_sq_eq hl,integral_norm_sq_eq hw.1.2.1,Lp.norm_toLp,Lp.norm_toLp]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg ht 2

lemma orthogonal_h10_of_tests {G : Space d → Space d}
    (hG : MemLp G 2 (volume.restrict D))
    (ht : ∀φ, Test D φ → (∫x in D, inner ℝ (G x) (gradient φ x))=0) :
    ∀v V, H10 D v V → (∫x in D, inner ℝ (G x) (V x))=0 := by
  intro v V hv
  obtain ⟨f,hf,_,hfG⟩ := SobolevCalculus.H10_sequence hv
  have hl : Tendsto (fun n => (hf n).memLp_gradient.toLp (gradient (f n)))
      atTop (𝓝 (hv.1.2.1.toLp V)) := by
    apply tendsto_iff_enorm_sub_tendsto_zero.mpr
    simpa only [← MemLp.toLp_sub,Lp.enorm_toLp] using hfG
  have hi : Tendsto (fun n => inner ℝ (hG.toLp G)
      ((hf n).memLp_gradient.toLp (gradient (f n)))) atTop
      (𝓝 (inner ℝ (hG.toLp G) (hv.1.2.1.toLp V))) := tendsto_const_nhds.inner hl
  have he n : inner ℝ (hG.toLp G) ((hf n).memLp_gradient.toLp (gradient (f n)))=0 := by
    rw [L2.inner_def]
    convert! ht (f n) (hf n) using 1
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp,(hf n).memLp_gradient.coeFn_toLp] with x hx hy
    rw [hx,hy]
  simp only [he] at hi
  have hz := tendsto_nhds_unique hi tendsto_const_nhds
  rw [L2.inner_def] at hz
  convert! hz using 1
  apply integral_congr_ae
  filter_upwards [hG.coeFn_toLp,hv.1.2.1.coeFn_toLp] with x hx hy
  rw [hx,hy]

theorem harmonic_h10 (hD : IsOpen D) {u w : Space d → ℝ} {G : Space d → Space d}
    (hu : ContDiffOn ℝ ∞ u D) (hLap : ∀x∈D, Δ u x=0)
    (hG : MemLp (gradient u) 2 (volume.restrict D)) (hw : H10 D w G) :
    (∫x in D, inner ℝ (gradient u x) (G x))=0 := by
  apply orthogonal_h10_of_tests hG _ w G hw
  intro φ hφ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx=>by rw [hφ.gradient_eq_zero_outside hx,inner_zero_right])]
  rw [local_green hD hu hφ]
  suffices hh : (fun x=>Δ u x*φ x)=(fun _=>0) by rw [hh,integral_zero,neg_zero]
  ext x
  by_cases hx:x∈D
  · simp [hLap x hx]
  · simp [hφ.eq_zero_outside hx]

end GroundState
end Bernoulli

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SobolevIdeals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff
namespace Bernoulli.SobolevCalculus

lemma cutPrimitive_eq_zero_of_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) :
    cutPrimitive n t = 0 := by
  unfold cutPrimitive
  rw [intervalIntegral.integral_symm]
  have hz : (∫ s in t..(0:ℝ), cutSlope n s) = 0 := by
    apply intervalIntegral.integral_zero_ae
    exact ae_of_all _ fun s hs => by
      have hs0 : s ≤ 0 := (mem_Ioc.mp (uIoc_of_le ht ▸ hs)).2
      have hh : ((n:ℝ)+1)*s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hs0
      simp [cutSlope,max_eq_right hh]
  simp [hz]

lemma innerCut_zero (n : ℕ) : innerCut n 0 = 0 := by
  apply cutPrimitive_eq_zero_of_nonpos
  simp only [zero_sub]
  exact neg_nonpos.mpr (by positivity)
lemma innerCut_deriv (n : ℕ) (t : ℝ) : HasDerivAt (innerCut n) (innerSlope n t) t := by
  convert! (cutPrimitive_deriv n (t-1/((n:ℝ)+1))).comp t ((hasDerivAt_id t).sub_const (1/((n:ℝ)+1))) using 1
  dsimp [innerSlope]
  ring
lemma innerCut_contDiff (n : ℕ) : ContDiff ℝ 1 (innerCut n) :=
  (cutPrimitive_contDiff n).comp (contDiff_id.sub contDiff_const)
lemma innerCut_lipschitz (n : ℕ) : LipschitzWith 1 (innerCut n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [innerCut,Real.dist_eq,sub_sub_sub_cancel_right,NNReal.coe_one,one_mul] using (cutPrimitive_lipschitz n).dist_le_mul (x-1/((n:ℝ)+1)) (y-1/((n:ℝ)+1))
lemma innerSlope_continuous (n : ℕ) : Continuous (innerSlope n) :=
  (cutSlope_continuous n).comp (continuous_id.sub continuous_const)
lemma innerSlope_norm_le (n : ℕ) (t : ℝ) : ‖innerSlope n t‖ ≤ 1 := cutSlope_norm_le _ _
lemma innerCut_vanish (n : ℕ) {t : ℝ} (ht : t ≤ 1/((n:ℝ)+1)) : innerCut n t = 0 :=
  cutPrimitive_eq_zero_of_nonpos n (sub_nonpos.mpr ht)

lemma innerCut_tendsto (t : ℝ) : Tendsto (fun n => innerCut n t) atTop (𝓝 (max t 0)) := by
  have he : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hd : Tendsto (fun n => innerCut n t - cutPrimitive n t) atTop (𝓝 (0:ℝ)) := by
    apply squeeze_zero_norm _ he
    intro n
    have hh := (cutPrimitive_lipschitz n).norm_sub_le (t-1/((n:ℝ)+1)) t
    simpa only [innerCut,NNReal.coe_one,one_mul,sub_sub_cancel_left,norm_neg,Real.norm_of_nonneg (by positivity : 0≤1/((n:ℝ)+1))] using hh
  simpa only [sub_add_cancel,zero_add] using hd.add (cutPrimitive_tendsto t)

lemma innerSlope_tendsto (t : ℝ) :
    Tendsto (fun n => innerSlope n t) atTop (𝓝 (if 0<t then (1:ℝ) else 0)) := by
  by_cases ht : 0<t
  · simp only [ite_eq_left ht]
    have hg : Tendsto (fun n : ℕ => ((n:ℝ)+1)*t-1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ (-1) ((tendsto_atTop_mono (fun n : ℕ => (show (n:ℝ)≤(n:ℝ)+1 by linarith))
        tendsto_natCast_atTop_atTop).atTop_mul_const ht)
    apply tendsto_const_nhds.congr'
    filter_upwards [hg.eventually_ge_atTop 1] with n hn
    have he : ((n:ℝ)+1)*(t-1/((n:ℝ)+1))=((n:ℝ)+1)*t-1 := by
      field_simp
    dsimp only [innerSlope,cutSlope]
    rw [he,max_eq_left (by linarith),min_eq_right hn]
  · simp only [ite_eq_right ht]
    have hz (n : ℕ) : innerSlope n t=0 := by
      have hm : ((n:ℝ)+1)*(t-1/((n:ℝ)+1))≤0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [show 0≤1/((n:ℝ)+1) by positivity])
      dsimp only [innerSlope,cutSlope]
      rw [max_eq_right hm]
      norm_num
    simp only [hz]
    exact tendsto_const_nhds

lemma h10_innerCut {d : ℕ} {D : Set (Space d)} {w : Space d → ℝ} {G : Space d → Space d}
    (hD : IsOpen D) (hw : H10 D w G) (n : ℕ) :
    H10 D (innerCut n ∘ w) (fun x => innerSlope n (w x) • G x) := by
  have hh := h10_comp_C1 hD hw (innerCut_contDiff n) (innerCut_lipschitz n) (innerCut_zero n)
  have he : deriv (innerCut n)=innerSlope n := funext fun t => (innerCut_deriv n t).deriv
  rwa [he] at hh

theorem h10_positive_domain_inter {d : ℕ} {D : Set (Space d)}
    {S : Set (Space d)} (hS : IsOpen S) (hDS : closure D ⊆ S)
    {w U : Space d → ℝ} {G : Space d → Space d}
    (hD : IsOpen D) (hDc : IsCompact (closure D)) (hw : H10 D w G)
    (hU : Continuous U) (hwn : ∀x, 0≤w x) (hbound : ∀x, w x≤U x)
    (hw0 : ∀x, x∉D → w x=0) :
    H10 ({x | 0<U x} ∩ S) w (D.indicator G) := by
  let P := {x | 0<U x} ∩ S
  have hP : IsOpen P := (isOpen_lt continuous_const hU).inter hS
  have hwg : H10 univ w (D.indicator G) := by
    have hh := hw.zero_extension hD.measurableSet (subset_univ D)
    have he : D.indicator w=w := by
      ext x
      by_cases hx:x∈D <;> simp [hx,hw0 x]
    rwa [he] at hh
  have hwp := hwg.1.mono (subset_univ P)
  have hcut (n : ℕ) : H10 P (innerCut n ∘ w) (fun x=>innerSlope n (w x) • D.indicator G x) := by
    have hh := (h10_innerCut isOpen_univ hwg n).1.mono (subset_univ P)
    have hs : tsupport (innerCut n ∘ w) ⊆ closure D ∩ {x | 1/((n:ℝ)+1)≤U x} := by
      apply closure_minimal _ (isClosed_closure.inter (isClosed_le continuous_const hU))
      intro x hx
      have hx' : innerCut n (w x)≠0 := hx
      have hlt : 1/((n:ℝ)+1)<w x := lt_of_not_ge (fun hn=>hx' (innerCut_vanish n hn))
      refine ⟨subset_closure ?_,(hlt.le.trans (hbound x))⟩
      by_contra hn
      rw [hw0 x hn] at hlt
      have : 0<1/((n:ℝ)+1) := by positivity
      linarith
    apply h10_of_local_compact_support hP hh
    · exact (hDc.inter_right (isClosed_le continuous_const hU)).of_isClosed_subset (isClosed_tsupport _) hs
    · intro x hx
      exact ⟨lt_of_lt_of_le (by positivity : 0<1/((n:ℝ)+1)) (hs hx).2, hDS (hs hx).1⟩
  apply h10_of_strong hwp.1 hwp.2.1 hcut
  · apply tendsto_eLpNorm_zero_of_dominated
      (fun n=>((innerCut_lipschitz n).continuous.comp_aestronglyMeasurable hwp.1.aestronglyMeasurable).sub hwp.1.aestronglyMeasurable)
      (hwp.1.norm.const_smul (2:ℝ))
    · intro n
      exact ae_of_all _ fun x=>by
        have hn : ‖innerCut n (w x)‖≤‖w x‖ := by
          simpa [innerCut_zero] using (innerCut_lipschitz n).norm_sub_le (w x) 0
        calc ‖innerCut n (w x)-w x‖ ≤ ‖innerCut n (w x)‖+‖w x‖ := norm_sub_le _ _
             _ ≤ ‖((2:ℝ) • fun y=>‖w y‖) x‖ := by
                simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),norm_norm]
                linarith
    · exact ae_of_all _ fun x=>by
        simpa only [Pi.sub_apply,Function.comp_apply,max_eq_left (hwn x),sub_self] using (innerCut_tendsto (w x)).sub_const (w x)
  · have hz := gradient_zero_on_zero_set isOpen_univ hwg.1
    simp only [Measure.restrict_univ] at hz
    apply tendsto_eLpNorm_zero_of_dominated
      (fun n=>(((innerSlope_continuous n).comp_aestronglyMeasurable hwp.1.aestronglyMeasurable).smul hwp.2.1.aestronglyMeasurable).sub hwp.2.1.aestronglyMeasurable)
      (hwp.2.1.norm.const_smul (2:ℝ))
    · intro n
      exact ae_of_all _ fun x=>by
        calc ‖innerSlope n (w x) • D.indicator G x-D.indicator G x‖ ≤
            ‖innerSlope n (w x) • D.indicator G x‖+‖D.indicator G x‖ := norm_sub_le _ _
          _ ≤ ‖((2:ℝ) • fun y=>‖D.indicator G y‖) x‖ := by
            rw [norm_smul]
            have hh:=mul_le_mul_of_nonneg_right (innerSlope_norm_le n (w x)) (norm_nonneg (D.indicator G x))
            simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),norm_norm]
            linarith
    · filter_upwards [ae_restrict_of_ae hz] with x hx
      by_cases hp : 0<w x
      · have ht := (innerSlope_tendsto (w x)).smul (tendsto_const_nhds : Tendsto (fun _ : ℕ=>D.indicator G x) atTop (𝓝 (D.indicator G x)))
        simpa only [Pi.sub_apply,Pi.smul_apply',ite_eq_left hp,one_smul,sub_self] using ht.sub_const (D.indicator G x)
      · have hwz : w x=0 := le_antisymm (not_lt.mp hp) (hwn x)
        simp only [Pi.sub_apply,Pi.smul_apply',hx hwz,smul_zero,sub_self]
        exact tendsto_const_nhds

end Bernoulli.SobolevCalculus

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.LowerComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Laplacian
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}
namespace GroundState

lemma lower_variation (c : Space d) (r : ℝ) (hr : 0<r)
    {u Y w : Space d → ℝ} {G : Space d → Space d}
    (hu : Continuous u) (hun : ∀x, 0≤u x)
    (huc : ContDiffOn ℝ ∞ u {x | 0<u x}) (hul : ∀x, 0<u x → Δ u x=0)
    (huG : H1Loc univ u (gradient u))
    (hY : ContDiffOn ℝ ∞ Y {x | 0<u x})
    (hYp : ∀x, 0<u x → 0<Y x) (hYlap : ∀x, 0<u x → Δ Y x≤0)
    (hw : H10 (Metric.ball c r) w G) (hwn : ∀x, 0≤w x)
    (hwu : ∀x, w x≤u x) (hw0 : ∀x, x∉Metric.ball c r → w x=0) :
    (∫x in Metric.ball c r, inner ℝ (gradient u x) (G x))=0 ∧
    MemLp (fun x=>G x-(w x/Y x) • gradient Y x) 2 (volume.restrict (Metric.ball c r)) ∧
    (∫x in Metric.ball c r, ‖G x-(w x/Y x) • gradient Y x‖^2) ≤
      (∫x in Metric.ball c r, ‖G x‖^2) := by
  let B := Metric.ball c r
  let S := Metric.ball c (r+1)
  let Q := {x | 0<u x} ∩ S
  let E := B.indicator G
  let L := fun x=>E x-(w x/Y x) • gradient Y x
  have hB : IsOpen B := Metric.isOpen_ball
  have hS : IsOpen S := Metric.isOpen_ball
  have hQ : IsOpen Q := (isOpen_lt continuous_const hu).inter hS
  have hBS : closure B ⊆ S := by
    change closure (Metric.ball c r) ⊆ Metric.ball c (r+1)
    exact (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball (by linarith))

  have hwQ : H10 Q w E := SobolevCalculus.h10_positive_domain_inter hS hBS hB
    (Metric.isBounded_ball.isCompact_closure) hw hu hwn hwu hw0
  have hwE : H10 univ w E := by
    have hh := hw.zero_extension hB.measurableSet (subset_univ B)
    have he : B.indicator w=w := by
      ext x
      by_cases hx:x∈B
      · simp [hx]
      · simp [hx,hw0 x hx]
    rwa [he] at hh
  have hE0 : ∀ᵐ x ∂volume, w x=0 → E x=0 := by
    simpa only [Measure.restrict_univ] using SobolevCalculus.gradient_zero_on_zero_set isOpen_univ hwE.1
  have hwQ0 : ∀x, x∉Q → w x=0 := by
    intro x hx
    by_cases hxu:0<u x
    · have hxS : x∉S := fun h=>hx ⟨hxu,h⟩
      exact hw0 x (fun h=>hxS (hBS (subset_closure h)))
    · have hu0 : u x = 0 := le_antisymm (not_lt.mp hxu) (hun x)
      exact le_antisymm (by simpa only [hu0] using hwu x) (hwn x)
  have hEint : (∫x in Q, ‖E x‖^2)=(∫x in B, ‖G x‖^2) := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero (s:=Q) (by
      filter_upwards [hE0] with x hx hy
      simp [hx (hwQ0 x hy)])]
    rw [← integral_indicator hB.measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ fun x=>by by_cases hx:x∈B <;> simp [E,hx]
  have hEorth : (∫x in Q, inner ℝ (gradient u x) (E x))=(∫x in B, inner ℝ (gradient u x) (G x)) := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero (s:=Q) (by
      filter_upwards [hE0] with x hx hy
      simp [hx (hwQ0 x hy)])]
    rw [← integral_indicator hB.measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ fun x=>by by_cases hx:x∈B <;> simp [E,hx]
  have hL0 : ∀ᵐ x ∂volume, x∉Q → L x=0 := by
    filter_upwards [hE0] with x hx hy
    simp [L,hwQ0 x hy,hx (hwQ0 x hy)]
  have hLQ : MemLp L 2 (volume.restrict Q) :=
    (picone_h10_eLpNorm hQ (hY.mono inter_subset_left) (fun x hx=>hYp x hx.1)
      (fun x hx=>hYlap x hx.1) hwQ).1
  have hLglobal : MemLp L 2 volume := by
    apply ((memLp_indicator_iff_restrict hQ.measurableSet).mpr hLQ).ae_eq
    filter_upwards [hL0] with x hx
    by_cases hy:x∈Q <;> simp [hy,hx]
  have hLB : MemLp (fun x=>G x-(w x/Y x) • gradient Y x) 2 (volume.restrict B) := by
    apply (hLglobal.mono_measure Measure.restrict_le_self).ae_eq
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    simp [L,E,hx]
  have hLint : (∫x in Q, ‖L x‖^2)=(∫x in B, ‖G x-(w x/Y x) • gradient Y x‖^2) := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero (s:=Q) (by
      filter_upwards [hL0] with x hx hy
      simp [hx hy])]
    rw [← integral_indicator hB.measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ fun x=>by
      by_cases hx:x∈B
      · simp [L,E,hx]
      · simp [L,E,hx,hw0 x hx]
  refine ⟨?_,hLB,?_⟩
  · rw [← hEorth]
    exact harmonic_h10 hQ (huc.mono inter_subset_left) (fun x hx=>hul x hx.1)
      ((huG c (r+1) (by linarith) (subset_univ _)).2.1.mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)) hwQ
  · rw [← hLint,← hEint]
    exact picone_h10 hQ (hY.mono inter_subset_left) (fun x hx=>hYp x hx.1)
      (fun x hx=>hYlap x hx.1) hwQ

theorem lower_comparison (c : Space d) (r : ℝ) (hr : 0<r)
    {u Y v : Space d → ℝ} {V : Space d → Space d}
    (hu : Continuous u) (hun : ∀x, 0≤u x)
    (huc : ContDiffOn ℝ ∞ u {x | 0<u x}) (hul : ∀x, 0<u x → Δ u x=0)
    (huG : H1Loc univ u (gradient u))
    (hY : ContDiffOn ℝ ∞ Y {x | 0<u x})
    (hYp : ∀x, 0<u x → 0<Y x) (hYlap : ∀x, 0<u x → Δ Y x≤0)
    (hslope : ∀x, 0<u x → 1≤‖gradient u x-(u x/Y x) • gradient Y x‖^2)
    (hv : H1 (Metric.ball c r) v V)
    (hvn : ∀ᵐ x ∂volume.restrict (Metric.ball c r), 0≤v x)
    (hvu : ∀ᵐ x ∂volume.restrict (Metric.ball c r), v x≤u x)
    (htrace : H10 (Metric.ball c r) (fun x=>v x-u x) (fun x=>V x-gradient u x)) :
    energy (Metric.ball c r) u (gradient u)≤energy (Metric.ball c r) v V := by
  let B := Metric.ball c r
  let A := gradient u
  let G := fun x=>A x-V x
  let w := B.indicator (fun x=>min (max (u x-v x) 0) (u x))
  have hB : IsOpen B := Metric.isOpen_ball
  have hw0 : ∀x, x∉B → w x=0 := fun x hx=>by simp [w,hx]
  have hwn : ∀x, 0≤w x := by
    intro x
    by_cases hx:x∈B
    · simp only [w,indicator_of_mem hx]
      exact le_min (le_max_right _ _) (hun x)
    · simp [w,hx]
  have hwu : ∀x, w x≤u x := by
    intro x
    by_cases hx:x∈B
    · simp only [w,indicator_of_mem hx]
      exact min_le_right _ _
    · simpa [w,hx] using hun x
  have hweq : w =ᵐ[volume.restrict B] (fun x=>u x-v x) := by
    filter_upwards [hvn,hvu,ae_restrict_mem hB.measurableSet] with x hx hy hz
    simp [w,hz,max_eq_left (sub_nonneg.mpr hy),min_eq_left (by linarith : u x-v x≤u x)]
  have hw : H10 B w G := by
    apply htrace.neg.congr
    · filter_upwards [hweq] with x hx
      simp [hx]
    · exact ae_of_all _ fun x=>neg_sub (V x) (A x)
  obtain ⟨hort,hL,hlower⟩ := lower_variation c r hr hu hun huc hul huG hY hYp hYlap hw hwn hwu hw0
  let L := fun x=>G x-(w x/Y x) • gradient Y x
  have huB := huG c r hr (subset_univ _)
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hU2 := huB.2.1.integrable_norm_pow (by norm_num)
  have hV2 := hv.2.1.integrable_norm_pow (by norm_num)
  have hG : MemLp G 2 (volume.restrict B) := huB.2.1.sub hv.2.1
  have hG2 := hG.integrable_norm_pow (by norm_num)
  have hL2 := hL.integrable_norm_pow (by norm_num)
  have hUV := integrable_inner_of_memLp huB.2.1 hG
  have hUE := hU2.add (integrable_phase huB.1.aestronglyMeasurable)
  have hVE := hV2.add (integrable_phase hv.1.aestronglyMeasurable)
  have hz := SobolevCalculus.gradient_zero_on_zero_set hB hv
  change Integrable (fun x=>‖A x‖^2) (volume.restrict B) at hU2
  change Integrable (fun x=>‖L x‖^2) (volume.restrict B) at hL2
  change Integrable (fun x=>inner ℝ (A x) (G x)) (volume.restrict B) at hUV
  change Integrable (fun x=>‖A x‖^2+(if 0<u x then (1:ℝ) else 0)) (volume.restrict B) at hUE
  change Integrable (fun x=>‖V x‖^2+(if 0<v x then (1:ℝ) else 0)) (volume.restrict B) at hVE
  have hip : energy B u A ≤ energy B v V + 2*(∫x in B, inner ℝ (A x) (G x))+
      (∫x in B, ‖L x‖^2)-(∫x in B, ‖G x‖^2) := by
    have hint := integral_mono_ae hUE (((hVE.add (hUV.const_mul 2)).add hL2).sub hG2)
    have he := integral_sub ((hVE.add (hUV.const_mul 2)).add hL2) hG2
    have he1 := integral_add (hVE.add (hUV.const_mul 2)) hL2
    have he2 := integral_add hVE (hUV.const_mul 2)
    have he3 := integral_const_mul (μ:=volume.restrict B) 2 (fun x=>inner ℝ (A x) (G x))
    suffices hp : _ from by
      have ht := hint hp
      dsimp only [Pi.add_apply,Pi.sub_apply] at ht he he1 he2 he3
      change (∫x in B, ‖A x‖^2+(if 0<u x then (1:ℝ) else 0))≤_
      change _≤(∫x in B, ‖V x‖^2+(if 0<v x then (1:ℝ) else 0))+_+_-_
      linarith
    clear he he1 he2 he3 hint
    filter_upwards [hvn,hweq,hz] with x hxn hxw hxz
    have hphase : (if 0<u x then (1:ℝ) else 0)-(if 0<v x then (1:ℝ) else 0)≤‖L x‖^2 := by
      by_cases hu0:0<u x
      · by_cases hv0:0<v x
        · simp [hu0,hv0]
        · have hvz : v x=0 := le_antisymm (not_lt.mp hv0) hxn
          have hLx : L x=A x-(u x/Y x) • gradient Y x := by simp [L,G,hxw,hvz,hxz hvz]
          simpa [hu0,hv0,hLx] using hslope x hu0
      · by_cases hv0:0<v x
        · simp only [hu0,hv0,ite_false,ite_true,zero_sub]
          nlinarith [sq_nonneg ‖L x‖]
        · simp [hu0,hv0]
    have hid : ‖V x‖^2=‖A x‖^2+‖G x‖^2-2*inner ℝ (A x) (G x) := by
      simp only [G,inner_sub_right,real_inner_self_eq_norm_sq,norm_sub_sq_real]
      ring
    simp only [Pi.sub_apply,Pi.add_apply] at *
    linarith
  change (∫x in B, inner ℝ (A x) (G x))=0 at hort
  change (∫x in B, ‖L x‖^2)≤(∫x in B, ‖G x‖^2) at hlower
  linarith
end GroundState

namespace DeSilvaJerison
lemma U_smooth_positive : ContDiffOn ℝ ∞ U {x | 0<U x} := by
  intro x hx
  obtain ⟨hx0,ha⟩ := (U_pos_iff x).mp hx
  have hs : ContDiffAt ℝ ∞ Usigned x :=
    (signed_contDiffAt hx0 (ha.trans t7_lt_one)).const_smul κ
  exact (hs.congr_of_eventuallyEq (U_eventuallyEq_Usigned hx)).contDiffWithinAt

theorem U_lower_comparison (c : Space 7) (r : ℝ) (hr : 0<r)
    {v : Space 7 → ℝ} {V : Space 7 → Space 7}
    (hv : H1 (Metric.ball c r) v V)
    (hvn : ∀ᵐ x ∂volume.restrict (Metric.ball c r), 0≤v x)
    (hvu : ∀ᵐ x ∂volume.restrict (Metric.ball c r), v x≤U x)
    (htrace : H10 (Metric.ball c r) (fun x=>v x-U x) (fun x=>V x-gradient U x)) :
    energy (Metric.ball c r) U (gradient U)≤energy (Metric.ball c r) v V := by
  apply GroundState.lower_comparison c r hr U_continuous U_nonneg U_smooth_positive
    (fun x hx=>(U_harmonic x hx).2.self_of_nhds) U_h1loc (Y:=YSub)
    (fun x hx=>(YSub_contDiffAt ((U_pos_iff x).mp hx).1).contDiffWithinAt)
    (fun x hx=>YSub_pos ((U_pos_iff x).mp hx).1)
    (fun x hx=>YSub_superharmonic ((U_pos_iff x).mp hx).1)
    (fun x hx=>lower_groundstate_slope hx) hv hvn hvu htrace
end DeSilvaJerison
end Bernoulli

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ThresholdRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uF

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Bernoulli.ThresholdRecovery

section L2
variable {α : Type uα} {F : Type uF} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma integral_norm_sq_eq {f : α → F} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

lemma tendsto_integral_norm_sq {f : ℕ → α → F} {g : α → F}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hc : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖f n x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖g x‖ ^ 2 ∂μ)) := by
  have ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
    apply tendsto_iff_enorm_sub_tendsto_zero.mpr
    simpa only [← MemLp.toLp_sub, Lp.enorm_toLp] using hc
  have hi (n : ℕ) := integral_norm_sq_eq (hf n)
  simp_rw [hi, integral_norm_sq_eq hg]
  exact ht.norm.pow 2

end L2

lemma ramp_continuous (ε:ℝ) : Continuous (ramp ε) := by
  unfold ramp
  fun_prop
lemma ramp_nonneg (ε t:ℝ) : 0≤ramp ε t := le_min (le_max_right _ _) zero_le_one
lemma ramp_le_one (ε t:ℝ) : ramp ε t≤1 := min_le_right _ _
lemma ramp_norm_le (ε t:ℝ) : ‖ramp ε t‖≤1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (ramp_nonneg _ _)]
  exact ramp_le_one _ _
lemma envelope_norm_le (ε u w:ℝ) : ‖envelope ε u w‖≤1 := by
  unfold envelope
  split_ifs
  · norm_num
  · exact ramp_norm_le _ _
lemma phase_threshold_le {ε u w:ℝ} (hε:0<ε) (hu:0≤u) :
    (if 0<u+max (w-ε) 0 then (1:ℝ) else 0)≤envelope ε u w := by
  by_cases hup:0<u
  · rw [envelope,ite_eq_left hup]
    split_ifs <;> norm_num
  · have hu0:u=0:=le_antisymm (not_lt.mp hup) hu
    subst u
    rw [envelope,ite_eq_right (lt_irrefl _)]
    by_cases hw:ε<w
    · have hdiv:1<w/ε:=(lt_div_iff₀ hε).mpr (by simpa using hw)
      simp only [ramp,max_eq_left (by linarith : 0≤w/ε),min_eq_right hdiv.le]
      split_ifs <;> norm_num
    · have he:w-ε≤0:=sub_nonpos.mpr (not_lt.mp hw)
      simp only [max_eq_right he,add_zero,lt_self_iff_false,ite_false]
      exact ramp_nonneg _ _
lemma envelope_le_phase {ε u w:ℝ} (_hε:0<ε) (hu:0≤u) (hw:0≤w) :
    envelope ε u w≤(if 0<u+w then (1:ℝ) else 0) := by
  by_cases hup:0<u
  · simp only [envelope,ite_eq_left hup,ite_eq_left (by linarith : 0<u+w),le_refl]
  · rw [envelope,ite_eq_right hup]
    by_cases hsum:0<u+w
    · rw [ite_eq_left hsum]; exact ramp_le_one _ _
    · have hw0:w=0:=by linarith
      simp [hw0,hup,ramp]
section Integrals
variable {α : Type uα} [MeasurableSpace α] {μ:Measure α} [IsFiniteMeasure μ]
omit [IsFiniteMeasure μ] in
lemma envelope_measurable {u w:α→ℝ} (hu:AEStronglyMeasurable u μ)
    (hw:AEStronglyMeasurable w μ) (ε:ℝ) :
    AEStronglyMeasurable (fun x=>envelope ε (u x) (w x)) μ := by
  have hm:Measurable (fun p:ℝ×ℝ=>envelope ε p.1 p.2) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
      ((ramp_continuous ε).measurable.comp measurable_snd)
  exact (hm.comp_aemeasurable (hu.aemeasurable.prodMk hw.aemeasurable)).aestronglyMeasurable
lemma envelope_integrable {u w:α→ℝ} (hu:AEStronglyMeasurable u μ)
    (hw:AEStronglyMeasurable w μ) (ε:ℝ) :
    Integrable (fun x=>envelope ε (u x) (w x)) μ :=
  (integrable_const (1:ℝ)).mono' (envelope_measurable hu hw ε)
    (Eventually.of_forall fun _=>envelope_norm_le _ _ _)
lemma envelope_integral_tendsto {u w:α→ℝ} {f:ℕ→α→ℝ}
    (hu:AEStronglyMeasurable u μ) (hf:∀n,AEStronglyMeasurable (f n) μ)
    (hp:∀ᵐ x ∂μ,Tendsto (fun n=>f n x) atTop (𝓝 (w x))) (ε:ℝ) :
    Tendsto (fun n=>∫x,envelope ε (u x) (f n x) ∂μ) atTop
      (𝓝 (∫x,envelope ε (u x) (w x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _=>1)
  · exact fun n=>envelope_measurable hu (hf n) ε
  · exact integrable_const _
  · exact fun _=>Eventually.of_forall fun _=>envelope_norm_le _ _ _
  · filter_upwards [hp] with x hx
    by_cases hu':0<u x
    · simp only [envelope,ite_eq_left hu']; exact tendsto_const_nhds
    · simp only [envelope,ite_eq_right hu']
      exact ((ramp_continuous ε).tendsto (w x)).comp hx
end Integrals

variable {d:ℕ}
lemma h1_const_ball (c:Space d) (r a:ℝ) :
    H1 (Metric.ball c r) (fun _=>a) (fun _=>0) := by
  simpa only [gradient_fun_const',Pi.zero_apply] using (LipschitzSobolev.h1_ball (LipschitzWith.const a) c r)
lemma h1_sub_const_ball {c:Space d} {r:ℝ} {u:Space d→ℝ} {G:Space d→Space d}
    (hu:H1 (Metric.ball c r) u G) (a:ℝ) :
    H1 (Metric.ball c r) (fun x=>u x-a) G := by
  simpa only [sub_zero] using hu.sub (h1_const_ball c r a)
/-- Strong H1-density gives the exact upper comparison after fixed positive
threshold truncation. The discontinuous phase term is controlled by a continuous
ramp, not by an unjustified continuity assertion for positivity sets. -/
lemma fixed_threshold_limit {c:Space d} {r:ℝ} {u w:Space d→ℝ}
    {G W:Space d→Space d} (hu:H1 (Metric.ball c r) u G)
    (hw:H10 (Metric.ball c r) w W)
    (hun:∀ᵐ x ∂volume.restrict (Metric.ball c r),0≤u x)
    (hwn:∀ᵐ x ∂volume.restrict (Metric.ball c r),0≤w x)
    {ε:ℝ} (hε:0<ε)
    (hcomp:∀φ:Space d→ℝ,Test (Metric.ball c r) φ →
      energy (Metric.ball c r) u G≤energy (Metric.ball c r)
        (fun x=>u x+max (φ x-ε) 0)
        (fun x=>G x+(if 0<φ x-ε then (1:ℝ) else 0) • gradient φ x)) :
    energy (Metric.ball c r) u G≤
      (∫x in Metric.ball c r,‖G x+(if 0<w x-ε then (1:ℝ) else 0) • W x‖^2)+
      (∫x in Metric.ball c r,if 0<u x+w x then (1:ℝ) else 0) := by
  let B:=Metric.ball c r
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨f,hf,hfw,hfW⟩:=SobolevCalculus.H10_sequence hw
  obtain ⟨ns,hns,hpoint⟩:=(tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2:ℝ≥0∞)≠0) (fun n => (hf n).memLp.aestronglyMeasurable) hw.1.1.aestronglyMeasurable hfw).exists_seq_tendsto_ae
  let F:ℕ→Space d→Space d:=fun n x=>G x+(if 0<f (ns n) x-ε then (1:ℝ) else 0) • gradient (f (ns n)) x
  let V:Space d→Space d:=fun x=>G x+(if 0<w x-ε then (1:ℝ) else 0) • W x
  have hs (n:ℕ):H1 B (fun x=>max (f (ns n) x-ε) 0)
      (fun x=>(if 0<f (ns n) x-ε then (1:ℝ) else 0) • gradient (f (ns n)) x):=
    SobolevCalculus.h1_positivePart Metric.isOpen_ball (h1_sub_const_ball (hf (ns n)).h1 ε)
  have hV:H1 B (fun x=>u x+max (w x-ε) 0) V :=
    hu.add (SobolevCalculus.h1_positivePart Metric.isOpen_ball (h1_sub_const_ball hw.1 ε))
  have hF(n:ℕ):H1 B (fun x=>u x+max (f (ns n) x-ε) 0) (F n):=hu.add (hs n)
  have hstrong:Tendsto (fun n=>eLpNorm (F n-V) 2 (volume.restrict B)) atTop (𝓝 0) := by
    have hp:∀ᵐ x ∂volume.restrict B,Tendsto (fun n=>f (ns n) x-ε) atTop (𝓝 (w x-ε)):=by
      filter_upwards [hpoint] with x hx
      exact hx.sub_const ε
    have hh:=SobolevCalculus.positivePart_gradient_strong_of_ae Metric.isOpen_ball
      (h1_sub_const_ball hw.1 ε) (fun n=>h1_sub_const_ball (hf (ns n)).h1 ε) hp
      (hfW.comp hns.tendsto_atTop)
    convert hh using 1
    funext n
    congr 1
    funext x
    dsimp [F,V]
    abel
  have hlim:=tendsto_integral_norm_sq (fun n=>(hF n).2.1) hV.2.1 hstrong
  have henv:=envelope_integral_tendsto hu.1.aestronglyMeasurable
    (fun n=>(hf (ns n)).h1.1.aestronglyMeasurable) hpoint ε
  have hbound(n:ℕ):energy B u G≤(∫x in B,‖F n x‖^2)+
      (∫x in B,envelope ε (u x) (f (ns n) x)) := by
    apply (hcomp _ (hf (ns n))).trans
    rw [energy,integral_add ((hF n).2.1.integrable_norm_pow (by norm_num))
      (integrable_phase (hF n).1.aestronglyMeasurable)]
    apply add_le_add le_rfl
    apply integral_mono_ae (integrable_phase (hF n).1.aestronglyMeasurable)
      (envelope_integrable hu.1.aestronglyMeasurable (hf (ns n)).h1.1.aestronglyMeasurable ε)
    filter_upwards [hun] with x hx
    exact phase_threshold_le hε hx
  have hh:=ge_of_tendsto (hlim.add henv) (Eventually.of_forall hbound)
  apply hh.trans
  apply add_le_add le_rfl
  apply integral_mono_ae (envelope_integrable hu.1.aestronglyMeasurable hw.1.1.aestronglyMeasurable ε)
    (integrable_phase (hu.add hw.1).1.aestronglyMeasurable)
  filter_upwards [hun,hwn] with x hx hwx
  exact envelope_le_phase hε hx hwx
/-- The faithful arbitrary-Sobolev upper-variation bridge. The sole comparison
input here is the concrete thresholded compact-test inequality; all density and
phase-limit steps are proved, without regularity assumptions on the competitor. -/
theorem upper_variation_of_threshold_tests {c:Space d} {r:ℝ} {u w:Space d→ℝ}
    {G W:Space d→Space d} (hu:H1 (Metric.ball c r) u G)
    (hw:H10 (Metric.ball c r) w W)
    (hun:∀ᵐ x ∂volume.restrict (Metric.ball c r),0≤u x)
    (hwn:∀ᵐ x ∂volume.restrict (Metric.ball c r),0≤w x)
    (hcomp:∀ε:ℝ,0<ε → ∀φ:Space d→ℝ,Test (Metric.ball c r) φ →
      energy (Metric.ball c r) u G≤energy (Metric.ball c r)
        (fun x=>u x+max (φ x-ε) 0)
        (fun x=>G x+(if 0<φ x-ε then (1:ℝ) else 0) • gradient φ x)) :
    energy (Metric.ball c r) u G≤energy (Metric.ball c r)
      (fun x=>u x+w x) (fun x=>G x+W x) := by
  let B:=Metric.ball c r
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let ε:ℕ→ℝ:=fun n=>1/((n:ℝ)+1)
  have hε(n:ℕ):0<ε n:=by dsimp [ε]; positivity
  have hεlim:Tendsto ε atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  let F:ℕ→Space d→Space d:=fun n x=>G x+(if 0<w x-ε n then (1:ℝ) else 0) • W x
  let V:Space d→Space d:=fun x=>G x+(if 0<w x then (1:ℝ) else 0) • W x
  have hF(n:ℕ):H1 B (fun x=>u x+max (w x-ε n) 0) (F n):=
    hu.add (SobolevCalculus.h1_positivePart Metric.isOpen_ball (h1_sub_const_ball hw.1 (ε n)))
  have hV:H1 B (fun x=>u x+max (w x) 0) V:=
    hu.add (SobolevCalculus.h1_positivePart Metric.isOpen_ball hw.1)
  have hstrong:Tendsto (fun n=>eLpNorm (F n-V) 2 (volume.restrict B)) atTop (𝓝 0) := by
    have hp:∀ᵐ x ∂volume.restrict B,Tendsto (fun n=>w x-ε n) atTop (𝓝 (w x)):=
      Eventually.of_forall fun x=>by simpa only [sub_zero] using tendsto_const_nhds.sub hεlim
    have hWW:Tendsto (fun _n:ℕ=>eLpNorm (W-W) 2 (volume.restrict B)) atTop (𝓝 0):=by
      simp only [sub_self,eLpNorm_zero]
      exact tendsto_const_nhds
    have hh:=SobolevCalculus.positivePart_gradient_strong_of_ae Metric.isOpen_ball
      hw.1 (fun n=>h1_sub_const_ball hw.1 (ε n)) hp hWW
    convert hh using 1
    funext n
    congr 1
    funext x
    dsimp [F,V]
    abel
  have hVe:V =ᵐ[volume.restrict B] (fun x=>G x+W x):=by
    filter_upwards [hwn,SobolevCalculus.gradient_zero_on_zero_set Metric.isOpen_ball hw.1] with x hx h0
    by_cases hp:0<w x
    · simp [V,hp]
    · have hz:w x=0:=le_antisymm (not_lt.mp hp) hx
      simp [V,hp,h0 hz]
  have hnorm:(∫x in B,‖V x‖^2)=(∫x in B,‖G x+W x‖^2):=
    integral_congr_ae (hVe.mono fun x hx=>by
      change ‖V x‖^2=‖G x+W x‖^2
      rw [hx])
  have hlim:=tendsto_integral_norm_sq (fun n=>(hF n).2.1) hV.2.1 hstrong
  rw [hnorm] at hlim
  have hb(n:ℕ):energy B u G≤(∫x in B,‖F n x‖^2)+
      (∫x in B,if 0<u x+w x then (1:ℝ) else 0):=
    fixed_threshold_limit hu hw hun hwn (hε n) (hcomp (ε n) (hε n))
  have hh:=ge_of_tendsto (hlim.add_const (∫x in B,if 0<u x+w x then (1:ℝ) else 0))
    (Eventually.of_forall hb)
  change energy B u G ≤ energy B (fun x=>u x+w x) (fun x=>G x+W x)
  change energy B u G ≤ ∫x in B, ‖G x+W x‖^2 + if 0<u x+w x then (1:ℝ) else 0
  rw [integral_add ((hu.add hw.1).2.1.integrable_norm_pow (by norm_num))
    (integrable_phase (hu.add hw.1).1.aestronglyMeasurable)]
  exact hh
end Bernoulli.ThresholdRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison

lemma threshold_lipschitz {φ:Space 7→ℝ} {D:Set (Space 7)} (hφ:Test D φ) (δ:ℝ) :
    ∃K:ℝ≥0,LipschitzWith K (fun x=>max (φ x-δ) 0) := by
  obtain ⟨K,hK⟩:=hφ.1.lipschitzWith_of_hasCompactSupport hφ.2.1 (by simp)
  have hD:LipschitzWith K (fun x=>φ x-δ):=by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hK.dist_le_mul x y
  exact ⟨K,hD.max_const 0⟩
lemma threshold_support {φ:Space 7→ℝ} {δ:ℝ} (hδ:0≤δ):
    tsupport (fun x=>U x+max (φ x-δ) 0-U x)⊆tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hφ:φ x=0:=image_eq_zero_of_notMem_tsupport hn
  have hh:max (φ x-δ) 0=0:=by rw [hφ,max_eq_right (by linarith)]
  exact hx (by dsimp; rw [hh]; ring)

/-- The actual upper foliation comparison, transferred through H1-zero trace
closure to every admissible upper Sobolev competitor on every ball. -/
theorem U_upper_comparison (c:Space 7) (r:ℝ) (hr:0<r)
    {v:Space 7→ℝ} {V:Space 7→Space 7}
    (hv:H1 (Metric.ball c r) v V)
    (hUv:∀ᵐ x ∂volume.restrict (Metric.ball c r),U x≤v x)
    (htrace:H10 (Metric.ball c r) (fun x=>v x-U x) (fun x=>V x-gradient U x)) :
    energy (Metric.ball c r) U (gradient U)≤energy (Metric.ball c r) v V := by
  have hu:=U_h1loc c r hr (subset_univ _)
  have hh:=ThresholdRecovery.upper_variation_of_threshold_tests hu ⟨hv.sub hu, htrace.2⟩
    (Eventually.of_forall U_nonneg) (hUv.mono fun x hx=>sub_nonneg.mpr hx)
  have hcomp:∀δ:ℝ,0<δ → ∀φ:Space 7→ℝ,Test (Metric.ball c r) φ →
      energy (Metric.ball c r) U (gradient U)≤energy (Metric.ball c r)
      (fun x=>U x+max (φ x-δ) 0)
      (fun x=>gradient U x+(if 0<φ x-δ then (1:ℝ) else 0) • gradient φ x):=by
    intro δ hδ φ hφ
    obtain ⟨K,hK⟩:=exists_lipschitz_U
    obtain ⟨L,hL⟩:=threshold_lipschitz hφ δ
    have hvL:=hK.add hL
    have hsub:=threshold_support (φ:=φ) hδ.le
    have hc:HasCompactSupport (fun x=>U x+max (φ x-δ) 0-U x):=
      hφ.2.1.of_isClosed_subset (isClosed_tsupport _) hsub
    have he:=U_upper_lipschitz_comparison hvL (fun x=>by have hh:=le_max_right (φ x-δ) 0; linarith) hc (hsub.trans hφ.2.2)
    have hH:H1 (Metric.ball c r) (fun x=>U x+max (φ x-δ) 0)
        (fun x=>gradient U x+(if 0<φ x-δ then (1:ℝ) else 0) • gradient φ x):=
      hu.add (SobolevCalculus.h1_positivePart Metric.isOpen_ball (ThresholdRecovery.h1_sub_const_ball hφ.h1 δ))
    rwa [energy_congr (EventuallyEq.refl _ _) ((LipschitzSobolev.h1_ball hvL c r).gradient_unique Metric.isOpen_ball hH)] at he
  simpa only [add_sub_cancel] using hh hcomp
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.GlobalMinimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison

/-- The constructed double-cone is a global energy minimizer against the full
arbitrary Sobolev competitor class. Upper and lower comparisons are joined by
the exact Sobolev lattice identity, including its contact-level gradients. -/
theorem U_global_minimizer_oai : GlobalMinimizer U := by
  refine ⟨isOpen_univ,gradient U,U_h1loc,?_,?_⟩
  · simpa only [Measure.restrict_univ] using (Eventually.of_forall U_nonneg : ∀ᵐ x:Space 7 ∂volume,0≤U x)
  intro c r hr hB v V hv hvn htrace
  let B:=Metric.ball c r
  let G:=gradient U
  have hu:H1 B U G:=U_h1loc c r hr (subset_univ _)
  have hpos:=SobolevCalculus.h10_positivePart Metric.isOpen_ball htrace
  have hneg:H10 B (fun x=>max (U x-v x) 0)
      (fun x=>(if 0<U x-v x then (1:ℝ) else 0) • (G x-V x)):=by
    simpa only [neg_sub] using SobolevCalculus.h10_positivePart Metric.isOpen_ball htrace.neg
  let p:=fun x=>U x+max (v x-U x) 0
  let P:=fun x=>G x+(if 0<v x-U x then (1:ℝ) else 0) • (V x-G x)
  let m:=fun x=>U x-max (U x-v x) 0
  let M:=fun x=>G x-(if 0<U x-v x then (1:ℝ) else 0) • (G x-V x)
  have hp:H1 B p P:=hu.add hpos.1
  have hm:H1 B m M:=hu.sub hneg.1
  have hpt:H10 B (fun x=>p x-U x) (fun x=>P x-G x):=by
    apply hpos.congr
    · exact Eventually.of_forall (fun x=>by dsimp [p]; ring)
    · exact Eventually.of_forall (fun x=>by dsimp [P]; abel)
  have hmt:H10 B (fun x=>m x-U x) (fun x=>M x-G x):=by
    apply hneg.neg.congr
    · exact Eventually.of_forall (fun x=>by dsimp [m]; ring)
    · exact Eventually.of_forall (fun x=>by dsimp [M]; abel)
  have hUp:∀ᵐ x ∂volume.restrict B,U x≤p x:=
    Eventually.of_forall fun x=>le_add_of_nonneg_right (le_max_right _ _)
  have hmU:∀ᵐ x ∂volume.restrict B,m x≤U x:=
    Eventually.of_forall fun x=>sub_le_self _ (le_max_right _ _)
  have hmn:∀ᵐ x ∂volume.restrict B, 0 ≤ m x:=by
    filter_upwards [hvn] with x hx
    change 0≤U x-max (U x-v x) 0
    exact sub_nonneg.mpr (max_le (by linarith) (U_nonneg x))
  have hupper:=U_upper_comparison c r hr hp hUp hpt
  have hlower:=U_lower_comparison c r hr hm hmn hmU hmt
  let :IsFiniteMeasure (volume.restrict B):=isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hI {f:Space 7→ℝ} {F:Space 7→Space 7} (h:H1 B f F):
      Integrable (fun x=>‖F x‖^2+if 0<f x then (1:ℝ) else 0) (volume.restrict B):=
    (h.2.1.integrable_norm_pow (by norm_num)).add (integrable_phase h.1.aestronglyMeasurable)
  have henergy:energy B m M+energy B p P=energy B U G+energy B v V:=by
    rw [energy,energy,energy,energy,←integral_add (hI hm) (hI hp),←integral_add (hI hu) (hI hv)]
    apply integral_congr_ae
    filter_upwards [SobolevCalculus.gradient_zero_on_zero_set Metric.isOpen_ball htrace.1] with x hz
    rcases lt_trichotomy (v x) (U x) with hlt|he|hgt
    · have h1:¬0<v x-U x:=by linarith
      have h2:0<U x-v x:=by linarith
      have he:m x=v x:=by dsimp [m]; rw [max_eq_left h2.le]; ring
      simp only [he,p,P,M,ite_eq_right h1,ite_eq_left h2,zero_smul,one_smul,add_zero,
        sub_sub_cancel,max_eq_right (not_lt.mp h1)]
      ring
    · have hVG:V x=G x:=sub_eq_zero.mp (hz (by rw [he,sub_self]))
      simp only [p,P,m,M,he,hVG,sub_self,lt_self_iff_false,ite_false,zero_smul,
        max_self,add_zero,sub_zero]
    · have h1:0<v x-U x:=by linarith
      have h2:¬0<U x-v x:=by linarith
      have he:p x=v x:=by dsimp [p]; rw [max_eq_left h1.le]; ring
      simp only [he,m,M,P,ite_eq_left h1,ite_eq_right h2,zero_smul,one_smul,sub_zero,
        add_sub_cancel,max_eq_right (not_lt.mp h2)]
  change energy B U G≤energy B p P at hupper
  change energy B U G≤energy B m M at hlower
  linarith

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

theorem solution : type_of% @OAI.Bernoulli.DeSilvaJerison.U_global_minimizer_oai := @OAI.Bernoulli.DeSilvaJerison.U_global_minimizer_oai
