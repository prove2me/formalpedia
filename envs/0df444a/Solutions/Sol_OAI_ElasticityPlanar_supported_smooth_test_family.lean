-- Prove2me | solution 1 for OAI.ElasticityPlanar.supported_smooth_test_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:24:39.303712+00:00
-- url     : https://prove2.me/submissions/d37d67e6-8666-429a-9f4c-441d0ae659f9

import Mathlib
import Definitions.Def_OAIQ6El005

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
namespace ElasticityRegularity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma compact_derivative {g : E → ℂ} (hg : HasCompactSupport g) (m : E) :
    HasCompactSupport (fun x => fderiv ℝ g x m) :=
  (hg.fderiv ℝ).comp_left (g := fun T : E →L[ℝ] ℂ => T m) (by simp)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma smooth_derivative {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ g x m) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

end ElasticityRegularity

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity


section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma decay_memLp {s : ℝ} (hs : Module.finrank ℝ E < 2*s) :
    MemLp (fun x : E => (1+‖x‖^2)^(-s/2)) 2 := by
  have growth : (fun x : E => (1+‖x‖^2)^(-s/2)).HasTemperateGrowth := by fun_prop
  refine ⟨growth.1.continuous.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num)]
  suffices h : ∫⁻ x : E, ENNReal.ofReal ‖(1+‖x‖^2)^(-s)‖ < ⊤ from by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h
    rw [← Real.rpow_mul_natCast (by positivity)]
    simp
  apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weighted_decay_bound (x : E) (n k : ℕ) :
    ‖x‖^n*(1+‖x‖^2)^(-(n+k : ℝ)) ≤ (1+‖x‖^2)^(-(k : ℝ)) := by
  have hpos : 0 < 1+‖x‖^2 := by positivity
  have hbase : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
  calc
    _ ≤ (1+‖x‖^2)^n*(1+‖x‖^2)^(-(n+k : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hbase n) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_add hpos]
      congr 1
      ring

lemma all_orders_fourier_moments {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolev n 2 u) :
    ∃ v : Lp F 1 (volume : Measure E), 𝓕 u = (v : 𝓢'(E,F)) ∧
      ∀ n : ℕ, Integrable (fun x => ‖x‖^n*‖v x‖) := by
  let k : ℕ := Module.finrank ℝ E+1
  have hk : (Module.finrank ℝ E : ℝ) < 2*k := by dsimp [k]; push_cast; linarith
  obtain ⟨v,hv⟩ := (hu k).fourier_memL1 hk
  refine ⟨v,hv,fun n => ?_⟩
  obtain ⟨w,hw⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp (hu (2*(n+k)))
  have hdec (m : ℕ) (hm : k ≤ m) : MemLp (fun x : E => (1+‖x‖^2)^(-(m : ℝ))) 2 := by
    have hh : (Module.finrank ℝ E : ℝ) < 2*(2*m) := by
      have : (k : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    convert decay_memLp hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    congr 1
    ring
  have hg : MemLp (fun x : E => Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ)))) 2 :=
    (hdec (n+k) (Nat.le_add_left _ _)).ofReal
  let q : Lp F 1 (volume : Measure E) := hg.toLp _ • w
  have hq : (q : 𝓢'(E,F)) = 𝓕 u := by
    rw [Lp.toTemperedDistribution_smul_eq (by fun_prop),← hw,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert (smulLeftCLM_const (1 : ℂ) (𝓕 u)) using 1
    · congr 2
      ext x
      change Complex.ofReal ((1+‖x‖^2)^((↑(2*(n+k)) : ℝ)/2)) *
        Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ))) = 1
      rw [← Complex.ofReal_mul,← Complex.ofReal_one,Complex.ofReal_inj]
      rw [← Real.rpow_add (by positivity : 0 < (1+‖x‖^2 : ℝ))]
      convert Real.rpow_zero (1+‖x‖^2) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      push_cast
      ring
    · simp
  have heq : q=v := by
    apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F))
    change (q : 𝓢'(E,F)) = (v : 𝓢'(E,F))
    rw [hq,hv]
  have hqa : ∀ᵐ x, v x = Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ))) • w x := by
    rw [← heq]
    filter_upwards [Lp.coeFn_lpSMul (r := 1) (hg.toLp _) w, hg.coeFn_toLp] with x hx hy
    change q x = _ at hx
    rw [hx]
    change (hg.toLp _ : E → ℂ) x • w x = _
    rw [hy]
  have hi : Integrable (fun x : E => (1+‖x‖^2)^(-(k : ℝ))*‖w x‖) :=
    (hdec k le_rfl).integrable_mul (Lp.memLp w).norm
  apply hi.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v).norm)
  filter_upwards [hqa] with x hx
  change ‖‖x‖^n*‖v x‖‖ ≤ _
  rw [hx,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),← mul_assoc]
  simpa only [Nat.cast_add] using
    mul_le_mul_of_nonneg_right (weighted_decay_bound x n k) (norm_nonneg (w x))

end

section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma l1_inverse_fourier_distribution (v : Lp F 1 (volume : Measure E)) :
    (((Real.Lp.fourierTransformInv v).memLp_top.toLp _ : Lp F ∞ (volume : Measure E)) : 𝓢'(E,F)) =
      𝓕⁻ (v : 𝓢'(E,F)) := by
  ext φ
  rw [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x : E, φ x • 𝓕⁻ (v : E → F) x := by
      apply integral_congr_ae
      filter_upwards [(Real.Lp.fourierTransformInv v).memLp_top.coeFn_toLp] with x hx
      rw [hx,Real.Lp.fourierTransformInv_apply]
    _ = ∫ x : E, (𝓕⁻ φ) x • v x := by
      have hf : (-innerₗ E).flip = -innerₗ E := by
        ext x y
        exact congrArg Neg.neg (real_inner_comm x y)
      have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := -innerₗ E) (μ := (volume : Measure E)) (ν := volume) Real.continuous_fourierChar
        (show Continuous (fun p : E × E => -inner ℝ p.1 p.2) by fun_prop) φ.integrable (L1.integrable_coeFn v)
      rw [hf] at h
      simp only [SchwartzMap.fourierInv_coe]
      convert h.symm using 1
      all_goals try with_reducible_and_instances rfl
    _ = _ := rfl
  rfl

/-- A tempered distribution lying in all integral Sobolev spaces has an actual
bounded smooth representative. All moments of a single L1 Fourier representative
are proved first, so the smooth representatives do not depend on the order. -/
theorem all_orders_smooth_representative {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolev n 2 u) :
    ∃ g : BoundedContinuousFunction E F, ContDiff ℝ (⊤ : ℕ∞) (g : E → F) ∧
      u = ((g.memLp_top.toLp _ : Lp F ∞ (volume : Measure E)) : 𝓢'(E,F)) := by
  obtain ⟨v,hv,hm⟩ := all_orders_fourier_moments hu
  refine ⟨Real.Lp.fourierTransformInv v,?_,?_⟩
  · have hs := Real.contDiff_fourier (N := (⊤ : ℕ∞)) (fun n _ => hm n)
    convert hs.comp contDiff_neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact (Real.Lp.fourierTransformInv_apply v x).trans (Real.fourierInv_eq_fourier_neg _ _)
  · rw [l1_inverse_fourier_distribution,← hv,fourierInv_fourier_eq]

end

end ElasticityRegularity

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_LocalRegularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
namespace ElasticityRegularity


section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace LocalEqual
variable {Ω : Set E} {u v w u' v' : 𝓢'(E,ℂ)}
lemma symm (h : LocalEqual Ω u v) : LocalEqual Ω v u := fun φ hc hs => (h φ hc hs).symm
lemma trans (h : LocalEqual Ω u v) (h' : LocalEqual Ω v w) : LocalEqual Ω u w :=
  fun φ hc hs => (h φ hc hs).trans (h' φ hc hs)
lemma cutoff (h : LocalEqual Ω u v) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    smulLeftCLM ℂ g u = smulLeftCLM ℂ g v := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ g φ) = v (SchwartzMap.smulLeftCLM ℂ g φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_right : HasCompactSupport (g * (φ : E → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_left (f := g) (g := (φ : E → ℂ))).trans hs
end LocalEqual
end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_dist_injective : Function.Injective (fun u : 𝓢(E,ℂ) => (u : 𝓢'(E,ℂ))) := by
  intro u v h
  apply SchwartzMap.injective_toLp 2 volume
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  change ((u.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ)) =
    ((v.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ))
  simpa only [Lp.toTemperedDistribution_toLp_eq] using h

lemma distribution_schwartz_product {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢(E,ℂ)) :
    smulLeftCLM ℂ g (u : 𝓢'(E,ℂ)) = (SchwartzMap.smulLeftCLM ℂ g u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply,SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma LocalEqual.cutoff_one {Ω : Set E} (u : 𝓢'(E,ℂ)) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (h1 : Set.EqOn g 1 Ω) :
    LocalEqual Ω (smulLeftCLM ℂ g u) u := by
  intro φ _ hs
  rw [smulLeftCLM_apply_apply]
  congr 1
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg,smul_eq_mul]
  by_cases hx : φ x=0
  · simp [hx]
  · rw [h1 (hs (subset_tsupport _ hx))]
    simp

lemma LocalEqual.schwartz_eqOn {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : 𝓢(E,ℂ)} (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    Set.EqOn (u : E → ℂ) (v : E → ℂ) Ω := by
  intro x hx
  obtain ⟨g,hs,hc,hg,_,h1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hΩ.mem_nhds hx)
  let f : E → ℂ := fun y => (g y : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  have hfs : tsupport f ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro y hy
    change g y ≠ 0
    intro hy0
    apply hy
    change (g y : ℂ)=0
    rw [hy0,Complex.ofReal_zero]
  have he := h.cutoff hfg hfc hfs
  rw [distribution_schwartz_product (hfc.hasTemperateGrowth hfg),
    distribution_schwartz_product (hfc.hasTemperateGrowth hfg)] at he
  have he' := congrArg (fun w : 𝓢(E,ℂ) => w x) (schwartz_dist_injective he)
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hfc.hasTemperateGrowth hfg),smul_eq_mul] at he'
  have hx1 : f x=1 := by simp only [f,h1,Complex.ofReal_one]
  simpa only [hx1,one_mul] using he'

lemma smooth_Linfty_product {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (v : BoundedContinuousFunction E ℂ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (v : E → ℂ)) :
    let f : 𝓢(E,ℂ) := (hc.mul_right : HasCompactSupport (g*(v : E → ℂ))).toSchwartzMap (hg.mul hv)
    smulLeftCLM ℂ g (((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))) : 𝓢'(E,ℂ)) = (f : 𝓢'(E,ℂ)) := by
  intro f
  ext φ
  simp only [smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply,SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [v.memLp_top.coeFn_toLp] with x hx
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hc.hasTemperateGrowth hg),hx,smul_eq_mul]
  change g x*φ x*v x = φ x*(g x*v x)
  ring

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma LocalEqual.lp_ae {Ω : Set E} (hΩ : IsOpen Ω)
    (u v : Lp ℂ 2 (volume : Measure E))
    (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → u x=v x := by
  have hu : LocallyIntegrable (u : E → ℂ) (volume : Measure E) := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hv : LocallyIntegrable (v : E → ℂ) (volume : Measure E) := (Lp.memLp v).locallyIntegrable (by norm_num)
  have he : ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → (u x-v x)=0 := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hu.sub hv).locallyIntegrableOn Ω) ?_
  · filter_upwards [he] with x hx
    intro hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  intro g hg hc hs
  let f : E → ℂ := fun x => (g x : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  let φ : 𝓢(E,ℂ) := hfc.toSchwartzMap hfg
  have hfs : tsupport (φ : E → ℂ) ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro x hx hzero
    apply hx
    change (g x : ℂ)=0
    rw [hzero,Complex.ofReal_zero]
  have hh := h φ hfc hfs
  simp only [Lp.toTemperedDistribution_apply] at hh
  have hiu := hu.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  have hiv := hv.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  simp only [smul_sub]
  rw [integral_sub hiu hiv,sub_eq_zero]
  simp only [show (φ : E → ℂ)=f from rfl,f,Complex.real_smul,smul_eq_mul] at hh ⊢
  convert hh using 1
  all_goals try with_reducible_and_instances rfl

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
namespace ElasticityRegularity

/-- The closed graph argument supplies norms for genuine distribution operators,
not additional quantitative regularity assumptions. -/
theorem exists_continuous_lift
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
    (J : Y →L[ℂ] Z) (hJ : Function.Injective J) (T : X →L[ℂ] Z)
    (hT : ∀ x, ∃ y, J y=T x) :
    ∃ L : X →L[ℂ] Y, ∀ x, J (L x)=T x := by
  choose l hl using hT
  let L : X →ₗ[ℂ] Y := {
    toFun := l
    map_add' := fun x y => hJ (by rw [map_add,hl,hl,hl,map_add])
    map_smul' := fun c x => hJ (by rw [map_smul,hl,hl,map_smul]; rfl) }
  have hc : IsClosed (L.graph : Set (X × Y)) := by
    have he : (L.graph : Set (X × Y))={p | T p.1=J p.2} := by
      ext p
      change p.2=L p.1 ↔ T p.1=J p.2
      constructor
      · intro h
        rw [h]
        exact (hl p.1).symm
      · intro h
        apply hJ
        exact h.symm.trans (hl p.1).symm
    rw [he]
    exact isClosed_eq (T.continuous.comp continuous_fst) (J.continuous.comp continuous_snd)
  exact ⟨⟨L,L.continuous_of_isClosed_graph hc⟩,hl⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lp_distribution_injective : Function.Injective
    (fun u : Lp ℂ 2 (volume : Measure E) => (u : 𝓢'(E,ℂ))) := by
  intro u v huv
  apply Lp.ext
  have h : LocalEqual Set.univ (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ)) :=
    fun _ _ _ => congrArg (fun T : 𝓢'(E,ℂ) => T _) huv
  filter_upwards [h.lp_ae isOpen_univ u v] with x hx
  exact hx (Set.mem_univ x)

lemma sobolevInjection_injective (s : ℝ) :
    Function.Injective (sobolevInjection (E := E) s) := by
  intro u v huv
  have h := congrArg (besselPotential E ℂ s) huv
  have hh : (u : 𝓢'(E,ℂ))=(v : 𝓢'(E,ℂ)) := by
    simpa only [sobolevInjection,ContinuousLinearMap.comp_apply,
      besselPotential_besselPotential_apply,neg_add_cancel,besselPotential_zero,
      ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply] using h
  exact lp_distribution_injective hh

lemma sobolevInjection_mem (s : ℝ) (f : Lp ℂ 2 (volume : Measure E)) :
    MemSobolev s 2 (sobolevInjection s f) := by
  refine ⟨f,?_⟩
  simp only [sobolevInjection,ContinuousLinearMap.comp_apply,
    besselPotential_besselPotential_apply,neg_add_cancel,besselPotential_zero,
    ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply]

lemma memSobolev_iff_range (s : ℝ) (u : 𝓢'(E,ℂ)) :
    MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure E), sobolevInjection s f=u := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨f,?_⟩
    change besselPotential E ℂ (-s) (f : 𝓢'(E,ℂ))=u
    exact (besselPotential_neg_apply_eq_iff s (f : 𝓢'(E,ℂ)) u).mpr hf
  · rintro ⟨f,rfl⟩
    exact sobolevInjection_mem s f

/-- A qualitative everywhere-defined Sobolev mapping theorem for a continuous
actual distribution operator automatically gives its bounded Sobolev realization.
This is useful for smooth multipliers and coordinate derivatives on cutoffs. -/
theorem exists_sobolev_realization (s t : ℝ) (P : 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ))
    (hP : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (P u)) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection t (L f)=P (sobolevInjection s f) := by
  exact exists_continuous_lift (sobolevInjection t) (sobolevInjection_injective t)
    (P.comp (sobolevInjection s)) (fun f =>
      (memSobolev_iff_range t _).mp (hP _ (sobolevInjection_mem s f)))

theorem exists_bounded_sobolev_derivative (s : ℝ) (m : E) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (s-1) (L f)=∂_{m} (sobolevInjection s f) := by
  exact exists_sobolev_realization s (s-1) (LineDeriv.lineDerivOpCLM ℂ 𝓢'(E,ℂ) m)
    (fun _ h => h.lineDerivOp)

theorem exists_bounded_sobolev_inclusion {s t : ℝ} (hst : t ≤ s) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection t (L f)=sobolevInjection s f := by
  exact exists_sobolev_realization s t (ContinuousLinearMap.id ℂ _)
    (fun _ h => h.mono hst)

end ElasticityRegularity

end

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Parameters
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

namespace SmoothSobolev
variable {s t : ℝ} {u v : P → 𝓢'(E,ℂ)}
lemma mono (hu : SmoothSobolev s u) (hst : t ≤ s) : SmoothSobolev t u := by
  obtain ⟨L,hL⟩ := exists_bounded_sobolev_inclusion (E := E) hst
  obtain ⟨f,hf,he⟩ := hu
  exact ⟨fun p => L (f p),(L.restrictScalars ℝ).contDiff.comp hf,fun p => (hL _).trans (he p)⟩
lemma derivative (hu : SmoothSobolev s u) (a : E) :
    SmoothSobolev (s-1) (fun p => ∂_{a} (u p)) := by
  obtain ⟨L,hL⟩ := exists_bounded_sobolev_derivative (E := E) s a
  obtain ⟨f,hf,he⟩ := hu
  exact ⟨fun p => L (f p),(L.restrictScalars ℝ).contDiff.comp hf,fun p => by rw [hL,he]⟩
end SmoothSobolev

end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The continuous Sobolev embedding is a genuinely bounded operator, obtained
from the actual Fourier representative and the closed graph theorem. -/
theorem exists_bounded_continuous_embedding {s : ℝ} (hs : Module.finrank ℝ E < 2*s) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] BoundedContinuousFunction E ℂ,
      ∀ f, sobolevInjection s f=
        (((L f).memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E,ℂ)) := by
  let J := Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 1
  have hJ : Function.Injective J :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  obtain ⟨T,hT⟩ := exists_continuous_lift J hJ
    ((fourierCLM ℂ 𝓢'(E,ℂ)).comp (sobolevInjection s)) (fun f => by
      obtain ⟨v,hv⟩ := (sobolevInjection_mem s f).fourier_memL1 hs
      exact ⟨v,hv.symm⟩)
  let R : Lp ℂ 1 (volume : Measure E) →L[ℂ] BoundedContinuousFunction E ℂ :=
    (BoundedContinuousFunction.compContinuousCLM ℂ ℂ (-ContinuousMap.id E)).comp
      (Real.Lp.fourierTransformCLM E ℂ)
  refine ⟨R.comp T,fun f => ?_⟩
  change sobolevInjection s f=
    (((Real.Lp.fourierTransformInv (T f)).memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E,ℂ))
  rw [l1_inverse_fourier_distribution]
  have h := hT f
  change (T f : 𝓢'(E,ℂ))=𝓕 (sobolevInjection s f) at h
  rw [h,fourierInv_fourier_eq]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma SmoothSobolev.continuous_representative {s : ℝ} {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev s u) (hs : Module.finrank ℝ E < 2*s) :
    ∃ g : P → BoundedContinuousFunction E ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∀ p, u p=(((g p).memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E,ℂ)) := by
  obtain ⟨f,hf,he⟩ := hu
  obtain ⟨L,hL⟩ := exists_bounded_continuous_embedding hs
  exact ⟨fun p => L (f p),(L.restrictScalars ℝ).contDiff.comp hf,fun p => (he p).symm.trans (hL _)⟩

end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma bcfToDist_apply (g : BoundedContinuousFunction E ℂ) :
    bcfToDist g=(((g.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))) : 𝓢'(E,ℂ)) := rfl
lemma bcfToDist_injective : Function.Injective (bcfToDist (E := E)) := by
  intro f g h
  have hh : (f.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))=g.memLp_top.toLp _ :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)) h
  have ha : (f : E → ℂ)=ᵐ[volume] (g : E → ℂ) :=
    f.memLp_top.coeFn_toLp.symm.trans (hh ▸ g.memLp_top.coeFn_toLp)
  exact DFunLike.coe_injective ((f.continuous.ae_eq_iff_eq volume g.continuous).mp ha)
lemma bcf_smooth_of_all_orders (g : BoundedContinuousFunction E ℂ)
    (hg : ∀ n : ℕ, MemSobolev n 2 (bcfToDist g)) :
    ContDiff ℝ (⊤ : ℕ∞) (g : E → ℂ) := by
  obtain ⟨h,hh,he⟩ := all_orders_smooth_representative hg
  have : g=h := bcfToDist_injective he
  rwa [this]

/-- Distributional and classical derivatives agree for the actual bounded smooth
representatives. A compact smooth multiplier makes every term Schwartz. -/
lemma bcf_derivative (g h : BoundedContinuousFunction E ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) (g : E → ℂ))
    (hh : ContDiff ℝ (⊤ : ℕ∞) (h : E → ℂ)) (a x : E)
    (he : ∂_{a} (bcfToDist g)=bcfToDist h) :
    fderiv ℝ (g : E → ℂ) x a=h x := by
  obtain ⟨q,_,hc,hq,_,h1⟩ := exists_contDiff_tsupport_subset (x := x) (n := (⊤ : ℕ∞))
    (s := Set.univ) Filter.univ_mem
  let c : E → ℂ := fun y => (q y : ℂ)
  have hcg : ContDiff ℝ (⊤ : ℕ∞) c := Complex.ofRealCLM.contDiff.comp hq
  have hcc : HasCompactSupport c := hc.comp_left Complex.ofReal_zero
  have hdg := smooth_derivative hcg a
  have hdc := compact_derivative hcc a
  let cg : 𝓢(E,ℂ) := (hcc.mul_right : HasCompactSupport (c*(g : E → ℂ))).toSchwartzMap (hcg.mul hg)
  let ch : 𝓢(E,ℂ) := (hcc.mul_right : HasCompactSupport (c*(h : E → ℂ))).toSchwartzMap (hcg.mul hh)
  let cdg : 𝓢(E,ℂ) := (hdc.mul_right : HasCompactSupport ((fun y => fderiv ℝ c y a)*(g : E → ℂ))).toSchwartzMap (hdg.mul hg)
  have hd := distribution_leibniz (hcc.hasTemperateGrowth hcg) a
    (hdc.hasTemperateGrowth hdg) (bcfToDist g)
  rw [he,bcfToDist_apply,bcfToDist_apply,smooth_Linfty_product hcg hcc g hg,
    smooth_Linfty_product hcg hcc h hh,smooth_Linfty_product hdg hdc g hg] at hd
  have hdist : ((∂_{a} cg : 𝓢(E,ℂ)) : 𝓢'(E,ℂ))=((cdg+ch : 𝓢(E,ℂ)) : 𝓢'(E,ℂ)) := by
    simpa only [← lineDerivOp_toTemperedDistributionCLM_eq,map_add] using hd
  have hv := congrArg (fun f : 𝓢(E,ℂ) => f x) (schwartz_dist_injective hdist)
  change fderiv ℝ (c*(g : E → ℂ)) x a=fderiv ℝ c x a*g x+c x*h x at hv
  rw [fderiv_mul (hcg.differentiable (by simp) x) (hg.differentiable (by simp) x)] at hv
  have hx : c x=1 := by simp only [c,h1,Complex.ofReal_one]
  simp only [add_apply,smul_apply,smul_eq_mul,hx,one_mul] at hv
  linear_combination hv
end ElasticityRegularity
namespace ElasticityRegularity

section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma bcf_family_spatial_smooth (g : P → BoundedContinuousFunction E ℂ)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (p : P) :
    ContDiff ℝ (⊤ : ℕ∞) (g p : E → ℂ) := by
  apply bcf_smooth_of_all_orders
  intro n
  obtain ⟨f,_,he⟩ := hu n
  dsimp only at he
  rw [← he p]
  exact sobolevInjection_mem _ _

lemma bcf_parameter_derivative (g : P → BoundedContinuousFunction E ℂ)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (a : P) :
    ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (fderiv ℝ g p a)) := by
  intro n
  let t : ℕ := n+Module.finrank ℝ E+1
  have ht : Module.finrank ℝ E < 2*(t : ℝ) := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
  obtain ⟨f,hf,he⟩ := hu t
  obtain ⟨T,hT⟩ := exists_bounded_continuous_embedding ht
  have hge : g=fun p => T (f p) := by
    funext p
    apply bcfToDist_injective
    exact (he p).symm.trans (hT _)
  have hd (p : P) : fderiv ℝ g p a=T (fderiv ℝ f p a) := by
    have h := (T.restrictScalars ℝ).hasFDerivAt.comp p (hf.differentiable (by simp) p).hasFDerivAt
    change HasFDerivAt (fun p => T (f p)) _ p at h
    rw [← hge] at h
    exact congrArg (fun L : P →L[ℝ] BoundedContinuousFunction E ℂ => L a) h.fderiv
  have h : SmoothSobolev (t : ℝ) (fun p => bcfToDist (fderiv ℝ g p a)) := by
    refine ⟨fun p => fderiv ℝ f p a,?_,fun p => ?_⟩
    · exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
    · dsimp only
      rw [hd]
      exact hT _
  exact h.mono (by dsimp [t]; norm_cast; omega)

/-- Actual spatial derivatives have smoothly parameter-dependent bounded
representatives in every Sobolev order. -/
lemma bcf_spatial_derivative (g : P → BoundedContinuousFunction E ℂ)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (a : E) :
    ∃ h : P → BoundedContinuousFunction E ℂ,
      ContDiff ℝ (⊤ : ℕ∞) h ∧
      (∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (h p))) ∧
      ∀ p x, fderiv ℝ (g p : E → ℂ) x a=h p x := by
  have hd (n : ℕ) : SmoothSobolev n (fun p => ∂_{a} (bcfToDist (g p))) := by
    have h := (hu (n+1)).derivative a
    convert h using 1; push_cast; ring
  let t : ℕ := Module.finrank ℝ E+1
  obtain ⟨h,hh,he⟩ := (hd t).continuous_representative (by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)])
  change ∀ p, ∂_{a} (bcfToDist (g p))=bcfToDist (h p) at he
  have hs (n : ℕ) : SmoothSobolev n (fun p => bcfToDist (h p)) := by
    simpa only [he] using hd n
  refine ⟨h,hh,hs,fun p x => ?_⟩
  exact bcf_derivative (g p) (h p) (bcf_family_spatial_smooth g hu p)
    (bcf_family_spatial_smooth h hs p) a x (he p)
end
open MeasureTheory TemperedDistribution Filter Topology
open scoped SchwartzMap ENNReal LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma bcf_joint_hasFDerivAt (g : P → BoundedContinuousFunction E ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (q : P × E) :
    HasFDerivAt (fun q : P × E => g q.1 q.2)
      (((BoundedContinuousFunction.evalCLM ℝ q.2).comp (fderiv ℝ g q.1)).coprod
        (fderiv ℝ (g q.1 : E → ℂ) q.2)) q := by
  let A : P → E → P →L[ℝ] ℂ := fun p x =>
    (BoundedContinuousFunction.evalCLM ℝ x).comp (fderiv ℝ g p)
  let B : P → E → E →L[ℝ] ℂ := fun p x => fderiv ℝ (g p : E → ℂ) x
  have hA : Continuous (fun q : P × E => A q.1 q.2) := by
    apply continuous_clm_apply.mpr
    intro a
    have ht : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ g p a) :=
      (hg.fderiv_right (by simp)).clm_apply contDiff_const
    exact (ht.continuous.comp continuous_fst).eval continuous_snd
  have hB : Continuous (fun q : P × E => B q.1 q.2) := by
    apply continuous_clm_apply.mpr
    intro a
    obtain ⟨h,hh,_,he⟩ := bcf_spatial_derivative g hu a
    change Continuous (fun q : P × E => fderiv ℝ (g q.1 : E → ℂ) q.2 a)
    simp only [he]
    exact (hh.continuous.comp continuous_fst).eval continuous_snd
  apply (hasStrictFDerivAt_uncurry_coprod (f := fun p x => g p x)
    (f₁ := A) (f₂ := B) ?_ ?_ hA.continuousAt hB.continuousAt).hasFDerivAt
  · apply Filter.Eventually.of_forall
    intro v
    exact (BoundedContinuousFunction.evalCLM ℝ v.2).hasFDerivAt.comp v.1
      (hg.differentiable (by simp) v.1).hasFDerivAt
  · apply Filter.Eventually.of_forall
    intro v
    exact ((bcf_family_spatial_smooth g hu v.1).differentiable (by simp) v.2).hasFDerivAt

/-- Strong smoothness in every Sobolev order yields actual joint smoothness,
including mixed parameter and spatial derivatives. -/
theorem bcf_joint_smooth (g : P → BoundedContinuousFunction E ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => g q.1 q.2) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing g with
  | zero =>
    simp only [Nat.cast_zero,contDiff_zero]
    exact (hg.continuous.comp continuous_fst).eval continuous_snd
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv_apply]
    refine ⟨fun q => (bcf_joint_hasFDerivAt g hg hu q).differentiableAt,by simp,fun a => ?_⟩
    have hp : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ g p a.1) :=
      (hg.fderiv_right (by simp)).clm_apply contDiff_const
    have hpu := bcf_parameter_derivative g hu a.1
    obtain ⟨h,hh,hs,he⟩ := bcf_spatial_derivative g hu a.2
    have hp' := ih (fun p => fderiv ℝ g p a.1) hp hpu
    have hs' := ih h hh hs
    have hf (q : P × E) :
        fderiv ℝ (fun q : P × E => g q.1 q.2) q a=
          (fderiv ℝ g q.1 a.1) q.2+h q.1 q.2 := by
      rw [(bcf_joint_hasFDerivAt g hg hu q).fderiv]
      change (fderiv ℝ g q.1 a.1) q.2+fderiv ℝ (g q.1 : E → ℂ) q.2 a.2=_
      rw [he]
    simp only [hf]
    exact hp'.add hs'

theorem SmoothSobolev.joint_smooth_representative {u : P → 𝓢'(E,ℂ)}
    (hu : ∀ n : ℕ, SmoothSobolev n u) :
    ∃ g : P → BoundedContinuousFunction E ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => g q.1 q.2) ∧
      ∀ p, u p=bcfToDist (g p) := by
  let t : ℕ := Module.finrank ℝ E+1
  obtain ⟨g,hg,he⟩ := (hu t).continuous_representative
    (by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)])
  change ∀ p, u p=bcfToDist (g p) at he
  have hs (n : ℕ) : SmoothSobolev n (fun p => bcfToDist (g p)) := by
    rw [← show u=(fun p => bcfToDist (g p)) from funext he]
    exact hu n
  exact ⟨g,hg,bcf_joint_smooth g hg hs,he⟩
end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Joint smoothness on an arbitrary smaller fixed open set. The representative
is an actual Schwartz function in space for every parameter. -/
theorem SmoothLocalSobolev.joint_schwartz_representative {Ω Ω' : Set E}
    (u : P → 𝓢'(E,ℂ)) (hu : ∀ N : ℕ, SmoothLocalSobolev Ω N u)
    {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ f : P → 𝓢(E,ℂ), ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => f q.1 q.2) ∧
      ∀ p, LocalEqual Ω' (u p) (f p : 𝓢'(E,ℂ)) := by
  obtain ⟨v,_,hv,he⟩ := SmoothSobolev.joint_smooth_representative
    (fun N => hu N g hg hc hs)
  have hvs (p : P) : ContDiff ℝ (⊤ : ℕ∞) (v p : E → ℂ) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  let f : P → 𝓢(E,ℂ) := fun p =>
    (hc.mul_right : HasCompactSupport (g*(v p : E → ℂ))).toSchwartzMap (hg.mul (hvs p))
  refine ⟨f,?_,fun p => ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => g q.2*v q.1 q.2)
    exact (hg.comp contDiff_snd).mul hv
  · have he' := smooth_Linfty_product hg hc (v p) (hvs p)
    have hl := (LocalEqual.cutoff_one (u p) (hc.hasTemperateGrowth hg) h1).symm
    have hl' := (LocalEqual.cutoff_one (smulLeftCLM ℂ g (u p)) (hc.hasTemperateGrowth hg) h1).symm
    have h := hl.trans hl'
    rw [he p] at h
    exact h.trans (by intro φ _ _; exact congrArg (fun T : 𝓢'(E,ℂ) => T φ) he')
end ElasticityRegularity

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Supported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/- The exact extension proofs are reused from their canonical original module. -/

namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

open ElasticityRegularity
variable {n : Type*} [Fintype n]
lemma L2_distribution (u : Test) : (L2 u : 𝓢'(ℂ,ℂ))=(toSchwartz u : 𝓢'(ℂ,ℂ)) :=
  Lp.toTemperedDistribution_toLp_eq (toSchwartz u)
end ElasticityPlanar
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma supported_smooth_test_family_oai {S : Set ℂ} (hS : IsCompact S)
    (u : P → Lp ℂ 2 (volume : Measure ℂ))
    (hu : ∀ N : ℕ, SmoothLocalSobolev univ N (fun p => (u p : 𝓢'(ℂ,ℂ))))
    (hs : ∀ p, LocalEqual Sᶜ (u p : 𝓢'(ℂ,ℂ)) 0) :
    ∃ v : P → Test, ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 q.2) ∧
      ∀ p, L2 (v p)=u p ∧ tsupport (v p : ℂ → ℂ)⊆S := by
  obtain ⟨R,hR,hSR⟩ := hS.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : ℂ) := ⟨R,R+1,hR,by simp⟩
  let c : ContDiffBump (0 : ℂ) := ⟨R+3,R+4,by linarith,by linarith⟩
  have hc : HasCompactSupport (fun z : ℂ => (c z : ℂ)) :=
    c.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  have hcs : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (c z : ℂ)) := Complex.ofRealCLM.contDiff.comp c.contDiff
  have h1 : EqOn (fun z : ℂ => (c z : ℂ)) 1 (Metric.ball 0 (R+3)) := by
    intro z hz
    change (c z : ℂ)=1
    rw [c.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)]
    rfl
  obtain ⟨w,hw,hwe⟩ := SmoothLocalSobolev.joint_schwartz_representative
    (fun p => (u p : 𝓢'(ℂ,ℂ))) hu hcs hc (subset_univ _) h1
  have hb : HasCompactSupport (fun z : ℂ => (b z : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  let v : P → Test := fun p => ⟨fun z => (b z : ℂ)*w p z,
    ⟨(Complex.ofRealCLM.contDiff.comp b.contDiff).mul ((w p).smooth ⊤),hb.mul_right⟩⟩
  refine ⟨v,((Complex.ofRealCLM.contDiff.comp b.contDiff).comp contDiff_snd).mul hw,fun p => ?_⟩
  have hsch (p : P) : ((w p).toLp 2 (volume : Measure ℂ) : 𝓢'(ℂ,ℂ))=(w p : 𝓢'(ℂ,ℂ)) := by
    exact Lp.toTemperedDistribution_toLp_eq (w p)
  have hlocal : ∀ᵐ z : ℂ, z∈Metric.ball 0 (R+3) → u p z=w p z := by
    have he : LocalEqual (Metric.ball 0 (R+3)) (u p : 𝓢'(ℂ,ℂ))
        ((w p).toLp 2 (volume : Measure ℂ) : 𝓢'(ℂ,ℂ)) := by rw [hsch]; exact hwe p
    filter_upwards [he.lp_ae Metric.isOpen_ball (u p) ((w p).toLp 2 volume),
      (w p).coeFn_toLp 2 volume] with z h hzw using fun hz => (h hz).trans hzw
  have hs' : LocalEqual Sᶜ (u p : 𝓢'(ℂ,ℂ)) ((0 : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ,ℂ)) := by
    change LocalEqual Sᶜ (u p : 𝓢'(ℂ,ℂ)) ((Lp.toTemperedDistributionCLM ℂ volume 2) 0)
    rw [map_zero]
    exact hs p
  have hzero := LocalEqual.lp_ae hS.isClosed.isOpen_compl (u p) 0 hs'
  have hev : L2 (v p)=u p := by
    apply Lp.ext
    filter_upwards [(toSchwartz (v p)).coeFn_toLp 2 volume,hlocal,hzero,Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz hzB hzout hz0
    change (L2 (v p) : ℂ → ℂ) z=v p z at hz
    rw [hz]
    change (b z : ℂ)*w p z=u p z
    by_cases hzS : z∈S
    · have hzn : ‖z‖≤R := hSR z hzS
      have hzB' : z∈Metric.ball 0 (R+3) := by simpa only [Metric.mem_ball,dist_zero_right] using (show ‖z‖<R+3 by linarith)
      have hzb : z∈Metric.closedBall 0 b.rIn := by simpa only [b,Metric.mem_closedBall,dist_zero_right] using hzn
      rw [b.one_of_mem_closedBall hzb,Complex.ofReal_one,one_mul]
      exact (hzB hzB').symm
    · have hu0 : u p z=0 := (hzout hzS).trans hz0
      rw [hu0]
      by_cases hzB' : z∈Metric.ball 0 (R+3)
      · rw [← hzB hzB',hu0,mul_zero]
      · have hn : R+3≤‖z‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hzB'
        rw [b.zero_of_le_dist (by change R+1≤dist z 0; rw [dist_zero_right]; linarith),Complex.ofReal_zero,zero_mul]
  refine ⟨hev,?_⟩
  have hveq : LocalEqual Sᶜ (toSchwartz (v p) : 𝓢'(ℂ,ℂ)) ((0 : 𝓢(ℂ,ℂ)) : 𝓢'(ℂ,ℂ)) := by
    rw [← L2_distribution,hev,map_zero]
    exact hs p
  have hpt := hveq.schwartz_eqOn hS.isClosed.isOpen_compl
  apply closure_minimal _ hS.isClosed
  intro z hz
  by_contra hzS
  exact hz (hpt hzS)
end ElasticityPlanar

end

end OAI
end

theorem solution.{u_2} : type_of% @OAI.ElasticityPlanar.supported_smooth_test_family_oai.{u_2} := @OAI.ElasticityPlanar.supported_smooth_test_family_oai.{u_2}
