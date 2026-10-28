-- Prove2me | solution 1 for OAI.ElasticityPlanar.supported_weak_unique
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:25:24.644861+00:00
-- url     : https://prove2.me/submissions/578b8762-2f38-40cc-9c39-95d3850df6d3

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

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma fourierMultiplier_add {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    fourierMultiplierCLM F (g+h) u=fourierMultiplierCLM F g u+fourierMultiplierCLM F h u := by
  simp only [fourierMultiplierCLM_apply,smulLeftCLM_add hg hh,add_apply,fourierInv_add]

omit [CompleteSpace F] in
lemma besselPotential_two (u : 𝓢'(E,F)) :
    besselPotential E F 2 u=u+fourierMultiplierCLM F (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) u := by
  have he : (fun x : E => (((1+‖x‖^2)^(2/2 : ℝ) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ))+(fun x : E => ((‖x‖^2 : ℝ) : ℂ)) := by
    funext x
    norm_num
  rw [besselPotential,he,fourierMultiplier_add (by fun_prop) (by fun_prop)]
  simp

lemma sobolev_real_smul {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (c : ℝ) :
    MemSobolev s 2 (c • u) := by
  convert hu.smul (c : ℂ) using 1
  all_goals try with_reducible_and_instances rfl

/-- Whole-space elliptic gain for the actual distributional Laplacian. -/
theorem laplacian_gain {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) : MemSobolev (s+2) 2 u := by
  have hp : (-(2*Real.pi)^2 : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hm := sobolev_real_smul hΔ (-(2*Real.pi)^2)⁻¹
  rw [laplacian_eq_fourierMultiplierCLM,smul_smul,inv_mul_cancel₀ hp,one_smul] at hm
  have h := hu.add hm
  rw [← besselPotential_two,memSobolev_besselPotential_iff] at h
  simpa only [add_comm] using h

/-- One derivative of gain from information on all coordinate first derivatives. -/
theorem coordinate_derivative_gain {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hd : ∀ i, MemSobolev s 2 (∂_{b i} u)) :
    MemSobolev (s+1) 2 u := by
  have hall : ∀ S : Finset ι, MemSobolev (s-1) 2 (∑ i ∈ S, ∂_{b i} (∂_{b i} u)) := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi hS =>
      rw [Finset.sum_insert hi]
      exact ((hd i).lineDerivOp).add hS
  have hsum := hall Finset.univ
  rw [← laplacian_eq_sum b] at hsum
  have h := laplacian_gain (hu.mono (by linarith : s-1 ≤ s)) hsum
  have he : s-1+2=s+1 := by ring
  rwa [he] at h

end

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

lemma sobolev_zero_product {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hb : MemLp g ∞ (volume : Measure E)) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (smulLeftCLM F g u) := by
  obtain ⟨v,rfl⟩ := memSobolev_zero_iff.mp hu
  apply memSobolev_zero_iff.mpr
  exact ⟨hb.toLp g • v, (Lp.toTemperedDistribution_smul_eq hg hb v).symm⟩

/-- Smooth compact coefficients preserve every nonnegative integral Sobolev order.
This is proved for the actual tempered distribution product, not an assumed
bounded multiplier on an unspecified Sobolev completion. -/
theorem sobolev_nat_product {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (n : ℕ) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    {u : 𝓢'(E,F)} (hu : MemSobolev n 2 u) : MemSobolev n 2 (smulLeftCLM F g u) := by
  induction n generalizing u g with
  | zero =>
    rw [Nat.cast_zero] at hu ⊢
    exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one] at hu ⊢
    apply coordinate_derivative_gain b (ih hg hc (hu.mono (by norm_num)))
    intro i
    have hd : MemSobolev (n : ℝ) 2 (∂_{b i} u) := by
      simpa only [add_sub_cancel_right] using hu.lineDerivOp (m := b i)
    rw [distribution_leibniz (hc.hasTemperateGrowth hg) (b i)
      ((compact_derivative hc (b i)).hasTemperateGrowth (smooth_derivative hg (b i)))]
    exact (ih (smooth_derivative hg (b i)) (compact_derivative hc (b i))
      (hu.mono (by norm_num))).add (ih hg hc hd)

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

lemma sobolev_sum {ι : Type*} (S : Finset ι) {s : ℝ} {v : ι → 𝓢'(E,F)}
    (hv : ∀ i ∈ S, MemSobolev s 2 (v i)) : MemSobolev s 2 (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi hS =>
    rw [Finset.sum_insert hi]
    exact (hv i (Finset.mem_insert_self _ _)).add
      (hS (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

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

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_support_subset (g : E → ℂ) (m : E) :
    tsupport (fun x => fderiv ℝ g x m) ⊆ tsupport g :=
  (tsupport_comp_subset (g := fun T : E →L[ℝ] ℂ => T m) (by simp) (fderiv ℝ g)).trans
    (tsupport_fderiv_subset ℝ)

lemma LocalSobolev.product_derivative {Ω : Set E} {s : ℝ} {u : 𝓢'(E,F)}
    (h : LocalSobolev Ω s u) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (m : E) :
    MemSobolev (s-1) 2 (smulLeftCLM F g (∂_{m} u)) := by
  have hdg := (compact_derivative hc m).hasTemperateGrowth (smooth_derivative hg m)
  have h1 := (h g hg hc hs).lineDerivOp (m := m)
  have h2 := h _ (smooth_derivative hg m) (compact_derivative hc m)
    ((derivative_support_subset g m).trans hs)
  have h3 := h1.sub (h2.mono (by linarith : s-1 ≤ s))
  rw [distribution_leibniz (hc.hasTemperateGrowth hg) m hdg,add_sub_cancel_left] at h3
  exact h3

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma laplacian_product {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (u : 𝓢'(E,F)) :
    Δ (smulLeftCLM F g u) = smulLeftCLM F g (Δ u)+
      ∑ d, (smulLeftCLM F (fun x => fderiv ℝ (fun y => fderiv ℝ g y (b d)) x (b d)) u+
        (2 : ℂ) • smulLeftCLM F (fun x => fderiv ℝ g x (b d)) (∂_{b d} u)) := by
  classical
  rw [laplacian_eq_sum b,laplacian_eq_sum b,map_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have hgd := smooth_derivative hg (b d)
  have hcd := compact_derivative hc (b d)
  rw [distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd),LineDeriv.lineDerivOp_add,
    distribution_leibniz (hcd.hasTemperateGrowth hgd) _
      ((compact_derivative hcd (b d)).hasTemperateGrowth (smooth_derivative hgd (b d))),
    distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd)]
  module

end ElasticityRegularity

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma MemSobolev.local_zero {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) (Ω : Set E) :
    LocalSobolev Ω 0 u := by
  intro g hg hc _
  exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu

end ElasticityRegularity

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
lemma sub (h : LocalEqual Ω u v) (h' : LocalEqual Ω u' v') : LocalEqual Ω (u-u') (v-v') := by
  intro φ hc hs
  simp only [sub_apply,h φ hc hs,h' φ hc hs]
lemma smul (h : LocalEqual Ω u v) (c : ℂ) : LocalEqual Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
lemma derivative (h : LocalEqual Ω u v) (a : E) : LocalEqual Ω (∂_{a} u) (∂_{a} v) := by
  intro φ hc hs
  change u (- ∂_{a} φ) = v (- ∂_{a} φ)
  apply h
  · change HasCompactSupport (fun x => -((∂_{a} φ : 𝓢(E,ℂ)) x))
    exact (hc.fderiv_apply (𝕜 := ℝ) a).neg
  · change tsupport (-((∂_{a} φ : 𝓢(E,ℂ)) : E → ℂ)) ⊆ Ω
    rw [tsupport_neg]
    exact (derivative_support_subset (φ : E → ℂ) a).trans hs
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
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma localSobolev {s : ℝ} (h : LocalEqual Ω u v) (hv : LocalSobolev Ω s v) : LocalSobolev Ω s u := by
  intro g hg hc hs
  rw [h.cutoff hg hc hs]
  exact hv g hg hc hs
end LocalEqual
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace LocalSobolev
variable {Ω : Set E} {s : ℝ} {u v : 𝓢'(E,ℂ)}
lemma add (h : LocalSobolev Ω s u) (h' : LocalSobolev Ω s v) : LocalSobolev Ω s (u+v) := by
  intro g hg hc hs
  rw [map_add]
  exact (h g hg hc hs).add (h' g hg hc hs)
lemma sub (h : LocalSobolev Ω s u) (h' : LocalSobolev Ω s v) : LocalSobolev Ω s (u-v) := by
  intro g hg hc hs
  rw [map_sub]
  exact (h g hg hc hs).sub (h' g hg hc hs)
lemma smul (h : LocalSobolev Ω s u) (c : ℂ) : LocalSobolev Ω s (c • u) := by
  intro g hg hc hs
  rw [map_smul]
  exact (h g hg hc hs).smul c
lemma sum {ι : Type*} (S : Finset ι) {u : ι → 𝓢'(E,ℂ)}
    (h : ∀ i ∈ S, LocalSobolev Ω s (u i)) : LocalSobolev Ω s (∑ i ∈ S, u i) := by
  intro g hg hc hs
  rw [map_sum]
  exact sobolev_sum S (fun i hi => h i hi g hg hc hs)
lemma coeff (h : LocalSobolev Ω s u) {a : E → ℂ} (ha : a.HasTemperateGrowth) :
    LocalSobolev Ω s (smulLeftCLM ℂ a u) := by
  intro g hg hc hs
  rw [smulLeftCLM_smulLeftCLM_apply ha (hc.hasTemperateGrowth hg),mul_comm]
  exact h (g*a) (hg.mul ha.1) hc.mul_right (tsupport_mul_subset_left.trans hs)
lemma derivative (h : LocalSobolev Ω s u) (a : E) : LocalSobolev Ω (s-1) (∂_{a} u) := by
  intro g hg hc hs
  exact h.product_derivative hg hc hs a
end LocalSobolev

lemma local_laplacian_gain_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {Ω : Set E} {s : ℝ} {u : 𝓢'(E,ℂ)} (hu : LocalSobolev Ω s u)
    (hΔ : LocalSobolev Ω (s-1) (Δ u)) : LocalSobolev Ω (s+1) u := by
  intro g hg hgc hgs
  have hb : MemSobolev (s-1) 2 (Δ (smulLeftCLM ℂ g u)) := by
    rw [laplacian_product b hg hgc]
    apply (hΔ g hg hgc hgs).add
    apply sobolev_sum Finset.univ
    intro d _
    have hgd := smooth_derivative hg (b d)
    have hcd := compact_derivative hgc (b d)
    have hsd := (derivative_support_subset g (b d)).trans hgs
    exact ((hu _ (smooth_derivative hgd (b d)) (compact_derivative hcd (b d))
      ((derivative_support_subset _ (b d)).trans hsd)).mono (by linarith)).add
        ((hu.product_derivative hgd hcd hsd (b d)).smul 2)
  have h := laplacian_gain ((hu g hg hgc hgs).mono (by linarith : s-1 ≤ s)) hb
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring
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

/-- Interior cutoff regularity yields an actual Schwartz representative on the
smaller open set; this is what is needed to construct physical smooth CGO
solutions on a ball from an L2 weak solution on a larger ball. -/
theorem local_schwartz_representative {Ω Ω' : Set E} (u : 𝓢'(E,ℂ))
    (hu : ∀ N : ℕ, LocalSobolev Ω N u) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : 𝓢(E,ℂ), LocalEqual Ω' u (v : 𝓢'(E,ℂ)) := by
  obtain ⟨v,hv,he⟩ := all_orders_smooth_representative (fun N => hu N g hg hc hs)
  let f : 𝓢(E,ℂ) := (hc.mul_right : HasCompactSupport (g*(v : E → ℂ))).toSchwartzMap (hg.mul hv)
  refine ⟨f,?_⟩
  have he' := smooth_Linfty_product hg hc v hv
  have hlocal := (LocalEqual.cutoff_one u (hc.hasTemperateGrowth hg) h1).symm
  have hlocal' := (LocalEqual.cutoff_one (smulLeftCLM ℂ g u) (hc.hasTemperateGrowth hg) h1).symm
  have h := hlocal.trans hlocal'
  rw [he,he'] at h
  exact h
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

/-- The smooth local representative really is the original L2 function almost
 everywhere, so the HB solution's L2 estimate is not lost in regularization. -/
theorem local_schwartz_l2_representative {Ω Ω' : Set E} (hΩ' : IsOpen Ω')
    (u : Lp ℂ 2 (volume : Measure E))
    (hu : ∀ N : ℕ, LocalSobolev Ω N (u : 𝓢'(E,ℂ))) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : 𝓢(E,ℂ), LocalEqual Ω' (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ)) ∧
      ∀ᵐ x ∂(volume : Measure E), x ∈ Ω' → u x=v x := by
  obtain ⟨v,hv⟩ := local_schwartz_representative (u : 𝓢'(E,ℂ)) hu hg hc hs h1
  refine ⟨v,hv,?_⟩
  have he : LocalEqual Ω' (u : 𝓢'(E,ℂ)) ((v.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ)) := by
    simpa only [Lp.toTemperedDistribution_toLp_eq] using hv
  filter_upwards [LocalEqual.lp_ae hΩ' u (v.toLp 2 volume) he,v.coeFn_toLp 2 volume] with x hx hxv
  intro hxΩ
  exact (hx hxΩ).trans hxv
end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions _root_.OAI.ElasticityPlanar.graphComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory Complex

lemma d_Z (v : ℂ) (f : Test) : d v (Z f) = v • f + Z (d v f) := by
  apply Subtype.ext
  funext z
  change fderiv ℝ (fun z => z * f z) z v = v * f z + z * ((d v f : ℂ → ℂ) z)
  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    ((hasFDerivAt_id z).mul ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  simpa [d_apply, add_comm, mul_comm, Pi.mul_def] using h

lemma deriv_conj (f : Test) (z v : ℂ) :
    fderiv ℝ (fun z => star (f z)) z v = star (fderiv ℝ (f : ℂ → ℂ) z v) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z
    ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) h

lemma d_Zbar (v : ℂ) (f : Test) : d v (Zbar f) = (star v) • f + Zbar (d v f) := by
  apply Subtype.ext
  funext z
  change fderiv ℝ (fun z => star z * f z) z v = star v * f z + star z * ((d v f : ℂ → ℂ) z)
  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    ((Complex.conjCLE.hasFDerivAt (x := z)).mul
      ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  simpa [d_apply, Complex.star_def, add_comm, mul_comm, Pi.mul_def] using h

lemma d_d (v w : ℂ) (f : Test) (z : ℂ) :
    (d v (d w f) : ℂ → ℂ) z = fderiv ℝ (fderiv ℝ (f : ℂ → ℂ)) z v w := by
  have hd : Differentiable ℝ (fderiv ℝ (f : ℂ → ℂ)) :=
    ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : ℂ → ℂ) y w) z v = _
  rw [fderiv_clm_apply (hd z) (differentiableAt_const w)]
  simp

lemma d_comm (v w : ℂ) (f : Test) : d v (d w f) = d w (d v f) := by
  apply Subtype.ext
  funext z
  rw [d_d, d_d]
  exact (smooth f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

lemma integrable_pair (f g : Test) : Integrable (fun z : ℂ => star (f z)*g z) := by
  exact ((Complex.conjCLE.continuous.comp (smooth f).continuous).mul (smooth g).continuous).integrable_of_hasCompactSupport (compact g).mul_left

lemma pair_add_right (f g h : Test) : pair f (g+h) = pair f g + pair f h := by
  simpa only [pair, Submodule.coe_add, Pi.add_apply, mul_add] using
    integral_add (integrable_pair f g) (integrable_pair f h)

lemma pair_add_left (f g h : Test) : pair (f+g) h = pair f h + pair g h := by
  simpa only [pair, Submodule.coe_add, Pi.add_apply, star_add, add_mul] using
    integral_add (integrable_pair f h) (integrable_pair g h)

lemma pair_sub_right (f g h : Test) : pair f (g-h) = pair f g - pair f h := by
  simpa only [pair, Submodule.coe_sub, Pi.sub_apply, mul_sub] using
    integral_sub (integrable_pair f g) (integrable_pair f h)

lemma pair_sub_left (f g h : Test) : pair (f-g) h = pair f h - pair g h := by
  simpa only [pair, Submodule.coe_sub, Pi.sub_apply, star_sub, sub_mul] using
    integral_sub (integrable_pair f h) (integrable_pair g h)

lemma pair_smul_right (f g : Test) (a : ℂ) : pair f (a • g) = a * pair f g := by
  simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (star (f _)) a, mul_assoc]
  exact integral_const_mul a _

lemma pair_smul_left (f g : Test) (a : ℂ) : pair (a • f) g = star a * pair f g := by
  simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul, mul_comm (star (f _)), mul_assoc]
  exact integral_const_mul (star a) _

/-- Coordinate derivatives are skew adjoint on the actual test space. -/
lemma pair_d (f g : Test) (v : ℂ) : pair f (d v g) = -pair (d v f) g := by
  have h1 : Integrable (fun z : ℂ => fderiv ℝ (fun z => star (f z)) z v * g z) := by
    simpa only [deriv_conj, d_apply] using integrable_pair (d v f) g
  have h2 : Integrable (fun z : ℂ => star (f z)*fderiv ℝ (g : ℂ → ℂ) z v) :=
    integrable_pair f (d v g)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 (integrable_pair f g)
    (fun z _ => Complex.conjCLE.differentiableAt.comp z ((smooth f).differentiable (by simp) z))
    (fun z _ => (smooth g).differentiable (by simp) z)
    |>.trans (by simp only [pair, deriv_conj, d_apply])

lemma pair_Z (f g : Test) : pair f (Z g) = pair (Zbar f) g := by
  apply integral_congr_ae
  filter_upwards [] with z
  simp [mul_comm, mul_left_comm, mul_assoc]

lemma pair_Zbar (f g : Test) : pair f (Zbar g) = pair (Z f) g := by
  apply integral_congr_ae
  filter_upwards [] with z
  simp [mul_comm, mul_left_comm]

lemma pair_B (f g : Test) (t : ℝ) : pair f (B t g) = pair (C t f) g := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, pair_add_right, pair_sub_right, pair_smul_right,
    pair_add_left, pair_sub_left, pair_smul_left, pair_d, pair_Z,
    ← neg_one_smul ℂ (d 1 f), pair_smul_left, map_neg, map_one,
    Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma pair_C (f g : Test) (t : ℝ) : pair f (C t g) = pair (B t f) g := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, pair_add_right, pair_sub_right, pair_smul_right,
    pair_add_left, pair_sub_left, pair_smul_left, pair_d, pair_Zbar,
    ← neg_one_smul ℂ (d 1 g), pair_smul_right, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma Z_Zbar (f : Test) : Z (Zbar f) = Zbar (Z f) := by
  apply Subtype.ext
  funext z
  change z * (star z * f z) = star z * (z * f z)
  ring

/-- Positive commutator of the two Gaussian-conjugated planar operators. -/
lemma commutator (t : ℝ) (f : Test) :
    C t (B t f) - B t (C t f) = (4 * (t : ℂ)) • f := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, map_add, map_sub, map_smul, map_neg, d_Z, d_Zbar,
    star_one, Complex.star_def, Complex.conj_I]
  rw [d_comm I 1 f, Z_Zbar f]
  trans (2 * (t : ℂ) - 2 * (t : ℂ) * I ^ 2) • f
  · module
  · congr 1
    rw [Complex.I_sq]
    ring

lemma energy_identity (t : ℝ) (f : Test) :
    pair (B t f) (B t f) - pair (C t f) (C t f) =
      (4 * (t : ℂ)) * pair f f := by
  calc
    _ = pair f (C t (B t f) - B t (C t f)) := by
      rw [pair_sub_right, pair_C f (B t f) t, pair_B f (C t f) t]
    _ = _ := by rw [commutator, pair_smul_right]

lemma mass_integral (f : Test) : mass f = ∫ z : ℂ, Complex.normSq (f z) := by
  have h := integral_re (integrable_pair f f)
  simpa only [mass, pair, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h.symm

lemma integrable_normSq (f : Test) : Integrable (fun z : ℂ => Complex.normSq (f z)) := by
  have h := (integrable_pair f f).re
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h

lemma mass_nonneg (f : Test) : 0 ≤ mass f := by
  rw [mass_integral]
  exact integral_nonneg fun _ => Complex.normSq_nonneg _

/-- An actual weighted support estimate, independent of any frame existence. -/
theorem gaussian_coercivity (t : ℝ) (f : Test) :
    4 * t * mass f ≤ mass (B t f) := by
  have h := congrArg Complex.re (energy_identity t f)
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, zero_mul, add_zero] at h
  change mass (B t f) - mass (C t f) = 4 * t * mass f at h
  linarith [mass_nonneg (C t f)]

lemma fderiv_gaussian (t : ℝ) (z v : ℂ) :
    fderiv ℝ (gaussian t) z v =
      gaussian t z * ((t : ℂ) / 2) * (v * star z + z * star v) := by
  have hd := (((hasFDerivAt_id z).mul (Complex.conjCLE.hasFDerivAt (x := z))).const_mul
    ((t : ℂ) / 2)).cexp
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hd.fderiv
  change fderiv ℝ (gaussian t) z v = _ at he
  rw [he]
  simp only [smul_apply, add_apply,
    smul_eq_mul, Complex.conjCLE_apply]
  change gaussian t z * ((t : ℂ) / 2 * (z * star v + star z * v)) = _
  ring

lemma d_W (t : ℝ) (v : ℂ) (f : Test) (z : ℂ) :
    (d v (W t f) : ℂ → ℂ) z = gaussian t z *
      (((t : ℂ) / 2) * (v * star z + z * star v) * f z + (d v f : ℂ → ℂ) z) := by
  have hd := ((smooth_gaussian t).differentiable (by simp) z).hasFDerivAt.mul
    ((smooth f).differentiable (by simp) z).hasFDerivAt
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hd.fderiv
  change fderiv ℝ (fun z => gaussian t z * f z) z v = _
  simp only [Pi.mul_def] at he
  rw [he]
  simp only [add_apply, smul_apply,
    smul_eq_mul, fderiv_gaussian, d_apply]
  ring

/-- Exact Gaussian conjugation of twice the planar Cauchy--Riemann operator. -/
lemma gaussian_conjugation (t : ℝ) (f : Test) :
    B t (W t f) = W t (d 1 f + I • d I f) := by
  apply Subtype.ext
  funext z
  change (d 1 (W t f) : ℂ → ℂ) z + I * (d I (W t f) : ℂ → ℂ) z -
      (t : ℂ) * (z * (gaussian t z * f z)) =
    gaussian t z * ((d 1 f : ℂ → ℂ) z + I * (d I f : ℂ → ℂ) z)
  rw [d_W, d_W]
  simp only [star_one, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

open scoped BigOperators

lemma normSq_sum_mul {n : Type*} [Fintype n] (a u : n → ℂ) :
    Complex.normSq (∑ j, a j * u j) ≤
      (∑ j, Complex.normSq (a j)) * ∑ j, Complex.normSq (u j) := by
  simp only [Complex.normSq_eq_norm_sq]
  have h := norm_sum_le Finset.univ (fun j => a j * u j)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖u j‖))

lemma mass_bound {n : Type*} [Fintype n] (f : Test) (u : n → Test) (K : ℝ)
    (h : ∀ z : ℂ, Complex.normSq (f z) ≤ K * ∑ j, Complex.normSq (u j z)) :
    mass f ≤ K * ∑ j, mass (u j) := by
  simp only [mass_integral]
  have hi : Integrable (fun z : ℂ => ∑ j, Complex.normSq (u j z)) :=
    integrable_finsetSum _ (fun j _ => integrable_normSq (u j))
  calc
    _ ≤ ∫ z : ℂ, K * ∑ j, Complex.normSq (u j z) :=
      integral_mono (integrable_normSq f) (hi.const_mul K) h
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => integrable_normSq (u j))]

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped BigOperators

lemma normSq_add_le (z w : ℂ) :
    normSq (z+w) ≤ 2*normSq z+2*normSq w := by
  simp only [normSq_eq_norm_sq]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le z w) 2
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

lemma mass_mul_bound (f g : Test) (K : ℝ)
    (hb : ∀ z, normSq (f z) ≤ K*normSq (g z)) : mass f ≤ K*mass g := by
  simpa using (mass_bound (n := Unit) f (fun _ => g) K (by simpa using hb))

/-- Quantitative Gaussian absorption for a system with no smallness of coefficients. -/
theorem weighted_inhomogeneous_bound {n : Type*} [Fintype n]
    (a : n → n → ℂ → ℂ) (u v : n → Test) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ z, (∃ j, u j z ≠ 0) → ∀ i, (∑ j, normSq (a i j z)) ≤ K)
    (heq : ∀ i z, (d 1 (u i)+I • d I (u i) : Test) z =
      v i z+∑ j, a i j z*u j z) :
    let t := (Fintype.card n : ℝ)*K+1
    (∑ i, mass (W t (u i))) ≤ ∑ i, mass (W t (v i)) := by
  classical
  dsimp only
  let t : ℝ := (Fintype.card n : ℝ)*K+1
  let w : n → Test := fun i => W t (u i)
  let f : n → Test := fun i => W t (v i)
  have hi (i : n) : mass (B t (w i)) ≤
      2*mass (f i)+2*K*∑ j, mass (w j) := by
    have hp (z : ℂ) : normSq ((B t (w i) : Test) z) ≤
        2*normSq (f i z)+2*K*∑ j, normSq (w j z) := by
      have he : (B t (w i) : Test) z=f i z+∑ j, a i j z*w j z := by
        dsimp [w,f]
        rw [gaussian_conjugation,W_apply,heq,mul_add,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      apply (normSq_add_le _ _).trans
      have hm : normSq (∑ j, a i j z*w j z) ≤ K*∑ j, normSq (w j z) := by
        by_cases hu : ∃ j, u j z ≠ 0
        · exact (normSq_sum_mul (fun j => a i j z) (fun j => w j z)).trans
            (mul_le_mul_of_nonneg_right (hb z hu i)
              (Finset.sum_nonneg fun j _ => normSq_nonneg _))
        · have hw : ∀ j, w j z=0 := by
            intro j
            have hj : u j z=0 := by simpa using not_exists.mp hu j
            simp [w,hj]
          simp [hw]
      linarith
    rw [mass_integral,mass_integral]
    simp only [mass_integral]
    calc
      _ ≤ ∫ z : ℂ, (2*normSq (f i z)+2*K*∑ j, normSq (w j z)) :=
        integral_mono (integrable_normSq _) (((integrable_normSq _).const_mul 2).add
          ((integrable_finsetSum _ (fun j _ => integrable_normSq (w j))).const_mul _)) hp
      _ = _ := by
        rw [integral_add ((integrable_normSq _).const_mul 2)
          ((integrable_finsetSum _ (fun j _ => integrable_normSq (w j))).const_mul _),
          integral_const_mul,integral_const_mul,
          integral_finsetSum _ (fun j _ => integrable_normSq (w j))]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (gaussian_coercivity t (w i)).trans (hi i))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul] at hs
  have hn : 0 ≤ (Fintype.card n : ℝ)*K := mul_nonneg (Nat.cast_nonneg _) hK
  have hw : 0 ≤ ∑ i, mass (w i) := Finset.sum_nonneg fun i _ => mass_nonneg _
  change (∑ i, mass (w i)) ≤ ∑ i, mass (f i)
  dsimp [t] at hs
  nlinarith [mul_nonneg hn hw]


lemma gaussian_inv (t : ℝ) (z : ℂ) : gaussian (-t) z*gaussian t z=1 := by
  rw [gaussian,gaussian,← Complex.exp_add]
  have h : (((-t : ℝ) : ℂ)/2)*(z*star z)+((t : ℂ)/2)*(z*star z)=0 := by
    push_cast
    ring
  rw [h,Complex.exp_zero]

lemma supported_weight_bound {S : Set ℂ} (hS : IsCompact S) (t : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ f : Test, tsupport (f : ℂ → ℂ) ⊆ S →
      mass (W t f) ≤ C*mass f := by
  have hc : Continuous (fun z => normSq (gaussian t z)) :=
    continuous_normSq.comp (smooth_gaussian t).continuous
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max K 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro f hf
  apply mass_mul_bound
  intro z
  rw [W_apply,normSq_mul]
  by_cases hz : f z=0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (normSq_nonneg _)
    exact (le_abs_self (normSq (gaussian t z))).trans
      ((hK z (hf (subset_tsupport _ hz))).trans (le_max_left _ _))

lemma supported_weight_equivalence {S : Set ℂ} (hS : IsCompact S) (t : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ f : Test, tsupport (f : ℂ → ℂ) ⊆ S →
      mass f ≤ C*mass (W t f) ∧ mass (W t f) ≤ C*mass f := by
  obtain ⟨C₁,hC₁,h₁⟩ := supported_weight_bound hS t
  obtain ⟨C₂,hC₂,h₂⟩ := supported_weight_bound hS (-t)
  refine ⟨max C₁ C₂,lt_of_lt_of_le hC₁ (le_max_left _ _),?_⟩
  intro f hf
  have hw : tsupport (W t f : ℂ → ℂ) ⊆ S :=
    (tsupport_mul_subset_right (f := gaussian t) (g := (f : ℂ → ℂ))).trans hf
  have he : W (-t) (W t f)=f := by
    apply Subtype.ext
    funext z
    change gaussian (-t) z*(gaussian t z*f z)=f z
    rw [← mul_assoc,gaussian_inv,one_mul]
  constructor
  · have hh := h₂ (W t f) hw
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (mass_nonneg _))
  · exact (h₁ f hf).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (mass_nonneg _))

lemma matrix_bound_on_compact {n : Type*} [Fintype n] {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, Continuous (a i j)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ S, ∀ i, (∑ j, normSq (a i j z)) ≤ K := by
  classical
  let F : ℂ → ℝ := fun z => ∑ i, ∑ j, normSq (a i j z)
  have hF : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max K 0,le_max_right _ _,?_⟩
  intro z hz i
  calc
    _ ≤ F z := Finset.single_le_sum (fun k _ => Finset.sum_nonneg
      (fun j _ => normSq_nonneg _)) (Finset.mem_univ i)
    _ ≤ ‖F z‖ := le_abs_self _
    _ ≤ K := hK z hz
    _ ≤ max K 0 := le_max_left _ _

/-- A true unweighted supported L2 estimate, uniform over all test columns on a
fixed compact set, for an arbitrary continuous matrix coefficient. -/
theorem supported_inhomogeneous_L2 {n : Type*} [Fintype n]
    {S : Set ℂ} (hS : IsCompact S) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, Continuous (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∀ u v : n → Test,
      (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      (∀ i, tsupport (v i : ℂ → ℂ) ⊆ S) →
      (∀ i z, (d 1 (u i)+I • d I (u i) : Test) z=v i z+∑ j, a i j z*u j z) →
      (∑ i, mass (u i)) ≤ C*∑ i, mass (v i) := by
  classical
  obtain ⟨K,hK,hb⟩ := matrix_bound_on_compact hS a ha
  let t : ℝ := (Fintype.card n : ℝ)*K+1
  obtain ⟨C,hC,hW⟩ := supported_weight_equivalence hS t
  refine ⟨C*C,mul_pos hC hC,?_⟩
  intro u v hu hv heq
  have hbound : ∀ z, (∃ j, u j z ≠ 0) → ∀ i, (∑ j, normSq (a i j z)) ≤ K := by
    intro z hz
    obtain ⟨j,hj⟩ := hz
    exact hb z (hu j (subset_tsupport _ hj))
  have hw := weighted_inhomogeneous_bound a u v K hK hbound heq
  change (∑ i, mass (W t (u i))) ≤ ∑ i, mass (W t (v i)) at hw
  calc
    _ ≤ ∑ i, C*mass (W t (u i)) := Finset.sum_le_sum fun i _ => (hW _ (hu i)).1
    _ = C*∑ i, mass (W t (u i)) := (Finset.mul_sum ..).symm
    _ ≤ C*∑ i, mass (W t (v i)) := mul_le_mul_of_nonneg_left hw hC.le
    _ ≤ C*(C*∑ i, mass (v i)) := mul_le_mul_of_nonneg_left (by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (hW _ (hv i)).2) hC.le
    _ = _ := by ring

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped SchwartzMap ENNReal BigOperators

lemma inner_L2 (f g : Test) : inner ℂ (L2 f) (L2 g)=pair f g := by
  simpa only [L2,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,SchwartzMap.toLpCLM_apply,
    RCLike.inner_apply',RCLike.star_def,toSchwartz_apply,pair] using
    SchwartzMap.inner_toL2_toL2_eq (toSchwartz f) (toSchwartz g) volume
lemma norm_L2_sq (f : Test) : ‖L2 f‖^2=mass f := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),inner_L2]
  rfl

variable {n : Type*}
variable [Fintype n]
lemma norm_embed_sq (u : n → Test) : ‖embed u‖^2=∑ i, mass (u i) := by
  rw [PiLp.norm_eq_of_L2,Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl (fun i _ => norm_L2_sq (u i))

lemma transport_supported {S : Set ℂ} (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) (u : n → Test)
    (hu : ∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) :
    ∀ i, tsupport (transport a ha u i : ℂ → ℂ) ⊆ S := by
  intro i
  apply (tsupport_add _ _).trans
  apply Set.union_subset
  · apply (tsupport_add _ _).trans
    apply Set.union_subset
    · exact (tsupport_fderiv_apply_subset ℝ _).trans (hu i)
    · exact (tsupport_smul_subset_right (fun _ : ℂ => (I : ℂ)) (d I (u i) : ℂ → ℂ)).trans ((tsupport_fderiv_apply_subset ℝ I).trans (hu i))
  · have hsum (s : Finset n) : tsupport ((∑ j ∈ s, mulSmooth (a i j) (ha i j) (u j) : Test) : ℂ → ℂ) ⊆ S := by
      classical
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty,Submodule.coe_zero,tsupport_zero,Set.empty_subset]
      | @insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact (tsupport_add _ _).trans (Set.union_subset ((tsupport_mul_subset_right).trans (hu j)) ih)
    exact hsum Finset.univ

/-- A true L2 lower bound for the actual transport operator. -/
theorem supported_transport_estimate {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∀ u : n → Test, (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      ‖embed u‖ ≤ C*‖embed (transport a ha u)‖ := by
  obtain ⟨C,hC,hest⟩ := supported_inhomogeneous_L2 hS (fun i j z => -(a i j z)) (fun i j => (ha i j).continuous.neg)
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun u hu => ?_⟩
  have heq : ∀ i z, (d 1 (u i)+I • d I (u i) : Test) z =
      transport a ha u i z+∑ j, -(a i j z)*u j z := by
    intro i z
    change _ = (d 1 (u i)+I • d I (u i) : Test) z+(∑ j, mulSmooth (a i j) (ha i j) (u j) : Test) z+_
    simp only [Submodule.coe_sum,Finset.sum_apply,mulSmooth,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_neg_distrib,neg_mul]
    ring
  have h := hest u (transport a ha u) hu (transport_supported a ha u hu) heq
  rw [← norm_embed_sq,← norm_embed_sq] at h
  have hs := Real.sq_sqrt hC.le
  have hp : 0 ≤ Real.sqrt C*‖embed (transport a ha u)‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (embed u)]
end ElasticityPlanar
namespace ElasticityPlanarDistribution
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap LineDeriv Laplacian ENNReal BigOperators
open ElasticityRegularity

lemma schwartz_derivative_commute (v w : ℂ) (f : Test) : ∂_{v} (∂_{w} f)=∂_{w} (∂_{v} f) := by
  ext x
  have hdd (v w : ℂ) : (∂_{v} (∂_{w} f) : Test) x =
      fderiv ℝ (fderiv ℝ (f : ℂ → ℂ)) x v w := by
    change fderiv ℝ (fun y => fderiv ℝ (f : ℂ → ℂ) y w) x v = _
    rw [fderiv_clm_apply (((f.smooth ⊤).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) x)
      (differentiableAt_const w)]
    simp
  rw [hdd,hdd]
  exact (f.smooth ⊤).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _
lemma derivative_commute (v w : ℂ) (u : Dist) : ∂_{v} (∂_{w} u)=∂_{w} (∂_{v} u) := by
  ext φ
  change u (- ∂_{w} (- ∂_{v} φ))=u (- ∂_{v} (- ∂_{w} φ))
  simp only [LineDeriv.lineDerivOp_neg,neg_neg]
  rw [schwartz_derivative_commute]
lemma dhol_dbar (u : Dist) : dhol (dbar u)=Δ u := by
  rw [laplacian_eq_sum Complex.orthonormalBasisOneI]
  simp only [Complex.coe_orthonormalBasisOneI,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [dhol,dbar,LineDeriv.lineDerivOp_add,LineDeriv.lineDerivOp_smul,
    smul_add,smul_smul,Complex.I_mul_I,neg_one_smul]
  rw [derivative_commute (1 : ℂ) I]
  module
lemma dhol_sum {ι : Type*} (S : Finset ι) (u : ι → Dist) :
    dhol (∑ i ∈ S, u i)=∑ i ∈ S, dhol (u i) := by
  simp only [dhol,LineDeriv.lineDerivOp_sum,Finset.smul_sum,Finset.sum_sub_distrib]
lemma dhol_add (u v : Dist) : dhol (u+v)=dhol u+dhol v := by
  simp only [dhol,LineDeriv.lineDerivOp_add,smul_add]
  module
lemma LocalEqual.dhol {Ω : Set ℂ} {u v : Dist} (h : ElasticityRegularity.LocalEqual Ω u v) :
    ElasticityRegularity.LocalEqual Ω (dhol u) (dhol v) :=
  (h.derivative 1).sub ((h.derivative I).smul I)
lemma LocalSobolev.dhol {Ω : Set ℂ} {s : ℝ} {u : Dist} (h : ElasticityRegularity.LocalSobolev Ω s u) :
    ElasticityRegularity.LocalSobolev Ω (s-1) (dhol u) :=
  (h.derivative 1).sub ((h.derivative I).smul I)

theorem local_gain {n : Type*} [Fintype n] {Ω : Set ℂ} {s : ℝ}
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u f : n → Dist) (heq : Equation Ω a u f)
    (hu : ∀ i, ElasticityRegularity.LocalSobolev Ω s (u i))
    (hf : ∀ i, ElasticityRegularity.LocalSobolev Ω s (f i)) :
    ∀ i, ElasticityRegularity.LocalSobolev Ω (s+1) (u i) := by
  intro i
  apply local_laplacian_gain_basis Complex.orthonormalBasisOneI (hu i)
  have he := LocalEqual.dhol (heq i)
  rw [dhol_dbar,dhol_add,dhol_sum] at he
  apply he.localSobolev
  exact (LocalSobolev.dhol (hf i)).add (ElasticityRegularity.LocalSobolev.sum Finset.univ (fun j _ =>
    LocalSobolev.dhol ((hu j).coeff (ha i j))))

theorem local_all_orders {n : Type*} [Fintype n] {Ω : Set ℂ}
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u f : n → Dist) (heq : Equation Ω a u f)
    (hu : ∀ i, ElasticityRegularity.LocalSobolev Ω 0 (u i))
    (hf : ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N (f i)) :
    ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N (u i) := by
  intro N
  induction N with
  | zero => rw [Nat.cast_zero]; exact hu
  | succ N hN =>
    rw [Nat.cast_add,Nat.cast_one]
    exact local_gain a ha u f heq hN (hf N)

end ElasticityPlanarDistribution
namespace ElasticityPlanar
open MeasureTheory Complex TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators LineDeriv
variable {n : Type*} [Fintype n]

lemma toSchwartz_d (v : ℂ) (φ : Test) : toSchwartz (d v φ)=∂_{v} (toSchwartz φ) := by
  ext z
  rfl
lemma toSchwartz_mul (a : ℂ → ℂ) (ha : a.HasTemperateGrowth) (φ : Test) :
    toSchwartz (mulSmooth a ha.1 φ)=SchwartzMap.smulLeftCLM ℂ a (toSchwartz φ) := by
  ext z
  simp only [toSchwartz_apply,SchwartzMap.smulLeftCLM_apply_apply ha,smul_eq_mul]
  rfl
end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Parameters
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions _root_.OAI.ElasticityPlanar.graphComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators LineDeriv Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]

omit [Fintype n] in
lemma entryInjection_apply (i : n) (f : Hilbert n) : entryInjection i f=(f i : 𝓢'(ℂ,ℂ)) := rfl

lemma planarOperator_apply (a : n → n → ℂ → ℂ) (i : n) (f : Hilbert n) :
    planarOperator a i f=ElasticityPlanarDistribution.dbar (f i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (f j : 𝓢'(ℂ,ℂ)) := by
  simp only [planarOperator,ContinuousLinearMap.comp_apply,add_apply,smul_apply,sum_apply,
    entryInjection_apply,LineDeriv.lineDerivOpCLM_apply,ElasticityPlanarDistribution.dbar]

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap ENNReal LineDeriv BigOperators
variable {n : Type*} [Fintype n]
open ElasticityRegularity

lemma dbar_schwartz (v : 𝓢(ℂ,ℂ)) :
    ElasticityPlanarDistribution.dbar (v : 𝓢'(ℂ,ℂ))=(schwartzDbar v : 𝓢'(ℂ,ℂ)) := by
  simp only [ElasticityPlanarDistribution.dbar,schwartzDbar,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]
  rw [map_add,map_smul]
end ElasticityPlanar

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
lemma planarOperator_test (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u : n → Test) (i : n) :
    planarOperator a i (embed u)=entryInjection i (embed (transport a (fun i j => (ha i j).1) u)) := by
  simp only [planarOperator_apply,entryInjection_apply,embed_apply,L2_distribution,dbar_schwartz]
  have ht : toSchwartz (transport a (fun i j => (ha i j).1) u i)=
      schwartzDbar (toSchwartz (u i))+∑ j, SchwartzMap.smulLeftCLM ℂ (a i j) (toSchwartz (u j)) := by
    simp only [transport,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_smul,map_sum,
      toSchwartz_d,schwartzDbar]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => toSchwartz_mul (a i j) (ha i j) (u j))
  rw [ht,map_add,map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => distribution_schwartz_product (ha i j) (toSchwartz (u j)))

end ElasticityPlanar
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution

section
open scoped ENNReal SchwartzMap
open ElasticityRegularity
lemma supported_smooth_test {S : Set ℂ} (hS : IsCompact S)
    (u : Lp ℂ 2 (volume : Measure ℂ))
    (hu : ∀ N : ℕ, LocalSobolev univ N (u : 𝓢'(ℂ,ℂ)))
    (hs : LocalEqual Sᶜ (u : 𝓢'(ℂ,ℂ)) 0) :
    ∃ v : Test, L2 v=u ∧ tsupport (v : ℂ → ℂ)⊆S := by
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
  obtain ⟨w,_,hw⟩ := local_schwartz_l2_representative Metric.isOpen_ball u hu hcs hc (subset_univ _) h1
  have hb : HasCompactSupport (fun z : ℂ => (b z : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  let v : Test := ⟨fun z => (b z : ℂ)*w z,
    ⟨(Complex.ofRealCLM.contDiff.comp b.contDiff).mul (w.smooth ⊤),hb.mul_right⟩⟩
  have hs' : LocalEqual Sᶜ (u : 𝓢'(ℂ,ℂ)) ((0 : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ,ℂ)) := by
    change LocalEqual Sᶜ (u : 𝓢'(ℂ,ℂ)) ((Lp.toTemperedDistributionCLM ℂ volume 2) 0)
    rw [map_zero]
    exact hs
  have hzero := LocalEqual.lp_ae hS.isClosed.isOpen_compl u 0 hs'
  have hev : L2 v=u := by
    apply Lp.ext
    filter_upwards [(toSchwartz v).coeFn_toLp 2 volume,hw,hzero,Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz hzB hzout hz0
    change (L2 v : ℂ → ℂ) z=v z at hz
    rw [hz]
    change (b z : ℂ)*w z=u z
    by_cases hzS : z∈S
    · have hzn : ‖z‖≤R := hSR z hzS
      have hzB' : z∈Metric.ball 0 (R+3) := by simpa only [Metric.mem_ball,dist_zero_right] using (show ‖z‖<R+3 by linarith)
      have hzb : z∈Metric.closedBall 0 b.rIn := by simpa only [b,Metric.mem_closedBall,dist_zero_right] using hzn
      rw [b.one_of_mem_closedBall hzb,Complex.ofReal_one,one_mul]
      exact (hzB hzB').symm
    · have hu0 : u z=0 := (hzout hzS).trans hz0
      rw [hu0]
      by_cases hzB' : z∈Metric.ball 0 (R+3)
      · rw [← hzB hzB',hu0,mul_zero]
      · have hn : R+3≤‖z‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hzB'
        rw [b.zero_of_le_dist (by change R+1≤dist z 0; rw [dist_zero_right]; linarith),Complex.ofReal_zero,zero_mul]
  refine ⟨v,hev,?_⟩
  have hveq : LocalEqual Sᶜ (toSchwartz v : 𝓢'(ℂ,ℂ)) ((0 : 𝓢(ℂ,ℂ)) : 𝓢'(ℂ,ℂ)) := by
    rw [← L2_distribution,hev,map_zero]
    exact hs
  have hpt := hveq.schwartz_eqOn hS.isClosed.isOpen_compl
  apply closure_minimal _ hS.isClosed
  intro z hz
  by_contra hzS
  exact hz (hpt hzS)
end
open scoped ENNReal SchwartzMap BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
lemma operator_all_orders (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (w : Hilbert n) (f : n → 𝓢(ℂ,ℂ))
    (he : ∀ i, planarOperator a i w=(f i : 𝓢'(ℂ,ℂ))) :
    ∀ N : ℕ, ∀ i, LocalSobolev univ N (entryInjection i w) := by
  have he' : ElasticityPlanarDistribution.Equation univ (fun i j z => -a i j z)
      (fun j => (w j : 𝓢'(ℂ,ℂ))) (fun j => (f j : 𝓢'(ℂ,ℂ))) := by
    intro i φ _ _
    have hh := congrArg (fun v : 𝓢'(ℂ,ℂ) => v φ) (he i)
    rw [planarOperator_apply] at hh
    have hn (j : n) : smulLeftCLM ℂ (fun z => -a i j z) (w j : 𝓢'(ℂ,ℂ))=
        -smulLeftCLM ℂ (a i j) (w j : 𝓢'(ℂ,ℂ)) := by
      change smulLeftCLM ℂ (-(a i j)) (w j : 𝓢'(ℂ,ℂ))=_
      rw [smulLeftCLM_neg (ha i j),neg_apply]
    simp only [hn,Finset.sum_neg_distrib,add_apply,neg_apply] at hh ⊢
    linear_combination hh
  exact ElasticityPlanarDistribution.local_all_orders (fun i j z => -a i j z)
    (fun i j => (ha i j).neg) (fun j => (w j : 𝓢'(ℂ,ℂ))) (fun j => (f j : 𝓢'(ℂ,ℂ))) he'
    (fun j => MemSobolev.local_zero (memSobolev_zero_iff.mpr ⟨w j,rfl⟩) univ)
    (fun N j g hg hc _ => sobolev_nat_product Complex.orthonormalBasisOneI N hg hc (f j).memSobolev)

/-- Smooth forcing upgrades every supported weak L2 solution to an actual compact
smooth test vector, by the established elliptic regularity and support identity. -/
theorem supported_weak_is_test {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (w : Hilbert n) (f : n → 𝓢(ℂ,ℂ))
    (he : ∀ i, planarOperator a i w=(f i : 𝓢'(ℂ,ℂ)))
    (hs : ∀ i, LocalEqual Sᶜ (entryInjection i w) 0) :
    ∃ v : n → Test, embed v=w ∧ ∀ i, tsupport (v i : ℂ → ℂ)⊆S := by
  have hall := operator_all_orders a ha w f he
  choose v hv hvs using fun i => supported_smooth_test hS (w i) (fun N => hall N i) (hs i)
  refine ⟨v,?_,hvs⟩
  apply PiLp.ext
  exact hv

/-- Compact support gives uniqueness for the genuine weak transport operator. -/
theorem supported_weak_kernel {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (w : Hilbert n) (he : ∀ i, planarOperator a i w=0)
    (hs : ∀ i, LocalEqual Sᶜ (entryInjection i w) 0) : w=0 := by
  obtain ⟨v,hv,hvs⟩ := supported_weak_is_test hS a ha w (fun _ => 0)
    (fun i => by simpa only [map_zero] using he i) hs
  have htr : embed (transport a (fun i j => (ha i j).1) v)=0 := by
    apply PiLp.ext
    intro i
    apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
    change entryInjection i (embed (transport a (fun i j => (ha i j).1) v))=entryInjection i 0
    rw [← planarOperator_test a ha v i,hv,he i,map_zero]
  obtain ⟨C,_,hC⟩ := supported_transport_estimate hS a (fun i j => (ha i j).1)
  have h := hC v hvs
  rw [htr,norm_zero,mul_zero,hv] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg w))
end ElasticityPlanar
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma supported_weak_unique_oai {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u v : Hilbert n) (he : ∀ i, planarOperator a i u=planarOperator a i v)
    (hu : ∀ i, LocalEqual Sᶜ (entryInjection i u) 0)
    (hv : ∀ i, LocalEqual Sᶜ (entryInjection i v) 0) : u=v := by
  apply sub_eq_zero.mp
  apply supported_weak_kernel hS a ha (u-v)
  · intro i
    rw [map_sub,he,sub_self]
  · intro i φ hφ hs
    simp only [map_sub,sub_apply,hu i φ hφ hs,hv i φ hφ hs,sub_self,zero_apply]
end ElasticityPlanar

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElasticityPlanar.supported_weak_unique_oai.{u_1} := @OAI.ElasticityPlanar.supported_weak_unique_oai.{u_1}
