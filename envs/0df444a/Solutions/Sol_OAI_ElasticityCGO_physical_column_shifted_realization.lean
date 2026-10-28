-- Prove2me | solution 1 for OAI.ElasticityCGO.physical_column_shifted_realization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:30:24.806836+00:00
-- url     : https://prove2.me/submissions/241e0cda-e1fe-4eba-9e46-ccb9652d2cdb

import Mathlib
import Definitions.Def_OAIQ6El006

section
-- module Solutions.OAIQ6_Elast.Elasticity_Bessel
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete Fourier Bessel potentials for the required negative-order
supported Carleman estimate. All functions and operators are actual Schwartz
maps; no Sobolev-shift estimate is being assumed. -/
open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityBessel

lemma temperate_weight (h s : ℝ) : (weight h s).HasTemperateGrowth := by
  exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow X (s/2)).comp
    (((2*Real.pi*h) • ContinuousLinearMap.id ℝ X).hasTemperateGrowth)

lemma temperate_complex_weight (h s : ℝ) :
    (fun x => (weight h s x : ℂ)).HasTemperateGrowth := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp (temperate_weight h s)

lemma weight_add (h s t : ℝ) (x : X) : weight h (s+t) x = weight h s x * weight h t x := by
  simp only [weight, add_div]
  exact Real.rpow_add (by positivity) _ _

@[simp] lemma M_apply (h s : ℝ) (f : S) (x : X) :
    M h s f x = (weight h s x : ℂ)*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (temperate_complex_weight h s) f x

lemma M_add (h s t : ℝ) (f : S) : M h (s+t) f = M h s (M h t f) := by
  ext x
  simp only [M_apply, weight_add, Complex.ofReal_mul]
  ring

@[simp] lemma M_zero (h : ℝ) (f : S) : M h 0 f = f := by
  ext x
  simp only [M_apply, weight_zero, Complex.ofReal_one, one_mul]

lemma fourier_J (h s : ℝ) (f : S) : 𝓕 (J h s f) = M h s (𝓕 f) := by
  simp only [J, FourierTransform.fourier_fourierInv_eq]

lemma J_add_order (h s t : ℝ) (f : S) : J h (s+t) f = J h s (J h t f) := by
  simp only [J, FourierTransform.fourier_fourierInv_eq, M_add]

@[simp] lemma J_zero (h : ℝ) (f : S) : J h 0 f = f := by
  simp only [J, M_zero, FourierTransform.fourierInv_fourier_eq]

lemma J_add (h s : ℝ) (f g : S) : J h s (f+g) = J h s f + J h s g := by
  simp only [J, FourierTransform.fourier_add, map_add, FourierTransform.fourierInv_add]

lemma norm2_nonneg (f : S) : 0 ≤ norm2 f := norm_nonneg _

lemma norm2_add_le (f g : S) : norm2 (f+g) ≤ norm2 f + norm2 g := by
  simpa only [norm2, map_add] using norm_add_le (L2 f) (L2 g)

lemma ip_integral (f g : S) : ip f g = ∫ x : X, star (f x) * g x := by
  simpa only [ip, L2, SchwartzMap.toLpCLM_apply, RCLike.inner_apply', RCLike.star_def]
    using SchwartzMap.inner_toL2_toL2_eq f g volume

lemma norm2_sq (f : S) : norm2 f ^ 2 = (ip f f).re := by
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (L2 f)).symm

lemma ip_fourier (f g : S) : ip (𝓕 f) (𝓕 g) = ip f g :=
  SchwartzMap.inner_fourier_toL2_eq f g

lemma ip_M (h s : ℝ) (f g : S) : ip (M h s f) g = ip f (M h s g) := by
  simp only [ip_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [M_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

lemma ip_J (h s : ℝ) (f g : S) : ip (J h s f) g = ip f (J h s g) := by
  rw [← ip_fourier (J h s f) g, ← ip_fourier f (J h s g), fourier_J, fourier_J]
  exact ip_M h s _ _

lemma norm2_J_sq (h s : ℝ) (f : S) :
    norm2 (J h s f)^2 = (ip f (J h (s+s) f)).re := by
  rw [norm2_sq, ip_J, ← J_add_order]

end ElasticityBessel

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap
namespace ElasticitySchwartzCarleman

lemma smooth (f : Test) : ContDiff ℝ (⊤ : ℕ∞) (f : X → ℂ) := f.smooth _

lemma deriv_conj (f : Test) (z v : X) :
    fderiv ℝ (fun z => star (f z)) z v = star (fderiv ℝ (f : X → ℂ) z v) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z
    ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  exact congrArg (fun L : X →L[ℝ] ℂ => L v) h

lemma integrable_pair (f g : Test) : Integrable (fun z : X => star (f z)*g z) := by
  have hi := (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ)
    (f.postcompCLM Complex.conjCLE.toContinuousLinearMap) g).integrable (μ := volume)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  rfl

lemma pair_add_right (f g h : Test) : pair f (g+h) = pair f g + pair f h := by
  simpa only [pair, FunLike.coe_add, Pi.add_apply, mul_add] using
    integral_add (integrable_pair f g) (integrable_pair f h)

lemma pair_sub_right (f g h : Test) : pair f (g-h) = pair f g - pair f h := by
  simpa only [pair, FunLike.coe_sub, Pi.sub_apply, mul_sub] using
    integral_sub (integrable_pair f g) (integrable_pair f h)

lemma pair_smul_right (f g : Test) (a : ℂ) : pair f (a • g) = a * pair f g := by
  simp only [pair, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (star (f _)) a, mul_assoc]
  exact integral_const_mul a _

lemma pair_d (f g : Test) (v : X) : pair f (d v g) = -pair (d v f) g := by
  have h1 : Integrable (fun z : X => fderiv ℝ (fun z => star (f z)) z v * g z) := by
    simpa only [deriv_conj, d_apply] using integrable_pair (d v f) g
  have h2 : Integrable (fun z : X => star (f z)*fderiv ℝ (g : X → ℂ) z v) :=
    integrable_pair f (d v g)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 (integrable_pair f g)
    (fun z _ => Complex.conjCLE.differentiableAt.comp z ((smooth f).differentiable (by simp) z))
    (fun z _ => (smooth g).differentiable (by simp) z)
    |>.trans (by simp only [pair, deriv_conj, d_apply])

lemma mass_integral (f : Test) : mass f = ∫ z : X, Complex.normSq (f z) := by
  have h := integral_re (integrable_pair f f)
  simpa only [mass, pair, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h.symm

lemma mass_nonneg (f : Test) : 0 ≤ mass f := by
  rw [mass_integral]
  exact integral_nonneg fun _ => Complex.normSq_nonneg _

lemma lap_apply (f : Test) : lap f = d (e 0) (d (e 0) f) +
    d (e 1) (d (e 1) f) + d (e 2) (d (e 2) f) := by
  simp [lap, Fin.sum_univ_three]

lemma gradientMass_nonneg (f : Test) : 0 ≤ gradientMass f :=
  Finset.sum_nonneg fun _ _ => mass_nonneg _

lemma lap_energy (f : Test) : (pair f (lap f)).re = -gradientMass f := by
  simp only [gradientMass, lap_apply, Fin.sum_univ_three, pair_add_right,
    pair_d, Complex.add_re, Complex.neg_re, mass]
  ring

end ElasticitySchwartzCarleman

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

lemma norm2_sq_mass (f : S) : norm2 f^2 = mass f := by
  rw [norm2_sq, ip_integral]
  rfl

lemma fourier_d (i : Fin 3) (f : S) (x : X) :
    𝓕 (d (e i) f) x = (2*Real.pi*Complex.I)*(x i : ℂ)*𝓕 f x := by
  have ht : (inner ℝ · (e i)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (e i)).hasTemperateGrowth
  change 𝓕 (∂_{e i} f) x = _
  simp only [SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply ht, Complex.real_smul, smul_eq_mul]
  simp only [e, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  ring

lemma J_two (h : ℝ) (f : S) : J h 2 f = f - (h : ℂ)^2 • lap f := by
  apply (FourierTransform.fourierCLE ℂ S).injective
  rw [map_sub, map_smul]
  simp only [FourierTransform.fourierCLE_apply, fourier_J, lap_apply,
    FourierTransform.fourier_add]
  ext x
  simp only [M_apply, weight_two, sub_apply, add_apply, smul_apply, smul_eq_mul,
    fourier_d, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    PiLp.smul_apply, smul_eq_mul]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma H1_energy (h : ℝ) (f : S) :
    norm2 (J h 1 f)^2 = mass f + h^2*gradientMass f := by
  rw [norm2_J_sq]
  norm_num only [show (1:ℝ)+1=2 by norm_num]
  rw [J_two, ip_integral]
  change (pair f (f-(h:ℂ)^2 • lap f)).re = _
  rw [pair_sub_right, pair_smul_right]
  have hc : (h:ℂ)^2 = ((h^2:ℝ):ℂ) := by push_cast; rfl
  rw [hc]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, lap_energy, mass]
  ring

lemma mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (f : S) (x : X) :
    mult a f x = a x * f x :=
  SchwartzMap.smulLeftCLM_apply_apply ha f x

lemma d_mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (v : X)
    (f : S) (x : X) :
    d v (mult a f) x = a x * d v f x + fderiv ℝ a x v * f x := by
  rw [d_apply]
  have he : (mult a f : X → ℂ) = a * (f : X → ℂ) := by
    funext y
    exact mult_apply a ha f y
  rw [he, fderiv_mul (ha.1.differentiable (by simp) x) (f.differentiable x)]
  simp only [add_apply, smul_apply,
    smul_eq_mul, d_apply]
  ring

lemma norm2_sum_le {ι : Type*} (T : Finset ι) (f : ι → S) :
    norm2 (∑ i ∈ T, f i) ≤ ∑ i ∈ T, norm2 (f i) := by
  simpa only [norm2, map_sum] using norm_sum_le T (fun i => L2 (f i))

lemma sumNorm_nonneg {n : ℕ} (h s : ℝ) (U : Fin n → S) : 0 ≤ sumNorm h s U :=
  Finset.sum_nonneg (fun _ _ => norm2_nonneg _)

lemma sobNorm_le_sumNorm {n : ℕ} (h s : ℝ) (U : Fin n → S) :
    sobNorm h s U ≤ sumNorm h s U := by
  have hn : 0 ≤ ∑ i, norm2 (J h s (U i))^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have ht := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => norm2 (J h s (U i))) (fun _ _ => norm2_nonneg _)
  dsimp only [sobNorm, sumNorm]
  have hsum := sumNorm_nonneg h s U
  dsimp only [sumNorm] at hsum
  nlinarith only [hs, ht, hsum, Real.sqrt_nonneg (∑ i, norm2 (J h s (U i))^2)]

end

end ElasticityNegativeOrder

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Carleman
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma J_sum {ι : Type*} (T : Finset ι) (h s : ℝ) (f : ι → S) :
    J h s (∑ i ∈ T, f i) = ∑ i ∈ T, J h s (f i) := by
  simp only [J, FourierTransform.fourier_sum, map_sum, FourierTransform.fourierInv_sum]

end ElasticityPhysicalEstimate

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma shiftD_apply (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    shiftD z i f = d (e i) f + z i • f := rfl

end ElasticityPhysicalAlgebra

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
open Set MeasureTheory SchwartzMap
open scoped BigOperators SchwartzMap Topology

end

end OAI
end

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
namespace ElasticityDistribution

open ElasticityAugmented ElasticityRegularity TemperedDistribution
lemma dd_apply (i : Fin 3) (u : Dist) : dd i u = ∂_{e i} u := rfl

open ElasticityAugmented TrivSqZeroExt

lemma sd_apply (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) : sd z i u = dd i u+z i • u := rfl
end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity


variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_support_subset (g : E → ℂ) (m : E) :
    tsupport (fun x => fderiv ℝ g x m) ⊆ tsupport g :=
  (tsupport_comp_subset (g := fun T : E →L[ℝ] ℂ => T m) (by simp) (fderiv ℝ g)).trans
    (tsupport_fderiv_subset ℝ)

end ElasticityRegularity

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators
namespace ElasticityDistribution
open ElasticityAugmented TemperedDistribution
namespace LocalEq
variable {Ω : Set X} {u v w u' v' : Dist}
lemma add (h : LocalEq Ω u v) (h' : LocalEq Ω u' v') : LocalEq Ω (u+u') (v+v') := by
  intro φ hc hs
  simp only [add_apply,h φ hc hs,h' φ hc hs]
lemma smul (h : LocalEq Ω u v) (c : ℂ) : LocalEq Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
lemma sum {ι : Type*} (s : Finset ι) {a b : ι → Dist} (h : ∀ i ∈ s, LocalEq Ω (a i) (b i)) :
    LocalEq Ω (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  intro φ hc hs
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun i hi => h i hi φ hc hs)
lemma derivative (h : LocalEq Ω u v) (i : Fin 3) : LocalEq Ω (dd i u) (dd i v) := by
  intro φ hc hs
  change u (- ∂_{e i} φ) = v (- ∂_{e i} φ)
  apply h
  · change HasCompactSupport (fun x => -((∂_{e i} φ : Test) x))
    exact (hc.fderiv_apply (𝕜 := ℝ) (e i)).neg
  · change tsupport (-((∂_{e i} φ : Test) : X → ℂ)) ⊆ Ω
    rw [tsupport_neg]
    exact (ElasticityRegularity.derivative_support_subset (φ : X → ℂ) (e i)).trans hs
end LocalEq

lemma LocalEq.shifted {Ω : Set X} {u v : Dist} (h : LocalEq Ω u v) (z : Fin 3 → ℂ) (i : Fin 3) :
    LocalEq Ω (sd z i u) (sd z i v) :=
  (h.derivative i).add (h.smul (z i))
lemma LocalEq.divergence {Ω : Set X} {u v : Fin 3 → Dist} (h : ∀ i, LocalEq Ω (u i) (v i))
    (z : Fin 3 → ℂ) : LocalEq Ω (divd z u) (divd z v) :=
  LocalEq.sum Finset.univ (fun i _ => (h i).shifted z i)

end ElasticityDistribution

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
namespace ElasticityDistribution
open ElasticityAugmented ElasticityPhysicalAlgebra ElasticityNegativeOrder

lemma coe_schwartz_add (u v : S) : ((u+v : S) : Dist)=(u : Dist)+(v : Dist) := map_add _ _ _
lemma coe_schwartz_smul (c : ℂ) (u : S) : ((c • u : S) : Dist)=c • (u : Dist) := map_smul _ _ _
lemma coe_schwartz_sum {ι : Type*} (s : Finset ι) (u : ι → S) :
    ((∑ i ∈ s, u i : S) : Dist)=∑ i ∈ s, (u i : Dist) := map_sum _ _ _
lemma sd_schwartz (z : Fin 3 → ℂ) (i : Fin 3) (u : S) :
    sd z i (u : Dist)=(shiftD z i u : Dist) := by
  rw [sd_apply,dd_apply,shiftD_apply,coe_schwartz_add,coe_schwartz_smul]
  congr 1
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq u (e i)
lemma divd_schwartz (z : Fin 3 → ℂ) (u : Fin 3 → S) :
    divd z (fun i => (u i : Dist))=(∑ i, shiftD z i (u i) : S) := by
  rw [divd,coe_schwartz_sum]
  simp only [sd_schwartz]
end ElasticityDistribution

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
-- module Solutions.OAIQ6_Elast.Elasticity_PhysicalCGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
local notation "X" => ElasticityBessel.X

lemma sobolevInjection_zero (q : Lp ℂ 2 (volume : Measure X)) :
    sobolevInjection 0 q=(q : 𝓢'(X,ℂ)) := by
  simp only [sobolevInjection,neg_zero,besselPotential_zero,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply]

/-- A standard Sobolev H1 representative controls the actual semiclassical
Fourier norm uniformly for h in (0,1]. The two Bessel conventions are not
identified: this follows from their concrete L2 derivative realizations. -/
theorem standard_H1_controls_semiclassical :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0≤h → h≤1 → ∀ f : S,
      ∀ q : Lp ℂ 2 (volume : Measure X),sobolevInjection 1 q=(f : 𝓢'(X,ℂ)) →
        norm2 (J h 1 f)≤C*‖q‖ := by
  obtain ⟨L₀,hL₀⟩ := exists_bounded_sobolev_inclusion (E := X) (s := 1) (t := 0) (by norm_num)
  have hd (i : Fin 3) := exists_bounded_sobolev_derivative (E := X) 1 (e i)
  choose L hL using hd
  let A := 1+‖L₀‖+∑ i,‖L i‖
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨2*A,by positivity,fun h hh hh1 f q hq => ?_⟩
  have hzero : L₀ q=L2 f := by
    apply lp_distribution_injective
    change (L₀ q : 𝓢'(X,ℂ))=(L2 f : 𝓢'(X,ℂ))
    rw [← sobolevInjection_zero,hL₀,hq]
    exact (Lp.toTemperedDistribution_toLp_eq f).symm
  have hder (i : Fin 3) : L i q=L2 (d (e i) f) := by
    apply lp_distribution_injective
    have hd := hL i q
    norm_num only [sub_self] at hd
    rw [sobolevInjection_zero,hq,
      lineDerivOp_toTemperedDistributionCLM_eq] at hd
    exact hd.trans (Lp.toTemperedDistribution_toLp_eq (d (e i) f)).symm
  have ha₀ : ‖L₀‖≤A := by
    have hs : 0≤∑ i,‖L i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (L i))
    dsimp [A]
    linarith
  have ha (i : Fin 3) : ‖L i‖≤A := by
    have hs := Finset.single_le_sum (fun j _ => norm_nonneg (L j)) (Finset.mem_univ i)
    dsimp [A]
    linarith [norm_nonneg L₀]
  have hf : norm2 f≤A*‖q‖ := by
    change ‖L2 f‖≤_
    rw [← hzero]
    exact (L₀.le_opNorm q).trans (mul_le_mul_of_nonneg_right ha₀ (norm_nonneg q))
  have hdf (i : Fin 3) : norm2 (d (e i) f)≤A*‖q‖ := by
    change ‖L2 (d (e i) f)‖≤_
    rw [← hder i]
    exact ((L i).le_opNorm q).trans (mul_le_mul_of_nonneg_right (ha i) (norm_nonneg q))
  have hf₂ := pow_le_pow_left₀ (norm2_nonneg f) hf 2
  have hd₂ (i : Fin 3) := pow_le_pow_left₀ (norm2_nonneg (d (e i) f)) (hdf i) 2
  have hg : gradientMass f≤3*(A*‖q‖)^2 := by
    simp only [gradientMass,Fin.sum_univ_three,← norm2_sq_mass]
    nlinarith only [hd₂ 0,hd₂ 1,hd₂ 2]
  have hh₂ : h^2≤1 := by nlinarith
  have he := H1_energy h f
  have hgm := mul_le_mul_of_nonneg_right hh₂ (gradientMass_nonneg f)
  rw [← norm2_sq_mass] at he
  have hb : norm2 (J h 1 f)^2≤4*(A*‖q‖)^2 := by nlinarith only [he,hgm,hg,hf₂]
  have hpos : 0≤2*A*‖q‖ := by positivity
  nlinarith only [hb,norm2_nonneg (J h 1 f),hpos]
/-- The same uniform bound after a compact cutoff, when only a local
standard-H1 representative is available. This is the localization needed
for the actual augmented CGO corrections. -/
theorem local_standard_H1_controls_semiclassical {U : Set X} {g : X → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (hs : tsupport g⊆U) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0≤h → h≤1 → ∀ f : S,
      ∀ q : Lp ℂ 2 (volume : Measure X),
      LocalEqual U (sobolevInjection 1 q) (f : 𝓢'(X,ℂ)) →
        norm2 (J h 1 (mult g f))≤C*‖q‖ := by
  have hmult (u : 𝓢'(X,ℂ)) (hu : MemSobolev 1 2 u) :
      MemSobolev 1 2 (smulLeftCLM ℂ g u) := by
    have hb : OrthonormalBasis (Fin 3) ℝ X := EuclideanSpace.basisFun (Fin 3) ℝ
    have ht := sobolev_nat_product (F := ℂ) hb 1 (g := g) hg hc (u := u)
    simpa only [Nat.cast_one] using ht (by simpa only [Nat.cast_one] using hu)
  obtain ⟨L,hL⟩ := exists_sobolev_realization (E := X) 1 1 (smulLeftCLM ℂ g) hmult
  obtain ⟨C,hC,hest⟩ := standard_H1_controls_semiclassical
  refine ⟨C*(1+‖L‖),by positivity,fun h hh hh1 f q hq => ?_⟩
  have he : sobolevInjection 1 (L q)=(mult g f : 𝓢'(X,ℂ)) := by
    rw [hL,hq.cutoff hg hc hs]
    exact distribution_schwartz_product (hc.hasTemperateGrowth hg) f
  have hb := hest h hh hh1 (mult g f) (L q) he
  have hn := L.le_opNorm q
  calc
    _ ≤ C*‖L q‖ := hb
    _ ≤ C*(‖L‖*‖q‖) := mul_le_mul_of_nonneg_left hn hC.le
    _ ≤ (C*(1+‖L‖))*‖q‖ := by nlinarith [mul_nonneg hC.le (norm_nonneg q)]
end ElasticityRegularity
namespace ElasticityCGO

open Set
open ElasticityAugmented
open ElasticityNegativeOrder (cutoff)

lemma fiveCutoff_one (R : ℝ) (hR : 1≤R) (i : Fin 5) {x : X}
    (hx : x∈Metric.closedBall 0 (R+(i.val : ℝ)+1)) : fiveCutoff R hR i x=1 := by
  have hh := (cutoff (R+(i.val : ℝ)) (by have h := Nat.cast_nonneg (α := ℝ) i.val; linarith)).one_of_mem_closedBall hx
  unfold fiveCutoff
  rw [hh,Complex.ofReal_one]
lemma fiveCutoff_initial (R : ℝ) (hR : 1≤R) :
    EqOn (fiveCutoff R hR 0) 1 (Metric.ball 0 R) := by
  intro x hx
  apply fiveCutoff_one
  simp only [Fin.val_zero,Nat.cast_zero,add_zero,Metric.mem_closedBall]
  have hh := Metric.mem_ball.mp hx
  linarith
end ElasticityCGO
namespace ElasticityCGO
open Set MeasureTheory TemperedDistribution

open scoped SchwartzMap LineDeriv BigOperators ENNReal
open ElasticityRegularity ElasticityAugmented
open ElasticityBessel (norm2 J)
open ElasticityNegativeOrder (mult sobNorm sumNorm)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityDistribution (HV Dist divd)

lemma local_lp_schwartz_of_ae {U : Set X} (w : Lp ℂ 2 (volume : Measure X)) (v : S)
    (hv : ∀ᵐ x ∂(volume : Measure X),x∈U → w x=v x) :
    LocalEqual U (w : Dist) (v : Dist) := by
  intro φ _ hs
  calc
    _ = ∫ x,φ x • w x := Lp.toTemperedDistribution_apply w φ
    _ = ∫ x,φ x • v x := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      by_cases hφ : φ x=0
      · rw [hφ,zero_smul,zero_smul]
      · rw [hx (hs (subset_tsupport _ hφ))]
    _ = _ := (SchwartzMap.coe_apply v φ).symm

/-- The local standard-H1 representative controls the SAME physical
correction and its actual shifted divergence. -/
lemma actual_augmented_local_representative {U : Set X} (z : Fin 3 → ℂ)
    (χ : X → ℂ) (hχ : χ.HasTemperateGrowth) (h1 : EqOn χ 1 U)
    (w : ElasticityPhysicalDual.H) (q : HV) (v : Fin 3 → S)
    (hv : ∀ i,∀ᵐ x ∂(volume : Measure X),x∈U → w i x=v i x)
    (hq : ∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ χ
      ((Fin.cons (divd z (fun j => (w j : Dist))) (fun j => (w j : Dist)) : Fin 4 → Dist) i)) :
    ∀ i,LocalEqual U (sobolevInjection 1 (q i)) (physicalAug z v i : Dist) := by
  have hl (i : Fin 3) := local_lp_schwartz_of_ae (w i) (v i) (hv i)
  intro i
  rw [hq i]
  apply (LocalEqual.cutoff_one _ hχ h1).trans
  refine Fin.cases ?_ (fun i => hl i) i
  have hd := ElasticityDistribution.LocalEq.divergence hl z
  rw [ElasticityDistribution.divd_schwartz] at hd
  exact hd

lemma divShift_mult (z : Fin 3 → ℂ) (g : X → ℂ) (hg : g.HasTemperateGrowth)
    (v : Fin 3 → S) :
    ElasticityPhysicalAlgebra.divShift z (fun i => mult g (v i))=
      mult g (ElasticityPhysicalAlgebra.divShift z v)+
        ∑ i,mult (fun x => fderiv ℝ g x (e i)) (v i) := by
  have hd (i : Fin 3) : (fun x => fderiv ℝ g x (e i)).HasTemperateGrowth :=
    ElasticityPhysicalAlgebra.temperate_partial g hg (e i)
  ext x
  simp only [ElasticityPhysicalAlgebra.divShift,sum_apply,
    ElasticityPhysicalAlgebra.shiftD_apply,add_apply,smul_apply,
    ElasticityNegativeOrder.d_mult_apply g hg,
    ElasticityNegativeOrder.mult_apply g hg,
    ElasticityNegativeOrder.mult_apply _ (hd _),smul_eq_mul,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [ElasticitySchwartzCarleman.e,ElasticityAugmented.e]
  ring

/-- Cutting off the displacement itself retains a uniformly controlled
ACTUAL augmented field. The derivative of the cutoff has no phase loss. -/
theorem cut_actual_augmented_bound {U : Set X} {g : X → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (hs : tsupport g⊆U) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0≤h → h≤1 → ∀ z : Fin 3 → ℂ,
      ∀ q : HV,∀ v : Fin 3 → S,
      (∀ i,LocalEqual U (sobolevInjection 1 (q i)) (physicalAug z v i : Dist)) →
      sobNorm h 1 (physicalAug z (fun i => mult g (v i)))≤C*‖q‖ := by
  obtain ⟨C,hC,hest⟩ := local_standard_H1_controls_semiclassical hg hc hs
  have hed (i : Fin 3) := local_standard_H1_controls_semiclassical
    (smooth_derivative hg (e i)) (compact_derivative hc (e i))
    ((tsupport_fderiv_apply_subset ℝ (e i)).trans hs)
  choose D hD hdest using hed
  have hDsum : 0≤∑ i,D i := Finset.sum_nonneg (fun i _ => (hD i).le)
  refine ⟨4*C+∑ i,D i,by positivity,fun h hh hh1 z q v hq => ?_⟩
  have hbase (i : Fin 4) : norm2 (J h 1 (mult g (physicalAug z v i)))≤C*‖q‖ :=
    (hest h hh hh1 _ (q i) (hq i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm q i) hC.le)
  have hder (i : Fin 3) :
      norm2 (J h 1 (mult (fun x => fderiv ℝ g x (e i)) (v i)))≤D i*‖q‖ :=
    (hdest i h hh hh1 _ (q i.succ) (hq i.succ)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm q i.succ) (hD i).le)
  have hsc : norm2 (J h 1 (ElasticityPhysicalAlgebra.divShift z (fun i => mult g (v i))))≤
      C*‖q‖+(∑ i,D i)*‖q‖ := by
    rw [divShift_mult z g (hc.hasTemperateGrowth hg),ElasticityBessel.J_add,
      ElasticityPhysicalEstimate.J_sum]
    calc
      _ ≤ norm2 (J h 1 (mult g (ElasticityPhysicalAlgebra.divShift z v)))+
        norm2 (∑ i,J h 1 (mult (fun x => fderiv ℝ g x (e i)) (v i))) :=
          ElasticityBessel.norm2_add_le _ _
      _ ≤ C*‖q‖+∑ i,D i*‖q‖ := add_le_add (hbase 0)
        ((ElasticityNegativeOrder.norm2_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hder i)))
      _ = _ := by rw [Finset.sum_mul]
  apply (ElasticityNegativeOrder.sobNorm_le_sumNorm h 1 _).trans
  change (∑ i : Fin 4,norm2 (J h 1 (physicalAug z (fun i => mult g (v i)) i)))≤_
  rw [Fin.sum_univ_succ]
  change norm2 (J h 1 (ElasticityPhysicalAlgebra.divShift z (fun i => mult g (v i))))+
    (∑ i : Fin 3,norm2 (J h 1 (mult g (v i))))≤_
  calc
    _ ≤ (C*‖q‖+(∑ i,D i)*‖q‖)+∑ _i : Fin 3,C*‖q‖ :=
      add_le_add hsc (Finset.sum_le_sum (fun i _ => hbase i.succ))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
end ElasticityCGO
namespace ElasticityCGO
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityRegularity (sobolevInjection)
open ElasticityDistribution (HV Dist divd)

/-- The actual physical CGO corrections have a uniform localized augmented
semiclassical H1 bound. Localize the displacement and then take its actual
shifted divergence: the scalar is not a separately prescribed amplitude. -/
theorem physical_column_shifted_realization_oai (R : ℝ) (hR : 1≤R) (α β : X)
    (lam m : Smooth)
    (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a)
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆Metric.ball 0 R) :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ h₀≤1 ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
        (∀ i,∀ᵐ x ∂(volume : Measure X),x∈Metric.ball 0 R → w i x=v i x) ∧
        (∀ i,EqOn (physical (phase h α β) lam m
          ((fun j => cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
            ((truncation (h : ℂ) 8 a).1 j))-v) i : X → ℂ) 0 (Metric.ball 0 R)) ∧
        (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (fiveCutoff R hR 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖≤C*h^7 ∧ ‖q‖≤C*h ∧
        sobNorm h 1 (physicalAug (phase h α β) (fun i => mult g (v i)))≤C*h := by
  obtain ⟨C₀,h₀,hC₀,hh₀,hsol⟩ := ha
  obtain ⟨D,hD,hest⟩ := cut_actual_augmented_bound hg hc hs
  let C := C₀*(1+D)
  have hC : 0<C := by dsimp [C]; positivity
  have hle : C₀≤C := by dsimp [C]; nlinarith
  have hmul : D*C₀≤C := by dsimp [C]; nlinarith
  refine ⟨C,min h₀ 1,hC,lt_min hh₀ (by norm_num),min_le_right _ _,fun h hh hsml => ?_⟩
  have hhh₀ : h≤h₀ := hsml.trans (min_le_left _ _)
  have hh1 : h≤1 := hsml.trans (min_le_right _ _)
  obtain ⟨w,q,v,hv,hp,hq,hw,hn⟩ := hsol h hh hhh₀
  refine ⟨w,q,v,hv,hp,hq,hw.trans (mul_le_mul_of_nonneg_right hle (by positivity)),
    hn.trans (mul_le_mul_of_nonneg_right hle hh.le),?_⟩
  have hloc := actual_augmented_local_representative (phase h α β) (fiveCutoff R hR 0)
    ((fiveCutoff_compact R hR 0).hasTemperateGrowth (fiveCutoff_smooth R hR 0))
    (fiveCutoff_initial R hR) w q v hv hq
  calc
    _ ≤ D*‖q‖ := hest h hh.le hh1 (phase h α β) q v hloc
    _ ≤ D*(C₀*h) := mul_le_mul_of_nonneg_left hn hD.le
    _ = (D*C₀)*h := by ring
    _ ≤ C*h := mul_le_mul_of_nonneg_right hmul hh.le
end ElasticityCGO

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityCGO.physical_column_shifted_realization_oai := @OAI.ElasticityCGO.physical_column_shifted_realization_oai
