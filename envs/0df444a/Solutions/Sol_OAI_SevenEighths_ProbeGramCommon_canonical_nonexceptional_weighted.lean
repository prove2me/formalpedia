-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGramCommon.canonical_nonexceptional_weighted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:00:31.371413+00:00
-- url     : https://prove2.me/submissions/9a49ba6a-80c7-423a-af2b-637d9a4a914d

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_exists_nonexceptional_residue

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.LogProfiles
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology

open MeasureTheory Real
open scoped FourierTransform SchwartzMap

open scoped ContDiff

namespace FourierBridge

theorem derivative_scale_absorption
    (R u m H CF : ℝ) (A n j : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m)
    (_hH : 0 ≤ H) (hCF : 0 ≤ CF)
    (hu : 0 ≤ u) (hlower : m * (1 + R) ≤ 1 + u)
    (hj : j ≤ n) :
    m ^ (A + n) * (1 + R) ^ A *
      ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j) ≤
      (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hRp : 1 ≤ 1 + R := by linarith
  have hden : 0 < (1 + u) ^ (A + n) := by positivity
  have hpowR : (1 + R) ^ (A + j) ≤ (1 + R) ^ (A + n) :=
    pow_le_pow_right₀ hRp (Nat.add_le_add_left hj A)
  have hscale : m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j ≤
      (1 + u) ^ (A + n) := by
    calc
      m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j =
          m ^ (A + n) * (1 + R) ^ (A + j) := by rw [pow_add]; ring
      _ ≤ m ^ (A + n) * (1 + R) ^ (A + n) :=
        mul_le_mul_of_nonneg_left hpowR (by positivity)
      _ = (m * (1 + R)) ^ (A + n) := by rw [mul_pow]
      _ ≤ (1 + u) ^ (A + n) := by gcongr
  let Q : ℝ := (j.factorial : ℝ) * CF * (H ^ 2) ^ j
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQscale : Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) ≤
      Q * (1 + u) ^ (A + n) := mul_le_mul_of_nonneg_left hscale hQ
  calc
    m ^ (A + n) * (1 + R) ^ A *
        ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
          (H ^ 2 * (1 + R)) ^ j) =
      Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) /
        (1 + u) ^ (A + n) := by dsimp [Q]; rw [mul_pow]; ring
    _ ≤ Q := (div_le_iff₀ hden).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hQscale)
    _ = (j.factorial : ℝ) * CF * (H ^ 2) ^ j := rfl

end FourierBridge

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

open Finset Complex

namespace ActualEisensteinCubic

theorem quotient_char_ne_two_of_two_not_mem (P : Ideal O) [P.IsMaximal]
    (h2 : (2 : O) ∉ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  intro heq
  have hz : ((ringChar (O ⧸ P) : ℕ) : O ⧸ P) = 0 := ringChar.Nat.cast_ringChar
  rw [heq] at hz
  apply h2
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (by simpa only [map_ofNat, Nat.cast_ofNat] using hz)

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace

theorem fourier_prod_eq_iterated (f : LogPlane → ℂ) (hf : Integrable f) (ξ η : ℝ) :
    𝓕 f (WithLp.toLp 2 (ξ, η)) =
      𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
  let w : LogPlane := WithLp.toLp 2 (ξ, η)
  let G : LogPlane → ℂ := fun z => Real.fourierChar (-⟪z, w⟫) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℝ × ℝ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℝ ℝ).integrable_comp_of_integrable hG
  calc
    𝓕 f (WithLp.toLp 2 (ξ, η)) = ∫ z : LogPlane, G z := rfl
    _ = ∫ z : ℝ × ℝ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
        (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding G).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          simp only [G, w, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

theorem verticalMajorant_integrable (f : SchwartzMap ℂ ℂ) : Integrable (verticalMajorant f) :=
  integrable_inv_one_add_sq.const_mul _

theorem norm_le_verticalMajorant (f : SchwartzMap ℂ ℂ) (x y : ℝ) :
    ‖f (complexPoint x y)‖ ≤ verticalMajorant f y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ f (complexPoint x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 (complexPoint x y)
  have hy : y ^ 2 ≤ ‖complexPoint x y‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, complexPoint]
    nlinarith [sq_nonneg x]
  have hym := mul_le_mul_of_nonneg_right hy (norm_nonneg (f (complexPoint x y)))
  have hden : 0 < 1 + y ^ 2 := by positivity
  rw [verticalMajorant, ← div_eq_mul_inv]
  apply (le_div_iff₀ hden).mpr
  nlinarith

theorem partialFourier_continuous (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Continuous (partialFourier f η) := by
  change Continuous (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  apply continuous_of_dominated
    (bound := verticalMajorant f)
  · intro x
    have hline : Continuous (fun y : ℝ => complexPoint x y) :=
      Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((by fun_prop : Continuous (fun y : ℝ => Real.fourierChar (-inner ℝ y η))).smul
      (f.continuous.comp hline)).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_verticalMajorant f x y
  · exact verticalMajorant_integrable f
  · exact Eventually.of_forall fun y => by
      have hf : Continuous (fun x : ℝ => f (complexPoint x y)) :=
        f.continuous.comp (horizontal_isometry y).continuous
      exact continuous_const.smul hf

theorem partialFourier_integrable (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Integrable (partialFourier f η) := by
  let G : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z.im η) • f z
  have hG : Integrable G := f.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℝ × ℝ => G (Complex.measurableEquivRealProd.symm z)) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hG
  change Integrable (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  simpa only [G, Complex.measurableEquivRealProd_symm_apply, complexPoint]
    using hGp.integral_prod_left

theorem fourier_partialFourier (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourier f η) ξ = 𝓕 (f : ℂ → ℂ) (complexPoint ξ η) := by
  let fp : SchwartzMap LogPlane ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeComplexIso.toContinuousLinearEquiv f
  have hprod := fourier_prod_eq_iterated (fp : LogPlane → ℂ) fp.integrable ξ η
  have hcoe : (fp : LogPlane → ℂ) = (f : ℂ → ℂ) ∘ planeComplexIso := rfl
  rw [hcoe, Real.fourier_comp_linearIsometry] at hprod
  change 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (complexPoint x y)) η) ξ = _
  simpa only [Function.comp_apply, planeComplexIso_apply] using hprod.symm

theorem partialFourierSchwartz_apply (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourierSchwartz f η x = partialFourier f η x := by
  have heq : 𝓕 (partialFourier f η) =
      (horizontalSlice (𝓕 f) η : ℝ → ℂ) := by
    funext ξ
    rw [fourier_partialFourier, horizontalSlice_apply]
    exact (congrFun (SchwartzMap.fourier_coe f) (complexPoint ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier f η)) := by
    rw [heq]
    exact (horizontalSlice (𝓕 f) η).integrable
  change (𝓕⁻ (horizontalSlice (𝓕 f) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice (𝓕 f) η)) x, ← heq]
  exact (partialFourier_integrable f η).fourierInv_fourier_eq hi
    (partialFourier_continuous f η).continuousAt

theorem partialFourierSchwartz_coe (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    (partialFourierSchwartz f η : ℝ → ℂ) = partialFourier f η :=
  funext (partialFourierSchwartz_apply f η)

theorem fourier_partialFourierSchwartz (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourierSchwartz f η : ℝ → ℂ) ξ =
      𝓕 (f : ℂ → ℂ) ((ξ : ℂ) + Complex.I * (η : ℂ)) := by
  rw [partialFourierSchwartz_coe, fourier_partialFourier, complexPoint_eq]

theorem horizontal_hasFDerivAt (η x : ℝ) :
    HasFDerivAt (fun y : ℝ => complexPoint y η) Complex.ofRealCLM x := by
  have heq : (fun y : ℝ => complexPoint y η) =
      (fun y : ℝ => Complex.ofRealCLM y + Complex.I * (η : ℂ)) := by
    funext y
    exact complexPoint_eq y η
  rw [heq]
  exact Complex.ofRealCLM.hasFDerivAt.add_const _

theorem horizontalSlice_lineDerivOp (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (horizontalSlice F η) = horizontalSlice (∂_{(1 : ℂ)} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, horizontalSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hcomp := (F.hasFDerivAt (complexPoint x η)).comp x (horizontal_hasFDerivAt η x)
  change fderiv ℝ (fun y : ℝ => F (complexPoint y η)) x (1 : ℝ) = _
  change fderiv ℝ ((F : ℂ → ℂ) ∘ (fun y => complexPoint y η)) x (1 : ℝ) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_one]

theorem horizontalSlice_lineDerivOp_twice (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (horizontalSlice F η)) =
      horizontalSlice (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η := by
  rw [horizontalSlice_lineDerivOp, horizontalSlice_lineDerivOp]

theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith

theorem norm_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η ξ : ℝ) :
    ‖horizontalSlice F η ξ‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹ := by
  rw [horizontalSlice_apply, ← div_eq_mul_inv, div_div]
  apply (le_div_iff₀ (by positivity : 0 < (1 + η ^ 2) * (1 + ξ ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay F ξ η]

theorem norm_inverse_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * Real.pi := by
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice F η)) x,
    Real.fourierInv_eq]
  have hb : Integrable (fun ξ : ℝ =>
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun ξ : ℝ => Real.fourierChar (inner ℝ ξ x) • horizontalSlice F η ξ) hb (Eventually.of_forall fun ξ => by
    simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
      norm_horizontalSlice_le F η ξ)
  simpa only [integral_const_mul, integral_univ_inv_one_add_sq] using h

theorem norm_inverse_lineDeriv (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(𝓕⁻ (∂_{(1 : ℝ)} g)) x‖ =
      (2 * Real.pi) * |x| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℝ => inner ℝ u (1 : ℝ)).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [ Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [_root_.smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul, hc]
  simp [RCLike.inner_apply, Real.norm_eq_abs, mul_assoc]

theorem sq_mul_norm_inverse_le_second (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  calc
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ((2 * Real.pi) ^ 2 * x ^ 2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg x) hp) (norm_nonneg _)
    _ = ((2 * Real.pi) ^ 2 * |x| ^ 2) * ‖(𝓕⁻ g) x‖ := by rw [sq_abs]
    _ = _ := by ring

theorem inverse_horizontalSlice_product_decay (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      Real.pi * (planeDecayConstant F +
        planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F))) := by
  have h0 := norm_inverse_horizontalSlice_le F η x
  have h2a := sq_mul_norm_inverse_le_second (horizontalSlice F η) x
  rw [horizontalSlice_lineDerivOp_twice] at h2a
  have h2 := h2a.trans
    (norm_inverse_horizontalSlice_le (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η x)
  have hden : 0 < 1 + η ^ 2 := by positivity
  have h0' : ‖(𝓕⁻ (horizontalSlice F η)) x‖ * (1 + η ^ 2) ≤
      planeDecayConstant F * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h0
  have h2' : (x ^ 2 * ‖(𝓕⁻ (horizontalSlice F η)) x‖) * (1 + η ^ 2) ≤
      planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h2
  nlinarith

theorem partialFourier_product_decay (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f := by
  rw [← partialFourierSchwartz_apply]
  exact inverse_horizontalSlice_product_decay (𝓕 f) η x

theorem norm_partialFourier_le (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f * ((1 + x ^ 2)⁻¹ * (1 + η ^ 2)⁻¹) := by
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + x ^ 2) * (1 + η ^ 2))).mpr
  nlinarith [partialFourier_product_decay f η x]

theorem partialFourier_gaussian_summable_norm (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖partialFourier f (p.2 : ℝ) (p.1 : ℝ)‖) := by
  apply summable_norm_of_cauchy_product
    (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ))
    (partialFourierDecayConstant f)
  intro p
  exact norm_partialFourier_le f (p.2 : ℝ) (p.1 : ℝ)

theorem partialFourier_gaussian_summable (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ)) :=
  (partialFourier_gaussian_summable_norm f).of_norm

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

theorem plane_lattice_summable (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) :=
  (plane_lattice_summable_norm f).of_norm

theorem schwartz_poisson_zero (g : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, g (n : ℝ)) = ∑' n : ℤ, 𝓕 (g : ℝ → ℂ) (n : ℝ) := by
  simpa [fourier_eval_zero, SchwartzMap.fourier_coe] using g.tsum_eq_tsum_fourier 0

theorem vertical_poisson (f : 𝓢(ℂ, ℂ)) (x : ℝ) :
    (∑' n : ℤ, f (complexPoint x (n : ℝ))) =
      ∑' n : ℤ, partialFourier f (n : ℝ) x := by
  exact schwartz_poisson_zero (verticalSlice f x)

private theorem horizontal_poisson (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    (∑' m : ℤ, partialFourier f (n : ℝ) (m : ℝ)) =
      ∑' k : ℤ, (𝓕 f) (complexPoint (k : ℝ) (n : ℝ)) := by
  have h := schwartz_poisson_zero (partialFourierSchwartz f n)
  simpa only [partialFourierSchwartz_apply, partialFourierSchwartz_coe,
    fourier_partialFourier, SchwartzMap.fourier_coe] using h

private theorem iterated_poisson_pair_sum
    (f g h : ℤ → ℤ → ℂ)
    (hf : Summable (Function.uncurry f))
    (hg : Summable (Function.uncurry g))
    (hh : Summable (Function.uncurry h))
    (hvertical : ∀ m, (∑' n, f m n) = ∑' n, h m n)
    (hhorizontal : ∀ n, (∑' m, h m n) = ∑' m, g m n) :
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' p : ℤ × ℤ, g p.1 p.2 := by
  calc
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' m, ∑' n, f m n := hf.tsum_prod
    _ = ∑' m, ∑' n, h m n := tsum_congr hvertical
    _ = ∑' n, ∑' m, h m n := hh.tsum_comm.symm
    _ = ∑' n, ∑' m, g m n := tsum_congr hhorizontal
    _ = ∑' m, ∑' n, g m n := hg.tsum_comm
    _ = ∑' p : ℤ × ℤ, g p.1 p.2 := hg.tsum_prod.symm

theorem integer_pair_poisson (f : 𝓢(ℂ, ℂ)) :
    (∑' p : ℤ × ℤ, f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, (𝓕 f) (complexPoint (p.1 : ℝ) (p.2 : ℝ)) := by
  exact iterated_poisson_pair_sum
    (fun m n => f (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n : ℤ => (𝓕 f : 𝓢(ℂ, ℂ)) (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n => partialFourier f (n : ℝ) (m : ℝ))
    (plane_lattice_summable f) (plane_lattice_summable (𝓕 f))
    (partialFourier_gaussian_summable f)
    (fun m => vertical_poisson f m) (horizontal_poisson f)

end EisensteinSchwartzPoisson

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem dualMap_trans (A B : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    dualMap (A.trans B) z = dualMap B (dualMap A z) := by
  change (ContinuousLinearMap.adjoint
    (A.symm.toContinuousLinearMap.comp B.symm.toContinuousLinearMap)) z = _
  rw [ContinuousLinearMap.adjoint_comp]
  rfl

theorem dual_basis_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    dualMap (basisEquiv w hw) z =
      complexPoint z.re ((z.im - w.re * z.re) / w.im) := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((basisEquiv w hw).symm v) z = _
  simp only [basisEquiv_symm_apply, Complex.inner, complexPoint,
    Complex.mul_re,  Complex.conj_re, Complex.conj_im]
  field_simp [hw]
  ring

theorem dual_mul_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    dualMap (complexMulEquiv c hc) z = (starRingEnd ℂ c)⁻¹ * z := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (c⁻¹ * v) z = _
  simp only [Complex.inner, map_mul, map_inv₀]
  congr 1
  ring

theorem eisensteinDualFrequency_explicit (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinDualFrequency c hc p =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) /
        starRingEnd ℂ c := by
  unfold eisensteinDualFrequency eisensteinLatticeMap scaledBasisEquiv
  rw [dualMap_trans, dual_basis_apply, dual_mul_apply]
  have he : complexPoint (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re
      (((complexPoint (p.1 : ℝ) (p.2 : ℝ)).im - omega3.re *
        (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re) / omega3.im) =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) := by
    apply Complex.ext
    · rfl
    · simp only [complexPoint, omega3_im]
      have hr : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]
      rw [hr]
      ring
  rw [he]
  ring

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem explicitDualFrequency_eq_paperFrequency (c : ℂ) (p : ℤ × ℤ) :
    explicitDualFrequency c p = paperFrequency (eisEmbedding (dualFrequencyEquiv p) / c) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hnum : complexPoint (p.1 : ℝ)
      (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) =
      (2 * Complex.I / (Real.sqrt 3 : ℂ)) *
        starRingEnd ℂ (eisEmbedding (dualFrequencyEquiv p)) := by
    rw [dualFrequencyEquiv_coordinates]
    apply Complex.ext <;>
      norm_num [complexPoint, Complex.div_re, Complex.div_im] <;>
      field_simp <;>
      simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  unfold explicitDualFrequency paperFrequency
  rw [map_div₀, hnum]
  ring

theorem explicitDualFrequency_norm_sq (c : ℂ) (p : ℤ × ℤ) :
    ‖explicitDualFrequency c p‖ ^ 2 =
      (4 / 3 : ℝ) * ‖eisEmbedding (dualFrequencyEquiv p)‖ ^ 2 / ‖c‖ ^ 2 := by
  rw [explicitDualFrequency_eq_paperFrequency, paperFrequency_norm_sq, norm_div, div_pow]
  ring

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_hasDerivAt (t x : ℝ) :
    HasDerivAt (logPhase t) (phaseDerivative t * logPhase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (phaseDerivative t)).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  have he (y : ℝ) : Complex.exp (phaseDerivative t * (y : ℂ)) = logPhase t y := by
    unfold phaseDerivative logPhase
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  simpa only [mul_comm] using h

lemma logPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logPhase t) = fun x => phaseDerivative t ^ n * logPhase t x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun y => phaseDerivative t ^ n * logPhase t y) x =
        phaseDerivative t ^ n * (phaseDerivative t * logPhase t x) from
      ((logPhase_hasDerivAt t x).const_mul _).deriv]
    simp only [pow_succ]
    ring

lemma phaseDerivative_norm (t : ℝ) : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  simp only [phaseDerivative, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_of_nonneg Real.pi_pos.le]

lemma logPhase_iteratedFDeriv_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (logPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logPhase_iteratedDeriv]
  simp only [norm_mul, norm_pow, phaseDerivative_norm, logPhase_norm, mul_one]

end JointLogSeparation

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CenteredExceptionalProfile
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredExceptionalProfile
open UniqueFactorizationMonoid HeckeFamily CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O
open CenteredExceptionalCount CenteredMomentCanonical
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem outside_fixed_support (Q : Ideal O) (hQ : Q ≠ 0)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (P : Ideal O) (hP : Prime P)
    (hPS : P ∉ (normalizedFactors Q).toFinset) :
    λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := (inferInstance : P.IsMaximal).eq_of_le hJ.ne_top hPJ
    apply hPS
    apply Multiset.mem_toFinset.mpr
    apply (Ideal.mem_normalizedFactors_iff hQ).mpr
    exact ⟨Ideal.isPrime_of_prime hP, hPJ' ▸ hQJ⟩
  have h72 : (72 : O) ∉ P := by
    intro hh
    have hle : Q ≤ P := hQ72.trans ((Ideal.span_singleton_le_iff_mem _).mpr hh)
    have he := Ideal.isCoprime_iff_sup_eq.mp hcop
    rw [sup_eq_right.mpr hle] at he
    exact hP.ne_one (by simpa only [Ideal.one_eq_top] using he)
  have hl : λ₀ ∣ (72 : O) :=
    (dvd_pow_self λ₀ (by decide : (2 : ℕ) ≠ 0)).trans
      (ActualEisensteinCubic.lambda_sq_dvd_three.trans (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩))
  have h2 : (2 : O) ∣ 72 := ⟨36, by norm_num⟩
  refine ⟨?_, ?_, hcop⟩
  · intro hh
    obtain ⟨v, hv⟩ := hl
    exact h72 (hv ▸ P.mul_mem_right v hh)
  · intro hh
    obtain ⟨v, hv⟩ := h2
    exact h72 (hv ▸ P.mul_mem_right v hh)

end SevenEighths.CenteredExceptionalProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramLatticeDecay
namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramLatticeDecay
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem sourceControl_nonneg (S : Finset (ℕ × ℕ)) (W : 𝓢(Joint, ℂ)) :
    0 ≤ sourceControl S W := apply_nonneg _ _

theorem product_decay (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ((1+‖x‖^2)^2 * (1+‖y‖^2)^2) * ‖W (point x y)‖ ≤
      (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W := by
  have hx := WithLp.norm_fst_le ℂ (point x y)
  have hy := WithLp.norm_snd_le ℂ (point x y)
  change ‖x‖ ≤ ‖point x y‖ at hx
  change ‖y‖ ≤ ‖point x y‖ at hy
  have hx2 : 1+‖x‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hy2 : 1+‖y‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hpow : (1+‖x‖^2)^2 * (1+‖y‖^2)^2 ≤ (1+‖point x y‖)^8 := by
    calc
      _ ≤ ((1+‖point x y‖)^2)^2 * ((1+‖point x y‖)^2)^2 := by gcongr
      _ = _ := by ring
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (8,0)) (k := 8) (n := 0) le_rfl le_rfl W (point x y)
  simp only [norm_iteratedFDeriv_zero] at h
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans h

theorem physicalPoint_eq_smul (N : ℝ) (m : O × O) :
    physicalPoint N m = (Real.sqrt N)⁻¹ • point (eisEmbedding m.1) (eisEmbedding m.2) := by
  apply WithLp.ofLp_injective
  simp [physicalPoint, point, div_eq_mul_inv, Algebra.smul_def, mul_comm]

theorem physical_summable (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => ‖W (physicalPoint N m)‖) := by
  let g : O → ℝ := fun m => ((1+N⁻¹*‖eisEmbedding m‖^2)^2)⁻¹
  have hg : Summable g := scaled_eisenstein_cauchy_summable _ (inv_pos.mpr hN)
  have hp := hg.mul_of_nonneg hg (fun _ => by dsimp [g]; positivity)
    (fun _ => by dsimp [g]; positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hp.mul_left ((2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W))
  intro m
  have hb := product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
    (eisEmbedding m.2 / (Real.sqrt N : ℂ))
  have hnorm (m : O) : ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = N⁻¹*‖eisEmbedding m‖^2 := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN.le]
    ring
  simp only [hnorm] at hb
  change ‖W (physicalPoint N m)‖ ≤ ((2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W) * (g m.1*g m.2)
  dsimp only [g]
  rw [ ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [physicalPoint, mul_comm] using hb

theorem physical_lattice_bound :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (N : ℝ), 1 ≤ N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  refine ⟨Finset.Iic (8,0), (2:ℝ)^8 * (4*(1+Real.pi)^2)^2, by positivity, ?_⟩
  intro W N hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let g : O → ℝ := fun m => ((1+N⁻¹*‖eisEmbedding m‖^2)^2)⁻¹
  have hg : Summable g := scaled_eisenstein_cauchy_summable _ (inv_pos.mpr hNp)
  have hp := hg.mul_of_nonneg hg (fun _ => by dsimp [g]; positivity)
    (fun _ => by dsimp [g]; positivity)
  have hpoint (m : O × O) : ‖W (physicalPoint N m)‖ ≤
      ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W) * (g m.1*g m.2) := by
    have hb := product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
      (eisEmbedding m.2 / (Real.sqrt N : ℂ))
    have hn (m : O) : ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = N⁻¹*‖eisEmbedding m‖^2 := by
      rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hNp.le]
      ring
    simp only [hn] at hb
    dsimp only [g]
    rw [ ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simpa only [physicalPoint, mul_comm] using hb
  have hmass : (∑' m : O, g m) ≤ (4*(1+Real.pi)^2)*N := by
    have h := scaled_eisenstein_cauchy_small N⁻¹ (inv_pos.mpr hNp) ((inv_le_one₀ hNp).mpr hN)
    have hh := mul_le_mul_of_nonneg_left h hNp.le
    simpa only [g, ← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul, mul_comm] using hh
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(g m.1*g m.2) :=
      (physical_summable W N hNp).tsum_le_tsum hpoint (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, g m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*((4*(1+Real.pi)^2)*N)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by dsimp [g]; positivity)) hmass 2
    _ = _ := by ring

theorem dualCoordinates_injective : Function.Injective dualCoordinates := by
  intro p q hp
  have h := CubicEisenstein.rowCoordinates_injective hp
  apply Prod.ext
  · exact dualFrequencyEquiv.injective (congrFun h 0)
  · exact dualFrequencyEquiv.injective (congrFun h 1)

theorem dualCoordinates_norm_le (p : DualIndex) :
    ‖dualCoordinates p‖ ≤ 2 * ‖dualPoint p‖ := by
  have hc := CubicEisenstein.coordinates_norm_bound (dualRow p)
  have hp : ‖fun i => eisEmbedding (dualRow p i)‖ ≤ ‖dualPoint p‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h1 := explicitDualFrequency_norm_sq 1 p.1
    have h2 := explicitDualFrequency_norm_sq 1 p.2
    norm_num only [norm_one, one_pow, div_one] at h1 h2
    have hq := norm_point_sq (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)
    fin_cases i
    · change ‖eisEmbedding (dualFrequencyEquiv p.1)‖ ≤ ‖dualPoint p‖
      dsimp only [dualPoint]
      nlinarith [sq_nonneg ‖eisEmbedding (dualFrequencyEquiv p.2)‖,
        norm_nonneg (point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)),
        norm_nonneg (eisEmbedding (dualFrequencyEquiv p.1))]
    · change ‖eisEmbedding (dualFrequencyEquiv p.2)‖ ≤ ‖dualPoint p‖
      dsimp only [dualPoint]
      nlinarith [sq_nonneg ‖eisEmbedding (dualFrequencyEquiv p.1)‖,
        norm_nonneg (point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)),
        norm_nonneg (eisEmbedding (dualFrequencyEquiv p.2))]
  exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

theorem dualPoint_norm_pos (p : DualIndex) (hp : p ≠ 0) : 0 < ‖dualPoint p‖ := by
  have hc : dualCoordinates p ≠ 0 := by
    intro h
    exact hp (dualCoordinates_injective (h.trans dualCoordinates_zero.symm))
  have hh := norm_pos_iff.mpr hc
  have hb := dualCoordinates_norm_le p
  linarith

theorem dual_power_summable (k : ℝ) (hk : 4 < k) :
    Summable (fun p : {p : DualIndex // p ≠ 0} => ‖dualPoint p.val‖ ^ (-k)) := by
  have hs : Summable (fun p : {p : DualIndex // p ≠ 0} => ‖dualCoordinates p.val‖ ^ (-k)) :=
    (CubicEisenstein.summable_integer_four_rpow k hk).comp_injective
    (dualCoordinates_injective.comp (Subtype.val_injective))
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _) _
    (hs.mul_left ((2:ℝ)^k))
  intro p
  have hc : 0 < ‖dualCoordinates p.val‖ := norm_pos_iff.mpr (by
    intro h
    exact p.property (dualCoordinates_injective (h.trans dualCoordinates_zero.symm)))
  have h := Real.rpow_le_rpow_of_nonpos (half_pos hc)
    (by have := dualCoordinates_norm_le p.val; linarith : ‖dualCoordinates p.val‖ / 2 ≤ ‖dualPoint p.val‖)
    (by linarith : -k ≤ 0)
  calc
    _ ≤ (‖dualCoordinates p.val‖ / 2) ^ (-k) := h
    _ = (2:ℝ)^k * ‖dualCoordinates p.val‖ ^ (-k) := by
      rw [Real.div_rpow (norm_nonneg _) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      simp only [div_inv_eq_mul, mul_comm]

theorem norm_scaledDualPoint (L : ℝ) (hL : 0 ≤ L) (u : ℂ) (hu : ‖u‖ = 1)
    (p : DualIndex) : ‖scaledDualPoint L u p‖ = L * ‖dualPoint p‖ := by
  have h1 := norm_point_sq (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)
  have h2 := norm_point_sq (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)
  simp only [norm_mul, hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL,
    one_mul] at h1
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖point (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)‖^2 =
      (L*‖point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)‖)^2
  simp only [h1, mul_pow, h2]
  ring

theorem fourier_seminorm_control (k : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(Joint, ℂ),
      SchwartzMap.seminorm ℝ k 0 (𝓕 W) ≤ C * sourceControl S W := by
  let T : 𝓢(Joint, ℂ) →L[ℝ] 𝓢(Joint, ℂ) := SchwartzMap.fourierTransformCLM ℝ
  let q : Seminorm ℝ 𝓢(Joint, ℂ) := (SchwartzMap.seminorm ℝ k 0).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ Joint ℂ).continuous_seminorm (k,0)).comp T.continuous
  obtain ⟨S,C,hC,hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Joint ℂ) q hq
  refine ⟨S,C,?_,?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

theorem scaledDual_decay (F : 𝓢(Joint, ℂ)) (k : ℕ) (L : ℝ) (hL : 0 < L)
    (u : ℂ) (hu : ‖u‖ = 1) (p : DualIndex) (hp : p ≠ 0) :
    ‖F (scaledDualPoint L u p)‖ ≤ SchwartzMap.seminorm ℝ k 0 F *
      L^(-(k:ℝ)) * ‖dualPoint p‖^(-(k:ℝ)) := by
  have hn : 0 < ‖scaledDualPoint L u p‖ := by
    rw [norm_scaledDualPoint L hL.le u hu]
    exact mul_pos hL (dualPoint_norm_pos p hp)
  have hb := SchwartzMap.norm_pow_mul_le_seminorm ℝ F k (scaledDualPoint L u p)
  have hh : ‖F (scaledDualPoint L u p)‖ ≤
      SchwartzMap.seminorm ℝ k 0 F * ‖scaledDualPoint L u p‖^(-(k:ℝ)) := by
    rw [Real.rpow_neg hn.le, Real.rpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos hn k)]
    simpa only [mul_comm] using hb
  rw [norm_scaledDualPoint L hL.le u hu,
    Real.mul_rpow hL.le (norm_nonneg _)] at hh
  simpa only [mul_assoc] using hh

theorem dual_fourier_summable (A : ℕ) (hA : 2 < A)
    (W : 𝓢(Joint, ℂ)) (L : ℝ) (hL : 0 < L) (u : ℂ) (hu : ‖u‖ = 1) :
    Summable (fun p : {p : DualIndex // p ≠ 0} => ‖(𝓕 W) (scaledDualPoint L u p.val)‖) := by
  have hdim : (4:ℝ) < ((2*A:ℕ):ℝ) := by exact_mod_cast (by omega : 4 < 2*A)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((dual_power_summable ((2*A:ℕ):ℝ) hdim).mul_left
      (SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ))))
  intro p
  exact scaledDual_decay (𝓕 W) (2*A) L hL u hu p.val p.property

theorem dual_fourier_lattice_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (L : ℝ), 1 ≤ L → ∀ (u : ℂ), ‖u‖ = 1 →
        (∑' p : {p : DualIndex // p ≠ 0}, ‖(𝓕 W) (scaledDualPoint L u p.val)‖) ≤
          C * sourceControl S W * L^(-((2*A:ℕ):ℝ)) := by
  obtain ⟨S,C,hC,hbound⟩ := fourier_seminorm_control (2*A)
  let mass : ℝ := ∑' p : {p : DualIndex // p ≠ 0}, ‖dualPoint p.val‖^(-((2*A:ℕ):ℝ))
  have hm : 0 ≤ mass := tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨S,C*(mass+1),mul_pos hC (by positivity),?_⟩
  intro W L hL u hu
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdim : (4:ℝ) < ((2*A:ℕ):ℝ) := by exact_mod_cast (by omega : 4 < 2*A)
  calc
    _ ≤ ∑' p : {p : DualIndex // p ≠ 0},
        (SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ))) *
          ‖dualPoint p.val‖^(-((2*A:ℕ):ℝ)) :=
      (dual_fourier_summable A hA W L hLp u hu).tsum_le_tsum
        (fun p => scaledDual_decay (𝓕 W) (2*A) L hLp u hu p.val p.property)
        ((dual_power_summable ((2*A:ℕ):ℝ) hdim).mul_left _)
    _ = SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ)) * mass := tsum_mul_left
    _ ≤ (C * sourceControl S W) * L^(-((2*A:ℕ):ℝ)) * (mass+1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hbound W) (Real.rpow_nonneg hLp.le _)
      · linarith
      · exact hm
      · exact mul_nonneg (mul_nonneg hC.le (sourceControl_nonneg S W)) (Real.rpow_nonneg hLp.le _)
    _ = _ := by ring

theorem sourceControl_mono {S T : Finset (ℕ × ℕ)} (hST : S ⊆ T)
    (W : 𝓢(Joint, ℂ)) : sourceControl S W ≤ sourceControl T W :=
  Seminorm.le_def.mp (Finset.sup_mono hST) W

end ProbeGramLatticeDecay

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramAnnularLattice
namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramAnnularLattice
open ProbeGramLatticeDecay ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem scaled_embedding_norm_sq (m : O) (N : ℝ) (hN : 0 ≤ N) :
    ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = ‖eisEmbedding m‖^2 / N := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN]

theorem physical_sample_eq_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (W : 𝓢(Joint, ℂ)) (hW : AnnularSupport a b W)
    (N : ℝ) (hN : 0 < N) (hsmall : N < b⁻¹) (m : O × O) :
    W (physicalPoint N m) = 0 := by
  by_contra h
  have hw := hW h
  change a ≤ ‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2 ∧
    ‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2 ≤ b ∧ _ at hw
  have hm : m.1 ≠ 0 := by
    intro hz
    have hh := hw.1
    rw [hz, map_zero, zero_div, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hh
    linarith
  have hl := one_le_eisenstein_norm_sq m.1 hm
  have hu := hw.2.1
  rw [scaled_embedding_norm_sq m.1 N hN.le, div_le_iff₀ hN] at hu
  have hs : b*N < 1 := by
    have hh := mul_lt_mul_of_pos_left hsmall hb
    simpa only [mul_inv_cancel₀ hb.ne'] using hh
  linarith

theorem cauchyWeight_summable : Summable cauchyWeight := by
  change Summable (fun m : O => ((1+‖eisEmbedding m‖^2)^2)⁻¹)
  simpa only [one_mul] using scaled_eisenstein_cauchy_summable 1 zero_lt_one

theorem cauchyWeight_mass_le : (∑' m : O, cauchyWeight m) ≤ 4*(1+Real.pi)^2 := by
  simpa only [cauchyWeight, one_mul] using scaled_eisenstein_cauchy_small 1 zero_lt_one le_rfl

theorem physical_subunit_majorant (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) (m : O × O) :
    ‖W (physicalPoint N m)‖ ≤ (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W *
      (cauchyWeight m.1 * cauchyWeight m.2) := by
  have hn (m : O) : ‖eisEmbedding m‖^2 ≤ ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 := by
    rw [scaled_embedding_norm_sq m N hN.le, le_div_iff₀ hN]
    exact mul_le_of_le_one_right (sq_nonneg _) hN1
  have hd : (1+‖eisEmbedding m.1‖^2)^2 * (1+‖eisEmbedding m.2‖^2)^2 ≤
      (1+‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2)^2 *
        (1+‖eisEmbedding m.2 / (Real.sqrt N : ℂ)‖^2)^2 := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.1)) 2)
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.2)) 2) (by positivity) (by positivity)
  have hp := (mul_le_mul_of_nonneg_right hd (norm_nonneg (W (physicalPoint N m)))).trans
    (product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
      (eisEmbedding m.2 / (Real.sqrt N : ℂ)))
  dsimp only [cauchyWeight]
  rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using hp

theorem physical_subunit_bound (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) :
    (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤
      ((2:ℝ)^8*(4*(1+Real.pi)^2)^2) * sourceControl (Finset.Iic (8,0)) W := by
  have hg := cauchyWeight_summable
  have hp := hg.mul_of_nonneg hg (fun _ => by unfold cauchyWeight; positivity)
    (fun _ => by unfold cauchyWeight; positivity)
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*
        (cauchyWeight m.1*cauchyWeight m.2) :=
      (physical_summable W N hN).tsum_le_tsum (physical_subunit_majorant W N hN hN1)
        (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, cauchyWeight m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(4*(1+Real.pi)^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by unfold cauchyWeight; positivity))
        cauchyWeight_mass_le 2
    _ = _ := by ring

theorem annular_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W → ∀ (N : ℝ), 0 < N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  obtain ⟨S₀,C₀,hC₀,h₀⟩ := physical_lattice_bound
  let K : ℝ := (2:ℝ)^8*(4*(1+Real.pi)^2)^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : 0 < b := ha.trans hab
  refine ⟨S₀ ∪ Finset.Iic (8,0),C₀ + K*b^2,by positivity,?_⟩
  intro W hW N hN
  have hS₀ := sourceControl_mono (S := S₀) (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_left W
  have hS₁ := sourceControl_mono (S := Finset.Iic (8,0))
    (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_right W
  by_cases hN1 : 1 ≤ N
  · apply (h₀ W N hN1).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right (by positivity)) hS₀
      (sourceControl_nonneg _ _) (by positivity)
  · by_cases hs : N < b⁻¹
    · have hz : (∑' m : O × O, ‖W (physicalPoint N m)‖) = 0 := by
        calc
          _ = ∑' _m : O × O, (0:ℝ) := tsum_congr (fun m => by
            rw [physical_sample_eq_zero a b ha hb W hW N hN hs m, norm_zero])
          _ = 0 := tsum_zero
      rw [hz]
      exact mul_nonneg (mul_nonneg (by positivity) (sourceControl_nonneg _ _)) (sq_nonneg _)
    · have hBN : 1 ≤ b*N := by
        have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hs) hb.le
        simpa only [mul_inv_cancel₀ hb.ne'] using hh
      have hBN2 : 1 ≤ b^2*N^2 := by nlinarith [sq_nonneg (b*N-1)]
      calc
        _ ≤ K * sourceControl (Finset.Iic (8,0)) W :=
          physical_subunit_bound W N hN (le_of_not_ge hN1)
        _ ≤ K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W :=
          mul_le_mul_of_nonneg_left hS₁ hK.le
        _ ≤ (K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W) * (b^2*N^2) :=
          le_mul_of_one_le_right (mul_nonneg hK.le (sourceControl_nonneg _ _)) hBN2
        _ = (K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by ring
        _ ≤ (C₀+K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀.le)
              (sourceControl_nonneg _ _)) (sq_nonneg _)

theorem weighted_summable (W : 𝓢(Joint, ℂ)) (d : O × O → ℂ) (B : ℝ)
    (hd : ∀ m, ‖d m‖ ≤ B) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => d m * W (physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((physical_summable W N hN).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)

theorem annular_weighted_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W →
      ∀ (d : O × O → ℂ) (B : ℝ), 0 ≤ B → (∀ m, ‖d m‖ ≤ B) →
      ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O => d m * W (physicalPoint N m)) ∧
        ‖∑' m : O × O, d m * W (physicalPoint N m)‖ ≤ C * sourceControl S W * B * N^2 := by
  obtain ⟨S,C,hC,hbound⟩ := annular_lattice_bound a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW d B hB hd N hN
  refine ⟨weighted_summable W d B hd N hN,?_⟩
  calc
    _ ≤ ∑' m : O × O, B * ‖W (physicalPoint N m)‖ := by
      apply (norm_tsum_le_tsum_norm ((weighted_summable W d B hd N hN).norm)).trans
      apply ((weighted_summable W d B hd N hN).norm).tsum_le_tsum _
        ((physical_summable W N hN).mul_left B)
      intro m
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)
    _ = B * ∑' m : O × O, ‖W (physicalPoint N m)‖ := tsum_mul_left
    _ ≤ B * (C * sourceControl S W * N^2) := mul_le_mul_of_nonneg_left (hbound W hW N hN) hB
    _ = _ := by ring

end ProbeGramAnnularLattice

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowPeriod
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibrationRowModulus_ne_zero (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : calibrationRowModulus C B D≠0 := by
  unfold calibrationRowModulus
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero one_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hB)
    · apply Ideal.span_singleton_eq_bot.not.mpr
      norm_num
  · exact D.numeratorSupported.1

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowGramFixedCoefficient
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gramFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : gramFixedModulus S hS≠0 := by
  unfold gramFixedModulus
  apply mul_ne_zero
  · exact mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (calibrationForSet S hS).generator_ne_zero)
      (calibrationRowModulus_ne_zero _ _ (calibrationForSet S hS).generator_ne_zero _)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramJointFixed
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma jointFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : jointFixedModulus S hS≠0 := by
  apply mul_ne_zero
  · apply mul_ne_zero (gramFixedModulus_nonzero S hS)
    exact Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ ConcretePrimeRowBridge.goodLambda_prime.ne_zero)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramPeriodicPoisson
namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramPeriodicPoisson

theorem fourier_joint_eq_iterated (f : Joint → ℂ) (hf : Integrable f) (ξ η : ℂ) :
    𝓕 f (point ξ η) =
      𝓕 (fun x : ℂ => 𝓕 (fun y : ℂ => f (point x y)) η) ξ := by
  let w : Joint := point ξ η
  let G : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z w) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℂ × ℂ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℂ ℂ).integrable_comp_of_integrable hG
  calc
    𝓕 f (point ξ η) = ∫ z : Joint, G z := rfl
    _ = ∫ z : ℂ × ℂ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℂ ℂ).integral_comp
        (MeasurableEquiv.toLp 2 (ℂ × ℂ)).measurableEmbedding G).symm
    _ = ∫ x : ℂ, ∫ y : ℂ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = _ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          simp only [G, w, point, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

theorem planeMajorant_integrable : Integrable planeMajorant := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
    (r := 4) (by norm_num)
  change Integrable (fun y : ℂ => ((1 + ‖y‖ ^ 2) ^ 2)⁻¹)
  convert (preTransparency := .instances) h using 1
  funext y
  rw [show -(4:ℝ)/2 = -(2:ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_two]

theorem norm_le_planeMajorant (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ‖W (point x y)‖ ≤ majorantConstant W * planeMajorant y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ W (point x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ W 2 (point x y)
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ W 4 (point x y)
  have hy : ‖y‖^2 ≤ ‖point x y‖^2 := by rw [norm_point_sq]; exact le_add_of_nonneg_left (sq_nonneg _)
  have hy4 : ‖y‖^4 ≤ ‖point x y‖^4 := by nlinarith [sq_nonneg (‖x‖^2)]
  have hm2 := mul_le_mul_of_nonneg_right hy (norm_nonneg (W (point x y)))
  have hm4 := mul_le_mul_of_nonneg_right hy4 (norm_nonneg (W (point x y)))
  rw [planeMajorant, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  dsimp [majorantConstant]
  nlinarith

theorem partialFourier_continuous (W : 𝓢(Joint, ℂ)) (η : ℂ) :
    Continuous (partialFourier W η) := by
  change Continuous (fun x : ℂ => ∫ y : ℂ,
    Real.fourierChar (-inner ℝ y η) • W (point x y))
  apply continuous_of_dominated (bound := fun y => majorantConstant W * planeMajorant y)
  · intro x
    exact ((by fun_prop : Continuous (fun y : ℂ => Real.fourierChar (-inner ℝ y η))).smul
      (W.continuous.comp (show Continuous (fun y : ℂ => point x y) from by
        simp only [point_eq_add]; fun_prop))).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_planeMajorant W x y
  · exact planeMajorant_integrable.const_mul _
  · exact Eventually.of_forall fun y =>
      continuous_const.smul (W.continuous.comp (slice_isometry y).continuous)

theorem partialFourier_integrable (W : 𝓢(Joint, ℂ)) (η : ℂ) :
    Integrable (partialFourier W η) := by
  let G : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z.snd η) • W z
  have hG : Integrable G := W.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℂ × ℂ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℂ ℂ).integrable_comp_of_integrable hG
  change Integrable (fun x : ℂ => ∫ y : ℂ,
    Real.fourierChar (-inner ℝ y η) • W (point x y))
  exact hGp.integral_prod_left

theorem partialFourierSchwartz_apply (W : 𝓢(Joint, ℂ)) (η x : ℂ) :
    partialFourierSchwartz W η x = partialFourier W η x := by
  have heq : 𝓕 (partialFourier W η) = (leftSlice (𝓕 W) η : ℂ → ℂ) := by
    funext ξ
    change 𝓕 (fun x : ℂ => 𝓕 (fun y : ℂ => W (point x y)) η) ξ = _
    rw [← fourier_joint_eq_iterated W W.integrable ξ η]
    exact (congrFun (SchwartzMap.fourier_coe W) (point ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier W η)) := by
    rw [heq]
    exact (leftSlice (𝓕 W) η).integrable
  change (𝓕⁻ (leftSlice (𝓕 W) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (leftSlice (𝓕 W) η)) x, ← heq]
  exact (partialFourier_integrable W η).fourierInv_fourier_eq hi
    (partialFourier_continuous W η).continuousAt

theorem fourier_partialFourierSchwartz (W : 𝓢(Joint, ℂ)) (ξ η : ℂ) :
    𝓕 (partialFourierSchwartz W η) ξ = (𝓕 W) (point ξ η) := by
  simp [partialFourierSchwartz]

theorem product_decay (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ((1+‖x‖^2)^2 * (1+‖y‖^2)^2) * ‖W (point x y)‖ ≤ productDecayConstant W := by
  have hx := WithLp.norm_fst_le ℂ (point x y)
  have hy := WithLp.norm_snd_le ℂ (point x y)
  change ‖x‖ ≤ ‖point x y‖ at hx
  change ‖y‖ ≤ ‖point x y‖ at hy
  have hx2 : 1+‖x‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hy2 : 1+‖y‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hpow : (1+‖x‖^2)^2 * (1+‖y‖^2)^2 ≤ (1+‖point x y‖)^8 := by
    calc
      _ ≤ ((1+‖point x y‖)^2)^2 * ((1+‖point x y‖)^2)^2 := by gcongr
      _ = _ := by ring
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (8,0)) (k := 8) (n := 0) le_rfl le_rfl W (point x y)
  simp only [norm_iteratedFDeriv_zero] at h
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans h

theorem norm_le_product_majorant (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ‖W (point x y)‖ ≤ productDecayConstant W * (planeMajorant x * planeMajorant y) := by
  rw [planeMajorant, planeMajorant, ← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using product_decay W x y

theorem planeMajorant_eisenstein_summable :
    Summable (fun m : ActualEisensteinCubic.O =>
      planeMajorant (ConcreteTraceCRT.eisEmbedding m)) := by
  have hs := CubicEisenstein.summable_embedding_rpow (-4) (by norm_num)
  rw [← Finset.summable_compl_iff (s := ({0} : Finset ActualEisensteinCubic.O))]
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    (hs.subtype (fun m : ActualEisensteinCubic.O => m ∉ ({0} : Finset _)))
  intro m
  have hm : m.val ≠ 0 := by simpa using m.property
  have hn : 0 < ‖ConcreteTraceCRT.eisEmbedding m.val‖ := norm_pos_iff.mpr
    (ConcreteTraceCRT.eisEmbedding_ne_zero hm)
  change ((1+‖ConcreteTraceCRT.eisEmbedding m.val‖^2)^2)⁻¹ ≤
    ‖ConcreteTraceCRT.eisEmbedding m.val‖ ^ (-4:ℝ)
  rw [show (-4:ℝ) = -(4:ℝ) by rfl, Real.rpow_neg hn.le, Real.rpow_ofNat]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg (‖ConcreteTraceCRT.eisEmbedding m.val‖^2)]

theorem joint_eisenstein_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
      ‖W (embeddingPair m)‖) := by
  have hs := planeMajorant_eisenstein_summable.mul_of_nonneg
    planeMajorant_eisenstein_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hs.mul_left (productDecayConstant W))
  intro m
  exact norm_le_product_majorant W _ _

theorem joint_weighted_summable {R : Type*} (q : ActualEisensteinCubic.O → R)
    (a : R × R → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B) (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
      a (q m.1,q m.2) * W (embeddingPair m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((joint_eisenstein_summable_norm W).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

open scoped LineDeriv

theorem leftSlice_lineDeriv (F : 𝓢(Joint, ℂ)) (η v : ℂ) :
    ∂_{v} (leftSlice F η) = leftSlice (∂_{leftInjection v} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, leftSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hd : HasFDerivAt (fun x : ℂ => point x η) leftInjection x := by
    simp only [point_eq_add]
    exact leftInjection.hasFDerivAt.add_const _
  have hc := (F.hasFDerivAt (point x η)).comp x hd
  change fderiv ℝ ((F : Joint → ℂ) ∘ (fun y => point y η)) x v = _
  rw [hc.fderiv]
  rfl

theorem norm_inverse_lineDeriv (g : 𝓢(ℂ, ℂ)) (v x : ℂ) :
    ‖(𝓕⁻ (∂_{v} g)) x‖ = (2 * Real.pi) * |inner ℝ x v| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℂ => inner ℝ u v).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul]
  rw [hc]
  simp only [Real.norm_eq_abs, mul_assoc]

theorem inner_sq_mul_norm_inverse_le (g : 𝓢(ℂ, ℂ)) (v x : ℂ) :
    (inner ℝ x v)^2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{v} (∂_{v} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ ((2 * Real.pi)^2 * (inner ℝ x v)^2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg _) hp) (norm_nonneg _)
    _ = _ := by rw [← sq_abs (inner ℝ x v)]; ring

theorem norm_sq_mul_norm_inverse_le (g : 𝓢(ℂ, ℂ)) (x : ℂ) :
    ‖x‖^2 * ‖(𝓕⁻ g) x‖ ≤
      ‖(𝓕⁻ (∂_{(1:ℂ)} (∂_{(1:ℂ)} g))) x‖ +
      ‖(𝓕⁻ (∂_{Complex.I} (∂_{Complex.I} g))) x‖ := by
  have h1 := inner_sq_mul_norm_inverse_le g 1 x
  have hi := inner_sq_mul_norm_inverse_le g Complex.I x
  have he : (inner ℝ x (1:ℂ))^2 + (inner ℝ x Complex.I)^2 = ‖x‖^2 := by
    rw [Complex.sq_norm]
    simp [Complex.inner, Complex.normSq_apply, sq]
  rw [← he, add_mul]
  exact add_le_add h1 hi

theorem norm_inverse_leftSlice_le (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
      productDecayConstant F * planeMajorant η * ∫ y : ℂ, planeMajorant y := by
  have hb : Integrable (fun y : ℂ =>
      productDecayConstant F * planeMajorant η * planeMajorant y) :=
    planeMajorant_integrable.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun y : ℂ => Real.fourierChar (inner ℝ y x) • leftSlice F η y) hb
    (Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul,
        leftSlice_apply, mul_left_comm, mul_assoc, mul_comm] using norm_le_product_majorant F y η)
  rw [congrFun (SchwartzMap.fourierInv_coe (leftSlice F η)) x, Real.fourierInv_eq]
  simpa only [integral_const_mul] using h

theorem inverse_leftSlice_weight_le (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2) * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
      ‖(𝓕⁻ (leftSlice F η)) x‖ +
      ‖(𝓕⁻ (leftSlice (leftSecondReal F) η)) x‖ +
      ‖(𝓕⁻ (leftSlice (leftSecondImag F) η)) x‖ := by
  have h := norm_sq_mul_norm_inverse_le (leftSlice F η) x
  simp only [leftSlice_lineDeriv] at h
  change ‖x‖^2 * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
    ‖(𝓕⁻ (leftSlice (leftSecondReal F) η)) x‖ +
    ‖(𝓕⁻ (leftSlice (leftSecondImag F) η)) x‖ at h
  nlinarith

theorem inverse_leftSlice_first_decay (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2) * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤ firstDecayBound F * planeMajorant η := by
  apply (inverse_leftSlice_weight_le F η x).trans
  have h0 := norm_inverse_leftSlice_le F η x
  have h1 := norm_inverse_leftSlice_le (leftSecondReal F) η x
  have h2 := norm_inverse_leftSlice_le (leftSecondImag F) η x
  dsimp [firstDecayBound, sliceIntegralBound]
  nlinarith

theorem inverse_leftSlice_second_decay (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2)^2 * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤ secondDecayBound F * planeMajorant η := by
  have h := mul_le_mul_of_nonneg_left (inverse_leftSlice_weight_le F η x)
    (show 0 ≤ 1+‖x‖^2 by positivity)
  have h0 := inverse_leftSlice_first_decay F η x
  have h1 := inverse_leftSlice_first_decay (leftSecondReal F) η x
  have h2 := inverse_leftSlice_first_decay (leftSecondImag F) η x
  dsimp [secondDecayBound]
  nlinarith

theorem norm_partialFourier_le (W : 𝓢(Joint, ℂ)) (η x : ℂ) :
    ‖partialFourier W η x‖ ≤
      secondDecayBound (𝓕 W) * (planeMajorant x * planeMajorant η) := by
  rw [← partialFourierSchwartz_apply]
  change ‖(𝓕⁻ (leftSlice (𝓕 W) η)) x‖ ≤ _
  have h := inverse_leftSlice_second_decay (𝓕 W) η x
  have hd : ‖(𝓕⁻ (leftSlice (𝓕 W) η)) x‖ ≤
      secondDecayBound (𝓕 W) * planeMajorant η / (1+‖x‖^2)^2 :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith [h])
  convert (preTransparency := .instances) hd using 1
  simp only [planeMajorant, div_eq_mul_inv]
  ring

open EisensteinSchwartzPoisson hiding O

theorem planeMajorant_cartesian_summable :
    Summable (fun p : ℤ × ℤ => planeMajorant (complexPoint (p.1:ℝ) (p.2:ℝ))) := by
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    summable_int_cauchy_product
  intro p
  change ((1+‖complexPoint (p.1:ℝ) (p.2:ℝ)‖^2)^2)⁻¹ ≤ _
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  rw [Complex.sq_norm]
  simp only [complexPoint, Complex.normSq_apply]
  nlinarith [sq_nonneg (p.1:ℝ), sq_nonneg (p.2:ℝ),
    mul_nonneg (sq_nonneg (p.1:ℝ)) (sq_nonneg (p.2:ℝ))]

theorem joint_cartesian_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖W (point (cartesianPoint p.1) (cartesianPoint p.2))‖) := by
  have hs := planeMajorant_cartesian_summable.mul_of_nonneg
    planeMajorant_cartesian_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_le_product_majorant W _ _) (hs.mul_left (productDecayConstant W))

theorem partialFourier_cartesian_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖partialFourier W (cartesianPoint p.2) (cartesianPoint p.1)‖) := by
  have hs := planeMajorant_cartesian_summable.mul_of_nonneg
    planeMajorant_cartesian_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_partialFourier_le W _ _) (hs.mul_left (secondDecayBound (𝓕 W)))

theorem rightSlice_poisson (W : 𝓢(Joint, ℂ)) (x : ℂ) :
    (∑' p : ℤ × ℤ, W (point x (cartesianPoint p))) =
      ∑' p : ℤ × ℤ, partialFourier W (cartesianPoint p) x := by
  have h := integer_pair_poisson (rightSlice W x)
  have hcoe : (rightSlice W x : ℂ → ℂ) = fun y => W (point x y) := rfl
  simpa only [rightSlice_apply, SchwartzMap.fourier_coe, hcoe, partialFourier, cartesianPoint] using h

private theorem joint_cartesian_eq_partial (W : 𝓢(Joint, ℂ)) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
  have hp := (joint_cartesian_summable_norm W).of_norm
  have hm := (partialFourier_cartesian_summable_norm W).of_norm
  calc
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        W (point (cartesianPoint m) (cartesianPoint n)) := hp.tsum_prod
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
      apply tsum_congr
      intro m
      exact rightSlice_poisson W _
    _ = _ := hm.tsum_comm.symm

private theorem partial_cartesian_poisson (W : 𝓢(Joint, ℂ)) (n : ℤ × ℤ) :
    (∑' m : ℤ × ℤ, partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' m : ℤ × ℤ, (𝓕 W) (point (cartesianPoint m) (cartesianPoint n)) := by
  calc
    _ = ∑' m : ℤ × ℤ, partialFourierSchwartz W (cartesianPoint n) (cartesianPoint m) :=
      tsum_congr fun m =>
        (partialFourierSchwartz_apply W (cartesianPoint n) (cartesianPoint m)).symm
    _ = ∑' m : ℤ × ℤ,
        (𝓕 (partialFourierSchwartz W (cartesianPoint n)) : 𝓢(ℂ, ℂ)) (cartesianPoint m) := by
      simpa only [cartesianPoint] using
        integer_pair_poisson (partialFourierSchwartz W (cartesianPoint n))
    _ = _ := tsum_congr fun m =>
      fourier_partialFourierSchwartz W (cartesianPoint m) (cartesianPoint n)

private theorem cartesian_swap_tsum (F : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ, F (point (cartesianPoint m) (cartesianPoint n))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), F (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  have hF := (joint_cartesian_summable_norm F).of_norm
  exact hF.tsum_comm.trans hF.tsum_prod.symm

private theorem partial_cartesian_eq_fourier (W : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
      partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (tsum_congr (partial_cartesian_poisson W)).trans (cartesian_swap_tsum (𝓕 W))

theorem joint_cartesian_poisson (W : 𝓢(Joint, ℂ)) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (joint_cartesian_eq_partial W).trans (partial_cartesian_eq_fourier W)

theorem blockMap_det (A : ℂ ≃L[ℝ] ℂ) :
    LinearMap.det (blockMap A : Joint →ₗ[ℝ] Joint) =
      LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) ^ 2 := by
  have h := LinearMap.det_conj
    ((A : ℂ →ₗ[ℝ] ℂ).prodMap (A : ℂ →ₗ[ℝ] ℂ))
    (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm
  rw [LinearMap.det_prodMap] at h
  convert (preTransparency := .instances) h using 1 <;> first | rfl | ring

theorem jointInverseJacobian_blockMap (A : ℂ ≃L[ℝ] ℂ) :
    jointInverseJacobian (blockMap A) = inverseJacobian A ^ 2 := by
  rw [jointInverseJacobian, blockMap_det, ← inv_pow, abs_pow]
  rfl

theorem joint_inner_linear_dual (A : Joint ≃L[ℝ] Joint) (x y : Joint) :
    inner ℝ (A x) (jointDual A y) = inner ℝ x y := by
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem jointDual_blockMap (A : ℂ ≃L[ℝ] ℂ) (ξ η : ℂ) :
    jointDual (blockMap A) (point ξ η) = point (dualMap A ξ) (dualMap A η) := by
  apply ext_inner_left ℝ
  intro z
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (point (A.symm z.fst) (A.symm z.snd)) (point ξ η) = _
  simp only [point, WithLp.prod_inner_apply, dualMap,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem joint_integral_comp_linearEquiv (A : Joint ≃L[ℝ] Joint) (f : Joint → ℂ) :
    (∫ x : Joint, f (A x)) = jointInverseJacobian A • ∫ x : Joint, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure Joint))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure Joint) =
      ENNReal.ofReal (jointInverseJacobian A) • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : Joint, f y ∂Measure.map A volume) = (∫ x : Joint, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal
    (show 0 ≤ jointInverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem joint_fourier_comp_linearEquiv (A : Joint ≃L[ℝ] Joint)
    (f : Joint → ℂ) (w : Joint) :
    𝓕 (f ∘ A) w = jointInverseJacobian A • 𝓕 f (jointDual A w) := by
  let H : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z (jointDual A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : Joint, H (A x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [H, joint_inner_linear_dual, Function.comp_apply]
        rfl
    _ = jointInverseJacobian A • ∫ z : Joint, H z := joint_integral_comp_linearEquiv A H
    _ = _ := rfl

theorem joint_fourier_affine (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b w : Joint) :
    (𝓕 (jointAffine W A b)) w =
      jointInverseJacobian A •
        (Real.fourierChar (inner ℝ b (jointDual A w)) • (𝓕 W) (jointDual A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => W (z+b)) ∘ A) w = _
  rw [joint_fourier_comp_linearEquiv]
  have ht : 𝓕 (fun z => W (z+b)) (jointDual A w) =
      Real.fourierChar (inner ℝ b (jointDual A w)) • 𝓕 (W : Joint → ℂ) (jointDual A w) :=
    congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure Joint) (innerₗ Joint) (W : Joint → ℂ) b) (jointDual A w)
  rw [ht]
  rw [congrFun (SchwartzMap.fourier_coe W) (jointDual A w)]

theorem joint_affine_poisson (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b : Joint) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ),
      W (A (point (cartesianPoint p.1) (cartesianPoint p.2))+b)) =
      jointInverseJacobian A • ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        Real.fourierChar (inner ℝ b
          (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))) •
        (𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2))) := by
  have h := joint_cartesian_poisson (jointAffine W A b)
  simp only [jointAffine_apply, joint_fourier_affine] at h
  rw [tsum_const_smul''] at h
  exact h

open ActualEisensteinCubic ConcreteTraceCRT

theorem actual_joint_coset_poisson (W : 𝓢(Joint, ℂ)) (b : O × O) (c : O) (hc : c ≠ 0) :
    (∑' m : O × O, W (embeddingPair (b.1+c*m.1,b.2+c*m.2))) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
          Real.fourierChar (inner ℝ (embeddingPair b)
            (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
            (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have h := joint_affine_poisson W (blockMap A) (embeddingPair b)
  simp only [jointInverseJacobian_blockMap, jointDual_blockMap] at h
  rw [eisenstein_inverseJacobian] at h
  calc
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (embeddingPair
        (b.1+c*latticeCoordEquiv.symm p.1,b.2+c*latticeCoordEquiv.symm p.2)) :=
      ((latticeCoordEquiv.symm.prodCongr latticeCoordEquiv.symm).tsum_eq _).symm
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        W (blockMap A (point (cartesianPoint p.1) (cartesianPoint p.2))+embeddingPair b) := by
      apply tsum_congr
      intro p
      congr 1
      change point (eisEmbedding (b.1+c*ActualEisensteinCoordinates.eval p.1.1 p.1.2))
        (eisEmbedding (b.2+c*ActualEisensteinCoordinates.eval p.2.1 p.2.2)) = _
      simp only [map_add, map_mul, blockMap_apply, point]
      rw [← eisensteinLatticeMap_point (eisEmbedding c) (eisEmbedding_ne_zero hc) p.1,
        ← eisensteinLatticeMap_point (eisEmbedding c) (eisEmbedding_ne_zero hc) p.2]
      change point (eisEmbedding b.1 + A (cartesianPoint p.1))
        (eisEmbedding b.2 + A (cartesianPoint p.2)) =
          point (A (cartesianPoint p.1)+eisEmbedding b.1)
            (A (cartesianPoint p.2)+eisEmbedding b.2)
      simp only [add_comm]
    _ = _ := h

theorem joint_dual_summable_norm (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖) := by
  have hJ : 0 < jointInverseJacobian A :=
    abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)
  have hs := joint_cartesian_summable_norm (𝓕 (jointAffine W A 0))
  have hn (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (jointAffine W A 0)) (point (cartesianPoint p.1) (cartesianPoint p.2))‖ =
      jointInverseJacobian A *
        ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖ := by
    rw [joint_fourier_affine]
    simp [abs_of_pos hJ]
  simp_rw [hn] at hs
  have hi := hs.mul_left (jointInverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

theorem jointFrequency_summable_norm (W : 𝓢(Joint, ℂ)) (c : ℂ) (hc : c ≠ 0) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) => ‖(𝓕 W) (jointFrequency c hc p)‖) := by
  have h := joint_dual_summable_norm W (blockMap (eisensteinLatticeMap c hc))
  simpa only [jointDual_blockMap, jointFrequency, eisensteinDualFrequency, cartesianPoint] using h

theorem joint_fiber_tsum (c : O) (hc : c ≠ 0) (r : Residue c × Residue c)
    (W : O × O → ℂ) :
    (∑' m : quotientPair c ⁻¹' {r}, W m.1) =
      ∑' m : O × O, W ((representativePair c r).1+c*m.1,
        (representativePair c r).2+c*m.2) := by
  let e1 := GaussianFiberEquiv.fiberEquiv c hc r.1
    (GaussianShiftedPartition.representative c r.1)
    (GaussianShiftedPartition.representative_spec c r.1)
  let e2 := GaussianFiberEquiv.fiberEquiv c hc r.2
    (GaussianShiftedPartition.representative c r.2)
    (GaussianShiftedPartition.representative_spec c r.2)
  let e := (e1.prodCongr e2).trans (jointFiberSplit c r).symm
  exact (e.tsum_eq (fun m => W m.1)).symm

theorem actual_joint_periodic_poisson (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    letI : Finite (Residue c) := finite_quotient_span hc
    letI : Fintype (Residue c) := Fintype.ofFinite _
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      ∑ r : Residue c × Residue c, a r *
        ((2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
          ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
            Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
              (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
              (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  have ha (r : Residue c × Residue c) : ‖a r‖ ≤ ∑ t : Residue c × Residue c, ‖a t‖ :=
    Finset.single_le_sum (fun t _ => norm_nonneg (a t)) (Finset.mem_univ r)
  have hs := joint_weighted_summable (Ideal.Quotient.mk (Ideal.span {c})) a _ ha W
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition (quotientPair c) a
    (fun m => W (embeddingPair m)) hs]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (joint_fiber_tsum c hc r (fun m => W (embeddingPair m))).trans
    (actual_joint_coset_poisson W (representativePair c r) c hc)

theorem actual_joint_periodic_fourier (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ), residueFourier c hc a p *
          (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  rw [actual_joint_periodic_poisson W c hc a]
  have hs (r : Residue c × Residue c) : Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      a r * (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
        (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using
      jointFrequency_summable_norm W (eisEmbedding c) (eisEmbedding_ne_zero hc)
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [residueFourier, tsum_fintype, Circle.smul_def, smul_eq_mul,
    Finset.sum_mul, mul_assoc]

theorem residueFourier_norm_le (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    ‖residueFourier c hc a p‖ ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 * B := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  rw [residueFourier, tsum_fintype]
  calc
    _ ≤ ∑ r : Residue c × Residue c, ‖a r *
        (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
          (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r : Residue c × Residue c, B := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [norm_mul, Circle.norm_coe, mul_one] using hB r
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
        Nat.cast_mul, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, Residue, pow_two]

theorem principal_joint_inverse_covolume (c : O) (hc : c ≠ 0) :
    (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 *
      (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 = 4/3 := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)
  rw [← eisEmbedding_norm_sq_eq_absNorm_span]
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  nlinarith

theorem norm_periodic_zero_mean_le (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (hmean : (∑' r, a r) = 0) :
    ‖∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)‖ ≤
      (4/3:ℝ) * B *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
  let F (p : (ℤ × ℤ) × (ℤ × ℤ)) := residueFourier c hc a p *
    (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hF0 : F 0 = 0 := by simp [F, hmean]
  have hnorm (p : (ℤ × ℤ) × (ℤ × ℤ)) : ‖F p‖ ≤ q^2 * B *
      ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (residueFourier_norm_le c hc a B hB p) (norm_nonneg _)
  have hsF : Summable (fun p => ‖F p‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
      ((jointFrequency_summable_norm W (eisEmbedding c) (eisEmbedding_ne_zero hc)).mul_left _)
  have heq : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, F p.val) = ∑' p, F p := by
    apply tsum_subtype_eq_of_support_subset
    intro p hp
    change F p ≠ 0 at hp
    exact fun h => hp (h ▸ hF0)
  have hb : ‖∑' p, F p‖ ≤ q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
    rw [← heq]
    have hs1 : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} => ‖F p.val‖) :=
      hsF.subtype (fun p => p ≠ 0)
    have hm : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} =>
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      (jointFrequency_summable_norm W (eisEmbedding c)
        (eisEmbedding_ne_zero hc)).subtype (fun p => p ≠ 0)
    have ht : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, ‖F p.val‖) ≤
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, q^2 * B *
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ :=
      Summable.tsum_le_tsum (fun p => hnorm p.val) hs1 (hm.mul_left (q^2*B))
    exact (norm_tsum_le_tsum_norm hs1).trans (by simpa only [tsum_mul_left] using ht)
  rw [actual_joint_periodic_fourier W c hc a, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (2/(Real.sqrt 3*‖eisEmbedding c‖^2))^2 * (q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, principal_joint_inverse_covolume c hc]

theorem scaleMap_dual (t : ℝ) (ht : 0 < t) (z : Joint) :
    jointDual (scaleMap t ht) z = t • z := by
  have hz : z = point z.fst z.snd := rfl
  conv_lhs => rw [hz]
  rw [scaleMap, jointDual_blockMap, dual_mul_apply, dual_mul_apply]
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [point, Algebra.smul_def]

theorem scaleMap_inverseJacobian (t : ℝ) (ht : 0 < t) :
    jointInverseJacobian (scaleMap t ht) = t^4 := by
  rw [scaleMap, jointInverseJacobian_blockMap, inverseJacobian, complexMulEquiv_det,
    abs_inv, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos ht, ← inv_pow, inv_inv]
  ring

theorem fourier_scaledSource (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) (z : Joint) :
    (𝓕 (scaledSource W t ht)) z = t^4 • (𝓕 W) (t • z) := by
  rw [scaledSource, joint_fourier_affine, scaleMap_inverseJacobian, scaleMap_dual]
  simp

theorem scaledSource_physicalPoint (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N) (m : O × O) :
    scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN) (embeddingPair m) =
      W (ProbeGramLatticeDecay.physicalPoint N m) := by
  rw [scaledSource_apply, ProbeGramLatticeDecay.physicalPoint_eq_smul]
  rfl

theorem norm_generatorRotation (c : ℂ) (hc : c ≠ 0) : ‖generatorRotation c‖ = 1 := by
  simp [generatorRotation, Complex.norm_real, norm_ne_zero_iff.mpr hc]

theorem scaled_jointFrequency_eq (c : ℂ) (hc : c ≠ 0) (N : ℝ) (hN : 0 < N)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    Real.sqrt N • jointFrequency c hc p =
      ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/‖c‖^2)) (generatorRotation c) p := by
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hs : Real.sqrt (N/‖c‖^2) = Real.sqrt N / ‖c‖ := by
    rw [Real.sqrt_div hN.le, Real.sqrt_sq (norm_nonneg c)]
  have hcoord (v : ℤ × ℤ) : (Real.sqrt N:ℂ) * eisensteinDualFrequency c hc v =
      generatorRotation c * (Real.sqrt (N/‖c‖^2):ℂ) * explicitDualFrequency 1 v := by
    rw [eisensteinDualFrequency_explicit, hs]
    simp only [generatorRotation, explicitDualFrequency, map_one, div_one, Complex.ofReal_div]
    have hnC : (‖c‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    field_simp
  apply WithLp.ofLp_injective
  change (Real.sqrt N • eisensteinDualFrequency c hc p.1,
    Real.sqrt N • eisensteinDualFrequency c hc p.2) = _
  apply Prod.ext
  · simpa [Algebra.smul_def, ProbeGramLatticeDecay.scaledDualPoint, ProbeGramLatticeDecay.point] using hcoord p.1
  · simpa [Algebra.smul_def, ProbeGramLatticeDecay.scaledDualPoint, ProbeGramLatticeDecay.point] using hcoord p.2

theorem sqrt_ratio_decay (N q : ℝ) (hN : 0 < N) (hq : 0 < q) (A : ℕ) :
    (Real.sqrt (N/q))^(-((2*A:ℕ):ℝ)) = (q/N)^A := by
  rw [Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast, pow_mul,
    Real.sq_sqrt (div_nonneg hN.le hq.le), ← inv_pow, inv_div]

theorem physical_weighted_summable (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N)
    (d : O × O → ℂ) (B : ℝ) (hB : ∀ m, ‖d m‖ ≤ B) :
    Summable (fun m : O × O => d m * W (ProbeGramLatticeDecay.physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((ProbeGramLatticeDecay.physical_summable W N hN).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _)

theorem principal_high_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : O) (_hc : c ≠ 0)
        (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖a r‖ ≤ B) → (∑' r, a r) = 0 →
        ∀ (N : ℝ), 0 < N → (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N →
        ‖∑' m : O × O, a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A := by
  obtain ⟨S,C,hC,hhigh⟩ := ProbeGramLatticeDecay.dual_fourier_lattice_bound A hA
  refine ⟨S,(4/3)*C,mul_pos (by norm_num) hC,?_⟩
  intro W c hc a B hB0 hB hmean N hN hscale
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hq : 0 < q := by
    dsimp only [q]
    rw [← eisEmbedding_norm_sq_eq_absNorm_span]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
  have hL : 1 ≤ Real.sqrt (N/q) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only [one_pow]
    exact (le_div_iff₀ hq).mpr (by simpa only [one_mul] using hscale)
  let u : ℂ := generatorRotation (eisEmbedding c)
  have hu : ‖u‖ = 1 := norm_generatorRotation _ (eisEmbedding_ne_zero hc)
  have ht4 : (Real.sqrt N)^4 = N^2 := by
    rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, Real.sq_sqrt hN.le]
  have hf (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ =
      N^2 * ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p)‖ := by
    rw [fourier_scaledSource, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), ht4,
      scaled_jointFrequency_eq _ _ N hN]
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
  have h := norm_periodic_zero_mean_le
    (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)) c hc a B hB hmean
  simp_rw [scaledSource_physicalPoint W N hN, hf, tsum_mul_left] at h
  have hD := hhigh W (Real.sqrt (N/q)) hL u hu
  rw [sqrt_ratio_decay N q hN hq A] at hD
  calc
    _ ≤ (4/3:ℝ)*B*(N^2 *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p.val)‖) := h
    _ ≤ (4/3:ℝ)*B*(N^2 *
        (C * ProbeGramLatticeDecay.sourceControl S W * (q/N)^A)) := by
      gcongr
    _ = _ := by ring

theorem principal_annular_periodic_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (c : O), c ≠ 0 → ∀ (d : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖d r‖ ≤ B) → (∑' r, d r) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A) := by
  obtain ⟨Sl,Cl,hCl,hl⟩ := ProbeGramAnnularLattice.annular_weighted_lattice_bound a b ha hab
  obtain ⟨Sh,Ch,hCh,hh⟩ := principal_high_bound A hA
  refine ⟨Sl∪Sh,Cl+Ch,add_pos hCl hCh,?_⟩
  intro W hW c hc d B hB0 hB hm N hN
  refine ⟨physical_weighted_summable W N hN _ B (fun m => hB _),?_⟩
  have hSl : Cl*ProbeGramLatticeDecay.sourceControl Sl W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_right hCh.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_left W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hSh : Ch*ProbeGramLatticeDecay.sourceControl Sh W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_left hCl.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)/N := div_nonneg (by positivity) hN.le
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hN).mpr hscale)
    rw [min_eq_right hp]
    exact (hh W c hc d B hB0 hB hm N hN hscale).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hB0) (sq_nonneg _))
        (pow_nonneg hratio _))
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A :=
      one_le_pow₀ ((le_div_iff₀ hN).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    exact (hl W hW (fun m => d (quotientPair c m)) B hB0
      (fun m => hB _) N hN).2.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSl hB0) (sq_nonneg _))

theorem ideal_annular_periodic_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (r : Ideal O), r ≠ 0 → ∀ (d : (O ⧸ r) × (O ⧸ r) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖d v‖ ≤ B) → (∑' v, d v) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ)/N)^A) := by
  obtain ⟨S,C,hC,h⟩ := principal_annular_periodic_bound A hA a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW r hr
  obtain ⟨c,hc,heq⟩ : ∃ c : O, c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨ConcretePrimeRowBridge.idealGenerator r,
      ConcretePrimeRowBridge.idealGenerator_ne_zero r hr,
      ConcretePrimeRowBridge.span_idealGenerator r⟩
  subst r
  exact h W hW c hc

end ProbeGramPeriodicPoisson

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramNonexceptionalBlock
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "Joint" => ProbeGramPeriodicPoisson.Joint

theorem literal_nonexceptional_block (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃H : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*goodLambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,goodLambda∉P i)(c : ι→ℕ),
      (∀i,1≤ c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : goodLambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(W : SchwartzMap Joint ℂ),ProbeGramAnnularLattice.AnnularSupport a₀ b₀ W→
      ∀(d : O)(N : ℝ),0<N→
      Summable (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)‖≤
        K*ProbeGramLatticeDecay.sourceControl H W*(Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H,K,hK,hengine⟩ := ProbeGramPeriodicPoisson.ideal_annular_periodic_bound A hA a₀ b₀ ha₀ hab
  refine ⟨H,K,hK,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he W hW d N hN
  have hcount : (normalizedFactors (Ideal.span {k})).count p=
      (normalizedFactors (Ideal.span {r})).count p := by
    rw [hk]
    exact good_factor_count p hgp hchar u a b r hr
  have heR : ¬6∣(normalizedFactors (Ideal.span {r})).count p := hcount ▸ he
  obtain ⟨M,hM,hMN,hres⟩ := exists_nonexceptional_residue S hS σ C k hC hk0 u a b r hr hk
    P hg c hc hfac p hp0 hgp hchar hfixed hcommon heR
  let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype (O⧸M) := Fintype.ofFinite _
  obtain ⟨f,hf,hfn,hfm⟩ := hres d
  have hmean : (∑'v : (O⧸M)×(O⧸M),f v.1 v.2)=0 := by
    rw [tsum_fintype,Fintype.sum_prod_type]
    exact hfm
  have hh := hengine W hW M hM (fun v=>f v.1 v.2) (Ideal.absNorm (Ideal.span {C}))
    (Nat.cast_nonneg _) (fun v=>hfn v.1 v.2) hmean N hN
  have hfun : (fun m : O×O=>f (ProbeGramPeriodicPoisson.idealQuotientPair M m).1
      (ProbeGramPeriodicPoisson.idealQuotientPair M m).2*W (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) := by
    funext m
    rw [ProbeGramPeriodicPoisson.idealQuotientPair,hf]
  rw [hfun] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by unfold ProbeGramLatticeDecay.sourceControl;positivity)
  apply min_le_min_left
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ hN.le
  exact_mod_cast hMN

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramPhysicalScale
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma physicalPoint_first_norm (N : ℝ) (hN : 0<N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).1‖^2=‖eisEmbedding m.1‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]

lemma physicalPoint_second_norm (N : ℝ) (hN : 0<N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).2‖^2=‖eisEmbedding m.2‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramJointConstruction
namespace OAI

noncomputable section
open Filter Set
open scoped Classical SchwartzMap ContDiff Topology

namespace ProbeGramJointConstruction
open ProbeGramLatticeDecay EisensteinSchwartzPoisson

lemma rootScale_pos (a b : ℝ) (ha : 0<a) (z : Joint) : 0< rootScale a b ha z :=
  Real.exp_pos _

lemma tsupport_amplitude_subset (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) :
    tsupport (amplitude W a b ha)⊆sourceCompact b := by
  exact closure_minimal ((support_amplitude W a b ha hs).trans
    (annulus_subset_sourceCompact a b ha hab)) Metric.isClosed_closedBall

theorem jointProfile_factorization (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    jointProfile W U a b ha hab hs hW v T hT z=
      amplitude W a b ha z * FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z) *
        paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) :=
  rawProfile_eq_patchedProfile W U a b ha hs v T hT z

theorem jointProfile_annularSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) :
    ProbeGramAnnularLattice.AnnularSupport a b (jointProfile W U a b ha hab hs hW v T hT) :=
  support_rawProfile W U a b hs v T

end ProbeGramJointConstruction

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramJointProfile
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set FourierBridge
namespace ProbeGramJointProfile
open ProbeGramLatticeDecay EisensteinSchwartzPoisson

lemma rayControl_nonneg (B n : ℕ) (g : 𝓢(ℝ, ℂ)) :
    0 ≤ rayControl B n g := apply_nonneg _ _

lemma mul_derivative_bound {f g : Joint → ℂ} (n : ℕ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Joint)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hfb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ 2^n*C*D := by
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x (by simp)
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (hfb i (Finset.mem_range_succ_iff.mp hi)) (by positivity))
        (hgb (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

lemma compact_derivatives {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set Joint} (hK : IsCompact K) {f : Joint → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ n, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
    obtain ⟨D, hD⟩ := hK.bddAbove_image
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.continuousOn
    exact ⟨D, fun x hx => hD (Set.mem_image_of_mem _ hx)⟩
  choose D hD using hb
  refine ⟨1 + ∑ i ∈ Finset.range (n+1), |D i|, by
    have hn : 0 ≤ ∑ i ∈ Finset.range (n+1), |D i| := by positivity
    linarith, ?_⟩
  intro i hi x hx
  have hs : |D i| ≤ ∑ j ∈ Finset.range (n+1), |D j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_range.mpr (by omega))
  exact (hD i x hx).trans ((le_abs_self _).trans (by linarith))

lemma compact_positive_margin {K : Set Joint} (hK : IsCompact K)
    {h : Joint → ℝ} (hc : Continuous h) (hp : ∀ x ∈ K, 0 < h x) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ K, m ≤ h x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hm⟩ := hK.exists_isMinOn hne hc.continuousOn
    exact ⟨min 1 (h x), lt_min zero_lt_one (hp x hx), min_le_left _ _,
      fun y hy => (min_le_right _ _).trans (hm hy)⟩
  · exact ⟨1, zero_lt_one, le_rfl, fun x hx => False.elim (hne ⟨x,hx⟩)⟩

lemma scaled_argument_derivative {h : Joint → ℝ} (hh : ContDiff ℝ ∞ h)
    {D R : ℝ} (hD : 1 ≤ D) (hR : 0 ≤ R) (i : ℕ) (hi : 1 ≤ i)
    (x : Joint) (hb : ‖iteratedFDeriv ℝ i h x‖ ≤ D) :
    ‖iteratedFDeriv ℝ i (fun y => R*h y) x‖ ≤ (D^2*(1+R))^i := by
  have he : iteratedFDeriv ℝ i (fun y => R*h y) x = R • iteratedFDeriv ℝ i h x :=
    by simpa only [smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (a := R) (i := i) (x := x)
        ((hh.of_le (by exact_mod_cast le_top)).contDiffAt))
  rw [he, norm_smul, Real.norm_of_nonneg hR]
  have hDi : D ≤ D^i := by
    calc D = D^1 := by simp
         _ ≤ D^i := pow_le_pow_right₀ hD hi
  have hRi : R ≤ (1+R)^i := by
    calc R ≤ 1+R := by linarith
         _ = (1+R)^1 := by simp
         _ ≤ (1+R)^i := pow_le_pow_right₀ (by linarith) hi
  calc
    R * ‖iteratedFDeriv ℝ i h x‖ ≤ R*D := mul_le_mul_of_nonneg_left hb hR
    _ ≤ (1+R)^i * D^i := mul_le_mul hRi hDi (by linarith) (by positivity)
    _ ≤ (D^2*(1+R))^i := by
      rw [mul_pow, pow_two, mul_pow]
      have hhD : 1 ≤ D^i := one_le_pow₀ hD
      nlinarith [mul_nonneg (show 0 ≤ (1+R)^i by positivity)
        (show 0 ≤ (D^i)^2-D^i by nlinarith)]

lemma normalized_phase_derivative (v x : ℝ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (logPhase (v/(2*Real.pi))) x‖ = |v|^i := by
  rw [JointLogSeparation.logPhase_iteratedFDeriv_norm, norm_div,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi), Real.norm_eq_abs]
  congr 1
  field_simp

lemma phase_derivative_bound {φ : Joint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {D : ℝ} (hD : 1 ≤ D) (n j : ℕ) (hj : j ≤ n)
    (x : Joint) (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i φ x‖ ≤ D) (v : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y => logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
      (n.factorial : ℝ)*D^n*(1+|v|)^n := by
  have hcomp := norm_iteratedFDeriv_comp_le (JointLogSeparation.logPhase_temperate (v/(2*Real.pi))).1
    hφ (n := j) (by simp) x (C := (1+|v|)^n) (D := D)
  have hc : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (logPhase (v/(2*Real.pi))) (φ x)‖ ≤
      (1+|v|)^n := by
    intro i hi
    rw [normalized_phase_derivative]
    exact (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |v| ≤ 1+|v|) i).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg v]) (hi.trans hj))
  have hd : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i φ x‖ ≤ D^i := by
    intro i hi hij
    exact (hb i (hij.trans hj)).trans (by
      calc D = D^1 := by simp
           _ ≤ D^i := pow_le_pow_right₀ hD hi)
  calc
    _ ≤ (j.factorial : ℝ)*(1+|v|)^n*D^j := hcomp hc hd
    _ ≤ (n.factorial : ℝ)*(1+|v|)^n*D^n := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity))
        (pow_le_pow_right₀ hD hj) (by positivity) (by positivity)
    _ = _ := by ring

lemma kernel_derivative_bound {h : Joint → ℝ} (hh : ContDiff ℝ ∞ h)
    {D m R : ℝ} (hD : 1 ≤ D) (hm : 0 < m) (hm1 : m ≤ 1) (hR : 0 ≤ R)
    (B n j : ℕ) (hj : j ≤ n) (x : Joint)
    (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i h x‖ ≤ D) (hl : m ≤ h x)
    (g : 𝓢(ℝ, ℂ)) :
    ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (((n.factorial : ℝ)*2^(2*B+n)*(D^2)^n/m^(2*B+n))*rayControl B n g) /
        (1+R)^(2*B) := by
  have hu : 0 ≤ R*h x := mul_nonneg hR (hm.le.trans hl)
  have hden : 0 < (1+R*h x)^(2*B+n) := by positivity
  have harg : ContDiff ℝ ∞ (fun y => R*h y) := contDiff_const.mul hh
  have hcomp : ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g/(1+R*h x)^(2*B+n))*
        (D^2*(1+R))^j := by
    apply norm_iteratedFDeriv_comp_le (g.smooth ⊤) harg (by simp) x
    · intro i hi
      apply (le_div_iff₀ hden).mpr
      have hd := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (2*B+n,n)) (k := 2*B+n) (n := i) le_rfl (hi.trans hj) g (R*h x)
      change (1+‖R*h x‖)^(2*B+n) * ‖iteratedFDeriv ℝ i g (R*h x)‖ ≤
        2^(2*B+n)*rayControl B n g at hd
      rw [Real.norm_of_nonneg hu] at hd
      simpa only [mul_comm] using hd
    · intro i hi hij
      exact scaled_argument_derivative hh hD hR i hi x (hb i (hij.trans hj))
  have hscale : m*(1+R) ≤ 1+R*h x := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hl)]
  have habs := FourierBridge.derivative_scale_absorption R (R*h x) m D
    (2^(2*B+n)*rayControl B n g) (2*B) n j hR hm (by linarith)
    (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)) hu hscale hj
  have hbound : m^(2*B+n)*(1+R)^(2*B)*
      ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (n.factorial : ℝ)*(2^(2*B+n)*rayControl B n g)*(D^2)^n := by
    calc
      _ ≤ m^(2*B+n)*(1+R)^(2*B)*
          ((j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g/(1+R*h x)^(2*B+n))*
            (D^2*(1+R))^j) := mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ ≤ (j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g)*(D^2)^j := habs
      _ ≤ _ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj)
            (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)))
          (pow_le_pow_right₀ (one_le_pow₀ hD) hj) (by positivity)
          (mul_nonneg (by positivity) (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)))
  apply (le_div_iff₀ (by positivity : 0 < (1+R)^(2*B))).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < m^(2*B+n))).mpr
  convert (preTransparency := .instances) hbound using 1 <;> ring

lemma amplitudeControl_nonneg (n : ℕ) (A : 𝓢(Joint, ℂ)) :
    0 ≤ amplitudeControl n A := apply_nonneg _ _

lemma amplitude_derivative_bound (n i : ℕ) (hi : i ≤ n)
    (A : 𝓢(Joint, ℂ)) (x : Joint) :
    ‖iteratedFDeriv ℝ i A x‖ ≤ amplitudeControl n A := by
  have hp : schwartzSeminormFamily ℝ Joint ℂ (0, i) ≤
      (Finset.Iic (0,n)).sup (schwartzSeminormFamily ℝ Joint ℂ) :=
    Finset.le_sup (Finset.mem_Iic.mpr ⟨le_rfl, hi⟩)
  have hz : ‖iteratedFDeriv ℝ i A x‖ ≤ SchwartzMap.seminorm ℝ 0 i A := by
    simpa using SchwartzMap.le_seminorm ℝ 0 i A x
  exact hz.trans (Seminorm.le_def.mp hp A)

theorem compact_profile_seminorm
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (g : 𝓢(ℝ, ℂ)) (v R : ℝ), 0 ≤ R →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x)) →
      SchwartzMap.seminorm ℝ k n F ≤
        C*amplitudeControl n A*rayControl B n g*(1+|v|)^n/(1+R)^(2*B) := by
  obtain ⟨Dφ, hDφ, hbφ⟩ := compact_derivatives hK hφ n
  obtain ⟨Dh, hDh, hbh⟩ := compact_derivatives hK hh n
  obtain ⟨m, hm, hm1, hml⟩ := compact_positive_margin hK hh.continuous hhpos
  obtain ⟨L0, hL0⟩ := hK.bddAbove_image (continuous_norm.continuousOn : ContinuousOn (fun x : Joint => ‖x‖) K)
  let D := max Dφ Dh
  let L := max 1 L0
  have hD : 1 ≤ D := hDφ.trans (le_max_left _ _)
  have hL : 1 ≤ L := le_max_left _ _
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let Cg : ℝ := (n.factorial : ℝ)*2^(2*B+n)*(D^2)^n/m^(2*B+n)
  have hCg : 0 < Cg := by dsimp [Cg]; positivity
  let Cp : ℝ := (n.factorial : ℝ)*D^n
  have hCp : 0 < Cp := by dsimp [Cp]; positivity
  refine ⟨L^k*2^n*2^n*Cp*Cg, by positivity, ?_⟩
  intro A hA g v R hR F hF
  have hp : ContDiff ℝ ∞ (fun y => logPhase (v/(2*Real.pi)) (φ y)) :=
    (JointLogSeparation.logPhase_temperate _).1.comp hφ
  have hg : ContDiff ℝ ∞ (fun y => g (R*h y)) :=
    (g.smooth ⊤).comp (contDiff_const.mul hh)
  have hFfun : (F : Joint → ℂ) =
      fun x => A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x) := funext hF
  have hFs : tsupport (F : Joint → ℂ) ⊆ K := by
    rw [hFfun]
    exact (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hA
  have hAn := amplitudeControl_nonneg n A
  have hgn := rayControl_nonneg B n g
  have hden : 0 < (1+R)^(2*B) := by positivity
  apply SchwartzMap.seminorm_le_bound ℝ k n F (by positivity)
  intro x
  by_cases hx : x ∈ K
  · have hxb : ‖x‖ ≤ L := (hL0 (mem_image_of_mem _ hx)).trans (le_max_right _ _)
    have hpbd (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
          Cp*(1+|v|)^n :=
      phase_derivative_bound hφ hD n j hj x
        (fun i hi => (hbφ i hi x hx).trans (le_max_left _ _)) v
    have hgbd (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
          Cg*rayControl B n g/(1+R)^(2*B) :=
      kernel_derivative_bound hh hD hm hm1 hR B n j hj x
        (fun i hi => (hbh i hi x hx).trans (le_max_right _ _)) (hml x hx) g
    have hap (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => A y * logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
          2^n*amplitudeControl n A*(Cp*(1+|v|)^n) := by
      calc
        _ ≤ 2^j*amplitudeControl n A*(Cp*(1+|v|)^n) :=
          mul_derivative_bound j (A.smooth ⊤) hp x hAn (by positivity)
            (fun i hi => amplitude_derivative_bound n i (hi.trans hj) A x)
            (fun i hi => hpbd i (hi.trans hj))
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hAn) (by positivity)
    have hb := mul_derivative_bound n ((A.smooth ⊤).mul hp) hg x
      (C := 2^n*amplitudeControl n A*(Cp*(1+|v|)^n))
      (D := Cg*rayControl B n g/(1+R)^(2*B)) (by positivity) (by positivity) hap hgbd
    rw [hFfun]
    calc
      _ ≤ L^k * (2^n*(2^n*amplitudeControl n A*(Cp*(1+|v|)^n))*
          (Cg*rayControl B n g/(1+R)^(2*B))) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxb _) hb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ n (F : Joint → ℂ) x = 0 := by
      apply Function.notMem_support.mp
      intro hx'
      exact hx (hFs ((support_iteratedFDeriv_subset n) hx'))
    rw [hz, norm_zero, mul_zero]
    positivity

lemma amplitudeControl_mono {n N : ℕ} (hn : n ≤ N) (A : 𝓢(Joint, ℂ)) :
    amplitudeControl n A ≤ amplitudeControl N A := by
  exact Seminorm.le_def.mp (Finset.sup_mono (by
    intro p hp
    exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp) ⟨le_rfl, hn⟩))) A

lemma rayControl_mono (B : ℕ) {n N : ℕ} (hn : n ≤ N) (g : 𝓢(ℝ, ℂ)) :
    rayControl B n g ≤ rayControl B N g := by
  exact Seminorm.le_def.mp (Finset.sup_mono (by
    intro p hp
    exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp) ⟨by omega, hn⟩))) g

theorem compact_profile_finite
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (g : 𝓢(ℝ, ℂ)) (v R : ℝ), 0 ≤ R →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x)) →
      sourceControl H F ≤
        C*amplitudeControl (heightOrder H) A*rayControl B (heightOrder H) g*
          (1+|v|)^(heightOrder H)/(1+R)^(2*B) := by
  have hc (p : ℕ × ℕ) := compact_profile_seminorm hK hφ hh hhpos B p.1 p.2
  choose C hC hbound using hc
  let D : ℝ := 1+∑ p ∈ H, C p
  have hD : 0 < D := by
    have hs : 0 ≤ ∑ p ∈ H, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    dsimp [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro A hA g v R hR F hF
  have hAn := amplitudeControl_nonneg (heightOrder H) A
  have hgn := rayControl_nonneg B (heightOrder H) g
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro p hp
  have hn : p.2 ≤ heightOrder H := Finset.le_sup hp
  have hCD : C p ≤ D := by
    have hs := Finset.single_le_sum (fun p _ => (hC p).le) hp
    dsimp [D]
    linarith
  exact (hbound p A hA g v R hR F hF).trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul
    · exact mul_le_mul
        (mul_le_mul hCD (amplitudeControl_mono hn A)
          (amplitudeControl_nonneg _ _) hD.le)
        (rayControl_mono B hn g) (rayControl_nonneg _ _ _) (by positivity)
    · exact pow_le_pow_right₀ (by linarith [abs_nonneg v]) hn
    · positivity
    · positivity)

lemma sqrt_decay_absorption (T : ℝ) (hT : 0 ≤ T) (B : ℕ) :
    (1+T)^B ≤ (1+Real.sqrt T)^(2*B) := by
  have hbase : 1+T ≤ (1+Real.sqrt T)^2 := by
    nlinarith [Real.sq_sqrt hT, Real.sqrt_nonneg T]
  calc
    _ ≤ ((1+Real.sqrt T)^2)^B := pow_le_pow_left₀ (by positivity) hbase B
    _ = _ := by rw [pow_mul]

theorem compact_fourier_profile_finite
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (U : 𝓢(ℝ, ℂ)) (v T : ℝ), 0 ≤ T →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) *
        paperFourierRayCLM U (Real.sqrt T*h x)) →
      sourceControl H F ≤ C*amplitudeControl (heightOrder H) A*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^(heightOrder H)/(1+T)^B := by
  obtain ⟨D, hD, hbound⟩ := compact_profile_finite hK hφ hh hhpos B H
  obtain ⟨S, E, hE, hEbound⟩ := schwartzCLM_finite_seminorm_control
    paperFourierRayCLM (Finset.Iic (2*B+heightOrder H,heightOrder H))
  refine ⟨S, D*E, by positivity, ?_⟩
  intro A hA U v T hT F hF
  have hAn := amplitudeControl_nonneg (heightOrder H) A
  have hUn : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := apply_nonneg _ _
  have hg := hEbound U
  change rayControl B (heightOrder H) (paperFourierRayCLM U) ≤
    E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U at hg
  calc
    _ ≤ D*amplitudeControl (heightOrder H) A*
        rayControl B (heightOrder H) (paperFourierRayCLM U)*
        (1+|v|)^(heightOrder H)/(1+Real.sqrt T)^(2*B) :=
      hbound A hA (paperFourierRayCLM U) v (Real.sqrt T) (Real.sqrt_nonneg _) F hF
    _ ≤ D*amplitudeControl (heightOrder H) A*
        (E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        (1+|v|)^(heightOrder H)/(1+Real.sqrt T)^(2*B) := by
      gcongr
    _ ≤ D*amplitudeControl (heightOrder H) A*
        (E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        (1+|v|)^(heightOrder H)/(1+T)^B :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (sqrt_decay_absorption T hT B)
    _ = _ := by ring

open ProbeGramJointConstruction

theorem jointProfile_homogeneous (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
        (U : 𝓢(ℝ, ℂ)) (v T : ℝ) (hT : 0 ≤ T),
      sourceControl H (jointProfile W U a b ha hab hs hW v T hT) ≤
        C*amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW)*
          S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*
          (1+|v|)^(heightOrder H)/(1+T)^B := by
  obtain ⟨S, C, hC, hb⟩ := compact_fourier_profile_finite
    (sourceCompact_isCompact b) (phase_smooth a b ha) (rootScale_smooth a b ha)
    (fun z _ => rootScale_pos a b ha z) B H
  refine ⟨S, C, hC, ?_⟩
  intro W hs hW U v T hT
  exact hb (amplitudeSchwartz W a b ha hab hs hW)
    (tsupport_amplitude_subset W a b ha hab hs) U v T hT
    (jointProfile W U a b ha hab hs hW v T hT)
    (jointProfile_factorization W U a b ha hab hs hW v T hT)

theorem jointProfile_uniform_degree (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (J : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W),
      ∃ C : ℝ, 0 < C ∧ ∀ (U : 𝓢(ℝ, ℂ)) (v T : ℝ) (hT : 0 ≤ T),
        sourceControl H (jointProfile W U a b ha hab hs hW v T hT) ≤
          C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B := by
  obtain ⟨S, C, hC, hb⟩ := jointProfile_homogeneous a b ha hab B H
  refine ⟨heightOrder H, S, ?_⟩
  intro W hs hW
  let A := amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW)
  have hA : 0 ≤ A := amplitudeControl_nonneg _ _
  refine ⟨C*(1+A), by positivity, ?_⟩
  intro U v T hT
  have hU : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := apply_nonneg _ _
  exact (hb W hs hW U v T hT).trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by dsimp [A]; linarith :
        amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW) ≤ 1+A) hC.le) hU)

end ProbeGramJointProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramSourceBlock
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma jointProfile_physicalPoint (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (v T : ℝ) (hT : 0≤T) (N : ℝ) (hN : 0<N) (m : O×O) :
    ProbeGramJointConstruction.jointProfile W U a b ha hab hs hW v T hT
      (ProbeGramLatticeDecay.physicalPoint N m)=
      shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N) := by
  rw [ProbeGramJointConstruction.jointProfile_apply]
  unfold ProbeGramJointConstruction.rawProfile ProbeGramJointConstruction.q1 ProbeGramJointConstruction.q2
  change lowGramProfile W v _ * star (lowGramProfile W v _) * _ = _
  have h₁ : ‖WithLp.fst (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖eisEmbedding m.1‖^2/N := physicalPoint_first_norm N hN m
  have h₂ : ‖WithLp.snd (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖eisEmbedding m.2‖^2/N := physicalPoint_second_norm N hN m
  rw [h₁,h₂]
  rfl

theorem literal_nonexceptional_source (A B : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*goodLambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,goodLambda∉P i)(c : ι→ℕ),
      (∀i,1≤ c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : goodLambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(U : SchwartzMap ℝ ℂ)(v T : ℝ),0≤T→∀(d : O)(N : ℝ),0<N→
      Summable (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H₀,K₀,hK₀,hblock⟩ := literal_nonexceptional_block A hA a₀ b₀ ha₀ hab
  obtain ⟨J,H,hprofile⟩ := ProbeGramJointProfile.jointProfile_uniform_degree a₀ b₀ ha₀ hab B H₀
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K₁,hK₁,hprofile⟩ := hprofile W hs hW
  refine ⟨K₀*K₁,mul_pos hK₀ hK₁,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he U v T hT d N hN
  let V := ProbeGramJointConstruction.jointProfile W U a₀ b₀ ha₀ hab hs hW v T hT
  have hv := ProbeGramJointConstruction.jointProfile_annularSupport W U a₀ b₀ ha₀ hab hs hW v T hT
  have hb := hblock S hS σ C k hC hk0 u a b r hr hk P hg c hc hfac p hp0 hgp hchar hfixed hcommon he V hv d N hN
  have hfun : (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
      V (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
    funext m
    rw [jointProfile_physicalPoint W U a₀ b₀ ha₀ hab hs hW v T hT N hN m]
  rw [hfun] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hm : 0≤ min (1:ℝ) (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
      Ideal.absNorm (Ideal.span {k})/N)^A) := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hprofile U v T hT) hK₀.le)
        (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {C})))) (sq_nonneg N)) hm
  convert (preTransparency := .instances) hh using 1 ; ring

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramCanonical
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma gramExponent_pos (C : SupportedIdeal) (P : GramPrime C) : 1≤gramExponent C P :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramClassification
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma exceptionalModulus_nonzero (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    exceptionalModulus S hS C≠0 := mul_ne_zero (jointFixedModulus_nonzero S hS) C.property.1

lemma nonexceptional_prime (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency)
    (hk : ¬ExceptionalFrequency S hS C k) :
    ∃p : Id,Prime p ∧ p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C) ∧
      ¬6∣(normalizedFactors (Ideal.span {k.val})).count p := by
  unfold ExceptionalFrequency at hk
  push Not at hk
  obtain ⟨p,hp,he⟩ := hk
  have hcount : (normalizedFactors (Ideal.span {k.val})).count p≠0 := by
    intro hz
    apply he
    simp [valuation,hz]
  have hprime := prime_of_normalized_factor p (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount))
  exact ⟨p,hprime,hp,fun hd=>he (Nat.mod_eq_zero_of_dvd hd)⟩

lemma outside_exceptional_not_dvd (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C)) :
    (¬p∣jointFixedModulus S hS) ∧ (¬p∣∏i : GramPrime C,gramPrime C i) := by
  have hnot : ¬p∣exceptionalModulus S hS C := by
    intro hd
    apply hout
    exact Multiset.mem_toFinset.mpr ((Ideal.mem_normalizedFactors_iff (exceptionalModulus_nonzero S hS C)).mpr
      ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩)
  refine ⟨fun hd=>hnot (dvd_mul_of_dvd_left hd _),?_⟩
  intro hd
  apply hnot
  apply dvd_mul_of_dvd_right
  apply dvd_trans hd
  calc
    _∣∏i : GramPrime C,gramPrime C i^gramExponent C i :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (gramExponent_pos C i)))
    _=C.val := (gramPrime_product C).symm

lemma outside_exceptional_good (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C)) :
    λ₀∉p ∧ ringChar (O⧸p)≠2 := by
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hle : exceptionalModulus S hS C≤Ideal.span {(72:O)} :=
    le_trans Ideal.mul_le_left Ideal.mul_le_right
  have hh := CenteredExceptionalProfile.outside_fixed_support _ (exceptionalModulus_nonzero S hS C) hle p hp hout
  exact ⟨hh.1,ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem p hh.2.1⟩

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramCanonicalBlock
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem canonical_nonexceptional_block (A B : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v T N : ℝ),0≤T→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*
            Ideal.absNorm (Ideal.span {k.val})/N)^A) := by
  obtain ⟨J,H,hsource⟩ := literal_nonexceptional_source A B hA a₀ b₀ ha₀ hab
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hsource⟩ := hsource W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v T N hT hN
  obtain ⟨p,hp,hout,he⟩ := nonexceptional_prime S hS C k hk
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := outside_exceptional_good S hS C p hp hout
  have hd := outside_exceptional_not_dvd S hS C p hp hout
  have hcspan := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).1
  have hf : Ideal.span {primaryGenerator C.val}=∏i : GramPrime C,gramPrime C i^gramExponent C i := hcspan.trans (gramPrime_product C)
  have hh := hsource S hS σ (primaryGenerator C.val) k.val
    (supported_primaryGenerator_ne_zero _ C.property) k.property
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).factor
    (gramPrime C) (gramPrime_good C) (gramExponent C) (gramExponent_pos C) hf
    p hp.ne_zero hg.1 hg.2 hd.1 hd.2 he U v T hT d N hN
  simpa only [canonicalLatticeBlock,canonicalJoint,hcspan] using hh.2

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramWeightedFrequency
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma min_product_amplification (L T : ℝ) (hL : 0≤L) (hT : 0≤T) (A : ℕ) :
    min 1 ((L*T)^A)≤(1+T)^A*min 1 (L^A) := by
  by_cases h : L^A≤1
  · rw [min_eq_right h]
    apply (min_le_right _ _).trans
    rw [mul_pow,mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT (by linarith) _) (pow_nonneg hL _)
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    exact (min_le_left _ _).trans (one_le_pow₀ (by linarith))

theorem canonical_nonexceptional_weighted_oai (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)*
          (1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_block A (A+2) hA a₀ b₀ ha₀ hab
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v H N hH hN
  let t : ℝ := (Ideal.absNorm (Ideal.span {k.val}):ℝ)/H
  let L : ℝ := (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N
  have ht : 0≤t := by dsimp [t];positivity
  have hL : 0≤L := by dsimp [L];positivity
  have htp : 0<1+t := by linarith
  have he : (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*Ideal.absNorm (Ideal.span {k.val})/N=L*t := by
    dsimp [L,t]
    field_simp
  have hb := hblock S hS σ C k hk d U v t N ht hN
  rw [he] at hb
  apply hb.trans
  calc
    _≤K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+t)^(A+2)*
        (Ideal.absNorm C.val:ℝ)*N^2*((1+t)^A*min 1 (L^A)) :=
      mul_le_mul_of_nonneg_left (min_product_amplification L t hL ht A) (by positivity)
    _=K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
        min 1 (L^A)*(1+t)^(-2:ℝ) := by
      rw [Real.rpow_neg htp.le,Real.rpow_two,pow_add]
      field_simp
    _=_ := rfl

end SevenEighths.ProbeGramCommon
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeGramCommon.canonical_nonexceptional_weighted_oai := @OAI.SevenEighths.ProbeGramCommon.canonical_nonexceptional_weighted_oai
