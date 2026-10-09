-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.HasSieveExponent.annular_selected_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T00:41:26.337992+00:00
-- url     : https://prove2.me/submissions/e28c93ca-2cab-474b-bec1-d18966f721bf

import Mathlib
import Definitions.Def_OAIHecke78B008
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_masked_poisson_complete
import Theorems.Thm_OAI_CanonicalQuadraticSieve_highKernelNorm_le_squarePart_sum
import Theorems.Thm_OAI_CanonicalQuadraticSieve_originalPairLow_squarefree_tsum
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poisson_nine_terms_box

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section

namespace ActualEisensteinCoordinates

theorem eval_congr_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    ∃ z : O, eval a b - eval c d = 4 * z := by
  have ha4 : (4 : ℤ) ∣ a-c := (ZMod.intCast_eq_intCast_iff_dvd_sub c a 4).mp ha.symm
  have hb4 : (4 : ℤ) ∣ b-d := (ZMod.intCast_eq_intCast_iff_dvd_sub d b 4).mp hb.symm
  obtain ⟨u, hu⟩ := ha4
  obtain ⟨v, hv⟩ := hb4
  refine ⟨(u : O) + (v : O) * omega, ?_⟩
  dsimp [eval]
  rw [show a = c + 4*u by omega, show b = d + 4*v by omega]
  push_cast
  ring

theorem congr_mod_four_of_residue_eq {x y : O}
    (h : residue x = residue y) : ∃ z : O, x-y = 4*z := by
  rw [←eval_coords x, ←eval_coords y]
  apply eval_congr_mod_four
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

end ActualEisensteinCoordinates

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase
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

namespace ActualEisensteinCubic

theorem finiteSquarefreeRow_sixth_power
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSquarefreeRow P hgood S (a ^ 6) =
      if ∃ i ∈ S, a ∈ P i then 0 else 1 := by
  classical
  simp only [finiteSquarefreeRow]
  by_cases hex : ∃ i ∈ S, a ∈ P i
  · obtain ⟨i, hi, hai⟩ := hex
    rw [if_pos ⟨i, hi, hai⟩]
    apply Finset.prod_eq_zero hi
    rw [canonicalSextic_sixth_power_mask]
    simp [hai]
  · rw [if_neg hex]
    apply Finset.prod_eq_one
    intro i hi
    rw [canonicalSextic_sixth_power_mask]
    simp [show a ∉ P i by intro hai; exact hex ⟨i, hi, hai⟩]

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

namespace ActualEisensteinCubic

private theorem mask_powerset {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, p i then 1 else 0 := by
  have hprod : (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∏ i ∈ S, (1 - if p i then (1 : ℂ) else 0) := by
    by_cases h : ∃ i ∈ S, p i
    · rw [if_pos h]
      obtain ⟨i, hi, hp⟩ := h
      symm
      apply Finset.prod_eq_zero hi
      simp [hp]
    · rw [if_neg h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      simp [show ¬p i from fun hp => h ⟨i, hi, hp⟩]
  rw [hprod, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Finset.prod_const_one, mul_one]
  congr 1
  by_cases h : ∀ i ∈ E, p i
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi, hp⟩ := h
    apply Finset.prod_eq_zero hi
    simp [hp]

theorem rowCoprimeMask_subsets
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (u : O) :
    rowCoprimeMask P S u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, u ∈ P i then 1 else 0 := by
  classical
  exact mask_powerset S (fun i => u ∈ P i)

theorem prime_product_moebius
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
      (-1 : ℂ) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one, Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
    have hcop : IsCoprime (P i) (∏ j ∈ S, P j) := by
      apply IsCoprime.prod_right
      intro j hj
      apply Ideal.isCoprime_of_isMaximal
      exact hinj.ne (by intro h; subst j; exact hi hj)
    rw [Finset.prod_insert hi, hcop.isRelPrime.moebius_mul,
      (hprime i).irreducible.moebius_eq, Int.cast_mul, Int.cast_neg,
      Int.cast_one, ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

theorem mem_prime_product_iff
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (u : O) :
    u ∈ (∏ i ∈ S, P i) ↔ ∀ i ∈ S, u ∈ P i := by
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp
  · intro i hi j hj hij
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hij)

end ActualEisensteinCubic

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
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem integral_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) :
    (∫ x : ℂ, f (A x)) = inverseJacobian A • ∫ x : ℂ, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure ℂ))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure ℂ) =
      ENNReal.ofReal (inverseJacobian A) • volume := by
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : ℂ, f y ∂Measure.map A volume) = (∫ x : ℂ, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (show 0 ≤ inverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem inner_linear_dual (A : ℂ ≃L[ℝ] ℂ) (x y : ℂ) :
    inner ℝ (A x) (dualMap A y) = inner ℝ x y := by
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem fourier_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) (w : ℂ) :
    𝓕 (f ∘ A) w = inverseJacobian A • 𝓕 f (dualMap A w) := by
  let H : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z (dualMap A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : ℂ, H (A x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [H, inner_linear_dual, Function.comp_apply]
        rfl
    _ = inverseJacobian A • ∫ z : ℂ, H z := integral_comp_linearEquiv A H
    _ = inverseJacobian A • 𝓕 f (dualMap A w) := rfl

theorem fourier_translate (f : ℂ → ℂ) (b w : ℂ) :
    𝓕 (fun z => f (z + b)) w =
      Real.fourierChar (inner ℝ b w) • 𝓕 f w := by
  exact congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℂ) (innerₗ ℂ) f b) w

theorem fourier_affinePullback (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b w : ℂ) :
    (𝓕 (affinePullback f A b)) w =
      inverseJacobian A •
        (Real.fourierChar (inner ℝ b (dualMap A w)) • (𝓕 f) (dualMap A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => f (z + b)) ∘ A) w = _
  rw [fourier_comp_linearEquiv, fourier_translate]
  rw [congrFun (SchwartzMap.fourier_coe f) (dualMap A w)]

theorem affine_lattice_poisson (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    (∑' p : ℤ × ℤ, f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + b)) =
      inverseJacobian A • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ b (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
          (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  have h := integer_pair_poisson (affinePullback f A b)
  simp only [affinePullback_apply, fourier_affinePullback] at h
  rw [tsum_const_smul''] at h
  exact h

end

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]

theorem actual_eisenstein_coset_poisson (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    (∑' z : O, f (eisEmbedding (b + c * z))) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ (eisEmbedding b)
          (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
        (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have h := affine_lattice_poisson f A (eisEmbedding b)
  rw [eisenstein_inverseJacobian] at h
  calc
    (∑' z : O, f (eisEmbedding (b + c * z))) =
        ∑' p : ℤ × ℤ, f (eisEmbedding (b + c * latticeCoordEquiv.symm p)) :=
      (latticeCoordEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ,
        f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + eisEmbedding b) := by
      apply tsum_congr
      intro p
      congr 1
      rw [map_add, map_mul]
      change eisEmbedding b + eisEmbedding c *
          eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
      rw [← eisensteinLatticeMap_point]
      exact add_comm _ _
    _ = _ := h

theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (eisEmbedding (b + c * z))‖) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (eisEmbedding b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (eisEmbedding (b + c * latticeCoordEquiv.symm p))‖) := by
    convert (preTransparency := .instances) hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change eisEmbedding b + eisEmbedding c *
        eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (latticeCoordEquiv.symm.summable_iff).mp hpair

theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (eisEmbedding z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero

theorem actual_eisenstein_periodic_summable (f : 𝓢(ℂ, ℂ))
    {R : Type*} [Fintype R] (q : O → R) (P : R → ℂ) :
    Summable (fun z : O => P (q z) * f (eisEmbedding z)) := by
  classical
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun a _ => norm_nonneg (P a)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((actual_eisenstein_summable_norm f).mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP (q z)) (norm_nonneg _)

theorem actual_eisenstein_periodic_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      ∑ r : O ⧸ Ideal.span {c}, P r *
        ((2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
          Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => f (eisEmbedding z))
    (actual_eisenstein_periodic_summable f _ P)]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (GaussianFiberEquiv.fiber_tsum c hc r
    (GaussianShiftedPartition.representative c r)
    (GaussianShiftedPartition.representative_spec c r)
    (fun z => f (eisEmbedding z))).trans
      (actual_eisenstein_coset_poisson f _ c hc)

theorem inverseJacobian_pos (A : ℂ ≃L[ℝ] ℂ) : 0 < inverseJacobian A :=
  abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)

theorem dual_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖) := by
  have hJ := inverseJacobian_pos A
  have hp := plane_lattice_summable_norm (𝓕 (affinePullback f A 0))
  have hn (p : ℤ × ℤ) :
      ‖(𝓕 (affinePullback f A 0)) (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖ =
      inverseJacobian A * ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖ := by
    rw [fourier_affinePullback]
    simp [ abs_of_pos hJ]
  simp_rw [hn] at hp
  have hi := hp.mul_left (inverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

theorem finite_phase_sum {R : Type*} [Fintype R]
    (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : R → ℂ) (P : R → ℂ) :
    (∑ r : R, P r * (inverseJacobian A • ∑' p : ℤ × ℤ,
      Real.fourierChar (inner ℝ (b r) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) =
    inverseJacobian A • ∑' p : ℤ × ℤ,
      (∑ r : R, P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) : ℂ)) *
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  classical
  have hs (r : R) : Summable (fun p : ℤ × ℤ =>
      P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using dual_lattice_summable_norm f A
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [Circle.smul_def, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem actual_eisenstein_periodic_fourier (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)) *
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [actual_eisenstein_periodic_poisson f c hc P]
  have h := finite_phase_sum f
    (eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc))
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r)) P
  rw [eisenstein_inverseJacobian] at h
  exact h

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

theorem actual_eisenstein_poisson_explicit (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (explicitDualFrequency (eisEmbedding c) p)) : ℂ)) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
  simpa only [eisensteinDualFrequency_explicit, explicitDualFrequency] using
    actual_eisenstein_periodic_fourier f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem gauss_transform_finite_crt_scalar {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : T) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
      (∏ i, χ i (e h i))⁻¹ *
        ∑ x : T, (∏ i, χ i (e x i)) * ψ x := by
  classical
  have hbase := gauss_transform_finite_crt R e χ ψ hχ (1 : T)
  simp only [one_mul, map_one, Pi.one_apply, one_ne_zero, ↓reduceIte,
    inv_one, one_mul] at hbase
  rw [gauss_transform_finite_crt R e χ ψ hχ h, hbase]
  have hlocal (i : ι) :
      (if e h i = 0 then 0 else
        (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i)) =
      (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i) := by
    split_ifs with hi
    · simp [hi]
    · rfl
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end IdealGaussCRT

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

namespace ActualEisensteinCubic

theorem canonical_finite_prime_gauss_transform_scalar
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      (finiteSexticQuotientRow P hc hgood j h)⁻¹ *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  exact IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i)
    (IdealGaussCRT.quotientProdEquivPi P hc)
    (fun i => canonicalSextic (P i) (hgood i) ^ j i) ψ
    (fun i => canonicalSextic_pow_ne_one (P i) (hgood i) (hchar i) (hj0 i) (hj6 i)) h

theorem finiteSexticQuotientRow_inv_eq_star
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (h : O ⧸ ∏ i, P i) :
    (finiteSexticQuotientRow P hc hgood j h)⁻¹ =
      star (finiteSexticQuotientRow P hc hgood j h) := by
  classical
  simp only [finiteSexticQuotientRow, star_prod]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']

theorem canonical_finite_prime_gauss_transform_conj
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      star (finiteSexticQuotientRow P hc hgood j h) *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  rw [canonical_finite_prime_gauss_transform_scalar P hc hgood hchar j hj0 hj6 ψ,
    finiteSexticQuotientRow_inv_eq_star]

end ActualEisensteinCubic

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

theorem explicitDualFrequency_phase (r c : ℂ) (p : ℤ × ℤ) :
    (Real.fourierChar (inner ℝ r (explicitDualFrequency c p)) : ℂ) =
      paperE (r * eisEmbedding (dualFrequencyEquiv p) / c) := by
  rw [explicitDualFrequency_eq_paperFrequency, fourierChar_paperFrequency]
  congr 1
  ring

theorem actual_eisenstein_paper_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
            eisEmbedding h / eisEmbedding c)) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
      eisEmbedding h / eisEmbedding c)
  have ht : (∑' h : O, A h * paperFourier f (eisEmbedding h / eisEmbedding c)) =
      (2 / Real.sqrt 3 : ℝ) • ∑' p : ℤ × ℤ,
        A (dualFrequencyEquiv p) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
    calc
      _ = ∑' p : ℤ × ℤ, A (dualFrequencyEquiv p) *
          paperFourier f (eisEmbedding (dualFrequencyEquiv p) / eisEmbedding c) :=
        (dualFrequencyEquiv.tsum_eq _).symm
      _ = ∑' p : ℤ × ℤ, (2 / Real.sqrt 3 : ℝ) •
          (A (dualFrequencyEquiv p) *
            (𝓕 f) (explicitDualFrequency (eisEmbedding c) p)) := by
        apply tsum_congr
        intro p
        rw [paperFourier_eq_standard, ← explicitDualFrequency_eq_paperFrequency]
        change A (dualFrequencyEquiv p) *
          ((2 / Real.sqrt 3 : ℝ) • (𝓕 f) (explicitDualFrequency (eisEmbedding c) p)) = _
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
    rfl
  have hp := actual_eisenstein_poisson_explicit f c hc P
  simp_rw [explicitDualFrequency_phase] at hp
  change _ = (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) •
    ∑' h : O, A h * paperFourier f (eisEmbedding h / eisEmbedding c)
  rw [ht, smul_smul]
  convert (preTransparency := .instances) hp using 1
  congr 1
  ring

theorem actual_eisenstein_paper_poisson_trace (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  simpa only [eisTraceModChar_frequency] using actual_eisenstein_paper_poisson f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem paperFourier_comp_mul (f : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0) (u : ℂ) :
    paperFourier (fun z => f (a * z)) u =
      (1 / ‖a‖ ^ 2 : ℝ) • paperFourier f (u / a) := by
  have hd : dualMap (complexMulEquiv a ha) (paperFrequency u) =
      paperFrequency (u / a) := by
    rw [dual_mul_apply]
    unfold paperFrequency
    rw [map_div₀]
    ring
  have hj : inverseJacobian (complexMulEquiv a ha) = 1 / ‖a‖ ^ 2 := by
    rw [inverseJacobian, complexMulEquiv_det, abs_inv,
      abs_of_nonneg (Complex.normSq_nonneg a), Complex.sq_norm]
    ring
  rw [paperFourier_eq_standard, paperFourier_eq_standard]
  have hF := fourier_comp_linearEquiv (complexMulEquiv a ha) f (paperFrequency u)
  simp only [Function.comp_def, complexMulEquiv_apply] at hF
  rw [hF, hd, hj, smul_smul, smul_smul]
  congr 1
  ring

theorem paperFourier_radial (W : ℝ → ℂ) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2)) u =
      paperRadialFourier W (‖u‖ ^ 2) := by
  unfold paperRadialFourier
  rw [Real.sqrt_sq (norm_nonneg u)]
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnC : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let a : ℂ := u / (‖u‖ : ℂ)
  have ha : a ≠ 0 := div_ne_zero hu hnC
  have hna : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, hn]
  have hq : u / a = (‖u‖ : ℂ) := by
    dsimp [a]
    field_simp
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) = fun z : ℂ => W (‖z‖ ^ 2) := by
    funext z
    rw [norm_mul, hna, one_mul]
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, hq] at hF
  simpa using hF

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

theorem paperFourier_radial_scaled (W : ℝ → ℂ) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2 / K)) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  let a : ℂ := (Real.sqrt K : ℂ)⁻¹
  have ha : a ≠ 0 := inverseSqrt_ne_zero K hK
  have hna : ‖a‖ ^ 2 = 1 / K := inverseSqrt_norm_sq K hK
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) =
      fun z : ℂ => W (‖z‖ ^ 2 / K) := by
    funext z
    rw [norm_mul, mul_pow, hna]
    congr 1
    ring
  have hnorm : ‖u / a‖ ^ 2 = K * ‖u‖ ^ 2 := by
    rw [norm_div, div_pow, hna]
    field_simp
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, one_div_one_div, paperFourier_radial, hnorm] at hF
  exact hF

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

theorem paperFourier_scaledRadialTest (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (scaledRadialTest W K hK) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  change paperFourier (fun z => scaledRadialTest W K hK z) u = _
  simp only [scaledRadialTest_apply]
  exact paperFourier_radial_scaled W K hK u

theorem actual_radial_paper_poisson_trace (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      (K / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)
  have ht : (∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (eisEmbedding h / eisEmbedding c)) =
      K • ∑' h : O, A h *
        paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
    calc
      _ = ∑' h : O, K • (A h *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) := by
        apply tsum_congr
        intro h
        rw [paperFourier_scaledRadialTest, norm_div, div_pow]
        have hr : K * (‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) =
            K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 := by ring
        rw [hr]
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
  have hp := actual_eisenstein_paper_poisson_trace (scaledRadialTest W K hK) c hc P
  change (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
    scaledRadialTest W K hK (eisEmbedding z)) =
    (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (eisEmbedding h / eisEmbedding c) at hp
  rw [ht, smul_smul] at hp
  simpa only [scaledRadialTest_apply, one_div_mul_eq_div] using hp

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem canonical_principal_gauss_transform {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i)
    [Fintype (O ⧸ Ideal.span {c})]
    (ψ : AddChar (O ⧸ Ideal.span {c}) ℂ) (h : O ⧸ Ideal.span {c}) :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ (h * r)) =
      star (principalSexticRow P hcop hgood j c hc h) *
        ∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ r := by
  let e := Ideal.quotEquivOfEq hc
  let row := finiteSexticQuotientRow P hcop hgood j
  let φ : AddChar (O ⧸ ∏ i, P i) ℂ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hleft :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ (e h * x) := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ (e h * x))]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ (h * r) = row (e r) * ψ (e.symm (e h * e r))
    rw [← map_mul, e.symm_apply_apply]
  have hbase :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ x := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ x)]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ r = row (e r) * ψ (e.symm (e r))
    rw [e.symm_apply_apply]
  change (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
    star (row (e h)) * ∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r
  rw [hleft, hbase]
  exact canonical_finite_prime_gauss_transform_conj P hcop hgood hchar j hj0 hj6 φ (e h)

theorem canonical_radial_poisson {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    let hc0 := finitePrimeModulus_ne_zero P
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r) := by
    rw [canonical_principal_gauss_transform P hcop hgood hchar j hj0 hj6 c
      (span_finitePrimeModulus P) ψ, principalSexticRow_mk]
  have hp := actual_radial_paper_poisson_trace W scale hscale c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) *
    W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  simpa only [row, principalSexticRow_mk] using hp

theorem canonical_radial_poisson_normalized {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow P hgood j h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  let G := canonicalGaussSum P hcop hgood j
  let F : O → ℂ := fun h => star (finiteSexticRow P hgood j h) *
    paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)
  have hp := canonical_radial_poisson P hcop hgood hchar j hj0 hj6 W scale hscale
  change (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
    (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
      (star (finiteSexticRow P hgood j h) * G) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  have hsum : (∑' h : O, (star (finiteSexticRow P hgood j h) * G) *
      paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, F h := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    dsimp [F]
    ring
  rw [hsum] at hp
  rw [hp]
  change ((scale / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * ∑' h : O, F h) =
    ((scale : ℂ) * (G / (‖eisEmbedding c‖ : ℂ)) / (‖eisEmbedding c‖ : ℂ)) *
      ∑' h : O, F h
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  push_cast
  field_simp

theorem finiteSexticRow_eq_zero_iff {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    finiteSexticRow P hgood j a = 0 ↔ ∃ i, a ∈ P i := by
  classical
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  simp only [finiteSexticRow, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    MulChar.apply_eq_zero_iff, isUnit_iff_ne_zero, not_not, Ideal.Quotient.eq_zero_iff_mem]

theorem finiteSexticRow_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    finiteSexticRow P hgood j 0 = 0 := by
  rw [finiteSexticRow_eq_zero_iff]
  exact ⟨Classical.arbitrary ι, Ideal.zero_mem _⟩

theorem finiteSexticRow_radial_summable {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun z : O => finiteSexticRow P hgood j z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) := by
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W scale hscale)
    (Ideal.Quotient.mk (Ideal.span {c}))
    (principalSexticRow P hcop hgood j c (span_finitePrimeModulus P))
  simpa only [principalSexticRow_mk, scaledRadialTest_apply] using hs

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.RadialFourier
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

namespace EisensteinSchwartzPoisson

open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap

theorem polynomial_tail_majorant (A : ℕ) (K T q B f : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (htail : T ≤ K * q) (hbound : (1 + K * q) ^ (A + 2) * f ≤ B) :
    f ≤ (B / ((min 1 K) ^ 2 * (1 + T) ^ A)) * ((1 + q) ^ 2)⁻¹ := by
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hm1 : min 1 K ≤ 1 := min_le_left _ _
  have hmK : min 1 K ≤ K := min_le_right _ _
  have hbase : min 1 K * (1 + q) ≤ 1 + K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hmK hq]
  have htwo : (min 1 K) ^ 2 * (1 + q) ^ 2 ≤ (1 + K * q) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hpow : (1 + T) ^ A ≤ (1 + K * q) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hden : ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2 ≤
      (1 + K * q) ^ (A + 2) := by
    have hh := mul_le_mul hpow htwo (by positivity) (by positivity)
    rw [pow_add]
    nlinarith
  have hprod : f * (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) ≤ B := by
    calc
      _ = (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) * f := mul_comm _ _
      _ ≤ (1 + K * q) ^ (A + 2) * f := mul_le_mul_of_nonneg_right hden hf
      _ ≤ B := hbound
  have hraw := (le_div_iff₀ (show 0 < ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2
      by positivity)).mpr hprod
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem paperRadialFourier_lattice_summable_norm (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
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

namespace ConcretePrimeRowBridge

theorem tsum_ideal_eq_tsum_generator (J : Ideal O) (hJ : J ≠ ⊥)
    (f : O → ℂ) :
    (∑' u : O, if u ∈ J then f u else 0) =
      ∑' z : O, f (idealGenerator J * z) := by
  let d := idealGenerator J
  have hd : d ≠ 0 := idealGenerator_ne_zero J hJ
  let F : O → ℂ := fun u => if u ∈ J then f u else 0
  have hrange : Function.support F ⊆ Set.range (fun z : O => d * z) := by
    intro u hu
    have huJ : u ∈ J := by
      by_contra hn
      exact hu (by simp [F, hn])
    rw [← span_idealGenerator J, Ideal.mem_span_singleton] at huJ
    obtain ⟨z, hz⟩ := huJ
    exact ⟨z, hz.symm⟩
  have ht := (mul_right_injective₀ hd).tsum_eq hrange
  calc
    (∑' u : O, if u ∈ J then f u else 0) = ∑' z : O, F (d * z) := ht.symm
    _ = ∑' z : O, f (d * z) := by
      apply tsum_congr
      intro z
      have hz : d * z ∈ J := by
        rw [← span_idealGenerator J, Ideal.mem_span_singleton]
        exact ⟨z, rfl⟩
      simp only [F, if_pos hz]

end ConcretePrimeRowBridge

namespace ActualEisensteinCubic

theorem tsum_rowCoprimeMask_subsets
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι)
    (f : O → ℂ) (hf : Summable f) :
    (∑' u : O, rowCoprimeMask P S u * f u) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        ∑' u : O, if ∀ i ∈ E, u ∈ P i then f u else 0 := by
  have hterm (u : O) : rowCoprimeMask P S u * f u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        (if ∀ i ∈ E, u ∈ P i then f u else 0) := by
    rw [rowCoprimeMask_subsets, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro E hE
    by_cases h : ∀ i ∈ E, u ∈ P i <;> simp [h]
  have hsum (E : Finset ι) :
      Summable (fun u : O => (-1 : ℂ) ^ E.card *
        (if ∀ i ∈ E, u ∈ P i then f u else 0)) := by
    have hi := hf.indicator {u : O | ∀ i ∈ E, u ∈ P i}
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hi.mul_left ((-1 : ℂ) ^ E.card)
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun E _ => hsum E)]
  apply Finset.sum_congr rfl
  intro E hE
  exact tsum_mul_left

theorem primeSubsetGenerator_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    primeSubsetGenerator P E ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  change (∏ i ∈ E, P i) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))

theorem tsum_rowCoprimeMask_dilations
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (f : O → ℂ) (hf : Summable f) :
    (∑' u : O, rowCoprimeMask P S u * f u) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          ∑' z : O, f (primeSubsetGenerator P E * z) := by
  rw [tsum_rowCoprimeMask_subsets P S f hf]
  have hprime (i : ι) : Prime (P i) :=
    Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  apply Finset.sum_congr rfl
  intro E hE
  rw [prime_product_moebius P hprime hinj E]
  congr 1
  have hJ : (∏ i ∈ E, P i) ≠ ⊥ := by
    change (∏ i ∈ E, P i) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))
  calc
    _ = ∑' u : O, if u ∈ (∏ i ∈ E, P i) then f u else 0 := by
      apply tsum_congr
      intro u
      rw [mem_prime_product_iff P hinj E u]
      by_cases h : ∀ i ∈ E, u ∈ P i <;> simp [h]
    _ = _ := ConcretePrimeRowBridge.tsum_ideal_eq_tsum_generator _ hJ f

open ConcreteTraceCRT

theorem tsum_masked_radial_dilations
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P) (S : Finset ι)
    (r : O → ℂ) (hr : ∀ a b, r (a * b) = r a * r b)
    (W : ℝ → ℂ) (scale : ℝ)
    (hsum : Summable (fun u : O => r u * W (‖eisEmbedding u‖ ^ 2 / scale))) :
    (∑' u : O, rowCoprimeMask P S u * r u * W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          r (primeSubsetGenerator P E) *
          ∑' z : O, r z *
            W (‖eisEmbedding z‖ ^ 2 / (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)) := by
  calc
    _ = ∑' u : O, rowCoprimeMask P S u *
        (r u * W (‖eisEmbedding u‖ ^ 2 / scale)) := by
      apply tsum_congr
      intro u
      ring
    _ = _ := by
      rw [tsum_rowCoprimeMask_dilations P hinj S _ hsum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [mul_assoc]
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      rw [hr, map_mul, norm_mul, mul_pow, div_div_eq_mul_div]
      ring_nf

open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem primeSubset_reducedScale_pos {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset α)
    {scale : ℝ} (hscale : 0 < scale) :
    0 < scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 := by
  exact div_pos hscale (sq_pos_of_pos (norm_pos_iff.mpr
    (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E))))

theorem canonical_masked_radial_dilations
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset α)
    (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hgood : ∀ i, lambda ∉ Q i) (j : ι → ℕ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          finiteSexticRow Q hgood j (primeSubsetGenerator P E) *
          ∑' z : O, finiteSexticRow Q hgood j z *
            W (‖eisEmbedding z‖ ^ 2 /
              (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)) := by
  exact tsum_masked_radial_dilations P hinj S (finiteSexticRow Q hgood j)
    (finiteSexticRow_mul Q hgood j) W scale
    (finiteSexticRow_radial_summable Q hcop hgood j W scale hscale)

theorem canonical_masked_radial_poisson
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset α)
    (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hgood : ∀ i, lambda ∉ Q i)
    (hchar : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus Q
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        let d := primeSubsetGenerator P E
        let reducedScale := scale / ‖eisEmbedding d‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          finiteSexticRow Q hgood j d *
          ((reducedScale : ℂ) * canonicalNormalizedGauss Q hcop hgood j /
            (‖eisEmbedding c‖ : ℂ)) *
          ∑' h : O, star (finiteSexticRow Q hgood j h) *
            paperRadialFourier W
              (reducedScale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  dsimp only
  rw [canonical_masked_radial_dilations P hinj S Q hcop hgood j W scale hscale]
  apply Finset.sum_congr rfl
  intro E hE
  rw [canonical_radial_poisson_normalized Q hcop hgood hchar j hj0 hj6 W
    (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)
    (primeSubset_reducedScale_pos P E hscale)]
  ring

theorem canonical_masked_radial_poisson_collected
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset α)
    (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hgood : ∀ i, lambda ∉ Q i)
    (hchar : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus Q
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss Q hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator P E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
            finiteSexticRow Q hgood j d / (‖eisEmbedding d‖ ^ 2 : ℝ)) *
            ∑' h : O, star (finiteSexticRow Q hgood j h) *
              paperRadialFourier W
                (scale * ‖eisEmbedding h‖ ^ 2 /
                  (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2)) := by
  dsimp only
  rw [canonical_masked_radial_poisson P hinj S Q hcop hgood hchar j hj0 hj6 W scale hscale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  have harg (h : O) :
      scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 * ‖eisEmbedding h‖ ^ 2 /
          ‖eisEmbedding (finitePrimeModulus Q)‖ ^ 2 =
      scale * ‖eisEmbedding h‖ ^ 2 /
        (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 *
          ‖eisEmbedding (finitePrimeModulus Q)‖ ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [harg]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CubicTrace
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

namespace GaussGeneratorTransport

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem canonicalNormalizedGauss_eq_principal {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j =
      principalNormalizedGauss P hcop hgood j (finitePrimeModulus P)
        (span_finitePrimeModulus P) (finitePrimeModulus_ne_zero P) := rfl

theorem principalNormalizedGauss_eq_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    principalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j (∏ i, p i)
      (span_finset_prod Finset.univ p) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) =
      canonicalProductGauss p hp hcop hgood j := rfl

theorem modulusUnit_spec {ι : Type*} [Fintype ι] (p : ι → O) :
    finitePrimeModulus (fun i => Ideal.span {p i}) = (modulusUnit p : O) * ∏ i, p i :=
  Classical.choose_spec (exists_modulus_unit p)

theorem canonicalNormalizedGauss_eq_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j =
      finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
        canonicalProductGauss p hp hcop hgood j := by
  rw [canonicalNormalizedGauss_eq_principal,
    principalNormalizedGauss_unit_change (fun i => Ideal.span {p i}) hcop hgood j
      (finitePrimeModulus (fun i => Ideal.span {p i})) (∏ i, p i)
      (span_finitePrimeModulus _) (span_finset_prod Finset.univ p)
      (finitePrimeModulus_ne_zero _) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
      (modulusUnit p) (modulusUnit_spec p), principalNormalizedGauss_eq_product]

theorem canonicalNormalizedGauss_frequency_transport {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (h : O) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j ((modulusUnit p : O) * h)) =
      canonicalProductGauss p hp hcop hgood j *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hgood j,
    finiteSexticRow_mul, star_mul]
  calc
    _ = (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O))) *
        (canonicalProductGauss p hp hcop hgood j *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h)) := by ring
    _ = _ := by rw [finiteSexticRow_unit_mul_star, one_mul]

theorem gauss_weighted_radial_sum_transport {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (F : ℝ → ℂ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      (∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
        F (‖eisEmbedding h‖ ^ 2)) =
      canonicalProductGauss p hp hcop hgood j *
        (∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F (‖eisEmbedding h‖ ^ 2)) := by
  rw [← tsum_mul_left, ← tsum_mul_left]
  calc
    _ = ∑' h : O, canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
        (star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j
          ((modulusUnit p : O) * h)) * F (‖eisEmbedding ((modulusUnit p : O) * h)‖ ^ 2)) :=
      ((modulusUnit p).mulLeft.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro h
      rw [norm_eisEmbedding_unit_mul, ← mul_assoc,
        canonicalNormalizedGauss_frequency_transport p hp hcop hgood j, mul_assoc]

theorem gauss_weighted_finite_radial_sum_transport {ι κ : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (D : Finset κ) (a : κ → ℂ) (F : κ → ℝ → ℂ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      (∑ k ∈ D, a k * ∑' h : O,
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F k (‖eisEmbedding h‖ ^ 2)) =
      canonicalProductGauss p hp hcop hgood j *
        (∑ k ∈ D, a k * ∑' h : O,
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
            F k (‖eisEmbedding h‖ ^ 2)) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = a k * (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F k (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [gauss_weighted_radial_sum_transport p hp hcop hgood j]; ring

theorem finitePrimeModulus_norm_eq_product {ι : Type*} [Fintype ι] (p : ι → O) :
    ‖eisEmbedding (finitePrimeModulus (fun i => Ideal.span {p i}))‖ =
      ‖eisEmbedding (∏ i, p i)‖ := by
  rw [modulusUnit_spec p, norm_eisEmbedding_unit_mul]

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

end GaussGeneratorTransport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
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

open scoped BigOperators Classical

namespace CompletedGauss

section

open ActualEisensteinCubic

theorem primaryGenerator_norm_sq (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator I)‖ ^ 2 = (Ideal.absNorm I : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, (primaryGenerator_spec I h).1]

open ActualEisensteinCubic

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
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

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem quadraticRow_disjoint_union {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset α) (hd : Disjoint S T) (z : O) :
    quadraticRow P hg (S ∪ T) z = quadraticRow P hg S z * quadraticRow P hg T z := by
  simp only [quadraticRow, finiteSquarefreeRow, Finset.prod_union hd, mul_pow]

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CubeLabels
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

section
open scoped BigOperators Classical

open scoped BigOperators Classical
open UniqueFactorizationMonoid
namespace QuadraticSquarefreeKernel

theorem norm_decomposition (I : Ideal O) :
    Ideal.absNorm (squarePart I) ^ 2 * Ideal.absNorm (squarefreePart I) = Ideal.absNorm I := by
  simpa only [map_mul, map_pow] using congrArg Ideal.absNorm (squarePart_sq_mul_squarefreePart I)

open ActualEisensteinCubic QuadraticInitialBound CompletedGauss

theorem quadraticRow_square {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    quadraticRow P hg S (a ^ 2) = rowCoprimeMask P S a := by
  have heq : quadraticRow P hg S (a ^ 2) = finiteSquarefreeRow P hg S (a ^ 6) := by
    simp only [quadraticRow, finiteSquarefreeRow, map_pow, ← Finset.prod_pow, ← pow_mul]
  rw [heq, finiteSquarefreeRow_sixth_power]
  rfl

end QuadraticSquarefreeKernel
end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.InverseContour
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

namespace EisensteinSchwartzPoisson
open MeasureTheory Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem paperFrequency_imaginary (x : ℝ) :
    paperFrequency ((x : ℂ) * Complex.I) = (((2 / Real.sqrt 3) * x : ℝ) : ℂ) := by
  simp [paperFrequency]
  ring_nf
  simp

theorem paperRadialFourier_square (W : ℝ → ℂ) (x : ℝ) :
    paperRadialFourier W (x ^ 2) =
      (2 / Real.sqrt 3 : ℝ) • 𝓕 (fun z : ℂ => W (‖z‖ ^ 2))
        ((((2 / Real.sqrt 3) * x : ℝ) : ℂ)) := by
  have h := paperFourier_radial W ((x : ℂ) * Complex.I)
  have hn : ‖(x : ℂ) * Complex.I‖ ^ 2 = x ^ 2 := by
    simp [ Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hn, paperFourier_eq_standard, paperFrequency_imaginary] at h
  exact h.symm

end EisensteinSchwartzPoisson

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CrossFactorization
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

open scoped BigOperators Classical

namespace QuadraticGaussRay
open EisensteinEPrimaryPhase ActualEisensteinCoordinates ActualEisensteinCubic

theorem quadraticRayValue_square (r : Coord) (hr : odd r) :
    quadraticRayValue (mul r r) = 1 := by
  have hi : (Complex.I : ℂ)⁻¹ = -Complex.I := by
    apply inv_eq_of_mul_eq_one_right
    norm_num
  have h : mul r r = (1, 0) ∨ mul r r = (3, 3) ∨ mul r r = (0, 1) := by
    decide +revert
  rcases h with h | h | h
  · rw [h]
    change breveGaussianFourTerms 1 0 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 3 3 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 0 1 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
    ring

theorem quadraticRayValue_same_residue_product (a b : ActualEisensteinCubic.O)
    (ha : odd (residue a)) (hab : residue a = residue b) :
    quadraticRayValue (residue (a * b)) = 1 := by
  rw [residue_mul, ← hab]
  exact quadraticRayValue_square _ ha

end QuadraticGaussRay

namespace CoprimeSieveOperator
open FiniteSieveOperator CoprimeMobiusExtension

theorem square_norm_sum {n : Type*} [Fintype n] (z : n → ℂ) :
    (↑(‖∑ j, z j‖ ^ 2) : ℂ) = ∑ j, ∑ k, star (z j) * z k := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, starRingEnd_apply]
  rw [Finset.sum_mul_sum]

theorem disjoint_gram_expansion {ι n : Type*} [DecidableEq ι] [Fintype n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B) (z : n → ℂ) :
    (∑ j, ∑ k, if Disjoint (support j) (support k) then star (z j) * z k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (↑(‖∑ j, if D ⊆ support j then z j else 0‖ ^ 2) : ℂ) := by
  have hp (j k : n) :
      (if Disjoint (support j) (support k) then star (z j) * z k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) := by
    calc
      _ = (if Disjoint (support j) (support k) then (1 : ℂ) else 0) * (star (z j) * z k) := by
        split_ifs <;> simp
      _ = _ := by
        rw [disjoint_indicator_expansion B _ _ (hs j) (hs k), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D _
        split_ifs <;> simp
  simp_rw [hp]
  calc
    _ = ∑ j, ∑ D ∈ B.powerset, ∑ k,
        (-1 : ℂ) ^ D.card *
          (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ D ∈ B.powerset, ∑ j, ∑ k,
        (-1 : ℂ) ^ D.card *
          (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      simp_rw [← Finset.mul_sum]
      congr 1
      rw [square_norm_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hj : D ⊆ support j <;> by_cases hk : D ⊆ support k <;> simp [hj, hk]

theorem weighted_energy_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (↑(‖∑ j, A i j * a j‖ ^ 2) : ℂ)‖ ≤
      W * ‖operator A‖ ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  calc
    _ ≤ ∑ i, ‖w i * (↑(‖∑ j, A i j * a j‖ ^ 2) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, W * ‖∑ j, A i j * a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _)
    _ = W * ∑ i, ‖∑ j, A i j * a j‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (energy_bound A a) hW

theorem coprime_gram_operator_bound {ι m n : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B)
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (support j).card * ‖a j‖ ^ 2 := by
  have heq : (∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ i, w i * (↑(‖∑ j, A i j * (if D ⊆ support j then a j else 0)‖ ^ 2) : ℂ) := by
    simp_rw [disjoint_gram_expansion B support hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro i _
    have hz : (∑ j, if D ⊆ support j then A i j * a j else 0) =
        ∑ j, A i j * (if D ⊆ support j then a j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [hz]
    ring
  rw [heq]
  calc
    _ ≤ ∑ D ∈ B.powerset, ‖(-1 : ℂ) ^ D.card *
        ∑ i, w i * (↑(‖∑ j, A i j * (if D ⊆ support j then a j else 0)‖ ^ 2) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ D ∈ B.powerset,
        W * ‖operator A‖ ^ 2 * ∑ j, ‖if D ⊆ support j then a j else 0‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro D _
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact weighted_energy_bound A (fun j => if D ⊆ support j then a j else 0) w W hW hw
    _ = _ := by
      rw [← Finset.mul_sum, masked_coefficient_energy B support hs a]

end CoprimeSieveOperator

namespace IdealCoprimeSieveOperator
open IdealMobiusDivisorSum CoprimeSieveOperator FiniteSieveOperator
open UniqueFactorizationMonoid

theorem ideal_coprime_gram_operator_bound {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (_hN : 0 ≤ N) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N)
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (∑ j, ∑ k,
      if IsCoprime (column j) (column k) then
        star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  let B : Finset (Ideal O) := Finset.univ.biUnion (fun j => primeSupport (column j))
  have hs (j : n) : primeSupport (column j) ⊆ B := by
    intro P hP
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hP⟩
  have h := coprime_gram_operator_bound B (fun j => primeSupport (column j)) hs A a w W hW hw
  simp_rw [primeSupport_disjoint_iff (hcol _) (hcol _)] at h
  apply h.trans
  have hmass : (∑ j, (2 : ℝ) ^ (primeSupport (column j)).card * ‖a j‖ ^ 2) ≤
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (support_card_bound ε hε (column j) (hcol j)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le)
        (supportConstant_pos ε hε).le)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hW (sq_nonneg ‖operator A‖))

open ConcretePrimeRowBridge

end IdealCoprimeSieveOperator

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
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

namespace EisensteinSchwartzPoisson
open MeasureTheory MeasureTheory.Measure Set Real
open scoped SchwartzMap FourierTransform

@[simp] theorem quadraticTransformedSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticTransformedSquareProfile W x = paperRadialFourier W (x ^ 2) := by
  simp only [quadraticTransformedSquareProfile, _root_.smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, horizontalSlice_apply]
  rw [paperRadialFourier_square]
  simp only [complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero,
    SchwartzMap.fourier_coe, mul_comm x (2 / Real.sqrt 3)]
  rfl

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace PrimaryIdealUnitReindex
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

theorem tsum_good_elements_product (f : O → ℂ) :
    (∑' z : GoodElement, f z.val) =
      ∑' p : Oˣ × GoodIdeal, f (p.1.val * primaryGenerator p.2.val) := by
  exact (unitIdealEquiv.tsum_eq (fun z : GoodElement => f z.val)).symm

theorem tsum_good_elements_unit_invariant (f : O → ℂ)
    (hf : Summable (fun z : GoodElement => f z.val))
    (hu : ∀ (u : Oˣ) (I : GoodIdeal), f (u.val * primaryGenerator I.val) = f (primaryGenerator I.val)) :
    (∑' z : GoodElement, f z.val) =
      (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal, f (primaryGenerator I.val) := by
  let : Finite Oˣ := finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  have hp : Summable (fun p : Oˣ × GoodIdeal => f (p.1.val * primaryGenerator p.2.val)) :=
    unitIdealEquiv.summable_iff.mpr hf
  rw [tsum_good_elements_product, hp.tsum_prod]
  simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

theorem tsum_ramified_mask (f : O → ℂ) :
    (∑' z : O, if lambda ∣ z then 0 else f z) = ∑' z : GoodElement, f z.val := by
  calc
    _ = ∑' z : O, ({z : O | primaryGenerator (Ideal.span {z}) ≠ 0} : Set O).indicator f z := by
      apply tsum_congr
      intro z
      simp only [Set.indicator, Set.mem_ofPred_eq, primaryGenerator_span_ne_zero_iff]
      split_ifs <;> rfl
    _ = _ := (tsum_subtype ({z : O | primaryGenerator (Ideal.span {z}) ≠ 0} : Set O) f).symm

theorem tsum_ramified_mask_unit_invariant (f : O → ℂ) (hf : Summable f)
    (hu : ∀ (u : Oˣ) (I : GoodIdeal), f (u.val * primaryGenerator I.val) = f (primaryGenerator I.val)) :
    (∑' z : O, if lambda ∣ z then 0 else f z) =
      (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal, f (primaryGenerator I.val) := by
  rw [tsum_ramified_mask]
  exact tsum_good_elements_unit_invariant f (hf.subtype _) hu

end PrimaryIdealUnitReindex

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
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

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay EisensteinSchwartzPoisson
open PrimaryIdealUnitReindex CompletedGauss

theorem rowCoprimeMask_unit_mul {α : Type*} (R : α → Ideal O)
    (S : Finset α) (u : Oˣ) (z : O) :
    rowCoprimeMask R S (u.val * z) = rowCoprimeMask R S z := by
  simp only [rowCoprimeMask, Ideal.unit_mul_mem_iff_mem _ u.isUnit]

theorem rowCoprimeMask_norm_le_one {α : Type*} (R : α → Ideal O)
    (S : Finset α) (z : O) : ‖rowCoprimeMask R S z‖ ≤ 1 := by
  unfold rowCoprimeMask
  split_ifs <;> simp

end QuadraticUnitInvariance

namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem canonical_masked_radial_poisson_product
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask R S z * finiteSexticRow (fun i => Ideal.span {p i}) hg j z *
      W (‖eisEmbedding z‖ ^ 2 / M)) =
    ((M : ℂ) * canonicalProductGauss p hp hcop hg j / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
      ∑ E ∈ S.powerset,
        let d := primeSubsetGenerator R E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
          finiteSexticRow (fun i => Ideal.span {p i}) hg j d / (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) *
          paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i, p i)‖ ^ 2)) := by
  have ht := canonical_masked_radial_poisson_collected R hinj S
    (fun i => Ideal.span {p i}) hcop hg hchar j hj0 hj6 W M hM
  dsimp only at ht
  rw [finitePrimeModulus_norm_eq_product p] at ht
  rw [ht]
  let a : Finset α → ℂ := fun E =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
      finiteSexticRow (fun i => Ideal.span {p i}) hg j (primeSubsetGenerator R E) /
      (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 : ℝ)
  let F : Finset α → ℝ → ℂ := fun E t => paperRadialFourier W
    (M * t / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding (∏ i, p i)‖ ^ 2))
  have hu := gauss_weighted_finite_radial_sum_transport p hp hcop hg j S.powerset a F
  change ((M : ℂ) * canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg j /
      (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        (∑ E ∈ S.powerset, a E * ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) *
          F E (‖eisEmbedding h‖ ^ 2)) = _
  calc
    _ = ((M : ℂ) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
      (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg j *
        ∑ E ∈ S.powerset, a E * ∑' h : O,
          star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) * F E (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [hu]; ring
end GaussGeneratorTransport

namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open QuadraticGaussRay MixedCrossSeparation QuadraticInitialBound
open GaussGeneratorTransport EisensteinSchwartzPoisson

theorem quadraticBlock_union_eq_one_of_same_ray
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B)
    (hray : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i)) :
    quadraticBlock p hp hg (A ∪ B) = 1 := by
  have hnorm := norm_quadraticBlock p hp hcop hg hchar A
  rw [quadraticBlock_eq_rayValue p hp hcop hg hchar A] at hnorm
  have hodd := odd_of_quadraticRayValue_norm_eq_one _ hnorm
  rw [quadraticBlock_eq_rayValue p hp hcop hg hchar (A ∪ B), Finset.prod_union hd]
  exact quadraticRayValue_same_residue_product _ _ hodd hray

theorem same_ray_quadratic_pair_poisson
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B)
    (hray : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i))
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := ∏ i ∈ A ∪ B, p i
    let χ := fun z => quadraticRow (fun i => Ideal.span {p i}) hg A z *
      quadraticRow (fun i => Ideal.span {p i}) hg B z
    (∑' z : O, rowCoprimeMask R S z * χ z * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hcAB : Pairwise (Function.onFun IsCoprime
      (fun i : (A ∪ B : Finset ι) => Ideal.span {p i.val})) := by
    intro i k hik
    exact hcop (fun h => hik (Subtype.ext h))
  have ht := canonical_masked_radial_poisson_product R hinj S
    (fun i : (A ∪ B : Finset ι) => p i.val) (fun i => hp i.val) hcAB
    (fun i => hg i.val) (fun i => hchar i.val) (fun _ => 3)
    (fun _ => by decide) (fun _ => by decide) W M hM
  have hγ := quadraticBlock_union_eq_one_of_same_ray p hp hcop hg hchar A B hd hray
  rw [quadraticBlock_eq_productGauss p hp hcop hg (A ∪ B)] at hγ
  rw [hγ, mul_one, Finset.prod_coe_sort] at ht
  have hrow (z : O) : finiteSexticRow (fun i : (A ∪ B : Finset ι) => Ideal.span {p i.val})
      (fun i => hg i.val) (fun _ => 3) z =
      quadraticRow (fun i => Ideal.span {p i}) hg A z *
        quadraticRow (fun i => Ideal.span {p i}) hg B z := by
    rw [← quadraticRow_eq_canonical (fun i => Ideal.span {p i}) hg (A ∪ B) z,
      quadraticRow_disjoint_union _ _ _ _ hd]
  simp only [hrow, star_mul, quadraticRow_star] at ht
  simpa only [mul_comm] using ht

end QuadraticUnitInvariance

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.DivisorBlocks
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

open scoped BigOperators Classical

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel FiniteSieveOperator

theorem mem_fullRange {M : ℝ} {I : Ideal O} :
    I ∈ fullRange M ↔ Supported I ∧ (Ideal.absNorm I : ℝ) ≤ M := by
  rw [fullRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hM : 0 ≤ M := by
      by_contra hn
      have hz : ⌊M⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hM)
  · rintro ⟨ha, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => ha.1 (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, ha⟩

theorem mem_highKernelRange {M K : ℝ} {I : Ideal O} :
    I ∈ highKernelRange M K ↔
      Supported I ∧ (Ideal.absNorm I : ℝ) ≤ M ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) := by
  simp only [highKernelRange, Finset.mem_filter, mem_fullRange, and_assoc]

theorem highKernelNorm_nonneg (M N K : ℝ) : 0 ≤ highKernelNorm M N K := sq_nonneg _

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap

open MeasureTheory
open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.TupleWeights
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

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

theorem badPrime_mask (z : O) :
    rowCoprimeMask badPrime Finset.univ z = if Supported (Ideal.span {z}) then 1 else 0 := by
  rw [supported_span_iff]
  simp only [rowCoprimeMask, Finset.mem_univ, true_and, Bool.exists_bool, badPrime,
    Bool.false_eq_true, ite_false, ite_true, Ideal.mem_span_singleton]
  by_cases hLam : lambda ∣ z <;> by_cases htwo : (2 : O) ∣ z <;> simp [hLam, htwo]

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator

theorem highKernelNorm_mono {M N K M' N' K' : ℝ}
    (hM : M ≤ M') (hN : N ≤ N') (hK : K' ≤ K) :
    highKernelNorm M N K ≤ highKernelNorm M' N' K' := by
  let r : highKernelRange M K → highKernelRange M' K' := fun I => ⟨I.val, by
    obtain ⟨hs, hn, hk⟩ := mem_highKernelRange.mp I.property
    exact mem_highKernelRange.mpr ⟨hs, hn.trans hM, hK.trans_lt hk⟩⟩
  have hr : Function.Injective r := fun I J h =>
    Subtype.ext (congrArg (fun I : highKernelRange M' K' => I.val) h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hr
    (rangeInclusion hN) (rangeInclusion_injective hN) (highKernelMatrix M' N' K')
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem highKernel_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖operator (fun i j => quadraticRow (cols j) (primaryGenerator (rows i)))‖ ^ 2 ≤
      highKernelNorm M N K := by
  let r : m → highKernelRange M K := fun i => ⟨rows i, hrows i⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (highKernelMatrix M N K)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2
theorem highKernel_quotient_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hdiv : ∀ j, D ∣ cols j) (M N K : ℝ)
    (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (fun i j =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)))‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
  apply highKernel_family_squared_norm_le rows (fun j => idealQuotient D (cols j)) hr
  · intro j k heq
    exact hc (idealQuotient_injective_on D (hdiv j) (hdiv k) heq)
  · exact hrows
  · intro j
    exact ⟨admissible_idealQuotient (hcols j).1 (hdiv j),
      idealQuotient_norm_le hD (hdiv j) N (hcols j).2⟩

theorem highKernel_quotientMatrix_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols) (M N K : ℝ)
    (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (quotientMatrix D rows cols)‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
  let S : Finset n := Finset.univ.filter (fun j => D ∣ cols j)
  let A : Matrix m S ℂ := fun i j =>
    quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i))
  have hnorm : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
    apply highKernel_quotient_family_squared_norm_le D hD rows (fun j : S => cols j.val) hr
      (hc.comp Subtype.val_injective)
    · intro j
      exact (Finset.mem_filter.mp j.property).2
    · exact hrows
    · intro j
      exact hcols j.val
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _ (highKernelNorm_nonneg _ _ _)
  intro a
  have hinner (i : m) : (∑ j, quotientMatrix D rows cols i j * a j) =
      ∑ j : S, A i j * a j.val := by
    change (∑ j, (if D ∣ cols j then
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) else 0) * a j) =
      ∑ j : S, quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i)) * a j.val
    rw [Finset.sum_coe_sort S (fun j : n =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) * a j)]
    simp only [S, Finset.sum_filter, ite_mul, zero_mul]
  simp_rw [hinner]
  have henergy := FiniteSieveOperator.energy_bound A (fun j : S => a j.val)
  apply henergy.trans
  calc
    _ ≤ highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K * ∑ j : S, ‖a j.val‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (highKernelNorm_nonneg _ _ _)
      rw [Finset.sum_coe_sort S (fun j : n => ‖a j‖ ^ 2)]
      exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator

theorem totalQuotient_ne_zero (D I : Ideal O) (hI : Admissible I) : totalQuotient D I ≠ 0 := by
  by_cases h : D ∣ I
  · simpa only [totalQuotient, if_pos h] using (admissible_idealQuotient hI h).1
  · simp [totalQuotient, h]

theorem totalQuotient_norm_le (D I : Ideal O) (hI : Admissible I)
    (N : ℝ) (hN : 1 ≤ N) (hIN : (Ideal.absNorm I : ℝ) ≤ N) :
    (Ideal.absNorm (totalQuotient D I) : ℝ) ≤ N := by
  by_cases h : D ∣ I
  · rw [totalQuotient, if_pos h]
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    exact (Nat.cast_le.mpr (Nat.le_of_dvd hn (map_dvd Ideal.absNorm (idealQuotient_dvd h)))).trans hIN
  · simpa only [totalQuotient, if_neg h, map_one, Nat.cast_one] using hN

theorem gcdTerm_eq_quotient {m n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (i : m) (j k : n) :
    gcdTerm D rows cols a i j k =
      (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow D (primaryGenerator (rows i))) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) *
          (quotientMatrix D rows cols i k * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [gcdTerm, totalQuotient, quotientMatrix, if_pos hj, if_pos hk]
      rw [← gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD hj hk]
      by_cases hg : gcd (cols j) (cols k) = D
      · rw [if_pos hg, if_pos hg, quadraticRow_divisor_factor _ D (hcols j) hj,
          quadraticRow_divisor_factor _ D (hcols k) hk]
        simp only [star_mul]
        ring
      · simp only [if_neg hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        intro he
        exact hk (he ▸ gcd_dvd_right (cols j) (cols k))
      simp only [gcdTerm, if_neg hg]
      simp [quotientMatrix, hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      intro he
      exact hj (he ▸ gcd_dvd_left (cols j) (cols k))
    simp only [gcdTerm, if_neg hg]
    simp [quotientMatrix, hj]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.GcdReduction
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

theorem mem_gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) (j k : n) :
    gcd (cols j) (cols k) ∈ gcdPool cols :=
  Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩

theorem energy_eq_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    ((∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, gcdBlock D rows cols a := by
  have hp (i : m) (j k : n) : (∑ D ∈ gcdPool cols, gcdTerm D rows cols a i j k) =
      star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
        (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) := by
    rw [Finset.sum_eq_single (gcd (cols j) (cols k))]
    · simp only [gcdTerm, ite_true]
    · intro D hD hne
      exact if_neg (Ne.symm hne)
    · exact fun h => (h (mem_gcdPool cols j k)).elim
  have hi (i : m) : (∑ D ∈ gcdPool cols, ∑ j, ∑ k, gcdTerm D rows cols a i j k) =
      ∑ j, ∑ k, star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
        (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hp i j k)
  simp only [gcdBlock]
  rw [Finset.sum_comm]
  simp_rw [hi]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Complex.ofReal_pow] using CoprimeSieveOperator.square_norm_sum
    (fun j => quadraticRow (cols j) (primaryGenerator (rows i)) * a j)

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction

theorem sectorCoefficient_energy {n r : Type*} [Fintype n] [Fintype r] [DecidableEq r]
    (σ : n → r) (a : n → ℂ) :
    (∑ c, ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) = ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (σ j)]
  · simp [sectorCoefficient]
  · intro c hc hne
    simp [sectorCoefficient, Ne.symm hne]
  · simp

private theorem norm_sum_square_card {r : Type*} [Fintype r] (f : r → ℂ) :
    ‖∑ c, f c‖ ^ 2 ≤ (Fintype.card r : ℝ) * ∑ c, ‖f c‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : r => (1 : ℝ)) (fun c => ‖f c‖)
  have hh : ‖∑ c, f c‖ ^ 2 ≤ (∑ c, ‖f c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  exact hh.trans (by simpa using h)

theorem sector_energy_bound {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    (A : Matrix m n ℂ) (σ : n → r) (a : n → ℂ) :
    (∑ i, ‖∑ j, A i j * a j‖ ^ 2) ≤
      (Fintype.card r : ℝ) * ∑ c, ∑ i, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
  have hi (i : m) : (∑ j, A i j * a j) = ∑ c, ∑ j, A i j * sectorCoefficient σ c a j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, Finset.sum_eq_single (σ j)]
    · simp [sectorCoefficient]
    · intro c hc hne
      simp [sectorCoefficient, Ne.symm hne]
    · simp
  calc
    _ ≤ ∑ i, (Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [hi]
      exact norm_sum_square_card _
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy
open FiniteSieveRestriction

theorem rayGcdBlock_eq {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    rayGcdBlock D c rows cols a = ∑ i, ∑ j, ∑ k,
      if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
        star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
          (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) else 0 := by
  unfold rayGcdBlock gcdBlock gcdTerm sectorCoefficient
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hg : gcd (cols j) (cols k) = D <;>
    by_cases hj : columnRay (cols j) = c <;> by_cases hk : columnRay (cols k) = c <;>
      simp only [hg, hj, hk, ↓reduceIte, true_and, false_and, and_false,
        mul_zero, zero_mul, star_zero]

end CanonicalQuadraticSieve

namespace CanonicalQuadraticSieve

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
open IdealCoprimeSieveOperator DivisorBlockCauchy

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

theorem highKernel_weightedGcdBlock_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (D : Ideal O) (hD : D ≠ 0)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) (a : n → ℂ) :
    ‖weightedGcdBlock D rows cols w a‖ ≤ W * highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K *
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
  let v : m → ℂ := fun i => w i *
    (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow D (primaryGenerator (rows i)))
  have hv (i : m) : ‖v i‖ ≤ W := by
    dsimp only [v]
    simp only [norm_mul, norm_star]
    calc
      _ ≤ W * (1 * 1) := by
        apply mul_le_mul (hw i)
        · exact mul_le_mul (quadraticRow_norm_le_one D _) (quadraticRow_norm_le_one D _) (norm_nonneg _) (by norm_num)
        · positivity
        · exact hW
      _ = W := by ring
  have he : weightedGcdBlock D rows cols w a = ∑ i, v i * ∑ j, ∑ k,
      if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) *
          (quotientMatrix D rows cols i k * (if D ∣ cols k then a k else 0)) else 0 := by
    unfold weightedGcdBlock
    simp_rw [gcdTerm_eq_quotient D hD rows cols (fun j => (hcols j).1) a]
    simp only [v, ← Finset.mul_sum, mul_assoc]
  rw [he]
  have hb := ideal_coprime_gram_operator_bound ε hε (fun j => totalQuotient D (cols j))
    (fun j => totalQuotient_ne_zero D _ (hcols j).1) N (by linarith)
    (fun j => totalQuotient_norm_le D _ (hcols j).1 N hN (hcols j).2)
    (quotientMatrix D rows cols) (fun j => if D ∣ cols j then a j else 0) v W hW hv
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (highKernel_quotientMatrix_squared_norm_le D hD rows cols hr hc M N K hrows hcols) hW)
      (mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem highKernel_large_weighted_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O)) (G : ℝ) (hG : 0 < G)
    (hS : ∀ D ∈ S, G ≤ (Ideal.absNorm D : ℝ))
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) (a : n → ℂ) :
    (∑ D ∈ S, ‖weightedGcdBlock D rows cols w a‖) ≤
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have hfac : 0 ≤ supportConstant ε hε * N ^ ε :=
    mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)
  have hB : 0 ≤ highKernelNorm M (N / G) K := highKernelNorm_nonneg _ _ _
  have hb (D : Ideal O) (hD : D ∈ S) : ‖weightedGcdBlock D rows cols w a‖ ≤
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
    have hn : 0 < (Ideal.absNorm D : ℝ) := hG.trans_le (hS D hD)
    have hD0 : D ≠ 0 := by intro hz; simp [hz] at hn
    have hmono := highKernelNorm_mono (M := M) (K := K) (M' := M) (K' := K) le_rfl
      (div_le_div_of_nonneg_left (by linarith : 0 ≤ N) hG (hS D hD)) le_rfl
    exact (highKernel_weightedGcdBlock_bound ε hε D hD0 rows cols hr hc M N K hN hrows hcols w W hW hw a).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hW) hfac) (by positivity))
  calc
    _ ≤ ∑ D ∈ S, W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := Finset.sum_le_sum hb
    _ = W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ D ∈ S, ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (divisor_mask_energy_small_power ε hε S cols (fun j => (hcols j).1.1) N (fun j => (hcols j).2) a)
        (mul_nonneg (mul_nonneg hW hB) hfac)
    _ = _ := by ring

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction

theorem sector_weighted_energy_bound {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    (A : Matrix m n ℂ) (σ : n → r) (a : n → ℂ) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (∑ i, v i * ‖∑ j, A i j * a j‖ ^ 2) ≤
      (Fintype.card r : ℝ) * ∑ c, ∑ i, v i * ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
  have hi (i : m) : ‖∑ j, A i j * a j‖ ^ 2 ≤
      (Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
    simpa only [Fintype.sum_unique] using sector_energy_bound (fun _ : Unit => A i) σ a
  calc
    _ ≤ ∑ i, v i * ((Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi i) (hv i))
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      ring
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction

theorem weighted_energy_eq_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (a : n → ℂ) :
    ((∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a := by
  have hi (i : m) : ((‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, ∑ j, ∑ k, gcdTerm D rows cols a i j k := by
    simpa only [gcdBlock, Fintype.sum_unique, gcdTerm] using energy_eq_gcd_blocks (fun _ : Unit => rows i) cols a
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, hi, Finset.mul_sum, weightedGcdBlock]
  rw [Finset.sum_comm]

theorem weighted_energy_le_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      ∑ D ∈ gcdPool cols, ‖weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a‖ := by
  have he := congrArg norm (weighted_energy_eq_gcd_blocks rows cols v a)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (sq_nonneg _)))] at he
  rw [he]
  exact norm_sum_le _ _

theorem highKernel_weighted_energy_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (v : m → ℝ) (W : ℝ) (hW : 0 ≤ W) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ W) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      (∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        ‖weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a‖) +
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have he := weighted_energy_le_gcd_blocks rows cols v (fun i => (hv i).1) a
  rw [← Finset.sum_filter_add_sum_filter_not (gcdPool cols) (fun D => (Ideal.absNorm D : ℝ) ≤ G)] at he
  exact he.trans (add_le_add le_rfl (highKernel_large_weighted_gcd_blocks ε hε _ G hG
    (fun D hD => (lt_of_not_ge (Finset.mem_filter.mp hD).2).le)
    rows cols hr hc M N K hN hrows hcols (fun i => (v i : ℂ)) W hW
    (fun i => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv i).1] using (hv i).2) a))

theorem highKernel_weighted_energy_ray_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (v : m → ℝ) (W : ℝ) (hW : 0 ≤ W) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ W) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      16 * ((∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G), ‖weightedRayGcdBlock D c rows cols v a‖) +
        W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
          (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2) := by
  let σ : n → EisensteinEPrimaryPhase.Coord := fun j => columnRay (cols j)
  let C := W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2
  have hs := sector_weighted_energy_bound
    (fun i j => quadraticRow (cols j) (primaryGenerator (rows i))) σ a v (fun i => (hv i).1)
  have hcard : Fintype.card EisensteinEPrimaryPhase.Coord = 16 := by decide
  rw [hcard] at hs
  norm_num only [Nat.cast_ofNat] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
        ((∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖weightedRayGcdBlock D c rows cols v a‖) + C * ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      exact highKernel_weighted_energy_gcd_reduction ε hε G hG rows cols hr hc M N K hN hrows hcols v W hW hv
        (sectorCoefficient σ c a)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, sectorCoefficient_energy]

end

open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates

theorem idealSupport_disjoint_of_coprime (F : Finset (Ideal O)) (I J : Ideal O)
    (hIJ : IsCoprime I J) : Disjoint (idealSupport F I) (idealSupport F J) := by
  apply Finset.disjoint_left.mpr
  intro P hPI hPJ
  have hi := (mem_idealSupport_iff F I P).mp hPI
  have hj := (mem_idealSupport_iff F J P).mp hPJ
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val hi
  exact hp.not_isUnit (hIJ.isRelPrime
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hi)
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hj))

theorem primaryGenerator_unit_mod_four (I : Ideal O) (hI : Admissible I) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator I)) := by
  let F : Finset (Ideal O) := {I}
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have hJI : J = I := Finset.mem_singleton.mp hJ
    simpa only [hJI] using hI
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [primaryGenerator_eq_poolProduct F hF I (Finset.mem_singleton_self I)]
  exact RayFourExpansion.prime_product_unit_mod_four (poolPrimary F) (poolPrimary_odd F hF) _

theorem columnRay_idealQuotient_eq (D I J : Ideal O) (hI : Admissible I) (_hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : columnRay I = columnRay J) :
    columnRay (idealQuotient D I) = columnRay (idealQuotient D J) := by
  have hD : Admissible D := admissible_of_dvd hI hDI
  have hu := primaryGenerator_unit_mod_four D hD
  obtain ⟨u, hu⟩ := hu
  have hray : residue (primaryGenerator I) = residue (primaryGenerator J) := hIJ
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq hray
  have hquot : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator I) =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator J) := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨z, hz⟩
  have hprodI : primaryGenerator I = primaryGenerator D * primaryGenerator (idealQuotient D I) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDI]
  have hprodJ : primaryGenerator J = primaryGenerator D * primaryGenerator (idealQuotient D J) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDJ]
  rw [hprodI, hprodJ, map_mul, map_mul, ← hu] at hquot
  have heq := (Units.mul_right_inj u).mp hquot
  exact QuadraticGaussRay.residue_eq_of_quotient_four_eq _ _ heq

end

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

theorem quadraticRow_zero_of_ne_one (I : Ideal O) (hI : Admissible I) (hI1 : I ≠ 1) :
    quadraticRow I 0 = 0 := by
  let F : Finset (Ideal O) := {I}
  have hIF : I ∈ F := Finset.mem_singleton_self I
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have hJI := Finset.mem_singleton.mp hJ
    simpa only [hJI] using hI
  have hS : (idealSupport F I).Nonempty := by
    by_contra hn
    have he : idealSupport F I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hp := idealSupport_product_eq F hIF hI.2.1
    rw [he, Finset.prod_empty] at hp
    exact hI1 hp.symm
  let : Nonempty (idealSupport F I) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  rw [quadraticRow_eq_primeSubset F hF I hIF]
  exact finiteSexticRow_zero _ _ _

theorem quadratic_pair_zero_of_nontrivial (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (h : I ≠ 1 ∨ J ≠ 1) : quadraticRow I 0 * quadraticRow J 0 = 0 := by
  rcases h with h | h
  · rw [quadraticRow_zero_of_ne_one I hI h, zero_mul]
  · rw [quadraticRow_zero_of_ne_one J hJ h, mul_zero]

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

theorem idealSupport_singleton_univ (D : Ideal O) :
    idealSupport {D} D = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro P
  apply (mem_idealSupport_iff {D} D P).mpr
  obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
  have hID : I = D := Finset.mem_singleton.mp hI
  simpa only [hID] using hP

theorem singleton_rowCoprimeMask_eq_idealZeroMask (D : Ideal O) (z : O) :
    rowCoprimeMask (fun P : primePool {D} => P.val) Finset.univ z = idealZeroMask D z := by
  have he : (∃ P ∈ (Finset.univ : Finset (primePool {D})), z ∈ P.val) ↔
      ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P := by
    constructor
    · rintro ⟨P, _, hz⟩
      obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
      have hID : I = D := Finset.mem_singleton.mp hI
      exact ⟨P.val, hID ▸ hP, hz⟩
    · rintro ⟨P, hP, hz⟩
      have hp : P ∈ primePool {D} := mem_primePool_iff.mpr ⟨D, Finset.mem_singleton_self D, hP⟩
      exact ⟨⟨P, hp⟩, Finset.mem_univ _, hz⟩
  simp only [rowCoprimeMask, idealZeroMask, he]

theorem canonical_quadraticRow_star (D : Ideal O) (hD : Admissible D) (z : O) :
    star (quadraticRow D z) = quadraticRow D z := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  rw [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  exact QuadraticInitialBound.quadraticRow_star _ _ _ _

theorem canonical_quadraticRow_squared (D : Ideal O) (hD : Admissible D) (z : O) :
    quadraticRow D z * quadraticRow D z = idealZeroMask D z := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  rw [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  rw [← QuadraticSquarefreeKernel.quadraticRow_mul _ _ _ z z, ← pow_two,
    QuadraticSquarefreeKernel.quadraticRow_square, idealSupport_singleton_univ]
  exact singleton_rowCoprimeMask_eq_idealZeroMask D z

theorem gcdMaskPrimes_mask (D : Ideal O) (z : O) :
    rowCoprimeMask (fun P : gcdMaskPrimes D => P.val) Finset.univ z =
      rowCoprimeMask badPrime Finset.univ z * idealZeroMask D z := by
  have he : (∃ P ∈ (Finset.univ : Finset (gcdMaskPrimes D)), z ∈ P.val) ↔
      (lambda ∣ z ∨ (2 : O) ∣ z) ∨
        ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P := by
    constructor
    · rintro ⟨P, _, hz⟩
      rcases Finset.mem_union.mp P.property with hp | hp
      · rcases Finset.mem_insert.mp hp with hp | hp
        · exact Or.inl (Or.inl (Ideal.mem_span_singleton.mp (hp ▸ hz)))
        · exact Or.inl (Or.inr (Ideal.mem_span_singleton.mp ((Finset.mem_singleton.mp hp) ▸ hz)))
      · exact Or.inr ⟨P.val, Multiset.mem_toFinset.mp hp, hz⟩
    · rintro ((hz | hz) | ⟨P, hP, hz⟩)
      · exact ⟨⟨Ideal.span {lambda}, Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩,
          Finset.mem_univ _, Ideal.mem_span_singleton.mpr hz⟩
      · exact ⟨⟨Ideal.span {(2 : O)}, Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩,
          Finset.mem_univ _, Ideal.mem_span_singleton.mpr hz⟩
      · exact ⟨⟨P, Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hP)⟩, Finset.mem_univ _, hz⟩
  change (if ∃ P ∈ (Finset.univ : Finset (gcdMaskPrimes D)), z ∈ P.val then (0 : ℂ) else 1) = _
  simp only [he]
  rw [badPrime_mask, supported_span_iff]
  unfold idealZeroMask
  by_cases hl : lambda ∣ z <;> by_cases ht : (2 : O) ∣ z <;>
    by_cases hd : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P <;> simp [hl, ht, hd]

end
section

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance

theorem canonical_same_ray_pair_poisson
    {α : Type*} [DecidableEq α]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    (∑' z : O, rowCoprimeMask R S z * χ z * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  let F : Finset (Ideal O) := {I, J}
  have hF : ∀ lengthScale ∈ F, Admissible lengthScale := by
    intro lengthScale hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hI
    · have hLJ := Finset.mem_singleton.mp hL
      simpa only [hLJ] using hJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  let p := poolPrimary F
  let A := idealSupport F I
  let B := idealSupport F J
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by change (Ideal.span {poolPrimary F i}).IsMaximal; rw [poolPrimary_span F hF i]; infer_instance
  have hd : Disjoint A B := idealSupport_disjoint_of_coprime F I J hcop
  have hpgI : primaryGenerator I = ∏ i ∈ A, p i := primaryGenerator_eq_poolProduct F hF I hIF
  have hpgJ : primaryGenerator J = ∏ i ∈ B, p i := primaryGenerator_eq_poolProduct F hF J hJF
  have hr : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i) := by
    rw [← hpgI, ← hpgJ]
    exact hray
  have hn : (∏ i ∈ A ∪ B, p i) = primaryGenerator I * primaryGenerator J := by
    rw [Finset.prod_union hd, ← hpgI, ← hpgJ]
  have hrowI (z : O) : QuadraticInitialBound.quadraticRow
      (fun i => Ideal.span {p i}) (poolPrimary_good F hF) A z = quadraticRow I z :=
    (quadraticRow_eq_primaryPool F hF I hIF z).symm
  have hrowJ (z : O) : QuadraticInitialBound.quadraticRow
      (fun i => Ideal.span {p i}) (poolPrimary_good F hF) B z = quadraticRow J z :=
    (quadraticRow_eq_primaryPool F hF J hJF z).symm
  have ht := same_ray_quadratic_pair_poisson R hinj S p (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
    A B hd hr W M hM
  simpa only [hn, hrowI, hrowJ] using ht

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance PrimaryIdealUnitReindex

theorem canonical_masked_pair_summable {α : Type*} (R : α → Ideal O) (S : Finset α)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hW
  intro z
  simp only [norm_mul]
  calc
    _ ≤ 1 * (1 * 1) * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ := by
      gcongr
      · exact rowCoprimeMask_norm_le_one R S z
      · exact quadraticRow_norm_le_one I z
      · exact quadraticRow_norm_le_one J z
    _ = _ := by ring

theorem canonical_pair_lattice_eq_primary_ideal_sum
    {α : Type*} (R : α → Ideal O) (S : Finset α)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (Nat.card Oˣ : ℂ) * ∑' lengthScale : GoodIdeal,
      rowCoprimeMask R S (primaryGenerator lengthScale.val) *
      (quadraticRow I (primaryGenerator lengthScale.val) * quadraticRow J (primaryGenerator lengthScale.val)) *
      W ((Ideal.absNorm lengthScale.val : ℝ) / M) := by
  have hs := canonical_masked_pair_summable R S I J W M hM
  have hu (u : Oˣ) (lengthScale : GoodIdeal) :
      rowCoprimeMask R S (u.val * primaryGenerator lengthScale.val) *
        (quadraticRow I (u.val * primaryGenerator lengthScale.val) * quadraticRow J (u.val * primaryGenerator lengthScale.val)) *
        W (‖eisEmbedding (u.val * primaryGenerator lengthScale.val)‖ ^ 2 / M) =
      rowCoprimeMask R S (primaryGenerator lengthScale.val) *
        (quadraticRow I (primaryGenerator lengthScale.val) * quadraticRow J (primaryGenerator lengthScale.val)) *
        W (‖eisEmbedding (primaryGenerator lengthScale.val)‖ ^ 2 / M) := by
    rw [rowCoprimeMask_unit_mul, canonical_pair_unit_invariant I J hI hJ hray,
      norm_eisEmbedding_unit_mul]
  have ht := tsum_ramified_mask_unit_invariant _ hs hu
  change (∑' z : O, if lambda ∣ z then (0 : ℂ) else _) = _ at ht
  have hn (lengthScale : GoodIdeal) := primaryGenerator_norm_sq lengthScale.val lengthScale.property
  simpa only [hn] using ht

theorem canonical_mask_lattice_eq_six_all_ideals
    {α : Type*} (R : α → Ideal O) (S : Finset α)
    (hmask : ∀ z : O, lambda ∣ z → rowCoprimeMask R S z = 0)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (6 : ℂ) * ∑' lengthScale : Ideal O,
      rowCoprimeMask R S (primaryGenerator lengthScale) *
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) := by
  have ht := canonical_pair_lattice_eq_primary_ideal_sum R S I J hI hJ hray W M hM
  rw [card_units_eq_six] at ht
  have hl : (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ∑' z : O, rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M) := by
    apply tsum_congr
    intro z
    by_cases hz : lambda ∣ z
    · simp [hz, hmask z hz]
    · rw [if_neg hz]
  rw [hl] at ht
  rw [ht]
  congr 1
  let f : Ideal O → ℂ := fun lengthScale => rowCoprimeMask R S (primaryGenerator lengthScale) *
    (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
    W ((Ideal.absNorm lengthScale : ℝ) / M)
  change (∑' lengthScale : GoodIdeal, f lengthScale.val) = ∑' lengthScale : Ideal O, f lengthScale
  have hsub : (∑' lengthScale : GoodIdeal, f lengthScale.val) =
      ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | primaryGenerator lengthScale ≠ 0} : Set (Ideal O)).indicator f lengthScale :=
    tsum_subtype _ f
  rw [hsub]
  apply tsum_congr
  intro lengthScale
  by_cases hg : primaryGenerator lengthScale ≠ 0
  · exact Set.indicator_of_mem hg f
  · rw [Set.indicator_of_notMem hg]
    have hz : primaryGenerator lengthScale = 0 := not_not.mp hg
    dsimp only [f]
    rw [hz, hmask 0 (dvd_zero _)]
    simp only [zero_mul]

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

theorem badPrime_mask_primaryGenerator (lengthScale : Ideal O) :
    rowCoprimeMask badPrime Finset.univ (primaryGenerator lengthScale) = if Supported lengthScale then 1 else 0 := by
  rw [badPrime_mask, supported_span_primaryGenerator_iff]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularRecursion
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel

theorem rayPairValue_eq (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I : Ideal O) :
    rayPairValue N D c a I = ∑ J : idealRange N, ∑ lengthScale : idealRange N,
      if gcd J.val lengthScale.val = D ∧ columnRay J.val = c ∧ columnRay lengthScale.val = c then
        star (quadraticRow J.val (primaryGenerator I) * a J) *
          (quadraticRow lengthScale.val (primaryGenerator I) * a lengthScale) else 0 := by
  simpa only [rayPairValue, rayGcdBlock, gcdBlock, Fintype.sum_unique, gcdTerm] using
    rayGcdBlock_eq D c (fun _ : Unit => I) (fun J : idealRange N => J.val) a

end

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator

end CanonicalQuadraticSieve

open scoped SchwartzMap ContDiff
namespace QuadraticInitialBound

theorem annularSieveBump_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : annularSieveBump t = 0 := by
  apply annularSieveBump.zero_of_le_dist
  change 1 / 2 ≤ dist t (3 / 4)
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

theorem annularSieveBump_zero_of_ge {t : ℝ} (ht : 5 / 4 ≤ t) : annularSieveBump t = 0 := by
  apply annularSieveBump.zero_of_le_dist
  change 1 / 2 ≤ dist t (3 / 4)
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

@[simp] theorem annularSieveCutoff_zero : annularSieveCutoff 0 = 0 := by
  rw [annularSieveCutoff_apply, annularSieveBump_zero_of_le (by norm_num), Complex.ofReal_zero]

end QuadraticInitialBound

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel

theorem annularHighWeight_eq_zero (M : ℝ) (hM : 0 < M) (I : Ideal O)
    (hI : 2 * M ≤ (Ideal.absNorm I : ℝ)) : annularHighWeight M I = 0 := by
  have ht : 2 ≤ (Ideal.absNorm I : ℝ) / M := (le_div_iff₀ hM).mpr (by linarith)
  exact QuadraticInitialBound.annularSieveBump_zero_of_ge (by linarith)

theorem annularRayGcdBlock_eq_finite (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : highKernelRange (2 * M) K, (annularHighWeight M I.val : ℂ) * rayPairValue N D c a I.val := by
  rfl

theorem annularRayGcdBlock_eq_tsum (M N K : ℝ) (hM : 0 < M)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑' I : Ideal O, if Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) then
        QuadraticInitialBound.annularSieveCutoff ((Ideal.absNorm I : ℝ) / M) * rayPairValue N D c a I else 0 := by
  rw [annularRayGcdBlock_eq_finite,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => (annularHighWeight M I : ℂ) * rayPairValue N D c a I)]
  symm
  rw [tsum_eq_sum (s := highKernelRange (2 * M) K) (fun I hI => ?_)]
  · apply Finset.sum_congr rfl
    intro I hI
    have hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) := by
      have h := mem_highKernelRange.mp hI
      exact ⟨h.1, h.2.2⟩
    rw [if_pos hp, QuadraticInitialBound.annularSieveCutoff_apply]
    rfl
  · by_cases hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ)
    · have hn : 2 * M < (Ideal.absNorm I : ℝ) := by
        by_contra hh
        exact hI (mem_highKernelRange.mpr ⟨hp.1, le_of_not_gt hh, hp.2⟩)
      rw [if_pos hp, QuadraticInitialBound.annularSieveCutoff_apply]
      change (annularHighWeight M I : ℂ) * _ = 0
      rw [annularHighWeight_eq_zero M hM I hn.le]
      simp
    · exact if_neg hp

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.SquareParts
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson PrimaryIdealUnitReindex QuadraticSquarefreeKernel

theorem supported_generator_injective :
    Function.Injective (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => primaryGenerator lengthScale.val) := by
  intro I J h
  change primaryGenerator I.val = primaryGenerator J.val at h
  have hi := primaryGenerator_ne_zero_of_good_factors I.val I.property.1 (fun P hP => (I.property.2 P hP).1)
  have hj := primaryGenerator_ne_zero_of_good_factors J.val J.property.1 (fun P hP => (J.property.2 P hP).1)
  apply Subtype.ext
  rw [← (primaryGenerator_spec I.val hi).1, ← (primaryGenerator_spec J.val hj).1, h]

theorem supported_radial_norm_summable (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun lengthScale : Ideal O => if Supported lengthScale then ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖ else 0) := by
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  have hp := hs.comp_injective supported_generator_injective
  have hi : Summable (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => ‖W ((Ideal.absNorm lengthScale.val : ℝ) / M)‖) := by
    apply hp.congr
    intro lengthScale
    dsimp only [Function.comp_def]
    rw [primaryGenerator_norm_sq lengthScale.val (primaryGenerator_ne_zero_of_good_factors lengthScale.val
      lengthScale.property.1 (fun P hP => (lengthScale.property.2 P hP).1))]
  have ht : Summable (({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)).indicator
      (fun lengthScale => ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖)) := (summable_subtype_iff_indicator).mp hi
  exact ht

theorem originalPairSource_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (originalPairSource I J W M) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun lengthScale => norm_nonneg _) _ (supported_radial_norm_summable W M hM)
  intro lengthScale
  by_cases hL : Supported lengthScale
  · simp only [originalPairSource, if_pos hL, norm_mul, norm_star]
    calc
      _ ≤ (1 * 1) * ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖ := by
        gcongr
        · exact quadraticRow_norm_le_one I _
        · exact quadraticRow_norm_le_one J _
      _ = _ := by ring
  · simp only [originalPairSource, if_neg hL, norm_zero, le_refl]

theorem originalPairLow_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairLow I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

theorem originalPairHigh_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairHigh I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

theorem originalPairHigh_eq_source_sub_low (I J : Ideal O) (W : 𝓢(ℝ, ℂ))
    (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairHigh I J W M K lengthScale) =
      (∑' lengthScale : Ideal O, originalPairSource I J W M lengthScale) -
        ∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale := by
  calc
    _ = ∑' lengthScale : Ideal O, (originalPairSource I J W M lengthScale - originalPairLow I J W M K lengthScale) := by
      apply tsum_congr
      intro lengthScale
      by_cases hK : (Ideal.absNorm (squarefreePart lengthScale) : ℝ) ≤ K
      · simp [originalPairHigh, originalPairLow, hK, not_lt.mpr hK]
      · simp [originalPairHigh, originalPairLow, hK, lt_of_not_ge hK]
    _ = _ := (originalPairSource_summable I J W M hM).tsum_sub (originalPairLow_summable I J W M K hM)

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

theorem canonical_gcd_masked_pair_poisson
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    let R := fun P : gcdMaskPrimes D => P.val
    (∑' lengthScale : Ideal O, if Supported lengthScale then idealZeroMask D (primaryGenerator lengthScale) *
      χ (primaryGenerator lengthScale) * W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  let R := fun P : gcdMaskPrimes D => P.val
  have hm (z : O) (hz : lambda ∣ z) : rowCoprimeMask R Finset.univ z = 0 := by
    rw [gcdMaskPrimes_mask, badPrime_mask]
    have hns : ¬Supported (Ideal.span {z}) := fun h => (supported_span_iff z).mp h |>.1 hz
    simp only [if_neg hns, zero_mul]
  have hlat := canonical_same_ray_pair_poisson R Subtype.val_injective Finset.univ I J hI hJ hcop hray W M hM
  have hid := canonical_mask_lattice_eq_six_all_ideals R Finset.univ hm I J hI hJ hray W M hM
  have he : (∑' lengthScale : Ideal O, rowCoprimeMask R Finset.univ (primaryGenerator lengthScale) *
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M)) =
      ∑' lengthScale : Ideal O, if Supported lengthScale then idealZeroMask D (primaryGenerator lengthScale) *
        (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0 := by
    apply tsum_congr
    intro lengthScale
    rw [gcdMaskPrimes_mask, badPrime_mask_primaryGenerator]
    by_cases hL : Supported lengthScale <;> simp [hL]
  rw [he] at hid
  dsimp only at hlat ⊢
  rw [hid] at hlat
  calc
    _ = (6 : ℂ)⁻¹ * ((M : ℂ) / ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ * _) := by
      rw [← hlat]
      ring
    _ = _ := by ring

theorem canonical_pair_divisor_mask (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (z : O) :
    star (quadraticRow I z) * quadraticRow J z =
      idealZeroMask D z *
        (quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z) := by
  rw [canonical_quadraticRow_star I hI, quadraticRow_divisor_factor I D hI hDI,
    quadraticRow_divisor_factor J D hJ hDJ]
  calc
    _ = (quadraticRow D z * quadraticRow D z) *
        (quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z) := by ring
    _ = _ := by rw [canonical_quadraticRow_squared D (admissible_of_dvd hI hDI)]

theorem canonical_original_pair_poisson
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let I' := idealQuotient D I
    let J' := idealQuotient D J
    let n := primaryGenerator I' * primaryGenerator J'
    let χ := fun z => quadraticRow I' z * quadraticRow J' z
    let R := fun P : gcdMaskPrimes D => P.val
    (∑' lengthScale : Ideal O, if Supported lengthScale then
      (star (quadraticRow I (primaryGenerator lengthScale)) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hDI : D ∣ I := hgcd ▸ gcd_dvd_left I J
  have hDJ : D ∣ J := hgcd ▸ gcd_dvd_right I J
  have hD := admissible_of_dvd hI hDI
  have hIq := admissible_idealQuotient hI hDI
  have hJq := admissible_idealQuotient hJ hDJ
  have hcop := (gcd_eq_iff_quotient_coprime D I J hD.1 hDI hDJ).mp hgcd
  have hqray := columnRay_idealQuotient_eq D I J hI hJ hDI hDJ hray
  have h := canonical_gcd_masked_pair_poisson D (idealQuotient D I) (idealQuotient D J)
    hIq hJq hcop hqray W M hM
  simpa only [canonical_pair_divisor_mask D I J hI hJ hDI hDJ] using h

theorem residual_pair_nontrivial (D I J : Ideal O) (hDI : D ∣ I) (hDJ : D ∣ J)
    (hIJ : I ≠ J) : idealQuotient D I ≠ 1 ∨ idealQuotient D J ≠ 1 := by
  by_contra hn
  push Not at hn
  apply hIJ
  calc
    I = D * idealQuotient D I := (idealQuotient_mul hDI).symm
    _ = D := by rw [hn.1, mul_one]
    _ = D * idealQuotient D J := by rw [hn.2, mul_one]
    _ = J := idealQuotient_mul hDJ

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss QuadraticSquarefreeKernel

theorem annularRayGcdBlock_eq_pair_high
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        ∑' lengthScale : Ideal O, originalPairHigh I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale := by
  let W := QuadraticInitialBound.annularSieveCutoff
  let f := fun (I J : idealRange N) (lengthScale : Ideal O) =>
    rayPairCoefficient N D c a I J * originalPairHigh I.val J.val W M K lengthScale
  have hf (I J : idealRange N) : Summable (f I J) :=
    (originalPairHigh_summable I.val J.val W M K hM).mul_left _
  have hterm (lengthScale : Ideal O) :
      (if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
        W ((Ideal.absNorm lengthScale : ℝ) / M) * rayPairValue N D c a lengthScale else 0) =
      ∑ I : idealRange N, ∑ J : idealRange N, f I J lengthScale := by
    rw [rayPairValue_eq]
    by_cases hs : Supported lengthScale
    · by_cases hk : K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)
      · have hsk : Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) := ⟨hs, hk⟩
        rw [if_pos hsk]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I _
        apply Finset.sum_congr rfl
        intro J _
        dsimp only [f, rayPairCoefficient, originalPairHigh, originalPairSource]
        rw [if_pos hk, if_pos hs]
        by_cases hc : gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c
        · rw [if_pos hc, if_pos hc]
          simp only [star_mul]
          ring
        · rw [if_neg hc, if_neg hc, zero_mul, mul_zero]
      · simp [f, originalPairHigh, hk]
    · simp [f, originalPairHigh, originalPairSource, hs]
  rw [annularRayGcdBlock_eq_tsum M N K hM D c a]
  change (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
    W ((Ideal.absNorm lengthScale : ℝ) / M) * rayPairValue N D c a lengthScale else 0) = _
  calc
    _ = ∑' lengthScale : Ideal O, ∑ I : idealRange N, ∑ J : idealRange N, f I J lengthScale := tsum_congr hterm
    _ = ∑ I : idealRange N, ∑' lengthScale : Ideal O, ∑ J : idealRange N, f I J lengthScale :=
      Summable.tsum_finsetSum (fun I _ => summable_sum (fun J _ => hf I J))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      rw [Summable.tsum_finsetSum (fun J _ => hf I J)]
      apply Finset.sum_congr rfl
      intro J _
      exact tsum_mul_left

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

theorem originalPairSource_poisson (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairSource I J W M lengthScale) = originalPairDualKernel D I J W M :=
  canonical_original_pair_poisson D I J hI hJ hgcd hray W M hM

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.UnrestrictedCharacters
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
open scoped BigOperators Classical

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex GaussGeneratorTransport

theorem idealGenerator_norm_sq (lengthScale : Ideal O) :
    ‖eisEmbedding (idealGenerator lengthScale)‖ ^ 2 = (Ideal.absNorm lengthScale : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, span_idealGenerator]

theorem canonical_pair_fourier_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun h : O => (quadraticRow I h * quadraticRow J h) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W t ht)
  intro h
  simp only [norm_mul]
  calc
    _ ≤ (1 * 1) * ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
      gcongr
      · exact quadraticRow_norm_le_one I h
      · exact quadraticRow_norm_le_one J h
    _ = _ := by ring

theorem canonical_nonprincipal_dual_ideal_reindex
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hnt : I ≠ 1 ∨ J ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    (∑' h : O, (quadraticRow I h * quadraticRow J h) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) =
      (6 : ℂ) * ∑' lengthScale : NonzeroIdeal, unrestrictedPairCharacter I J lengthScale.val *
        paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ)) := by
  let f : O → ℂ := fun h => (quadraticRow I h * quadraticRow J h) *
    paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hf : Summable f := canonical_pair_fourier_summable I J W t ht
  have h0 : f 0 = 0 := by
    dsimp only [f]
    rw [quadratic_pair_zero_of_nontrivial I J hI hJ hnt, zero_mul]
  have hu (u : Oˣ) (z : O) : f (u.val * z) = f z := by
    dsimp only [f]
    rw [canonical_pair_unit_invariant I J hI hJ hray, norm_eisEmbedding_unit_mul]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  simpa only [f, idealGenerator_norm_sq, unrestrictedPairCharacter] using he

end

section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex

theorem originalPairDualKernel_eq_ideal
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    originalPairDualKernel D I J W M = originalPairIdealDualKernel D I J W M := by
  let Q := idealQuotient D I
  let T := idealQuotient D J
  let n := primaryGenerator Q * primaryGenerator T
  let R := fun P : gcdMaskPrimes D => P.val
  let χ := fun z => quadraticRow Q z * quadraticRow T z
  let a := fun E : Finset (gcdMaskPrimes D) =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ (primeSubsetGenerator R E) /
      (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 : ℝ)
  let f := fun E : Finset (gcdMaskPrimes D) => ∑' h : O, χ h * paperRadialFourier W
    (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
  let g := fun E : Finset (gcdMaskPrimes D) => ∑' lengthScale : NonzeroIdeal,
    unrestrictedPairCharacter Q T lengthScale.val * paperRadialFourier W
      (M * (Ideal.absNorm lengthScale.val : ℝ) / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
  have hQ : Admissible Q := admissible_idealQuotient hI hDI
  have hT : Admissible T := admissible_idealQuotient hJ hDJ
  have hn0 : n ≠ 0 := mul_ne_zero
    (supported_primaryGenerator_ne_zero Q (admissible_supported hQ))
    (supported_primaryGenerator_ne_zero T (admissible_supported hT))
  have hn : 0 < ‖eisEmbedding n‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hn0)
  have hfg (E : Finset (gcdMaskPrimes D)) : f E = 6 * g E := by
    have hd : 0 < ‖eisEmbedding (primeSubsetGenerator R E)‖ :=
      norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero R E))
    let X := M / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)
    have hX : 0 < X := div_pos hM (mul_pos (sq_pos_of_pos hd) (sq_pos_of_pos hn))
    have he := canonical_nonprincipal_dual_ideal_reindex Q T hQ hT
      (columnRay_idealQuotient_eq D I J hI hJ hDI hDJ hray)
      (residual_pair_nontrivial D I J hDI hDJ hIJ) W X hX
    have harg (r : ℝ) : X * r =
        M * r / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) := by
      dsimp only [X]
      ring
    simpa only [harg, f, g, χ] using he
  have hs : (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * f E) =
      6 * ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * g E := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E _
    rw [hfg]
    ring
  change ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * f E) =
    ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * g E)
  rw [hs]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel UnrestrictedIdealReindex

theorem unrestrictedPairCharacter_square
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A : Ideal O) :
    unrestrictedPairCharacter I J (A ^ 2) =
      idealZeroMask I (idealGenerator A) * idealZeroMask J (idealGenerator A) := by
  rw [pow_two, unrestrictedPairCharacter_mul I J hI hJ hray]
  unfold unrestrictedPairCharacter
  calc
    _ = (quadraticRow I (idealGenerator A) * quadraticRow I (idealGenerator A)) *
      (quadraticRow J (idealGenerator A) * quadraticRow J (idealGenerator A)) := by ring
    _ = _ := by rw [canonical_quadraticRow_squared I hI, canonical_quadraticRow_squared J hJ]

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedNormWeights
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

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

theorem idealZeroMask_span_eq (D : Ideal O) (x y : O) (hxy : Ideal.span {x} = Ideal.span {y}) :
    idealZeroMask D x = idealZeroMask D y := by
  have hm (P : Ideal O) : x ∈ P ↔ y ∈ P := by
    constructor
    · intro h
      exact (Ideal.span_singleton_le_iff_mem P).mp (hxy ▸ (Ideal.span_singleton_le_iff_mem P).mpr h)
    · intro h
      exact (Ideal.span_singleton_le_iff_mem P).mp (hxy.symm ▸ (Ideal.span_singleton_le_iff_mem P).mpr h)
  unfold idealZeroMask
  simp_rw [hm]

theorem idealZeroMask_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) (z : O) :
    idealZeroMask (I * J) z = idealZeroMask I z * idealZeroMask J z := by
  have he : (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors (I * J), z ∈ P) ↔
      (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors I, z ∈ P) ∨
        (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors J, z ∈ P) := by
    simp only [UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.mem_add,
      or_and_right, exists_or]
  unfold idealZeroMask
  simp only [he]
  by_cases h₁ : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors I, z ∈ P <;>
    by_cases h₂ : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors J, z ∈ P <;> simp [h₁, h₂]

theorem jointMask_generator (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (lengthScale : Ideal O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ (idealGenerator lengthScale) =
      if Supported lengthScale then idealZeroMask I (primaryGenerator lengthScale) * idealZeroMask J (primaryGenerator lengthScale) else 0 := by
  rw [gcdMaskPrimes_mask, idealZeroMask_mul I J hI.1 hJ.1, badPrime_mask, span_idealGenerator]
  by_cases hL : Supported lengthScale
  · rw [if_pos hL, if_pos hL, one_mul]
    have hs : Ideal.span {idealGenerator lengthScale} = Ideal.span {primaryGenerator lengthScale} :=
      (span_idealGenerator lengthScale).trans (primaryGenerator_spec lengthScale (supported_primaryGenerator_ne_zero lengthScale hL)).1.symm
    rw [idealZeroMask_span_eq I _ _ hs, idealZeroMask_span_eq J _ _ hs]
  · simp only [if_neg hL, zero_mul]

theorem jointMask_zero (I J : Ideal O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ 0 = 0 := by
  rw [gcdMaskPrimes_mask, badPrime_mask]
  have h : ¬Supported (Ideal.span {(0 : O)}) := by
    intro h
    exact h.1 (by simp)
  rw [if_neg h, zero_mul]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalTruncation
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex

theorem lowPrincipalLattice_eq_six_ideal (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (X : ℝ) (hX : 0 < X) :
    lowPrincipalLattice I J W X = 6 * lowPrincipalIdeal I J W X := by
  let R := fun P : gcdMaskPrimes (I * J) => P.val
  let V := quadraticSquareProfile W
  let f : O → ℂ := fun z => rowCoprimeMask R Finset.univ z * V (‖eisEmbedding z‖ ^ 2 / X)
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖ ^ 2 / X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one R Finset.univ z)
  have h0 : f 0 = 0 := by
    dsimp only [f, R]
    rw [jointMask_zero, zero_mul]
  have hu (u : Oˣ) (z : O) : f (u.val * z) = f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul, norm_eisEmbedding_unit_mul]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hnorm (A : Ideal O) : ‖eisEmbedding (idealGenerator A)‖ ^ 2 = (Ideal.absNorm A : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span, span_idealGenerator]
  simp only [f, V, quadraticSquareProfile_apply, hnorm] at he
  have hid : (∑' A : NonzeroIdeal, rowCoprimeMask R Finset.univ (idealGenerator A.val) *
      W (((Ideal.absNorm A.val : ℝ) / X) ^ 2)) = lowPrincipalIdeal I J W X := by
    let F : Ideal O → ℂ := fun A => if Supported A then
      (idealZeroMask I (primaryGenerator A) * idealZeroMask J (primaryGenerator A)) *
        W (((Ideal.absNorm A : ℝ) / X) ^ 2) else 0
    calc
      _ = ∑' A : NonzeroIdeal, F A.val := by
        apply tsum_congr
        intro A
        rw [jointMask_generator I J hI hJ]
        by_cases hA : Supported A.val <;> simp [hA, F]
      _ = ∑' A : Ideal O, F A := by
        apply tsum_subtype_eq_of_support_subset
        intro A hA
          hz
        subst A
        exact hA (by simp [F, Supported])
      _ = _ := by
        calc
          _ = ∑' A : Ideal O, ({A : Ideal O | Supported A} : Set (Ideal O)).indicator
              (fun A => (idealZeroMask I (primaryGenerator A) * idealZeroMask J (primaryGenerator A)) *
                W (((Ideal.absNorm A : ℝ) / X) ^ 2)) A := by
            apply tsum_congr
            intro A
            rfl
          _ = _ := (_root_.tsum_subtype _ _).symm
  rw [hid] at he
  exact he

theorem lowPrincipalIdeal_eq_lattice (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (X : ℝ) (hX : 0 < X) :
    lowPrincipalIdeal I J W X = (6 : ℂ)⁻¹ * lowPrincipalLattice I J W X := by
  rw [lowPrincipalLattice_eq_six_ideal I J hI hJ W X hX]
  ring

theorem originalPairLow_principal_lattice
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑' B : {B : Ideal O // Admissible B}, if (Ideal.absNorm B.val : ℝ) ≤ K then
        (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
          ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B.val : ℝ))))
      else 0 := by
  rw [originalPairLow_squarefree_tsum I J hI hJ W M K hM]
  apply tsum_congr
  intro B
  by_cases hB : (Ideal.absNorm B.val : ℝ) ≤ K
  · rw [if_pos hB, if_pos hB]
    congr 1
    have hN : 0 < (Ideal.absNorm B.val : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => B.property.1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hX : 0 < Real.sqrt (M / (Ideal.absNorm B.val : ℝ)) := Real.sqrt_pos.mpr (div_pos hM hN)
    rw [← lowPrincipalIdeal_eq_lattice I J hI hJ W _ hX]
    unfold lowPrincipalIdeal
    apply tsum_congr
    intro A
    congr 2
    rw [div_pow, Real.sq_sqrt (div_pos hM hN).le]
    field_simp
  · simp only [if_neg hB]

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss

theorem tsum_admissible_norm_cutoff (K : ℝ) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Admissible B}, if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) =
      ∑ B : idealRange K, f B.val := by
  let e : idealRange K → {B : Ideal O // Admissible B} :=
    fun B => ⟨B.val, (mem_idealRange.mp B.property).1⟩
  have he : Function.Injective e := by
    intro B C h
    apply Subtype.ext
    exact congrArg (fun D : {B : Ideal O // Admissible B} => D.val) h
  let F : {B : Ideal O // Admissible B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro B hB
    have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
      by_contra hn
      exact hB (if_neg hn)
    exact ⟨⟨B.val, mem_idealRange.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩
  have ht := he.tsum_eq hs
  change (∑' B, F B) = _
  rw [← ht, tsum_fintype]
  apply Finset.sum_congr rfl
  intro B _
  exact if_pos (mem_idealRange.mp B.property).2

theorem originalPairLow_principal_finite
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑ B : idealRange K,
        (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
          ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B.val : ℝ)))) := by
  rw [originalPairLow_principal_lattice I J hI hJ W M K hM]
  exact tsum_admissible_norm_cutoff K (fun B : Ideal O =>
    (quadraticRow I (primaryGenerator B) * quadraticRow J (primaryGenerator B)) *
      ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B : ℝ)))))

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConstantDirichletSeries
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

open scoped BigOperators Classical

namespace CanonicalQuadraticSieve

section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex
open TruncatedPrincipalPoisson QuadraticSquarefreeKernel

theorem canonical_pair_ideal_fourier_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ))
    (t : ℝ) (ht : 0 < t) :
    Summable (fun lengthScale : NonzeroIdeal => unrestrictedPairCharacter I J lengthScale.val *
      paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))) := by
  have hi : Function.Injective (fun lengthScale : NonzeroIdeal => idealGenerator lengthScale.val) := by
    intro A B he
    apply Subtype.ext
    have hs := congrArg (fun z : O => Ideal.span {z}) he
    simpa only [span_idealGenerator] using hs
  have h := (canonical_pair_fourier_summable I J W t ht).comp_injective hi
  simpa only [Function.comp_def, idealGenerator_norm_sq, unrestrictedPairCharacter] using h

end

open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

theorem columnDyadicLength_small_power (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N) :
    (columnDyadicLength N + 1 : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  have hL : (columnDyadicLength N + 1 : ℝ) ≤ 2 + Real.log N / Real.log 2 := by
    dsimp only [columnDyadicLength]
    linarith
  have hr : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hb : Real.log N / Real.log 2 ≤ (N ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hε) hlog.le
  calc
    _ ≤ 2 + Real.log N / Real.log 2 := hL
    _ ≤ 2 * N ^ ε + (N ^ ε / ε) / Real.log 2 := add_le_add (by linarith) hb
    _ = _ := by field_simp

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

theorem dual_ideal_low_add_tail (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t) :
    (∑' lengthScale : NonzeroIdeal, unrestrictedPairCharacter I J lengthScale.val *
      paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))) =
      dualSquarefreeLow I J W t K + dualSquarefreeTail I J W t K := by
  let F : Ideal O → ℂ := fun lengthScale => unrestrictedPairCharacter I J lengthScale *
    paperRadialFourier W (t * (Ideal.absNorm lengthScale : ℝ))
  have hs : Summable (fun lengthScale : NonzeroIdeal => F lengthScale.val) := canonical_pair_ideal_fourier_summable I J W t ht
  have hl : Summable (fun lengthScale : NonzeroIdeal => if (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K then F lengthScale.val else 0) :=
    hs.indicator _
  have hh : Summable (fun lengthScale : NonzeroIdeal => if K < (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) then F lengthScale.val else 0) :=
    hs.indicator _
  have htail : (∑' lengthScale : NonzeroIdeal, if K < (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) then F lengthScale.val else 0) =
      dualSquarefreeTail I J W t K := by
    have hleft : (∑' lengthScale : NonzeroIdeal, if K < (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) then F lengthScale.val else 0) =
        ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | lengthScale ≠ 0} : Set (Ideal O)).indicator
          (fun lengthScale => if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then F lengthScale else 0) lengthScale := by
      exact tsum_subtype {lengthScale : Ideal O | lengthScale ≠ 0}
        (fun lengthScale : Ideal O => if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then F lengthScale else 0)
    have hright : (∑' lengthScale : {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)}, F lengthScale.val) =
        ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)} : Set (Ideal O)).indicator F lengthScale :=
      tsum_subtype _ _
    change _ = ∑' lengthScale : {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)}, F lengthScale.val
    rw [hleft, hright]
    apply tsum_congr
    intro lengthScale
    by_cases h0 : lengthScale = 0 <;> by_cases hK : K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) <;>
      simp [Set.indicator, h0, hK, F]
  rw [← htail, dualSquarefreeLow, ← hl.tsum_add hh]
  apply tsum_congr
  intro lengthScale
  by_cases hK : (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K
  · simp only [hK, not_lt_of_ge hK, ite_true, ite_false, add_zero, F]
  · simp only [hK, lt_of_not_ge hK, ite_true, ite_false, zero_add, F]

theorem dualSquarefreeLow_principal
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t) :
    dualSquarefreeLow I J W t K =
      ∑' B : {B : Ideal O // Squarefree B}, if (Ideal.absNorm B.val : ℝ) ≤ K then
        unrestrictedPairCharacter I J B.val *
          dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
            (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) else 0 := by
  let G : NonzeroIdeal → ℂ := fun lengthScale => if (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K then
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ)) else 0
  let F : (NonzeroIdeal × {B : Ideal O // Squarefree B}) → ℂ := fun p =>
    if (Ideal.absNorm p.2.val : ℝ) ≤ K then
      (idealZeroMask I (idealGenerator p.1.val) * idealZeroMask J (idealGenerator p.1.val)) *
      unrestrictedPairCharacter I J p.2.val * paperRadialFourier W
        (t * ((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ))) else 0
  have hg : Summable G := (canonical_pair_ideal_fourier_summable I J W t ht).indicator _
  have hterm (p : NonzeroIdeal × {B : Ideal O // Squarefree B}) : G (decompositionEquiv.symm p) = F p := by
    change (if (Ideal.absNorm (squarefreePart (p.1.val ^ 2 * p.2.val)) : ℝ) ≤ K then
      unrestrictedPairCharacter I J (p.1.val ^ 2 * p.2.val) *
        paperRadialFourier W (t * (Ideal.absNorm (p.1.val ^ 2 * p.2.val) : ℝ)) else 0) = F p
    rw [(squarePart_mul_squarefree p.1.property p.2.property).2]
    by_cases hK : (Ideal.absNorm p.2.val : ℝ) ≤ K
    · simp only [hK, ite_true, F, unrestrictedPairCharacter_mul I J hI hJ hray,
        unrestrictedPairCharacter_square I J hI hJ hray, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    · simp only [hK, ite_false, F]
  have hf : Summable F := (decompositionEquiv.symm.summable_iff.mpr hg).congr hterm
  calc
    _ = ∑' p : NonzeroIdeal × {B : Ideal O // Squarefree B}, G (decompositionEquiv.symm p) :=
      (decompositionEquiv.symm.tsum_eq G).symm
    _ = ∑' p, F p := tsum_congr hterm
    _ = ∑' p : ({B : Ideal O // Squarefree B} × NonzeroIdeal), F (p.2, p.1) :=
      (Equiv.prodComm _ _).tsum_eq (fun p => F (p.2, p.1))
    _ = ∑' B : {B : Ideal O // Squarefree B}, ∑' A : NonzeroIdeal, F (A, B) := hf.prod_symm.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro B
      by_cases hK : (Ideal.absNorm B.val : ℝ) ≤ K
      · rw [if_pos hK, dualPrincipalIdeal, ← tsum_mul_left]
        apply tsum_congr
        intro A
        have hB : 0 < (Ideal.absNorm B.val : ℝ) := by
          exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => B.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
        have htb : 0 < t * (Ideal.absNorm B.val : ℝ) := mul_pos ht hB
        have harg : ((Ideal.absNorm A.val : ℝ) / Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) ^ 2 =
            t * ((Ideal.absNorm A.val : ℝ) ^ 2 * (Ideal.absNorm B.val : ℝ)) := by
          rw [div_pow, Real.sq_sqrt (one_div_pos.mpr htb).le]
          field_simp
        simp only [F, if_pos hK, quadraticTransformedSquareProfile_apply, harg]
        ring
      · simp only [F, if_neg hK, tsum_zero]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.TruncatedSecondTransfer
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex TruncatedPrincipalPoisson

theorem mem_squarefreeIdealRange {K : ℝ} {I : Ideal O} :
    I ∈ squarefreeIdealRange K ↔ Squarefree I ∧ (Ideal.absNorm I : ℝ) ≤ K := by
  rw [squarefreeIdealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, hs⟩
    refine ⟨hs, ?_⟩
    have hK : 0 ≤ K := by
      by_contra hn
      have hz : ⌊K⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hK)
  · rintro ⟨hs, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => hs.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, hs⟩

theorem tsum_squarefree_norm_cutoff (K : ℝ) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Squarefree B}, if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) =
      ∑ B : squarefreeIdealRange K, f B.val := by
  let e : squarefreeIdealRange K → {B : Ideal O // Squarefree B} :=
    fun B => ⟨B.val, (mem_squarefreeIdealRange.mp B.property).1⟩
  have he : Function.Injective e := by
    intro B C h
    apply Subtype.ext
    exact congrArg (fun D : {B : Ideal O // Squarefree B} => D.val) h
  let F : {B : Ideal O // Squarefree B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro B hB
    have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
      by_contra hn
      exact hB (if_neg hn)
    exact ⟨⟨B.val, mem_squarefreeIdealRange.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩
  have ht := he.tsum_eq hs
  change (∑' B, F B) = _
  rw [← ht, tsum_fintype]
  apply Finset.sum_congr rfl
  intro B _
  exact if_pos (mem_squarefreeIdealRange.mp B.property).2

theorem dualSquarefreeLow_principal_finite
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t) :
    dualSquarefreeLow I J W t K =
      ∑ B : squarefreeIdealRange K, unrestrictedPairCharacter I J B.val *
        dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
          (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) := by
  rw [dualSquarefreeLow_principal I J hI hJ hray W t K ht]
  exact tsum_squarefree_norm_cutoff K (fun B => unrestrictedPairCharacter I J B *
    dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
      (Real.sqrt (1 / (t * (Ideal.absNorm B : ℝ)))))

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.LogDensity
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

theorem squarefree_divisor_sum_eq_support (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors G, f D) =
      ∑ S ∈ (IdealMobiusDivisorSum.primeSupport G).powerset, f (∏ P ∈ S, P) := by
  have hfilter : (idealDivisors G).filter Squarefree = idealDivisors G := by
    apply Finset.filter_eq_self.mpr
    intro D hD
    exact hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp hD)
  rw [← hfilter, squarefree_divisors_eq_image G hG.ne_zero, Finset.sum_image]
  intro S hS T hT hST
  exact support_product_injective (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hST

end

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

theorem commonMaskIdeal_squarefree (D : Ideal O) : Squarefree (commonMaskIdeal D) := by
  have hp (P : Ideal O) (hP : P ∈ gcdMaskPrimes D) : Prime P := by
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P, hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro P hP Q hQ hne
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P, hP⟩
    let : Q.IsMaximal := gcdMaskPrimes_maximal D ⟨Q, hQ⟩
    exact (Ideal.isCoprime_of_isMaximal hne).isRelPrime
  · intro P hP
    exact (hp P hP).squarefree

theorem fixedBadPrimes_dvd_commonMaskIdeal (D P : Ideal O) (hP : P ∈ fixedBadPrimes) :
    P ∣ commonMaskIdeal D := by
  apply Finset.dvd_prod_of_mem
  exact Finset.mem_union_left _ hP

theorem coprimeSquarefreeRange_subset_idealRange (G : Ideal O)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) (K : ℝ) :
    coprimeSquarefreeRange G K ⊆ idealRange K := by
  intro H hH
  obtain ⟨hHs, hc⟩ := Finset.mem_filter.mp hH
  obtain ⟨hsf, hN⟩ := mem_squarefreeIdealRange.mp hHs
  exact mem_idealRange.mpr ⟨admissible_of_squarefree_coprime_bad H G hsf hc hbad, hN⟩

theorem commonMaskIdeal_eq_fixed_mul (D : Ideal O) (hD : Admissible D) :
    commonMaskIdeal D = (∏ P ∈ fixedBadPrimes, P) * D := by
  have hd : Disjoint fixedBadPrimes (IdealMobiusDivisorSum.primeSupport D) := by
    apply Finset.disjoint_left.mpr
    intro P hp hP
    have hfac := Multiset.mem_toFinset.mp hP
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hfac
    let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
    exact (prime_good_iff_not_bad P).mp (hD.2.2 P hfac) hp
  change (∏ P ∈ fixedBadPrimes ∪ IdealMobiusDivisorSum.primeSupport D, P) = _
  rw [Finset.prod_union hd, squarefree_support_product_self hD.2.1]

theorem commonMaskIdeal_norm (D : Ideal O) (hD : Admissible D) :
    Ideal.absNorm (commonMaskIdeal D) = Ideal.absNorm (∏ P ∈ fixedBadPrimes, P) * Ideal.absNorm D := by
  rw [commonMaskIdeal_eq_fixed_mul D hD, map_mul]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SmoothSummands
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ)^(divisorDyadicLabel N D).val/2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^(divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dif_pos ⟨hD,hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

theorem sum_divisorDyadicBins {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (N : ℝ) (f : Ideal O → A) :
    (∑ D ∈ S, f D) = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j, f D := by
  simp only [divisorDyadicBin,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  simp

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.LatticeEnvelopes
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

open scoped BigOperators Classical SchwartzMap

namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT

theorem nonzeroLatticeEnvelopeConstant_nonneg :
    0 ≤ nonzeroLatticeEnvelopeConstant := by
  have := eisensteinCauchyMass_nonneg
  unfold nonzeroLatticeEnvelopeConstant
  positivity

end EisensteinSchwartzPoisson

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem originalMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ originalMiddleDecayConstant W :=
  (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

theorem dualMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ dualMiddleDecayConstant W :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem divisorExponentConstant_pos {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    0 < divisorExponentConstant h deltaLoss hδ := (h.divisor_pair deltaLoss hδ).choose_spec.1

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CuspIntegration
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_subtype_powerset_products (S : Finset (Ideal O)) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset S).powerset, f (∏ P ∈ E, P.val)) =
      ∑ E ∈ S.powerset, f (∏ P ∈ E, P) := by
  classical
  have hS : (Finset.univ : Finset S).image Subtype.val = S := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, exists_prop,
      exists_eq_right]
  conv_rhs => rw [← hS, Finset.powerset_image]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro E hE
    congr 1
    rw [Finset.prod_image]
    exact fun _ _ _ _ h => Subtype.val_injective h
  · exact fun _ _ _ _ h => Finset.image_injective Subtype.val_injective h

end

open ActualEisensteinCubic

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.RetainedDualBounds
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

open scoped BigOperators Classical
open ActualEisensteinCubic QuadraticSquarefreeKernel CompletedGauss

theorem highSquareParts_bounds (M K : ℝ) (hK : 0 < K) (A : Ideal O)
    (hA : A ∈ highSquareParts M K) :
    Supported A ∧ 1 ≤ (Ideal.absNorm A : ℝ) ∧
    (Ideal.absNorm A : ℝ) ≤ Real.sqrt (M/K) ∧
    1 ≤ M/(Ideal.absNorm A : ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨hs,hN,hlarge⟩ := mem_highKernelRange.mp hI
  have hparts := (supported_square_parts I).mp hs
  have hna : 1 ≤ (Ideal.absNorm (squarePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hparts.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hnb : 1 ≤ (Ideal.absNorm (squarefreePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hparts.2.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hprod : (Ideal.absNorm (squarePart I) : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) ≤ M := by
    have he : (Ideal.absNorm (squarePart I) : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) =
        (Ideal.absNorm I : ℝ) := by exact_mod_cast norm_decomposition I
    rwa [he]
  have hsquare : (Ideal.absNorm (squarePart I) : ℝ)^2 ≤ M/K := by
    apply (le_div_iff₀ hK).mpr
    exact (mul_le_mul_of_nonneg_left hlarge.le (sq_nonneg _)).trans hprod
  have hM : 0 ≤ M/K := (sq_nonneg _).trans hsquare
  have hroot : (Ideal.absNorm (squarePart I) : ℝ) ≤ Real.sqrt (M/K) := by
    nlinarith [Real.sq_sqrt hM,Real.sqrt_nonneg (M/K)]
  refine ⟨hparts.1,hna,hroot,?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (Ideal.absNorm (squarePart I) : ℝ)^2)).mpr
  nlinarith

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.HighKernelGeometry
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic

theorem finite_inverse_norm_square_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I ∈ S, I ≠ 0)
    (hH : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (∑ I ∈ S, 1/(Ideal.absNorm I : ℝ)^2) ≤ 1024 := by
  have hpos (I : Ideal O) (hI : I ∈ S) : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑ I ∈ divisorDyadicBin S H j, 1/(Ideal.absNorm I : ℝ)^2) ≤
        512 * (1/(2:ℝ))^j.val := by
    have hp : 0 < (2:ℝ)^j.val := by positivity
    have hone : 1 ≤ (2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card : ℝ) ≤ 128 * (2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I ∈ divisorDyadicBin S H j) :
        1/(Ideal.absNorm I : ℝ)^2 ≤ 4/((2:ℝ)^j.val)^2 := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      have hni : 0 < (Ideal.absNorm I : ℝ) := lt_of_lt_of_le (by norm_num) (hpos I hIS)
      apply (div_le_div_iff₀ (sq_pos_of_pos hni) (sq_pos_of_pos hp)).mpr
      nlinarith
    calc
      _ ≤ ∑ _I ∈ divisorDyadicBin S H j, 4/((2:ℝ)^j.val)^2 :=
        Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card : ℝ) * (4/((2:ℝ)^j.val)^2) := by simp
      _ ≤ (128 * (2:ℝ)^j.val) * (4/((2:ℝ)^j.val)^2) := by gcongr
      _ = 512 * (1/(2:ℝ))^j.val := by
        rw [div_pow,one_pow]
        field_simp
        ; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength H+1), 512 * (1/(2:ℝ))^j.val :=
      Finset.sum_le_sum (fun j _ => hbin j)
    _ = 512 * ∑ j ∈ Finset.range (columnDyadicLength H+1), (1/(2:ℝ))^j := by
      rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range]
    _ ≤ 512 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by norm_num)
    _ = 1024 := by norm_num

theorem highSquareParts_card_le (M K : ℝ) (_hM : 0 ≤ M) (hK : 0 < K) :
    ((highSquareParts M K).card : ℝ) ≤ 128 * Real.sqrt (M/K) := by
  by_cases hempty : highSquareParts M K = ∅
  · simp only [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  · obtain ⟨A,hA⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hb := highSquareParts_bounds M K hK A hA
    apply DescentFiberCost.finite_ideal_count_real _ _ (hb.2.1.trans hb.2.2.1)
    · intro I hI
      exact (highSquareParts_bounds M K hK I hI).1.1
    · intro I hI
      exact (highSquareParts_bounds M K hK I hI).2.2.1

theorem HasSieveExponent.high_kernel {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ K →
      highKernelNorm M N K ≤ C * (M*N)^ε * (M + Real.sqrt (M/K)*N^α) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := h ε hε
  refine ⟨1024*C,by positivity,?_⟩
  intro M N K hM hN hK
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hK0 : 0 < K := by linarith
  let S := highSquareParts M K
  have hrow (A : Ideal O) (hA : A ∈ S) :
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N ≤
        C*(M*N)^ε*(M/(Ideal.absNorm A : ℝ)^2 + N^α) := by
    have hb := highSquareParts_bounds M K hK0 A hA
    have hquot : M/(Ideal.absNorm A : ℝ)^2 ≤ M :=
      div_le_self hM0 (by nlinarith [sq_nonneg ((Ideal.absNorm A : ℝ)-1)])
    apply (hbound _ N hb.2.2.2 hN).trans
    gcongr
  have hsum : (∑ A ∈ S, 1/(Ideal.absNorm A : ℝ)^2) ≤ 1024 := by
    apply finite_inverse_norm_square_sum S (Real.sqrt (M/K))
    · intro A hA
      exact (highSquareParts_bounds M K hK0 A hA).1.1
    · intro A hA
      exact (highSquareParts_bounds M K hK0 A hA).2.2.1
  have hcard : (S.card : ℝ) ≤ 128*Real.sqrt (M/K) := highSquareParts_card_le M K hM0 hK0
  have hcoeff : 0 ≤ C*(M*N)^ε := by positivity
  have hpow : 0 ≤ N^α := Real.rpow_nonneg hN0 _
  calc
    _ ≤ ∑ A ∈ S, sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N :=
      highKernelNorm_le_squarePart_sum M N K
    _ ≤ ∑ A ∈ S, C*(M*N)^ε*(M/(Ideal.absNorm A : ℝ)^2+N^α) :=
      Finset.sum_le_sum hrow
    _ = C*(M*N)^ε*(M*(∑ A ∈ S, 1/(Ideal.absNorm A : ℝ)^2)+(S.card:ℝ)*N^α) := by
      simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ C*(M*N)^ε*(M*1024+(128*Real.sqrt (M/K))*N^α) := by gcongr
    _ ≤ (1024*C)*(M*N)^ε*(M+Real.sqrt (M/K)*N^α) := by
      have hroot : 0 ≤ Real.sqrt (M/K)*N^α := mul_nonneg (Real.sqrt_nonneg _) hpow
      nlinarith [mul_nonneg hcoeff hroot]

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.PrincipalDensity
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem idealZeroMask_generator_eq_one (I G : Ideal O) (hcop : IsCoprime I G) :
    idealZeroMask I (idealGenerator G) = 1 := by
  apply if_neg
  rintro ⟨P,hP,hgen⟩
  have hPG : P ∣ G := by
    apply Ideal.dvd_iff_le.mpr
    rw [← span_idealGenerator G]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgen)
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor P hP).not_isUnit
    (hcop.isRelPrime (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP) hPG)

end

open ActualEisensteinCubic

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CuspCoercivity
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

open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex IdealMobiusDivisorSum

theorem commonMaskIdeal_primeSupport (D : Ideal O) :
    IdealMobiusDivisorSum.primeSupport (commonMaskIdeal D) = gcdMaskPrimes D := by
  have hp : ∀ P ∈ (gcdMaskPrimes D).val, Prime P := by
    intro P hP
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P,hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have hf : UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) = (gcdMaskPrimes D).val := by
    simpa [commonMaskIdeal] using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp
  rw [IdealMobiusDivisorSum.primeSupport,hf,Finset.val_toFinset]

theorem commonMask_subset_sum_eq_divisors (D : Ideal O) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      f (∏ P ∈ E, P.val)) = ∑ q ∈ idealDivisors (commonMaskIdeal D), f q := by
  rw [sum_subtype_powerset_products,← commonMaskIdeal_primeSupport D]
  exact (squarefree_divisor_sum_eq_support _ (commonMaskIdeal_squarefree D) f).symm

theorem primaryProduct_norm (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖ =
      Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hs : ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2 =
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ) := by
    rw [map_mul,norm_mul,mul_pow,
      primaryGenerator_norm_sq I (supported_primaryGenerator_ne_zero I (admissible_supported hI)),
      primaryGenerator_norm_sq J (supported_primaryGenerator_ne_zero J (admissible_supported hJ))]
  rw [← hs,Real.sqrt_sq (norm_nonneg _)]

theorem originalPairIdealDualKernel_eq_divisors
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (W : ℝ → ℂ) (M : ℝ) :
    originalPairIdealDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  let Q := idealQuotient D I
  let T := idealQuotient D J
  have hQ : Admissible Q := admissible_idealQuotient hI hDI
  have hT : Admissible T := admissible_idealQuotient hJ hDJ
  have hn := primaryProduct_norm Q T hQ hT
  have hnonneg : 0 ≤ (Ideal.absNorm Q:ℝ)*(Ideal.absNorm T:ℝ) := by positivity
  unfold originalPairIdealDualKernel maskedPairIdealDualKernel
  change ((M:ℂ)/(‖eisEmbedding (primaryGenerator Q*primaryGenerator T)‖:ℂ))*_ =
    ((M:ℂ)/(Real.sqrt ((Ideal.absNorm Q:ℝ)*(Ideal.absNorm T:ℝ)):ℂ))*_
  rw [hn]
  congr 1
  rw [← commonMask_subset_sum_eq_divisors D]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Real.sq_sqrt hnonneg,primeSubsetGenerator,unrestrictedPairCharacter,
    idealGenerator_norm_sq,Complex.ofReal_natCast]
  congr 1
  apply tsum_congr
  intro B
  congr 2
  ring

theorem originalPairDualKernel_eq_divisors
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (hray : columnRay I=columnRay J)
    (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0<M) :
    originalPairDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  rw [originalPairDualKernel_eq_ideal D I J hI hJ hDI hDJ hIJ hray W M hM]
  exact originalPairIdealDualKernel_eq_divisors D I J hI hJ hDI hDJ W M

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CommonMasks
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex IdealMobiusDivisorSum

theorem maskedPairIdealDualKernel_retained
    (G I J : Ideal O) (hG : G ≠ 0) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I=columnRay J) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    maskedPairIdealDualKernel G I J W M =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q*
        retainedDualPair I J (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K) +
      maskedPairDualTail G I J W M K := by
  have hNI : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNJ : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hJ.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hqpos (q : Ideal O) (hq : q ∈ idealDivisors G) : 0<(Ideal.absNorm q:ℝ) := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hpoint (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
        (((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
          ∑' B : NonzeroIdeal, unrestrictedPairCharacter I J B.val*paperRadialFourier W
            ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ))) =
        (UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q*
          retainedDualPair I J (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K +
        ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
          (((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
            dualSquarefreeTail I J W
              (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K) := by
    have hqN := hqpos q hq
    have ht : 0 < M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
      positivity
    rw [dual_ideal_low_add_tail I J W _ K ht,dualSquarefreeLow_principal_finite I J hI hJ hray W _ K ht,
      mul_add,mul_add]
    congr 1
    simp only [retainedDualPair,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    have hB : 0<(Ideal.absNorm B.val:ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr
        (fun hz => (mem_squarefreeIdealRange.mp B.property).1.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
    have harg : (1:ℝ)/((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ)) =
        (Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)/(M*(Ideal.absNorm B.val:ℝ)) := by
      field_simp
    rw [harg]
    push_cast
    ring
  unfold maskedPairIdealDualKernel maskedPairDualTail
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hpoint

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem retainedDualPrincipalSum_pair_expansion {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M F K : ℝ) :
    retainedDualPrincipalSum W (fun I : squarefreeIdealRange K => I.val) cols a M F =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (a j)*a k*retainedDualPair (cols j) (cols k) W M F K else 0 := by
  unfold retainedDualPrincipalSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [unrestrictedPairTerm,retainedDualPair,hc,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    ring
  · simp only [unrestrictedPairTerm,hc,ite_false,zero_mul,Finset.sum_const_zero]

theorem retainedDualPrincipalSum_twist_expansion {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M F K : ℝ) (q : Ideal O)
    (hcols : ∀ j, Admissible (cols j)) :
    retainedDualPrincipalSum W (fun I : squarefreeIdealRange K => I.val) cols
      (fun j => a j*quadraticRow (cols j) (idealGenerator q)) M F =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (a j)*a k*unrestrictedPairCharacter (cols j) (cols k) q*
          retainedDualPair (cols j) (cols k) W M F K else 0 := by
  rw [retainedDualPrincipalSum_pair_expansion]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [hc,ite_true,star_mul,canonical_quadraticRow_star _ (hcols j),unrestrictedPairCharacter]
    ring
  · simp only [hc,ite_false]

theorem maskedDualFamily_retained {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G ≠ 0) (cols : n → Ideal O) (a : n → ℂ)
    (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k)) :
    maskedDualFamily G cols a W M =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
          (fun I : squarefreeIdealRange K => I.val) cols
          (fun j => a j*quadraticRow (cols j) (idealGenerator q)) M (Ideal.absNorm q:ℝ)) +
      maskedDualTailFamily G cols a W M K := by
  have hp (j k : n) :
      (if IsCoprime (cols j) (cols k) then
        star (a j)*a k*maskedPairIdealDualKernel G (cols j) (cols k) W M else 0) =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        (if IsCoprime (cols j) (cols k) then
          star (a j)*a k*unrestrictedPairCharacter (cols j) (cols k) q*
            retainedDualPair (cols j) (cols k) (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K
          else 0)) +
      (if IsCoprime (cols j) (cols k) then
        star (a j)*a k*maskedPairDualTail G (cols j) (cols k) W M K else 0) := by
    by_cases hc : IsCoprime (cols j) (cols k)
    · simp only [hc,ite_true,maskedPairIdealDualKernel_retained G (cols j) (cols k)
        hG (hcols j) (hcols k) (hray j k) W M K hM,mul_add,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      ring
    · simp only [hc,ite_false,mul_zero,Finset.sum_const_zero,add_zero]
  simp only [maskedDualFamily,hp,Finset.sum_add_distrib,maskedDualTailFamily]
  congr 1
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [retainedDualPrincipalSum_twist_expansion _ cols a _ _ _ q hcols]
  simp only [Finset.mul_sum]

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

theorem normalizedFactors_commonMaskIdeal (D : Ideal O) :
    UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) = (gcdMaskPrimes D).val := by
  have hp (P : Ideal O) (hP : P∈(gcdMaskPrimes D).val) : Prime P := by
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P,hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have h := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp
  simpa only [commonMaskIdeal,Finset.prod_val,id_eq] using h

theorem idealZeroMask_commonMaskIdeal (D : Ideal O) (z : O) :
    idealZeroMask (commonMaskIdeal D) z =
      rowCoprimeMask (fun P : gcdMaskPrimes D => P.val) Finset.univ z := by
  classical
  simp only [idealZeroMask,normalizedFactors_commonMaskIdeal,rowCoprimeMask,
    Finset.mem_univ,true_and,Subtype.exists,exists_prop,Finset.mem_val]

lemma idealZeroMask_idempotent (D : Ideal O) (z : O) :
    idealZeroMask D z*idealZeroMask D z=idealZeroMask D z := by
  classical
  unfold idealZeroMask
  split_ifs <;> norm_num

theorem idealZeroMask_generator_eq_indicator (D B : Ideal O) (hD : D≠0) :
    idealZeroMask D (idealGenerator B) = if IsCoprime B D then 1 else 0 := by
  classical
  by_cases hc : IsCoprime B D
  · rw [if_pos hc,idealZeroMask_generator_eq_one D B hc.symm]
  · rw [if_neg hc]
    apply if_pos
    by_contra hn
    apply hc
    apply IsCoprime.symm
    apply ideals_coprime_of_relprime
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hD).mpr
    intro P hPD hPB hp
    have hfac : P∈UniqueFactorizationMonoid.normalizedFactors D :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hD).mpr ⟨hp,hPD⟩
    have hgen : idealGenerator B∈P := by
      apply (Ideal.span_singleton_le_iff_mem P).mp
      rw [span_idealGenerator]
      exact Ideal.dvd_iff_le.mp hPB
    exact hn ⟨P,hfac,hgen⟩

theorem idealZeroMask_primary_eq_indicator (D B : Ideal O) (hD : D≠0) (hB : Supported B) :
    idealZeroMask D (primaryGenerator B) = if IsCoprime B D then 1 else 0 := by
  have he : Ideal.span {primaryGenerator B}=Ideal.span {idealGenerator B} := by
    rw [(primaryGenerator_spec B (supported_primaryGenerator_ne_zero B hB)).1,span_idealGenerator]
  rw [idealZeroMask_span_eq D _ _ he,idealZeroMask_generator_eq_indicator D B hD]

theorem commonMask_primary_indicator (D B : Ideal O) (hB : Supported B) :
    idealZeroMask D (primaryGenerator B) = if IsCoprime B (commonMaskIdeal D) then 1 else 0 := by
  have he := idealZeroMask_commonMaskIdeal D (primaryGenerator B)
  rw [gcdMaskPrimes_mask,badPrime_mask_primaryGenerator,if_pos hB,one_mul] at he
  rw [←he,idealZeroMask_primary_eq_indicator _ B (commonMaskIdeal_squarefree D).ne_zero hB]

theorem residual_joint_mask (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (z : O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I*J) => P.val) Finset.univ z =
      rowCoprimeMask (fun P : primePool {commonMaskIdeal D*(idealQuotient D I*idealQuotient D J)} => P.val)
        Finset.univ z := by
  have hD := admissible_of_dvd hI hDI
  have hIq := admissible_idealQuotient hI hDI
  have hJq := admissible_idealQuotient hJ hDJ
  have hi : idealZeroMask I z=idealZeroMask D z*idealZeroMask (idealQuotient D I) z := by
    calc
      _ = idealZeroMask (D*idealQuotient D I) z := congrArg (fun A => idealZeroMask A z) (idealQuotient_mul hDI).symm
      _ = _ := idealZeroMask_mul D _ hD.1 hIq.1 z
  have hj : idealZeroMask J z=idealZeroMask D z*idealZeroMask (idealQuotient D J) z := by
    calc
      _ = idealZeroMask (D*idealQuotient D J) z := congrArg (fun A => idealZeroMask A z) (idealQuotient_mul hDJ).symm
      _ = _ := idealZeroMask_mul D _ hD.1 hJq.1 z
  rw [gcdMaskPrimes_mask,singleton_rowCoprimeMask_eq_idealZeroMask,
    idealZeroMask_mul I J hI.1 hJ.1,
    idealZeroMask_mul (commonMaskIdeal D) _ (commonMaskIdeal_squarefree D).ne_zero (mul_ne_zero hIq.1 hJq.1),
    idealZeroMask_mul _ _ hIq.1 hJq.1,idealZeroMask_commonMaskIdeal,gcdMaskPrimes_mask,hi,hj]
  calc
    _ = (rowCoprimeMask badPrime Finset.univ z)*(idealZeroMask D z*idealZeroMask D z)*
      (idealZeroMask (idealQuotient D I) z*idealZeroMask (idealQuotient D J) z) := by ring
    _ = _ := by rw [idealZeroMask_idempotent]

theorem lowPrincipalLattice_residual (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (W : 𝓢(ℝ,ℂ)) (X : ℝ) :
    lowPrincipalLattice I J W X =
      ∑' z : O, rowCoprimeMask
        (fun P : primePool {commonMaskIdeal D*(idealQuotient D I*idealQuotient D J)} => P.val) Finset.univ z *
        (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/X)) := by
  unfold lowPrincipalLattice
  apply tsum_congr
  intro z
  by_cases hz : z=0
  · subst z
    simp only [jointMask_zero,ite_true,mul_zero,zero_mul]
  · rw [if_neg hz,quadraticSquareProfile_apply,residual_joint_mask D I J hI hJ hDI hDJ]

theorem idealRange_filter_coprime (G : Ideal O) (K : ℝ)
    (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    (idealRange K).filter (fun B => IsCoprime B G)=coprimeSquarefreeRange G K := by
  classical
  ext B
  constructor
  · intro h
    obtain ⟨hb,hc⟩ := Finset.mem_filter.mp h
    have hB := mem_idealRange.mp hb
    exact Finset.mem_filter.mpr ⟨mem_squarefreeIdealRange.mpr ⟨hB.1.2.1,hB.2⟩,hc⟩
  · intro h
    refine Finset.mem_filter.mpr ⟨?_,(Finset.mem_filter.mp h).2⟩
    exact coprimeSquarefreeRange_subset_idealRange G hbad K h

theorem sum_idealRange_coprime (G : Ideal O) (K : ℝ)
    (hbad : ∀ P∈fixedBadPrimes, P∣G) (f : Ideal O → ℂ) :
    (∑ B : idealRange K, if IsCoprime B.val G then f B.val else 0) =
      ∑ B : coprimeSquarefreeRange G K, f B.val := by
  classical
  rw [Finset.sum_coe_sort (idealRange K) (fun B => if IsCoprime B G then f B else 0),
    ←Finset.sum_filter,idealRange_filter_coprime G K hbad,
    Finset.sum_coe_sort (coprimeSquarefreeRange G K) f]

theorem originalPairLow_residual_finite (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      (6:ℂ)⁻¹*∑ B : coprimeSquarefreeRange (commonMaskIdeal D) K,
        pairMaskedSquareSource (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M B.val := by
  classical
  rw [originalPairLow_principal_finite I J hI hJ W M K hM]
  have ht (B : idealRange K) :
      (quadraticRow I (primaryGenerator B.val)*quadraticRow J (primaryGenerator B.val))*
        ((6:ℂ)⁻¹*lowPrincipalLattice I J W (Real.sqrt (M/(Ideal.absNorm B.val:ℝ)))) =
      (6:ℂ)⁻¹*(if IsCoprime B.val (commonMaskIdeal D) then
        pairMaskedSquareSource (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M B.val else 0) := by
    have hB := admissible_supported (mem_idealRange.mp B.property).1
    have hp := canonical_pair_divisor_mask D I J hI hJ hDI hDJ (primaryGenerator B.val)
    rw [canonical_quadraticRow_star I hI,commonMask_primary_indicator D B.val hB] at hp
    rw [hp,lowPrincipalLattice_residual D I J hI hJ hDI hDJ]
    by_cases hc : IsCoprime B.val (commonMaskIdeal D)
    · simp only [hc,ite_true,one_mul,pairMaskedSquareSource,sourcePrincipalScale]
      ring
    · simp only [hc,ite_false,zero_mul,mul_zero]
  simp_rw [ht]
  rw [←Finset.mul_sum,sum_idealRange_coprime (commonMaskIdeal D) K
    (fun P hP => fixedBadPrimes_dvd_commonMaskIdeal D P hP)]

theorem originalLow_gcd_aggregate
    {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) =
      (6:ℂ)⁻¹ * maskedPrincipalSourceSum (commonMaskIdeal D) (quadraticSquareProfile W)
        (fun B : coprimeSquarefreeRange (commonMaskIdeal D) K => B.val)
        (fun j => idealQuotient D (cols j)) a M := by
  classical
  let S := coprimeSquarefreeRange (commonMaskIdeal D) K
  let q := fun j => idealQuotient D (cols j)
  have hq (j : n) : Admissible (q j) := admissible_idealQuotient (hcols j) (hdiv j)
  have ht (j k : n) :
      (if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) =
      (6:ℂ)⁻¹ * ∑ B : S,
        originalTerm (fun B : S => B.val) q q a a 1 1 B j k *
          ∑' z : O, rowCoprimeMask (fun P : primePool {commonMaskIdeal D*(q j*q k)} => P.val) Finset.univ z *
            (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/sourcePrincipalScale M B.val)) := by
    have heq := gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD (hdiv j) (hdiv k)
    by_cases hc : IsCoprime (q j) (q k)
    · rw [if_pos (heq.mpr hc),originalPairLow_residual_finite D _ _ (hcols j) (hcols k) (hdiv j) (hdiv k) W M K hM]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      simp only [originalTerm,hc,ite_true,one_dvd,pairMaskedSquareSource,star_mul,
        canonical_quadraticRow_star _ (hq j)]
      dsimp only [q]
      ring
    · have hg : ¬gcd (cols j) (cols k)=D := fun h => hc (heq.mp h)
      simp only [hg,ite_false,originalTerm,hc,Finset.sum_const_zero,zero_mul,mul_zero]
  simp_rw [ht,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ:Finset n)) (t := (Finset.univ:Finset S))]
  simp only [maskedPrincipalSourceSum,Finset.mul_sum,S,q,sourcePrincipalScale]

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem originalDual_gcd_aggregate {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (hproper : ∀ j, cols j≠D)
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*originalPairDualKernel D (cols j) (cols k) W M else 0) =
      maskedDualFamily (commonMaskIdeal D) (fun j => idealQuotient D (cols j)) a W M := by
  unfold maskedDualFamily
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have heq := gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD (hdiv j) (hdiv k)
  by_cases hg : gcd (cols j) (cols k)=D
  · have hneq : cols j≠cols k := by
      intro h
      rw [← h] at hg
      exact hproper j (by simpa using hg)
    rw [if_pos hg,if_pos (heq.mp hg),
      originalPairDualKernel_eq_divisors D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) hneq (hray j k) W M hM]
  · rw [if_neg hg,if_neg (fun hc => hg (heq.mpr hc))]

theorem originalHigh_gcd_principal_assembly {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (hproper : ∀ j, cols j≠D)
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
      (∑ q ∈ idealDivisors (commonMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*
        retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
          (fun I : squarefreeIdealRange K => I.val) (fun j => idealQuotient D (cols j))
          (fun j => a j*quadraticRow (idealQuotient D (cols j)) (idealGenerator q)) M (Ideal.absNorm q:ℝ)) +
      maskedDualTailFamily (commonMaskIdeal D) (fun j => idealQuotient D (cols j)) a W M K -
      (6:ℂ)⁻¹ * maskedPrincipalSourceSum (commonMaskIdeal D) (quadraticSquareProfile W)
        (fun B : coprimeSquarefreeRange (commonMaskIdeal D) K => B.val)
        (fun j => idealQuotient D (cols j)) a M := by
  have hsplit :
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*originalPairDualKernel D (cols j) (cols k) W M else 0) -
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hg : gcd (cols j) (cols k)=D
    · rw [if_pos hg,if_pos hg,if_pos hg,
        originalPairHigh_eq_source_sub_low (cols j) (cols k) W M K hM,
        originalPairSource_poisson D (cols j) (cols k) (hcols j) (hcols k) hg (hray j k) W M hM]
      ring
    · simp only [hg,ite_false,sub_self]
  rw [hsplit,originalDual_gcd_aggregate D hD cols hcols hdiv hproper hray a W M hM,
    originalLow_gcd_aggregate D hD cols hcols hdiv a W M K hM,
    maskedDualFamily_retained _ (commonMaskIdeal_squarefree D).ne_zero _ a W M K hM
      (fun j => admissible_idealQuotient (hcols j) (hdiv j))
      (fun j k => columnRay_idealQuotient_eq D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) (hray j k))]

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem residual_commonMask_coprime (D I : Ideal O) (hI : Admissible I) (hDI : D∣I) :
    IsCoprime (commonMaskIdeal D) (idealQuotient D I) := by
  have hD := admissible_of_dvd hI hDI
  have hQ := admissible_idealQuotient hI hDI
  have hs : Squarefree (D*idealQuotient D I) := by rw [idealQuotient_mul hDI]; exact hI.2.1
  have hrel := (squarefree_mul_iff.mp hs).1
  have hG := (commonMaskIdeal_squarefree D).ne_zero
  apply ideals_coprime_of_relprime
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hG).mpr
  intro P hPG hPQ hp
  have hf : P∈UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hG).mpr ⟨hp,hPG⟩
  rw [normalizedFactors_commonMaskIdeal] at hf
  have hmem : P∈fixedBadPrimes ∨ P∈primeSupport D := Finset.mem_union.mp hf
  rcases hmem with hbad | hPD
  · let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hfac : P∈UniqueFactorizationMonoid.normalizedFactors (idealQuotient D I) :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.1).mpr ⟨hp,hPQ⟩
    exact (prime_good_iff_not_bad P).mp (hQ.2.2 P hfac) hbad
  · have hd : P∣D := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPD)
    exact hp.not_isUnit (hrel hd hPQ)

theorem idealQuotient_norm_eq (D I : Ideal O) (hD : D≠0) (hDI : D∣I) :
    (Ideal.absNorm (idealQuotient D I):ℝ)=(Ideal.absNorm I:ℝ)/(Ideal.absNorm D:ℝ) := by
  have hn : (Ideal.absNorm D:ℝ)≠0 := by
    exact_mod_cast (show Ideal.absNorm D≠0 from fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  apply (eq_div_iff hn).mpr
  rw [mul_comm,←Nat.cast_mul,←map_mul,idealQuotient_mul hDI]

theorem idealQuotient_shell (D I : Ideal O) (hD : D≠0) (hDI : D∣I) (N : ℝ)
    (hI : N/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤N) :
    (N/(Ideal.absNorm D:ℝ))/2≤(Ideal.absNorm (idealQuotient D I):ℝ) ∧
      (Ideal.absNorm (idealQuotient D I):ℝ)≤N/(Ideal.absNorm D:ℝ) := by
  have hn : 0<(Ideal.absNorm D:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  rw [idealQuotient_norm_eq D I hD hDI]
  constructor
  · calc
      _ = (N/2)/(Ideal.absNorm D:ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hI.1 hn.le
  · exact div_le_div_of_nonneg_right hI.2 hn.le

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem mem_gcdRaySupport {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (j : n) :
    j∈gcdRaySupport cols a D c ↔ D∣cols j ∧ columnRay (cols j)=c ∧ a j≠0 := by
  simp only [gcdRaySupport,Finset.mem_filter,Finset.mem_univ,true_and]

theorem gcd_ray_pair_sum_restrict {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O)
    (c : EisensteinEPrimaryPhase.Coord) (H : n → n → ℂ) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D ∧ columnRay (cols j)=c ∧ columnRay (cols k)=c
      then star (a j)*a k*H j k else 0) =
    ∑ j : gcdRaySupport cols a D c, ∑ k : gcdRaySupport cols a D c,
      if gcd (cols j.val) (cols k.val)=D then star (a j.val)*a k.val*H j.val k.val else 0 := by
  classical
  let S := gcdRaySupport cols a D c
  let f := fun j k => if gcd (cols j) (cols k)=D ∧ columnRay (cols j)=c ∧ columnRay (cols k)=c
    then star (a j)*a k*H j k else 0
  have hjzero (j : n) (hj : j∉S) (k : n) : f j k=0 := by
    dsimp only [f]
    split_ifs with h
    · have hz : a j=0 := by
        by_contra hn
        apply hj
        exact (mem_gcdRaySupport cols a D c j).mpr
          ⟨h.1 ▸ GCDMonoid.gcd_dvd_left (cols j) (cols k),h.2.1,hn⟩
      simp only [hz,star_zero,zero_mul]
    · rfl
  have hkzero (k : n) (hk : k∉S) (j : n) : f j k=0 := by
    dsimp only [f]
    split_ifs with h
    · have hz : a k=0 := by
        by_contra hn
        apply hk
        exact (mem_gcdRaySupport cols a D c k).mpr
          ⟨h.1 ▸ GCDMonoid.gcd_dvd_right (cols j) (cols k),h.2.2,hn⟩
      simp only [hz,mul_zero,zero_mul]
    · rfl
  have hleft : (∑ j∈S, ∑ k, f j k) = ∑ j, ∑ k, f j k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j _ hj
    exact Finset.sum_eq_zero (fun k _ => hjzero j hj k)
  change (∑ j, ∑ k, f j k)=_
  rw [←hleft,←Finset.sum_coe_sort S (fun j => ∑ k, f j k)]
  apply Finset.sum_congr rfl
  intro j _
  have hright : (∑ k∈S, f j.val k) = ∑ k, f j.val k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro k _ hk
    exact hkzero k hk j.val
  rw [←hright,←Finset.sum_coe_sort S (fun k => f j.val k)]
  apply Finset.sum_congr rfl
  intro k _
  have hj := (mem_gcdRaySupport cols a D c j.val).mp j.property
  have hk := (mem_gcdRaySupport cols a D c k.val).mp k.property
  simp only [f,hj.2.1,hk.2.1,and_true]

theorem gcdRaySupport_quotient_properties (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (hD : D≠0)
    (c : EisensteinEPrimaryPhase.Coord) :
    let cols := fun j : gcdRaySupport (fun I : idealRange N => I.val) a D c =>
      idealQuotient D j.val.val
    Function.Injective cols ∧
    (∀ j, Admissible (cols j) ∧
      (X/(Ideal.absNorm D:ℝ))/2≤(Ideal.absNorm (cols j):ℝ) ∧
      (Ideal.absNorm (cols j):ℝ)≤X/(Ideal.absNorm D:ℝ) ∧
      IsCoprime (commonMaskIdeal D) (cols j)) ∧
    (∀ j k, columnRay (cols j)=columnRay (cols k)) := by
  dsimp only
  have hp (j : gcdRaySupport (fun I : idealRange N => I.val) a D c) :=
    (mem_gcdRaySupport (fun I : idealRange N => I.val) a D c j.val).mp j.property
  refine ⟨?_,?_,?_⟩
  · intro j k hjk
    apply Subtype.ext
    apply Subtype.ext
    exact idealQuotient_injective_on D (hp j).1 (hp k).1 hjk
  · intro j
    have hadm := (mem_idealRange.mp j.val.property).1
    have hshell := idealQuotient_shell D j.val.val hD (hp j).1 X
      ⟨(ha j.val (hp j).2.2).1.le,(ha j.val (hp j).2.2).2⟩
    exact ⟨admissible_idealQuotient hadm (hp j).1,hshell.1,hshell.2,
      residual_commonMask_coprime D j.val.val hadm (hp j).1⟩
  · intro j k
    exact columnRay_idealQuotient_eq D j.val.val k.val.val
      (mem_idealRange.mp j.val.property).1 (mem_idealRange.mp k.val.property).1
      (hp j).1 (hp k).1 ((hp j).2.1.trans (hp k).2.1.symm)

theorem gcdRaySupport_proper (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (hsmall : (Ideal.absNorm D:ℝ)≤X/2)
    (j : gcdRaySupport (fun I : idealRange N => I.val) a D c) : j.val.val≠D := by
  intro h
  have hp := (mem_gcdRaySupport (fun I : idealRange N => I.val) a D c j.val).mp j.property
  have hs := (ha j.val hp.2.2).1
  rw [h] at hs
  exact (not_lt_of_ge hsmall) hs

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonComparison
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

namespace CanonicalQuadraticSieve

section

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open DivisorBlockCauchy

theorem gcdRaySupport_energy_eq {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    (∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) =
      ∑j, if D∣cols j ∧ columnRay (cols j)=c then ‖a j‖^2 else 0 := by
  classical
  rw [Finset.sum_coe_sort (gcdRaySupport cols a D c) (fun j => ‖a j‖^2)]
  simp only [gcdRaySupport,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,ne_eq,not_true_eq_false,and_false,ite_self,zero_pow (by decide : 2≠0)]
  · simp only [hz,ne_eq,not_false_eq_true,and_true]

theorem gcdRaySupport_energy_ray_sum {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) =
      ∑j, ‖if D∣cols j then a j else 0‖^2 := by
  classical
  simp_rw [gcdRaySupport_energy_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd : D∣cols j
  · simp only [hd,true_and,ite_true]
    rw [Finset.sum_eq_single (columnRay (cols j))]
    · simp only [ite_true]
    · intro c hc hne
      exact if_neg (Ne.symm hne)
    · simp
  · simp only [hd,false_and,ite_false,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]

theorem gcdRaySupport_energy_divisor_sum {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (S : Finset (Ideal O)) (cols : n → Ideal O)
    (hcols : ∀j, cols j≠0) (a : n → ℂ) (X : ℝ)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j):ℝ)≤X) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
      ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) ≤
      (divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [gcdRaySupport_energy_ray_sum]
  apply (divisor_mask_energy S cols hcols a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero,le_refl]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 (cols j) (hcols j)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hX j hz) hε.le) (divisorConstant_pos ε hε).le

theorem gcdRaySupport_weighted_sum_bound {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (S : Finset (Ideal O)) (cols : n → Ideal O)
    (hcols : ∀j, cols j≠0) (a : n → ℂ) (X C : ℝ) (hC : 0≤C)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j):ℝ)≤X)
    (F : Ideal O → EisensteinEPrimaryPhase.Coord → ℝ)
    (hF : ∀D∈S, ∀c, F D c≤C*∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S, F D c) ≤
      C*(divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2 := by
  calc
    _ ≤ ∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
        C*∑j : gcdRaySupport cols a D c, ‖a j.val‖^2 :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun D hD => hF D hD c))
    _ = C*(∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
        ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) := by simp only [Finset.mul_sum]
    _ ≤ C*((divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left (gcdRaySupport_energy_divisor_sum ε hε S cols hcols a X hX) hC
    _ = _ := by ring

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

theorem divisorEnergyFactor_diagonal {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (N : ℝ) (a : n → ℂ) :
    divisorEnergyFactor ε hε N a a =
      (256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑j, ‖a j‖^2 := by
  unfold divisorEnergyFactor
  have hs : 0≤∑j, ‖a j‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [mul_assoc _ (Real.sqrt _) (Real.sqrt _),Real.mul_self_sqrt hs]

theorem poissonComparisonMajorant_energy_factor {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W =
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
        (fun _ : Unit => (1:ℂ)) W * ∑j, ‖a j‖^2 := by
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,mul_one]
  ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ArithmeticBins
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem originalHigh_gcd_eq_maskedPoissonDifference {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀j, Admissible (cols j))
    (hdiv : ∀j, D∣cols j) (hproper : ∀j, cols j≠D)
    (hray : ∀j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑j, ∑k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
    maskedPoissonDifference (commonMaskIdeal D) W (fun j => idealQuotient D (cols j)) a M K := by
  rw [originalHigh_gcd_principal_assembly D hD cols hcols hdiv hproper hray a W M K hM,
    maskedPoissonDifference,
    maskedDualFamily_retained _ (commonMaskIdeal_squarefree D).ne_zero _ a W M K hM
      (fun j => admissible_idealQuotient (hcols j) (hdiv j))
      (fun j k => columnRay_idealQuotient_eq D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) (hray j k))]

theorem annularRayGcdBlock_eq_active_difference (M N X K : ℝ) (hM : 0<M)
    (a : idealRange N → ℂ) (ha : CoefficientOnShell N X a)
    (D : Ideal O) (hD : D≠0) (hsmall : (Ideal.absNorm D:ℝ)≤X/2)
    (c : EisensteinEPrimaryPhase.Coord) :
    annularRayGcdBlock M N K D c a =
      maskedPoissonDifference (commonMaskIdeal D) QuadraticInitialBound.annularSieveCutoff
        (activeGcdColumns N a D c) (activeGcdCoefficient N a D c) M K := by
  classical
  rw [annularRayGcdBlock_eq_pair_high M N K hM D c a]
  simp only [rayPairCoefficient,ite_mul,zero_mul]
  rw [gcd_ray_pair_sum_restrict]
  let S := gcdRaySupport (fun I : idealRange N => I.val) a D c
  have hdiv (j : S) : D∣j.val.val :=
    ((mem_gcdRaySupport _ a D c j.val).mp j.property).1
  have hray (j k : S) : columnRay j.val.val=columnRay k.val.val := by
    have hj := ((mem_gcdRaySupport _ a D c j.val).mp j.property).2.1
    have hk := ((mem_gcdRaySupport _ a D c k.val).mp k.property).2.1
    exact hj.trans hk.symm
  exact originalHigh_gcd_eq_maskedPoissonDifference D hD
    (fun j : S => j.val.val) (fun j => (mem_idealRange.mp j.val.property).1) hdiv
    (gcdRaySupport_proper N X a ha D c hsmall) hray (fun j : S => a j.val)
    QuadraticInitialBound.annularSieveCutoff M K hM

theorem HasSieveExponent.annular_small_gcd_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ (ε : ℝ) (hε : 0<ε) (M N X K T : ℝ), 1≤M → 1≤K → 4≤T →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N X a →
      ∀ (D : Ideal O), D≠0 → (Ideal.absNorm D:ℝ)≤X/2 →
      ∀ (c : EisensteinEPrimaryPhase.Coord),
        ‖(6:ℂ)*annularRayGcdBlock M N K D c a‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
            (commonMaskIdeal D) K (X/(Ideal.absNorm D:ℝ)) M T
            (activeGcdCoefficient N a D c) QuadraticInitialBound.annularSieveCutoff := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hbound⟩ :=
    hexp.masked_poisson_complete hα deltaLoss hδ l A
  refine ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,?_⟩
  intro ε hε M N X K T hM hK hT a ha D hD hsmall c
  classical
  have hDn : 0<(Ideal.absNorm D:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤X/(Ideal.absNorm D:ℝ) := (le_div_iff₀ hDn).mpr (by linarith)
  have hp := gcdRaySupport_quotient_properties N X a ha D hD c
  rw [annularRayGcdBlock_eq_active_difference M N X K (by linarith) a ha D hD hsmall c]
  apply hbound ε hε (commonMaskIdeal D) (commonMaskIdeal_squarefree D)
    (fun P hP => fixedBadPrimes_dvd_commonMaskIdeal D P hP)
    K (X/(Ideal.absNorm D:ℝ)) M T hK hscale hM hT
    (activeGcdColumns N a D c) hp.1
    (fun j => ⟨(hp.2.1 j).1,(hp.2.1 j).2.1,(hp.2.1 j).2.2.1⟩)
    hp.2.2 (fun j => (hp.2.1 j).2.2.2) (activeGcdCoefficient N a D c)
    QuadraticInitialBound.annularSieveCutoff QuadraticInitialBound.annularSieveCutoff_zero

end

theorem selectedPoisson_radial_identity (C B M X q η : ℝ)
    (hM : 0<M) (hX : 0<X) (hq : 0<q) (hB : 0<B) :
    (M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η =
      selectedPoissonT C M X η*q/B := by
  unfold selectedPoissonK
  field_simp

theorem cutoff_middle_identity (M X T α : ℝ) (hM : 0<M) (hX : 0<X) (hT : 0<T) :
    T*Real.sqrt M*(T*X^2/M)^(α-1/2) =
      T^(α+1/2)*X^(2*α-1)*M^(1-α) := by
  rw [Real.div_rpow (by positivity : 0≤T*X^2) hM.le,
    Real.mul_rpow hT.le (sq_nonneg X),←Real.rpow_two,←Real.rpow_mul hX.le]
  have hx : 2*(α-1/2)=2*α-1 := by ring
  have hm : 1-α=1/2-(α-1/2) := by ring
  have ht : α+1/2=1+(α-1/2) := by ring
  have hmPow : M^(1-α)=M^(1/2:ℝ)/M^(α-1/2) := by
    calc
      _ = M^((1/2:ℝ)-(α-1/2)) := by rw [hm]
      _ = _ := Real.rpow_sub hM _ _
  have htPow : T^(α+1/2)=T*T^(α-1/2) := by
    calc
      _ = T^(1+(α-1/2)) := by rw [ht]
      _ = _ := by rw [Real.rpow_add hT,Real.rpow_one]
  rw [hx,hmPow,htPow,Real.sqrt_eq_rpow]
  ring

theorem selectedPoisson_middle_bound (C M X η α : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hη : 0≤η) (hα : α≤2) :
    selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) ≤
      4*C ^3*(M*X)^(3*η)*(X^(2*α-1)*M^(1-α)) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 0<M*X := by positivity
  have hP1 : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hP1 hη
  have hT : 1≤ selectedPoissonT C M X η := by unfold selectedPoissonT; nlinarith
  have hT0 : 0<selectedPoissonT C M X η := by linarith
  have hK0 : 0<selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have htwo : (2:ℝ)^(α-1/2)≤4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hp3 : ((M*X)^η)^3 = (M*X)^(3*η) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hP.le]
    congr 1
    ring
  have hT3 : (selectedPoissonT C M X η)^(α+1/2)≤C ^3*(M*X)^(3*η) := by
    calc
      _ ≤ (selectedPoissonT C M X η)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = C ^3*(M*X)^(3*η) := by norm_num only [selectedPoissonT,Real.rpow_ofNat,mul_pow,hp3]
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hK0.le]
  calc
    _ ≤ 4*(selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2)) := by
      have hh := mul_le_mul_of_nonneg_right htwo
        (show 0≤ selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) by positivity)
      nlinarith [hh]
    _ = 4*((selectedPoissonT C M X η)^(α+1/2)*X^(2*α-1)*M^(1-α)) := by
      rw [selectedPoissonK,cutoff_middle_identity M X _ α hM0 hX0 hT0]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hT3
        (show 0≤X^(2*α-1)*M^(1-α) by positivity)
      nlinarith [hh]

end CanonicalQuadraticSieve

open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.GlobalBinLoss
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

namespace CanonicalQuadraticSieve

theorem list_prod_le_power (xs : List ℝ) (U : ℝ) (hU : 0≤U)
    (hxs : ∀x∈xs, 0≤x ∧ x≤U) : xs.prod≤U^xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀y∈xs, 0≤y ∧ y≤U := fun y hy => hxs y (by simp [hy])
    simp only [List.prod_cons,List.length_cons,pow_succ]
    have hp : 0≤xs.prod := List.prod_nonneg (fun y hy => (ht y hy).1)
    exact (mul_le_mul hx.2 (ih ht) hp hU).trans_eq (mul_comm _ _)

theorem list_prod_budget (xs budget : List ℝ) (U : ℝ) (hU : 1≤U)
    (hbudget : ∀x∈budget, 0≤x ∧ x≤U) (hxs : ∀x∈xs, x∈budget) (hlen : xs.length≤8) :
    xs.prod≤U^8 := by
  apply (list_prod_le_power xs U (by linarith) (fun x hx => hbudget x (hxs x hx))).trans
  exact pow_le_pow_right₀ hU hlen

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

theorem poissonComparisonMajorant_unit_box
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T U S : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 0≤K) (hN : 0<N) (hM : 0≤M) (hT : 1≤T) (hU : 1≤U) (hS : 0≤S)
    (hbudget : ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp deltaLoss hδ ε hε G K N W, 0≤x ∧ x≤U)
    (hMS : M≤S) (hNS : N≤S) (hmid : T*Real.sqrt M*(2*K)^(α-1/2)≤S)
    (hpr : Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2)≤S)
    (hED : K*M/T^l≤S) (hES : K*N/T^l≤S)
    (htail : M/((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
      (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)≤S) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
      (fun _ : Unit => (1:ℂ)) W ≤ 262144*U^8*S := by
  have hh := poisson_nine_terms_box
    ((IdealMobiusDivisorSum.idealDivisors G).card:ℝ)
    (columnDyadicLength K+1:ℕ) (columnDyadicLength N+1:ℕ)
    (256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)
    (divisorExponentConstant hexp deltaLoss hδ*((2*K)*N)^deltaLoss)
    ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖
    ‖quadraticTransformedSquareProfile W 0‖
    (dualMiddleDecayConstant (quadraticTransformedSquareProfile W))
    ‖paperRadialFourier (quadraticSquareProfile W) 0‖
    (originalMiddleDecayConstant (quadraticSquareProfile W)) nonzeroLatticeEnvelopeConstant
    (supportConstant ε hε*(N*N)^ε*(CD*sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)))
    (supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε*(CS*sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)))
    (CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    (supportConstant ε hε*N^ε*CP*(K*N)^deltaLoss)
    M N T (Real.sqrt M*(2*K)^(α-1/2))
    (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))
    (K*M/T^l) (K*N/T^l)
    (M/((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*(1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))
    U S hU hS hbudget hM hN.le hT (by positivity) hMS hNS
    (by simpa only [mul_assoc] using hmid) ⟨by positivity,hpr⟩
    ⟨by positivity,hED⟩ ⟨by positivity,hES⟩ ⟨by positivity,htail⟩
  convert (preTransparency := .instances) hh using 1
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,
    mul_one,one_mul,div_one]
  field_simp
  ; ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularLifting
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open IdealCoprimeSieveOperator DivisorBlockCauchy

theorem gcdPool_admissible {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hcols : ∀j, Admissible (cols j)) (D : Ideal O) (hD : D∈gcdPool cols) : Admissible D := by
  obtain ⟨⟨j,k⟩,_,rfl⟩ := Finset.mem_image.mp hD
  exact admissible_of_dvd (hcols j) (GCDMonoid.gcd_dvd_left _ _)

theorem annularHighEnergy_gcd_reduction (M N K H : ℝ) (hN : 1≤N) (hH : 0<H)
    (ε : ℝ) (hε : 0<ε) (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ 16*((∑c : EisensteinEPrimaryPhase.Coord,
      ∑D∈(gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H),
        ‖annularRayGcdBlock M N K D c a‖) +
      highKernelNorm (2*M) (N/H) K*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by
  have h := highKernel_weighted_energy_ray_gcd_reduction ε hε H hH
    (fun I : highKernelRange (2*M) K => I.val) (fun J : idealRange N => J.val)
    Subtype.val_injective Subtype.val_injective (2*M) N K hN (fun I => I.property)
    (fun J => mem_idealRange.mp J.property) (fun I => annularHighWeight M I.val) 1 (by norm_num)
    (fun I => ⟨QuadraticInitialBound.annularSieveBump.nonneg,QuadraticInitialBound.annularSieveBump.le_one⟩) a
  simpa only [annularHighEnergy,annularRayGcdBlock,one_mul] using h

theorem HasSieveExponent.annular_energy_from_scalar_cost {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP CH : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧ 0<CH ∧
      ∀ (ε : ℝ) (hε : 0<ε) (M N K T H C : ℝ),
      1≤M → 1≤N → 1≤K → 4≤T → 0<H → H≤N/2 → 0≤C →
      (∀D∈gcdPool (fun J : idealRange N => J.val), (Ideal.absNorm D:ℝ)≤H →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
          (commonMaskIdeal D) K (N/(Ideal.absNorm D:ℝ)) M T
          (fun _ : Unit => (1:ℂ)) QuadraticInitialBound.annularSieveCutoff≤C) →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N K a ≤
        16*((C/6)*(divisorConstant ε hε*N^ε) +
          (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
            (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑J,‖a J‖^2 := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hsmall⟩ :=
    hexp.annular_small_gcd_complete hα deltaLoss hδ l A
  obtain ⟨CH,hCH,hhigh⟩ := hexp.high_kernel deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,?_⟩
  intro ε hε M N K T H C hM hN hK hT hH hHN hC hcost a ha
  classical
  let S := (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H)
  have hb (D : Ideal O) (hD : D∈S) (c : EisensteinEPrimaryPhase.Coord) :
      ‖annularRayGcdBlock M N K D c a‖ ≤
        (C/6)*∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 := by
    have hd := Finset.mem_filter.mp hD
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hd.1
    have hh := hsmall ε hε M N N K T hM hK hT a ha D hadm.1 (hd.2.trans hHN) c
    rw [poissonComparisonMajorant_energy_factor] at hh
    have hbound := mul_le_mul_of_nonneg_right (hcost D hd.1 hd.2)
      (show 0≤∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 by positivity)
    change _ ≤ C*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hbound
    have hn : ‖(6:ℂ)*annularRayGcdBlock M N K D c a‖=6*‖annularRayGcdBlock M N K D c a‖ := by
      rw [norm_mul]
      norm_num
    rw [hn] at hh
    change _≤_*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hh
    nlinarith
  have hs := gcdRaySupport_weighted_sum_bound ε hε S (fun J : idealRange N => J.val)
    (fun J => (mem_idealRange.mp J.property).1.1) a N (C/6) (by positivity)
    (fun J hJ => (mem_idealRange.mp J.property).2)
    (fun D c => ‖annularRayGcdBlock M N K D c a‖) hb
  have hNH : 1≤N/H := (le_div_iff₀ hH).mpr (by linarith)
  have hh := hhigh (2*M) (N/H) K (by linarith) hNH hK
  have hred := annularHighEnergy_gcd_reduction M N K H hN hH ε hε a
  apply hred.trans
  have hsupp := (supportConstant_pos ε hε).le
  have hdiv := (divisorConstant_pos ε hε).le
  calc
    _ ≤ 16*((C/6)*(divisorConstant ε hε*N^ε)*∑J,‖a J‖^2 +
      (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
        (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by
      gcongr
    _ = _ := by ring

end

open scoped BigOperators Classical

theorem largeGcdThreshold_quotient_power (α N : ℝ) (hα : α≠0) (hN : 0<N) :
    (N/largeGcdThreshold α N)^α=N := by
  have he : N/largeGcdThreshold α N=N^(1/α) := by
    rw [show 1/α=1-(1-1/α) by ring,Real.rpow_sub hN,Real.rpow_one]
    rfl
  rw [he,←Real.rpow_mul hN.le]
  field_simp
  rw [Real.rpow_one]

theorem largeGcdThreshold_bounds (α N : ℝ) (hα1 : 1≤α) (hα2 : α≤2) (hN : 4≤N) :
    1≤largeGcdThreshold α N ∧ largeGcdThreshold α N≤N/2 := by
  have hα : 0<α := by linarith
  have hN0 : 0<N := by linarith
  have ha : 0≤1-1/α := by
    have hi : 1/α≤1 := (div_le_one hα).mpr hα1
    linarith
  have hb : 1-1/α≤(1/2:ℝ) := by
    have hi : (1/2:ℝ)≤1/α := (le_div_iff₀ hα).mpr (by linarith)
    linarith
  refine ⟨Real.one_le_rpow (by linarith) ha,?_⟩
  calc
    largeGcdThreshold α N ≤ N^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hb
    _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
    _ ≤ N/2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩

theorem high_kernel_chosen_scale (M N K : ℝ) (hM : 0<M) (_hN : 0<N) (hK : 0<K)
    (hcut : N^2/M≤K) : Real.sqrt ((2*M)/K)*N≤2*M := by
  have hNK : N^2≤M*K := by
    have h := (div_le_iff₀ hM).mp hcut
    nlinarith
  let s := Real.sqrt ((2*M)/K)
  have hs0 : 0≤ s := Real.sqrt_nonneg _
  have hs : s^2*K=2*M := by
    dsimp only [s]
    rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ hK.ne']
  have hb : s^2*N^2≤2*M^2 := by
    calc
      _ ≤ s^2*(M*K) := mul_le_mul_of_nonneg_left hNK (sq_nonneg s)
      _ = (s^2*K)*M := by ring
      _ = _ := by rw [hs]; ring
  change s*N≤2*M
  nlinarith [sq_nonneg (s*N)]

theorem chosen_large_gcd_main (α M N K : ℝ) (hα : α≠0)
    (hM : 0<M) (hN : 0<N) (hK : 0<K) (hcut : N^2/M≤K) :
    2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α≤4*M := by
  rw [largeGcdThreshold_quotient_power α N hα hN]
  linarith [high_kernel_chosen_scale M N K hM hN hK hcut]

theorem chosen_large_gcd_full (α deltaLoss C M N K : ℝ) (hα1 : 1≤α) (hα2 : α≤2)
    (hδ : 0≤deltaLoss) (hC : 0≤C) (hM : 0<M) (hN : 4≤N) (hK : 0<K)
    (hcut : N^2/M≤K) :
    C*((2*M)*(N/largeGcdThreshold α N))^deltaLoss*
      (2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α) ≤
        (4*C*2^deltaLoss)*(M*N)^deltaLoss*M := by
  have hh := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hH : 0<largeGcdThreshold α N := by linarith
  have hN0 : 0<N := by linarith
  have hp : ((2*M)*(N/largeGcdThreshold α N))^deltaLoss≤(2*(M*N))^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ
    have hn := div_le_self hN0.le hh.1
    nlinarith
  have hm := chosen_large_gcd_main α M N K (by linarith) hM hN0 hK hcut
  calc
    _ ≤ C*(2*(M*N))^deltaLoss*(4*M) := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)]; ring

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonConstants
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

theorem list_exists_positive_bound (xs : List ℝ) :
    ∃ H : ℝ, 1≤H ∧ ∀x∈xs, x≤H := by
  induction xs with
  | nil => exact ⟨1,le_rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨H,hH,hxs⟩ := ih
    refine ⟨max H x, hH.trans (le_max_left _ _), ?_⟩
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact le_max_right _ _
    · exact (hxs y hy).trans (le_max_left _ _)

theorem poissonPrimitiveConstants_nonneg
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (D : ℝ) (hD : 0≤D) (W : 𝓢(ℝ,ℂ)) :
    ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, 0≤x := by
  intro x hx
  simp only [poissonPrimitiveConstants,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (divisorConstant_pos η hη).le
  · have : 0<Real.log 2 := Real.log_pos (by norm_num); positivity
  · norm_num
  · exact (supportConstant_pos η hη).le
  · exact (divisorExponentConstant_pos hexp η hη).le
  · positivity
  · positivity
  · exact dualMiddleDecayConstant_nonneg _
  · positivity
  · exact originalMiddleDecayConstant_nonneg _
  · exact nonzeroLatticeEnvelopeConstant_nonneg
  · exact hCD
  · exact hCS
  · exact hCT
  · exact hCP
  · positivity
  · positivity
  · positivity
  · exact Real.rpow_nonneg hD _

theorem poissonUnitBudget_power_envelope
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (G : Ideal O) (hG : G≠0) (K N P D H : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 1≤K) (hN : 1≤N) (hP : 1≤P) (hD : 1≤D) (hH : 1≤H)
    (hconst : ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, x≤H)
    (hscales : ∀x∈([(Ideal.absNorm G:ℝ), K,N,(2*K)*N,N*N,
      (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ), 0≤x ∧ x≤D*P^4) :
    ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp η hη η hη G K N W,
      0≤x ∧ x≤(H*P^(4*η))^8 := by
  let V := H*P^(4*η)
  have hP0 : 0<P := by linarith
  have hR : 1≤P^(4*η) := Real.one_le_rpow hP (by positivity)
  have hV : 1≤V := by dsimp [V]; nlinarith
  have hCV (x : ℝ)
      (hx : x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W) :
      0≤x ∧ x≤V := by
    refine ⟨poissonPrimitiveConstants_nonneg sD sS sT CD CS CT CP hCD hCS hCT hCP
      hexp η hη D (by linarith) W x hx, ?_⟩
    have hh := hconst x hx
    dsimp [V]
    nlinarith
  have hpow (x : ℝ)
      (hx : x∈([(Ideal.absNorm G:ℝ),K,N,(2*K)*N,N*N,
        (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ)) : 0≤x^η ∧ x^η≤V := by
    have hx0 := (hscales x hx).1
    refine ⟨Real.rpow_nonneg hx0 _, ?_⟩
    have hDpow : D^η≤H := hconst _ (by simp [poissonPrimitiveConstants])
    calc
      _ ≤ (D*P^4)^η := Real.rpow_le_rpow hx0 (hscales x hx).2 hη.le
      _ = D^η*P^(4*η) := by
        rw [Real.mul_rpow (by linarith : 0≤D) (by positivity : 0≤P^4)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
      _ ≤ V := mul_le_mul_of_nonneg_right hDpow (by positivity)
  let prims := poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W ++
    [(Ideal.absNorm G:ℝ)^η,K^η,N^η,((2*K)*N)^η,(N*N)^η,
      ((Ideal.absNorm G:ℝ)*(N*N))^η,(K*N)^η]
  have hprims : ∀x∈prims, 0≤x ∧ x≤V := by
    intro x hx
    simp only [prims,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hCV x hx
    all_goals exact hpow _ (by simp)
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈prims) (hn : xs.length≤8) : xs.prod≤V^8 :=
    list_prod_budget xs prims V hV hprims hx hn
  have hp1 (x : ℝ) (hx : x∈prims) : x≤V^8 := by
    simpa using hp [x] (by simpa using hx) (by simp)
  intro x hx
  simp only [poissonUnitBudget,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨by positivity, ?_⟩
    apply ((IdealDivisorBound.ideal_divisor_small_power η hη).choose_spec.2 G hG).trans
    have hh := hp [divisorConstant η hη,(Ideal.absNorm G:ℝ)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength K+1:ℕ) ≤ (2+1/(η*Real.log 2))*K^η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη K hK).trans
    have hh := hp [2+1/(η*Real.log 2),K^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength N+1:ℕ) ≤ (2+1/(η*Real.log 2))*N^η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη N hN).trans
    have hh := hp [2+1/(η*Real.log 2),N^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [256,supportConstant η hη,divisorConstant η hη,N^η,N^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [divisorExponentConstant hexp η hη,((2*K)*N)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖quadraticTransformedSquareProfile W 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨dualMiddleDecayConstant_nonneg _, ?_⟩
    have hh := hp [dualMiddleDecayConstant (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨originalMiddleDecayConstant_nonneg _, ?_⟩
    have hh := hp [originalMiddleDecayConstant (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨nonzeroLatticeEnvelopeConstant_nonneg, ?_⟩
    have hh := hp [nonzeroLatticeEnvelopeConstant] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,(N*N)^η,CD,sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,((Ideal.absNorm G:ℝ)*(N*N))^η,CS,sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [CT,sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,N^η,CP,(K*N)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh

end

section

theorem selectedPoisson_upper (C C1 M X η : ℝ)
    (hC : 4≤C) (hCC : C≤C1) (hM : 1≤M) (hX : 1≤X)
    (hη : 0≤η) (hη1 : η≤1) :
    4≤ selectedPoissonT C M X η ∧
    (M*X)^η≤ selectedPoissonT C M X η ∧
    selectedPoissonK C M X η≤C1*(M*X)^3 := by
  have hC10 : 0≤C1 := by linarith
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 1≤M*X := by nlinarith
  have hP0 : 0<M*X := by positivity
  have hR : 1≤(M*X)^η := Real.one_le_rpow hP hη
  have hT : 4≤ selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  refine ⟨hT,by dsimp [selectedPoissonT]; nlinarith,?_⟩
  have hXP : X≤M*X := by nlinarith
  have hfrac : X^2/M≤(M*X)^2 :=
    (div_le_self (sq_nonneg _) hM).trans (pow_le_pow_left₀ hX0.le hXP 2)
  have hrpow : (M*X)^η≤M*X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hη1
  calc
    selectedPoissonK C M X η = C*(M*X)^η*(X^2/M) := by
      unfold selectedPoissonK selectedPoissonT
      ring
    _ ≤ C1*(M*X)*(M*X)^2 := by gcongr
    _ = C1*(M*X)^3 := by ring

theorem poisson_seven_scale_bounds (g K N P B C1 : ℝ)
    (hP : 1≤P) (hB : 1≤B) (hC1 : 1≤C1)
    (hg0 : 0≤g) (hK0 : 0≤K) (hN0 : 0≤N)
    (hg : g≤B*P) (hK : K≤C1*P^3) (hN : N≤P) :
    ∀x∈([g,K,N,(2*K)*N,N*N,g*(N*N),K*N] : List ℝ),
      0≤x ∧ x≤(2*C1+B)*P^4 := by
  have hP0 : 0≤P := by linarith
  have hD : 1≤2*C1+B := by linarith
  have hp14 : P≤P^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hP (show 1≤4 by omega)
  have hp24 : P^2≤P^4 := pow_le_pow_right₀ hP (by omega)
  have hp34 : P^3≤P^4 := pow_le_pow_right₀ hP (by omega)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨hg0, hg.trans ?_⟩
    calc
      B*P ≤ B*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨hK0,hK.trans ?_⟩
    calc
      C1*P^3 ≤ C1*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨hN0,hN.trans (hp14.trans ?_)⟩
    nlinarith [show 0≤P^4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      2*K*N ≤ 2*(C1*P^3)*P := by gcongr
      _ = (2*C1)*P^4 := by ring
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      N*N ≤ P*P := by gcongr
      _ = P^2 := by ring
      _ ≤ P^4 := hp24
      _ ≤ (2*C1+B)*P^4 := by nlinarith [show 0≤P^4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      g*(N*N) ≤ (B*P)*(P*P) := by gcongr
      _ = B*P^3 := by ring
      _ ≤ B*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      K*N ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith

theorem power_cutoff_dominates (P T η : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l) :
    P^4≤T^l := by
  have hp0 : 0<P := by linarith
  calc
    P^4 = P^(4:ℝ) := by rw [Real.rpow_ofNat]
    _ ≤ P^(η*l) := Real.rpow_le_rpow_of_exponent_le hP hpow
    _ = (P^η)^l := by rw [Real.rpow_mul hp0.le,Real.rpow_natCast]
    _ ≤ T^l := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hT l

theorem poisson_truncation_small (P T η K M N C1 : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l)
    (_hK : 0≤K) (hM : 0≤M) (hN : 0≤N) (hC1 : 0≤C1)
    (hKP : K≤C1*P^3) (hMP : M≤P) (hNP : N≤P) :
    K*M/T^l≤C1 ∧ K*N/T^l≤C1 := by
  have hp0 : 0<P := by linarith
  have htpos : 0<T := lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) hT
  have hcut := power_cutoff_dominates P T η l hP hT hpow
  have hb (Y : ℝ) (hY : 0≤Y) (hYP : Y≤P) : K*Y/T^l≤C1 := by
    apply (div_le_iff₀ (pow_pos htpos _)).mpr
    calc
      K*Y ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ C1*T^l := by gcongr
  exact ⟨hb M hM hMP,hb N hN hNP⟩

theorem poisson_tail_abstract (B P t K η M : ℝ) (A : ℕ)
    (hB : 1≤B) (hP : 1≤P) (hM : 0≤M)
    (ht : 1/(B*P^2)≤t) (hu : P^η≤1+t*K) (hA : 4≤η*A) :
    M/((min 1 t)^2*(1+t*K)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hP0 : 0<P := by linarith
  have hBP : 1≤B*P^2 := by nlinarith [sq_nonneg (P-1)]
  have hinv : 1/(B*P^2)≤1 := (div_le_one (by positivity)).mpr hBP
  have htlo : 1/(B*P^2)≤ min 1 t := le_min hinv ht
  have htpos : 0< min 1 t := lt_of_lt_of_le (by positivity) htlo
  have hup : 0<1+t*K := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hu
  have hpow := power_cutoff_dominates P (1+t*K) η A hP hu hA
  have hprod : 1/B^2≤(min 1 t)^2*(1+t*K)^A := by
    calc
      1/B^2 = (1/(B*P^2))^2*P^4 := by field_simp
      _ ≤ (min 1 t)^2*(1+t*K)^A := by gcongr
  apply (div_le_iff₀ (by positivity : 0<(min 1 t)^2*(1+t*K)^A)).mpr
  have hh := mul_le_mul_of_nonneg_left hprod (show 0≤B^2*M by positivity)
  have he : (B^2*M)*(1/B^2)=M := by field_simp
  rw [he] at hh
  exact hh

theorem selectedPoisson_tail_shape (C B M X q η : ℝ) (A : ℕ)
    (hC : B≤C) (hB : 1≤B) (hM : 1≤M) (hX : 1≤X)
    (hq : 1≤q) (_hη : 0≤η) (hA : 4≤η*A) :
    M/((min 1 (M/((B*q)*(X/q)*(X/q))))^2*
      (1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hq0 : 0<q := by linarith
  have hC0 : 0<C := by linarith
  have hP : 1≤M*X := by nlinarith
  have hXP : X≤M*X := by nlinarith
  have hMQ : 1≤M*q := by nlinarith
  have hEq : M/((B*q)*(X/q)*(X/q))=M*q/(B*X^2) := by field_simp
  have ht : 1/(B*(M*X)^2)≤M/((B*q)*(X/q)*(X/q)) := by
    rw [hEq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      1*(B*X^2) ≤ B*(M*X)^2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0.le hXP 2) hB0.le
      _ ≤ (M*q)*(B*(M*X)^2) := by nlinarith [show 0≤B*(M*X)^2 by positivity]
  have hu : (M*X)^η≤1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η := by
    rw [selectedPoisson_radial_identity C B M X q η hM0 hX0 hq0 hB0]
    have hp : 0≤(M*X)^η := Real.rpow_nonneg (by positivity) _
    have hb : (M*X)^η≤ selectedPoissonT C M X η*q/B := by
      apply (le_div_iff₀ hB0).mpr
      dsimp [selectedPoissonT]
      calc
        (M*X)^η*B = B*(M*X)^η := by ring
        _ ≤ C*(M*X)^η := mul_le_mul_of_nonneg_right hC hp
        _ ≤ C*(M*X)^η*q := le_mul_of_one_le_right (by positivity) hq
    linarith
  exact poisson_tail_abstract B (M*X) _ _ η M A hB hP hM0.le ht hu hA

theorem selectedPoisson_principal_shape (C M X N η α : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hN : 0≤N) (hNX : N≤X)
    (hη : 0≤η) (hα : 1/2≤α) :
    Real.sqrt (M/selectedPoissonK C M X η)*N+
      Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) ≤
    M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hP hη
  have hT : 1≤ selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  have hT0 : 0<selectedPoissonT C M X η := by linarith
  have hK0 : 0<selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have hfrac : M/selectedPoissonK C M X η≤(M/X)^2 := by
    apply (div_le_iff₀ hK0).mpr
    have he : (M/X)^2*selectedPoissonK C M X η=M*selectedPoissonT C M X η := by
      unfold selectedPoissonK
      field_simp
    rw [he]
    nlinarith
  have hsqrt : Real.sqrt (M/selectedPoissonK C M X η)≤M/X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,hfrac⟩
  have hfirst : Real.sqrt (M/selectedPoissonK C M X η)*N≤M := by
    calc
      _ ≤ (M/X)*X := by gcongr
      _ = M := by field_simp
  have hsecond : Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) ≤
      selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
    calc
      _ ≤ Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
        gcongr ; linarith
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hT
          (show 0≤Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) by positivity)
        nlinarith
  exact add_le_add hfirst hsecond

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

theorem poisson_envelope_identity (H C P η Z : ℝ) (hP : 0<P) :
    262144*((H*P^(4*η))^8)^8*(C*P^(3*η)*Z) =
      (262144*H^64*C)*P^(259*η)*Z := by
  have hp : (P^(4*η))^64*P^(3*η)=P^(259*η) := by
    calc
      _ = P^((4*η)*64)*P^(3*η) := by rw [Real.rpow_mul hP.le (4*η) 64,Real.rpow_ofNat]
      _ = P^((4*η)*64+3*η) := (Real.rpow_add hP _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = (262144*H^64*C)*((P^(4*η))^64*P^(3*η))*Z := by ring
    _ = _ := by rw [hp]

theorem poissonComparisonMajorant_selected_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (η : ℝ) (hη : 0<η) (hη1 : η≤1) (l A : ℕ)
    (hl : 4≤η*l) (hA : 4≤η*A)
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    (B C1 : ℝ) (hB : 1≤B) (hC1 : 1≤C1) (W : 𝓢(ℝ,ℂ)) :
    ∃ Cfinal : ℝ, 0<Cfinal ∧
      ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
        1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
        1≤ selectedPoissonK C M X η →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
        (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
        (fun _ : Unit => (1:ℂ)) W ≤
        Cfinal*(M*X)^(259*η)*poissonShape M X α := by
  let D := 2*C1+B
  have hD : 1≤D := by dsimp [D]; linarith only [hC1,hB]
  obtain ⟨H,hH,hconst⟩ := list_exists_positive_bound
    (poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W)
  let Cshape := poissonShapeConstant B C1
  have hC10 : 0≤C1 := le_trans zero_le_one hC1
  have hCs : 1≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3,sq_nonneg B]
  have hCsC : C1≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [pow_nonneg hC10 3,sq_nonneg B]
  have hCsB : B^2≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3]
  have hCsMid : 1+4*C1^3≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,sq_nonneg B]
  refine ⟨262144*H^64*Cshape,by positivity,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  have hM0 : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hP : 1≤M*X := by nlinarith only [hM,hX]
  have hP0 : 0<M*X := by positivity
  have hMP : M≤M*X := by nlinarith only [hM,hX]
  have hXP : X≤M*X := by nlinarith only [hM,hX]
  have hN : 1≤X/q := (le_div_iff₀ hq0).mpr (by simpa using hqX)
  have hNX : X/q≤X := div_le_self hX0.le hq
  have hNP : X/q≤M*X := hNX.trans hXP
  obtain ⟨hT,hTP,hKP⟩ := selectedPoisson_upper C C1 M X η hC hCC hM hX hη.le hη1
  have hKg : 0≤ selectedPoissonK C M X η := le_trans zero_le_one hK
  have hg : (Ideal.absNorm G:ℝ)≤B*(M*X) := by rw [hGN]; gcongr; exact hqX.trans hXP
  have hb := poissonUnitBudget_power_envelope sD sS sT CD CS CT CP hCD hCS hCT hCP
    hexp η hη G hG (selectedPoissonK C M X η) (X/q) (M*X) D H W
    hK hN hP hD hH hconst
    (poisson_seven_scale_bounds (Ideal.absNorm G:ℝ) (selectedPoissonK C M X η) (X/q)
      (M*X) B C1 hP hB hC1 (Nat.cast_nonneg _) hKg (by positivity) hg hKP hNP)
  let R := (M*X)^(3*η)
  have hR : 1≤R := Real.one_le_rpow hP (by positivity)
  let Z := X^(2*α-1)*M^(1-α)
  have hZ : 0≤Z := by dsimp [Z]; positivity
  let S := Cshape*R*poissonShape M X α
  have hshape : 1≤poissonShape M X α := by
    change 1≤M+X+Z
    linarith only [hM,hX,hZ]
  have hshape0 : 0≤poissonShape M X α := le_trans zero_le_one hshape
  have hMshape : M≤poissonShape M X α := by
    change M≤M+X+Z
    linarith only [hX,hZ]
  have hXshape : X≤poissonShape M X α := by
    change X≤M+X+Z
    linarith only [hM,hZ]
  have hZshape : Z≤poissonShape M X α := by
    change Z≤M+X+Z
    linarith only [hM,hX]
  have hRshape : 1≤R*poissonShape M X α := by nlinarith only [hR,hshape]
  have hshapeS : poissonShape M X α≤S := by
    calc
      poissonShape M X α ≤ R*poissonShape M X α := le_mul_of_one_le_left hshape0 hR
      _ ≤ Cshape*(R*poissonShape M X α) :=
        le_mul_of_one_le_left (mul_nonneg (by linarith only [hR]) hshape0) hCs
      _ = S := by dsimp [S]; ring
  have hMS : M≤S := hMshape.trans hshapeS
  have hNS : X/q≤S := hNX.trans (hXshape.trans hshapeS)
  have hMiddle : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) ≤
      4*C1^3*R*poissonShape M X α := by
    apply (selectedPoisson_middle_bound C M X η α hC hM hX hη.le hα2).trans
    change 4*C ^3*R*Z≤4*C1^3*R*poissonShape M X α
    gcongr
  have hmidS : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2)≤S :=
    hMiddle.trans (by dsimp [S]; gcongr; linarith only [hCsMid])
  have hprS : Real.sqrt (M/selectedPoissonK C M X η)*(X/q)+
      Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2)≤S := by
    apply (selectedPoisson_principal_shape C M X (X/q) η α hC hM hX (by positivity) hNX hη.le hα).trans
    calc
      M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2)
          ≤ poissonShape M X α+4*C1^3*R*poissonShape M X α := add_le_add hMshape hMiddle
      _ ≤ R*poissonShape M X α+4*C1^3*R*poissonShape M X α :=
        add_le_add (le_mul_of_one_le_left hshape0 hR) (le_refl _)
      _ = (1+4*C1^3)*R*poissonShape M X α := by ring
      _ ≤ S := by dsimp [S]; gcongr
  obtain ⟨hED,hES⟩ := poisson_truncation_small (M*X) (selectedPoissonT C M X η) η
    (selectedPoissonK C M X η) M (X/q) C1 l hP hTP hl hKg hM0.le (by positivity) hC10 hKP hMP hNP
  have hC1S : C1≤S := by
    calc
      C1 ≤ Cshape := hCsC
      _ ≤ Cshape*(R*poissonShape M X α) := le_mul_of_one_le_right (by positivity) hRshape
      _ = S := by dsimp [S]; ring
  have htailS : M/((min 1 (M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q))))^2*
      (1+(M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q)))*selectedPoissonK C M X η)^A)≤S := by
    rw [hGN]
    apply (selectedPoisson_tail_shape C B M X q η A hBC hB hM hX hq hη.le hA).trans
    calc
      B^2*M ≤ B^2*(R*poissonShape M X α) := by
        gcongr
        exact hMshape.trans (le_mul_of_one_le_left hshape0 hR)
      _ ≤ Cshape*(R*poissonShape M X α) := by gcongr
      _ = S := by dsimp [S]; ring
  have hV : 1≤H*(M*X)^(4*η) := by
    have hh := Real.one_le_rpow hP (show 0≤4*η by positivity)
    nlinarith only [hH,hh]
  have hU : 1≤(H*(M*X)^(4*η))^8 := one_le_pow₀ hV
  apply (poissonComparisonMajorant_unit_box sD sS sT CD CS CT CP l A hexp η hη η hη G
    (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
    ((H*(M*X)^(4*η))^8) S W hKg (by positivity) hM0.le (by linarith only [hT]) hU (by dsimp [S]; positivity)
    hb hMS hNS hmidS hprS (hED.trans hC1S) (hES.trans hC1S) htailS).trans_eq
  exact poisson_envelope_identity H Cshape (M*X) η (poissonShape M X α) hP0

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents
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

open scoped BigOperators Classical SchwartzMap

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

namespace CanonicalQuadraticSieve

section

theorem improved_threshold_ge_column (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : N≤M := by
  have hp : 1≤2-1/α := by
    have hh : 1/α≤1 := (div_le_one (by linarith : 0<α)).mpr hα
    linarith
  calc
    N = N^(1:ℝ) := (Real.rpow_one N).symm
    _ ≤ N^(2-1/α) := Real.rpow_le_rpow_of_exponent_le hN hp
    _ ≤ M := hM

theorem improved_threshold_power (α N M : ℝ) (hα : 0<α) (hN : 0<N)
    (hM : N^(2-1/α)≤M) : N^(2*α-1)≤M^α := by
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hM hα.le
  rw [←Real.rpow_mul hN.le] at hh
  have he : (2-1/α)*α=2*α-1 := by field_simp
  rwa [he] at hh

theorem improved_threshold_main (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : N^(2*α-1)*M^(1-α)≤M := by
  have hNM := improved_threshold_ge_column α N M hα hN hM
  have hM0 : 0<M := by linarith
  have hh := improved_threshold_power α N M (by linarith) (by linarith) hM
  calc
    _ ≤ M^α*M^(1-α) := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hM0.le _)
    _ = M := by rw [←Real.rpow_add hM0]; simp

theorem improved_threshold_shape (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : M+N+N^(2*α-1)*M^(1-α)≤3*M := by
  linarith [improved_threshold_main α N M hα hN hM,
    improved_threshold_ge_column α N M hα hN hM]

open ActualEisensteinCubic CompletedGauss

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

theorem fixedBadNorm_one_le : 1≤fixedBadNorm := by
  have h1 : Admissible (1 : Ideal O) := by
    refine ⟨one_ne_zero, isUnit_one.squarefree, ?_⟩
    intro P hP
    simp only [UniqueFactorizationMonoid.normalizedFactors_one, Multiset.notMem_zero] at hP
  have he := commonMaskIdeal_eq_fixed_mul (1 : Ideal O) h1
  rw [mul_one] at he
  have hn : (∏P∈fixedBadPrimes,P)≠0 := by
    rw [←he]
    exact (commonMaskIdeal_squarefree 1).ne_zero
  unfold fixedBadNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hn (Ideal.absNorm_eq_zero_iff.mp h))

theorem fixedCutoffBase_bounds : 4≤fixedCutoffBase ∧ fixedBadNorm≤fixedCutoffBase :=
  ⟨le_max_left _ _,le_max_right _ _⟩

theorem HasSieveExponent.annular_selected_bound_oai {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) (C1 : ℝ) (hC1 : 1≤C1) :
    ∃ C : ℝ, 0<C ∧ ∀ (c M N : ℝ),
      fixedCutoffBase≤ c → c≤C1 → 1≤M → 4≤N → N^(2-1/α)≤M →
      1≤ selectedPoissonK c M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N (selectedPoissonK c M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hα : 1/2≤α := by linarith
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,henergy⟩ :=
    hexp.annular_energy_from_scalar_cost hα η hη l A
  obtain ⟨CF,hCF,hscalar⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l A hl hA sD sS sT CD CS CT CP hCD.le hCS.le hCT.le hCP.le
    fixedBadNorm C1 fixedBadNorm_one_le hC1 QuadraticInitialBound.annularSieveCutoff
  have hdiv : 0<divisorConstant η hη := divisorConstant_pos η hη
  let SD := supportConstant η hη*divisorConstant η hη
  have hSD : 0<SD := mul_pos (supportConstant_pos η hη) (divisorConstant_pos η hη)
  let F := 16*(3*CF*divisorConstant η hη + 4*CH*2^η*SD)
  refine ⟨F,by dsimp [F]; positivity,?_⟩
  intro c M N hc hc1 hM hN hthreshold hK a ha
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hN1 : 1≤N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hc4 : 4≤ c := fixedCutoffBase_bounds.1.trans hc
  have hcB : fixedBadNorm≤ c := fixedCutoffBase_bounds.2.trans hc
  have hT : 4≤ selectedPoissonT c M N η := by
    have hp := Real.one_le_rpow hP hη.le
    unfold selectedPoissonT
    nlinarith
  have hcut : N^2/M≤ selectedPoissonK c M N η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    have hp : 0≤N^2/M := by positivity
    nlinarith
  have hH := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hcost : ∀D∈gcdPool (fun J : idealRange N => J.val),
      (Ideal.absNorm D:ℝ)≤largeGcdThreshold α N →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη
        (commonMaskIdeal D) (selectedPoissonK c M N η) (N/(Ideal.absNorm D:ℝ)) M
        (selectedPoissonT c M N η) (fun _ : Unit => (1:ℂ))
        QuadraticInitialBound.annularSieveCutoff ≤ 3*CF*(M*N)^(259*η)*M := by
    intro D hD hd
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hD
    have hd1 : 1≤(Ideal.absNorm D:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hadm.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hgn : (Ideal.absNorm (commonMaskIdeal D):ℝ)=fixedBadNorm*(Ideal.absNorm D:ℝ) := by
      rw [commonMaskIdeal_norm D hadm, Nat.cast_mul]
      rfl
    have hb := hscalar c M N (Ideal.absNorm D:ℝ) (commonMaskIdeal D) hc4 hcB hc1 hM hN1 hd1
      (by linarith [hH.2]) (commonMaskIdeal_squarefree D).ne_zero hgn hK
    apply hb.trans
    have hs : poissonShape M N α≤3*M := improved_threshold_shape α N M hα1 hN1 hthreshold
    calc
      _ ≤ CF*(M*N)^(259*η)*(3*M) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have he := henergy η hη M N (selectedPoissonK c M N η) (selectedPoissonT c M N η)
    (largeGcdThreshold α N) (3*CF*(M*N)^(259*η)*M) hM hN1 hK hT
    (by linarith [hH.1]) hH.2 (by positivity) hcost a ha
  have hhigh := chosen_large_gcd_full α η CH M N (selectedPoissonK c M N η)
    hα1 hα2 hη.le hCH.le hM0 hN (by linarith) hcut
  have hn : N^η≤(M*N)^η := Real.rpow_le_rpow hN0.le (by nlinarith) hη.le
  have hcombine1 : (M*N)^(259*η)*(M*N)^η=(M*N)^(260*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  have hcombine2 : (M*N)^η*((M*N)^η)^2=(M*N)^(3*η) := by
    rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
    congr 1
    ring
  have hpow : (M*N)^(3*η)≤(M*N)^(260*η) :=
    Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hfirst : (3*CF*(M*N)^(259*η)*M/6)*(divisorConstant η hη*N^η) ≤
      (3*CF*divisorConstant η hη)*(M*N)^(260*η)*M := by
    calc
      _ ≤ (3*CF*(M*N)^(259*η)*M)*(divisorConstant η hη*(M*N)^η) := by
        gcongr
        nlinarith [show 0≤3*CF*(M*N)^(259*η)*M by positivity]
      _ = _ := by rw [←hcombine1]; ring
  have hsecond : (CH*((2*M)*(N/largeGcdThreshold α N))^η*
      (2*M+Real.sqrt ((2*M)/selectedPoissonK c M N η)*(N/largeGcdThreshold α N)^α))*
      SD*(N^η)^2 ≤ (4*CH*2^η*SD)*(M*N)^(260*η)*M := by
    calc
      _ ≤ ((4*CH*2^η)*(M*N)^η*M)*SD*((M*N)^η)^2 := by gcongr
      _ = (4*CH*2^η*SD)*(M*N)^(3*η)*M := by rw [←hcombine2]; ring
      _ ≤ _ := by gcongr
  apply he.trans
  change 16*(_+_*SD*(N^η)^2)*_≤_
  calc
    _ ≤ 16*((3*CF*divisorConstant η hη)*(M*N)^(260*η)*M+
      (4*CH*2^η*SD)*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by dsimp [F]; ring

end CanonicalQuadraticSieve

end

end OAI
end

theorem solution : type_of% @OAI.CanonicalQuadraticSieve.HasSieveExponent.annular_selected_bound_oai := @OAI.CanonicalQuadraticSieve.HasSieveExponent.annular_selected_bound_oai
