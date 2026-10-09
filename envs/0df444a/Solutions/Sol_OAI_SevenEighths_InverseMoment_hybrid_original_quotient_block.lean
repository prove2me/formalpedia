-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.hybrid_original_quotient_block
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T00:56:05.608207+00:00
-- url     : https://prove2.me/submissions/78d8f23a-1efa-4794-97d5-a6fde95c0def

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B010
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_lifted_annular_selected

section
-- module Solutions.OAIHecke.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open Polynomial

namespace Finset

/-- Backport (Mathlib d13f23b), additive form of `prod_le_prod_of_injOn`. -/
theorem sum_le_sum_of_injOn {ι α N : Type*} [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] [DecidableEq α]
    {f : ι → N} {g : α → N} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : image e s ⊆ t) (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ image e s → 0 ≤ g a) :
    ∑ i ∈ s, f i ≤ ∑ a ∈ t, g a := by
  refine le_trans ?_ <| sum_le_sum_of_subset_of_nonneg ht hg
  rw [sum_image he]
  exact sum_le_sum h

end Finset
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ThetaLocalRows
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

theorem theta_counter_lambda_eq : ActualEisensteinCubic.lambda =
    ActualEisensteinCoordinates.eval (-1) 1 := by
  have homega : ActualEisensteinCubic.omega = ActualEisensteinCoordinates.omega := by
    rfl
  rw [ActualEisensteinCubic.lambda, ActualEisensteinCoordinates.eval, homega]
  ring

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open MulChar AddChar

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

theorem finiteSquarefreeRow_pair_kernel
    {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S T : Finset ι) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u =
      rowCoprimeMask P (S ∩ T) u *
        star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by
  have hsplit (A B : Finset ι) :
      finiteSquarefreeRow P hgood A u =
        finiteSquarefreeRow P hgood (A ∩ B) u *
        finiteSquarefreeRow P hgood (A \ B) u := by
    exact (Finset.prod_inter_mul_prod_sdiff A B _).symm
  rw [hsplit S T, hsplit T S, Finset.inter_comm T S, star_mul]
  calc
    _ = (star (finiteSquarefreeRow P hgood (S ∩ T) u) *
          finiteSquarefreeRow P hgood (S ∩ T) u) *
        star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by ring
    _ = _ := by rw [finiteSquarefreeRow_self_pair]

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

theorem finitePrimeModulus_norm_sq {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) :
    ‖eisEmbedding (finitePrimeModulus P)‖ ^ 2 = (Ideal.absNorm (∏ i, P i) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, span_finitePrimeModulus]

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

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge

theorem idealSupport_injective_on_squarefree
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    (hsI : Squarefree I) (hsJ : Squarefree J)
    (h : idealSupport F I = idealSupport F J) : I = J := by
  have hfac : UniqueFactorizationMonoid.normalizedFactors I =
      UniqueFactorizationMonoid.normalizedFactors J := by
    rw [Multiset.Nodup.ext
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsI.ne_zero).mp hsI)
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsJ.ne_zero).mp hsJ)]
    intro P
    constructor
    · intro hP
      let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨I, hI, hP⟩⟩
      have hp : p ∈ idealSupport F I := (mem_idealSupport_iff F I p).mpr hP
      rw [h] at hp
      exact (mem_idealSupport_iff F J p).mp hp
    · intro hP
      let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨J, hJ, hP⟩⟩
      have hp : p ∈ idealSupport F J := (mem_idealSupport_iff F J p).mpr hP
      rw [← h] at hp
      exact (mem_idealSupport_iff F I p).mp hp
  rw [← Ideal.prod_normalizedFactors_eq_self hsI.ne_zero,
    ← Ideal.prod_normalizedFactors_eq_self hsJ.ne_zero, hfac]

end ConcretePrimeRowBridge

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

end ActualEisensteinCubic

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_canonicalGaussSum {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) :
    ‖canonicalGaussSum P hcop hgood j‖ = ‖eisEmbedding (finitePrimeModulus P)‖ := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let χ : ∀ i, MulChar (O ⧸ P i) ℂ := fun i => canonicalSextic (P i) (hgood i) ^ j i
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0
  have hχ : ∀ i, χ i ≠ 1 := fun i =>
    canonicalSextic_pow_ne_one (P i) (hgood i) (hchar i) (hj0 i) (hj6 i)
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i)
    e χ ψ hχ (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun i => O ⧸ P i) e ψ hψ i)
  change ‖canonicalGaussSum P hcop hgood j‖ ^ 2 =
    (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) at hnormsq
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using
      eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq

theorem norm_canonicalNormalizedGauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) :
    ‖canonicalNormalizedGauss P hcop hgood j‖ = 1 := by
  have hn : ‖eisEmbedding (finitePrimeModulus P)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  rw [canonicalNormalizedGauss, norm_div,
    norm_canonicalGaussSum P hcop hgood hchar j hj0 hj6,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self hn]

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ActiveConductor
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

namespace ActualEisensteinCubic

section

 theorem activeSupport_nonempty_of_ne {α : Type*} [DecidableEq α]
    {S T : Finset α} (h : S ≠ T) : (activeSupport S T).Nonempty := by
  by_contra hn
  apply h
  have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  ext i
  simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
  exact ⟨fun hi => he.1 hi, fun hi => he.2 hi⟩

open ConcreteTraceCRT EisensteinSchwartzPoisson

end

open EisensteinSchwartzPoisson

end ActualEisensteinCubic

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ActualEisensteinCubic

theorem activeSupport_product_mul_common_sq
    {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (P : ι → M) (S T : Finset ι) :
    (∏ i ∈ activeSupport S T, P i) * (∏ i ∈ S ∩ T, P i) ^ 2 =
      (∏ i ∈ S, P i) * (∏ i ∈ T, P i) := by
  have hset : activeSupport S T = (S ∪ T) \ (S ∩ T) := by
    ext i
    simp only [activeSupport, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsub : S ∩ T ⊆ S ∪ T := Finset.inter_subset_left.trans Finset.subset_union_left
  calc
    _ = ((∏ i ∈ activeSupport S T, P i) * (∏ i ∈ S ∩ T, P i)) *
      (∏ i ∈ S ∩ T, P i) := by rw [pow_two, mul_assoc]
    _ = (∏ i ∈ S ∪ T, P i) * (∏ i ∈ S ∩ T, P i) := by
      rw [hset, Finset.prod_sdiff hsub]
    _ = _ := Finset.prod_union_inter

theorem activePrimeModulus_norm_sq
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S T : Finset ι) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ activeSupport S T, P i) : ℝ) := by
  rw [finitePrimeModulus_norm_sq]
  congr 2
  exact Finset.prod_coe_sort (activeSupport S T) P

end ActualEisensteinCubic

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem pvConstant_pos : 0 < pvConstant :=
  (Classical.choose_spec
    (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)).1

theorem pvControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ pvControl W :=
  mul_nonneg pvConstant_pos.le (apply_nonneg _ _)

theorem pv_lattice_bound (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    t * (∑' h : {h : O // h ≠ 0},
      ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖) ≤ pvControl W :=
  (Classical.choose_spec
    (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)).2 W t ht

theorem norm_finite_character_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simpa only [MulChar.coe_equivToUnitHom] using
      (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    exact zero_le_one

theorem finiteSexticRow_norm_le_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    ‖finiteSexticRow P hg j a‖ ≤ 1 := by
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  rw [finiteSexticRow, norm_prod]
  calc
    _ ≤ ∏ i : ι, (1 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => norm_finite_character_le_one
        (canonicalSextic (P i) (hg i) ^ j i) _)
    _ = 1 := by simp

theorem canonical_polya_vinogradov {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, finiteSexticRow P hg j z * W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      pvControl W * ‖eisEmbedding (finitePrimeModulus P)‖ := by
  let c := finitePrimeModulus P
  let q := ‖eisEmbedding c‖
  have hq : 0 < q := norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  let t := M / q ^ 2
  have ht : 0 < t := div_pos hM (sq_pos_of_pos hq)
  let F : O → ℂ := fun h => star (finiteSexticRow P hg j h) *
    paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hF (h : O) : ‖F h‖ ≤ ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (finiteSexticRow_norm_le_one P hg j h)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF hs
  have hzero : F 0 = 0 := by simp only [F, finiteSexticRow_zero, star_zero, zero_mul]
  have heq : (∑' h : O, F h) = ∑' h : {h : O // h ≠ 0}, F h := by
    symm
    apply tsum_subtype_eq_of_support_subset
    intro h hh
      hz
    subst h
    exact hh hzero
  have hn : ‖∑' h : O, F h‖ ≤
      ∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [heq]
    exact (norm_tsum_le_tsum_norm (hFs.subtype _)).trans
      ((hFs.subtype _).tsum_le_tsum (fun h => hF h) (hs.subtype _))
  have hbound : t * ‖∑' h : O, F h‖ ≤ pvControl W :=
    (mul_le_mul_of_nonneg_left hn ht.le).trans (pv_lattice_bound W t ht)
  rw [canonical_radial_poisson_normalized P hcop hg hc j hj0 hj6 W M hM]
  have hargs (h : O) : M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 =
      t * ‖eisEmbedding h‖ ^ 2 := by dsimp [t, q]; ring
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) *
    ∑' h : O, star (finiteSexticRow P hg j h) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)‖ ≤ _
  simp_rw [hargs]
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) * ∑' h : O, F h‖ ≤ _
  rw [norm_mul, norm_div, norm_mul, norm_canonicalNormalizedGauss P hcop hg hc j hj0 hj6,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  change M / q * ‖∑' h : O, F h‖ ≤ pvControl W * q
  calc
    _ = q * (t * ‖∑' h : O, F h‖) := by dsimp [t]; field_simp
    _ ≤ q * pvControl W := mul_le_mul_of_nonneg_left hbound hq.le
    _ = _ := mul_comm _ _

theorem norm_ideal_moebius_le_one (I : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

theorem canonical_masked_polya_vinogradov
    {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset α) (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hg : ∀ i, lambda ∉ Q i) (hc : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, rowCoprimeMask P S z * finiteSexticRow Q hg j z *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ S.card * (pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖) := by
  rw [canonical_masked_radial_dilations P hinj S Q hcop hg j W M hM]
  calc
    _ ≤ ∑ E ∈ S.powerset, ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        finiteSexticRow Q hg j (primeSubsetGenerator P E) *
        ∑' z : O, finiteSexticRow Q hg j z *
          W (‖eisEmbedding z‖ ^ 2 / (M / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _E ∈ S.powerset, pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖ := by
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul, norm_mul]
      have hp := canonical_polya_vinogradov Q hcop hg hc j hj0 hj6 W _
        (primeSubset_reducedScale_pos P E hM)
      have hmul : ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ‖finiteSexticRow Q hg j (primeSubsetGenerator P E)‖ ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul (norm_ideal_moebius_le_one _)
            (finiteSexticRow_norm_le_one Q hg j _) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul _
      exact (mul_le_of_le_one_left (norm_nonneg _) hmul).trans hp
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

end QuadraticInitialBound

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

theorem quadraticRow_pair_kernel {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset α) (z : O) :
    star (quadraticRow P hg S z) * quadraticRow P hg T z =
      rowCoprimeMask P (S ∩ T) z *
        finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (fun _ => 3) z := by
  have h := congrArg (fun v : ℂ => v ^ 3) (finiteSquarefreeRow_pair_kernel P hg S T z)
  have hm : rowCoprimeMask P (S ∩ T) z ^ 3 = rowCoprimeMask P (S ∩ T) z := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  simp only [mul_pow, ← star_pow, hm] at h
  change star (quadraticRow P hg S z) * quadraticRow P hg T z =
    rowCoprimeMask P (S ∩ T) z * star (quadraticRow P hg (S \ T) z) *
      quadraticRow P hg (T \ S) z at h
  simp only [quadraticRow_star] at h ⊢
  rw [← quadraticRow_eq_canonical]
  change _ = rowCoprimeMask P (S ∩ T) z * quadraticRow P hg ((S \ T) ∪ (T \ S)) z
  rw [quadraticRow_disjoint_union P hg _ _ hd]
  simpa only [mul_assoc] using h

theorem quadratic_gram_offdiagonal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S T : Finset α) (hne : S ≠ T) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (quadraticRow P hg S z) * quadraticRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ (S ∩ T).card *
        (pvControl W * ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne hne).to_subtype
  simp_rw [quadraticRow_pair_kernel P hg S T]
  exact canonical_masked_polya_vinogradov P hinj (S ∩ T) (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val)
    (fun i => hc i.val) (fun _ => 3) (fun _ => by decide) (fun _ => by decide) W M hM

theorem supportNorm_nonneg {α : Type*} (P : α → Ideal O) (S : Finset α) :
    0 ≤ supportNorm P S := Nat.cast_nonneg _

theorem two_pow_card_le_supportNorm {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset α) :
    (2 : ℝ) ^ S.card ≤ supportNorm P S := by
  have hnorm (i : α) : (2 : ℝ) ≤ Ideal.absNorm (P i) := by
    have h0 : Ideal.absNorm (P i) ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact NeZero.ne (P i)
    have h1 : Ideal.absNorm (P i) ≠ 1 := by
      rw [ne_eq, Ideal.absNorm_eq_one_iff]
      exact (inferInstance : (P i).IsMaximal).ne_top
    exact_mod_cast (show 2 ≤ Ideal.absNorm (P i) by omega)
  change (2 : ℝ) ^ S.card ≤ (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  rw [map_prod, Nat.cast_prod]
  calc
    _ = ∏ _i ∈ S, (2 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) (fun i _ => hnorm i)

theorem divisor_conductor_bound {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S T : Finset α)
    (N : ℝ) (hN : 0 ≤ N) (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N) :
    (2 : ℝ) ^ (S ∩ T).card *
      ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ≤ N := by
  have hid := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
    (activeSupport_product_mul_common_sq P S T)
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hid
  rw [← activePrimeModulus_norm_sq] at hid
  change ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 *
    (supportNorm P (S ∩ T)) ^ 2 = supportNorm P S * supportNorm P T at hid
  have hpow := two_pow_card_le_supportNorm P (S ∩ T)
  have hmul := mul_le_mul_of_nonneg_right hpow
    (norm_nonneg (eisEmbedding (finitePrimeModulus (activePrimes P S T))))
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ (S ∩ T).card *
    ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) hmul 2
  have hprod := mul_le_mul hS hT (supportNorm_nonneg P T) hN
  nlinarith

theorem quadratic_gram_offdiagonal_of_norm_le {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S T : Finset α) (hne : S ≠ T) (N : ℝ) (hN : 0 ≤ N)
    (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (quadraticRow P hg S z) * quadraticRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ pvControl W * N := by
  apply (quadratic_gram_offdiagonal P hinj hg hc S T hne W M hM).trans
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (divisor_conductor_bound P S T N hN hS hT)
    (pvControl_nonneg W)

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

theorem radial_weight_lattice_bound (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    (∑' z : O, ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  let t := M⁻¹
  have ht : 0 < t := inv_pos.mpr hMp
  have ht1 : t ≤ 1 := (inv_le_one₀ hMp).mpr hM
  let B := 4 * (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (z : O) : ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      B * ((1 + t * ‖eisEmbedding z‖ ^ 2) ^ 2)⁻¹ := by
    have hq : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2, 0)) (k := 2) (n := 0) le_rfl le_rfl W (‖eisEmbedding z‖ ^ 2 / M)
    simp only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg hq] at hh
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    change (1 + ‖eisEmbedding z‖ ^ 2 / M) ^ 2 * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ B at hh
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  have hb := hs.tsum_le_tsum hp ((scaled_eisenstein_cauchy_summable t ht).mul_left B)
  rw [tsum_mul_left] at hb
  have hsmall := scaled_eisenstein_cauchy_small t ht ht1
  have hmul := mul_le_mul_of_nonneg_left hb ht.le
  have hcontrol := mul_le_mul_of_nonneg_left hsmall hB
  have hfinal : t * (∑' z : O, ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) ≤ diagonalControl W := by
    unfold diagonalControl
    dsimp [B] at hcontrol hmul
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hfinal hMp.le
  simpa only [t, ← mul_assoc, mul_inv_cancel₀ hMp.ne', one_mul, mul_comm] using hh

theorem quadraticRow_norm_le_one {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    ‖quadraticRow P hg S z‖ ≤ 1 := by
  rw [quadraticRow_eq_canonical]
  exact finiteSexticRow_norm_le_one _ _ _ _

theorem quadratic_pair_summable {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => (star (quadraticRow P hg S z) * quadraticRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hW
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (quadraticRow_norm_le_one P hg S z) (quadraticRow_norm_le_one P hg T z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem quadratic_gram_diagonal {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, (star (quadraticRow P hg S z) * quadraticRow P hg S z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  have hs := (quadratic_pair_summable P hg S S W M hMp).norm
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ?_ hW).trans
    (radial_weight_lattice_bound W M hM))
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (quadraticRow_norm_le_one P hg S z) (quadraticRow_norm_le_one P hg S z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

private theorem norm_sq_finite_sum {β : Type*} (C : Finset β) (a r : β → ℂ) :
    (↑(‖∑ n ∈ C, a n * r n‖ ^ 2) : ℂ) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) * (star (r n) * r m) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, starRingEnd_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem quadratic_mean_summable {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ)) := by
  have hs := summable_sum (s := C) (fun n hn => summable_sum (s := C) (fun m hm =>
    (quadratic_pair_summable P hg (support n) (support m) W M hM).mul_left (star (a n) * a m)))
  apply hs.congr
  intro z
  rw [norm_sq_finite_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem quadratic_mean_expand {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) *
        ∑' z : O, (star (quadraticRow P hg (support n) z) * quadraticRow P hg (support m) z) *
          W (‖eisEmbedding z‖ ^ 2 / M) := by
  let f : β → β → O → ℂ := fun n m z => (star (a n) * a m) *
    ((star (quadraticRow P hg (support n) z) * quadraticRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M))
  have hf (n m : β) : Summable (f n m) :=
    (quadratic_pair_summable P hg (support n) (support m) W M hM).mul_left _
  have heq (z : O) : W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ) =
        ∑ n ∈ C, ∑ m ∈ C, f n m z := by
    rw [norm_sq_finite_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [f]
    ring
  rw [tsum_congr heq, Summable.tsum_finsetSum (fun n hn => summable_sum (fun m hm => hf n m))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Summable.tsum_finsetSum (fun m hm => hf n m)]
  apply Finset.sum_congr rfl
  intro m hm
  exact tsum_mul_left

theorem quadratic_initial_mean_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (C : Finset β) (support : β → Finset α)
    (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) : ℂ)‖ ≤
        (diagonalControl W * M + pvControl W * N * C.card) * ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let D := diagonalControl W * M
  let B := pvControl W * N
  have hB : 0 ≤ B := mul_nonneg (pvControl_nonneg W) hN
  let K : β → β → ℂ := fun n m => ∑' z : O,
    (star (quadraticRow P hg (support n) z) * quadraticRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)
  have hK (n : β) (hn : n ∈ C) (m : β) (hm : m ∈ C) :
      ‖K n m‖ ≤ (if n = m then D else 0) + B := by
    by_cases hnm : n = m
    · subst m
      simp only [ite_true]
      exact (quadratic_gram_diagonal P hg (support n) W M hM).trans (le_add_of_nonneg_right hB)
    · simp only [hnm, ite_false, zero_add]
      exact quadratic_gram_offdiagonal_of_norm_le P hinj hg hc _ _
        (fun h => hnm (hsupp hn hm h)) N hN (hNorm n hn) (hNorm m hm) W M hMp
  have heq (n : β) (hn : n ∈ C) :
      (∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
        D * ‖a n‖ ^ 2 + B * ‖a n‖ * ∑ m ∈ C, ‖a m‖ := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq,  hn, ite_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hcalc : (∑ n ∈ C, ∑ m ∈ C,
      ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
      D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := by
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [quadratic_mean_expand P hg C support a W M hMp]
  calc
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖(star (a n) * a m) * K n m‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hK n hn m hm) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := hcalc
    _ ≤ D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * ((C.card : ℝ) * ∑ n ∈ C, ‖a n‖ ^ 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq C (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    _ = _ := by dsimp [D, B]; ring

theorem quadratic_initial_finite_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (C : Finset β) (support : β → Finset α) (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) ≤
      (diagonalControl sieveCutoff * M + pvControl sieveCutoff * N * C.card) *
        ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let E : O → ℝ := fun z => ‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2
  let F : O → ℝ := fun z => sieveBump (‖eisEmbedding z‖ ^ 2 / M) * E z
  let H : O → ℂ := fun z => sieveCutoff (‖eisEmbedding z‖ ^ 2 / M) * (E z : ℂ)
  have hF (z : O) : 0 ≤ F z := mul_nonneg sieveBump.nonneg (sq_nonneg _)
  have hH (z : O) : H z = (F z : ℂ) := by
    simp only [H, F, sieveCutoff_apply, Complex.ofReal_mul]
  have hHs : Summable H := quadratic_mean_summable P hg C support a sieveCutoff M hMp
  have hFs : Summable F := hHs.norm.congr (fun z => by
    rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF z)])
  have hsum : ‖∑' z : O, H z‖ = ∑' z : O, F z := by
    rw [tsum_congr hH, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg hF)]
  calc
    _ = ∑ z ∈ R, F z := by
      apply Finset.sum_congr rfl
      intro z hz
      have ht0 : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
      have ht1 : ‖eisEmbedding z‖ ^ 2 / M ≤ 1 := (div_le_one hMp).mpr (hR z hz)
      simp only [F, sieveBump_eq_one ht0 ht1, one_mul, E]
    _ ≤ ∑' z : O, F z := hFs.sum_le_tsum R (fun z _ => hF z)
    _ = ‖∑' z : O, H z‖ := hsum.symm
    _ ≤ _ := quadratic_initial_mean_bound P hinj hg hc C support hsupp N hN hNorm
      a sieveCutoff M hM

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

theorem initialSieveConstant_pos : 0 < initialSieveConstant := by
  have := diagonalControl_nonneg sieveCutoff
  have := pvControl_nonneg sieveCutoff
  unfold initialSieveConstant
  positivity

theorem ideal_initial_quadratic_sieve
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hsq : ∀ I ∈ F, Squarefree I)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (N : ℕ) (hN : 1 ≤ N) (hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ N)
    (a : Ideal O → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 3‖ ^ 2) ≤
      initialSieveConstant * (M + (N : ℝ) ^ 2) * ∑ I ∈ F, ‖a I‖ ^ 2 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsupp : Set.InjOn (idealSupport F) (↑F : Set (Ideal O)) := by
    intro I hI J hJ h
    exact idealSupport_injective_on_squarefree F hI hJ (hsq I hI) (hsq J hJ) h
  have hNorm (I : Ideal O) (hI : I ∈ F) :
      supportNorm (fun i : primePool F => i.val) (idealSupport F I) ≤ (N : ℝ) := by
    unfold supportNorm
    rw [idealSupport_product_eq F hI (hsq I hI)]
    exact_mod_cast hnorm I hI
  have hb := quadratic_initial_finite_bound (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood) hchar F (idealSupport F) hsupp
    (N : ℝ) (by positivity) hNorm a M hM R hR
  change (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 3‖ ^ 2) ≤
    (diagonalControl sieveCutoff * M + pvControl sieveCutoff * (N : ℝ) * F.card) *
      ∑ I ∈ F, ‖a I‖ ^ 2 at hb
  have hsub : F ⊆ idealsUpTo N := by
    intro I hI
    apply mem_idealsUpTo.mpr
    constructor
    · apply Nat.one_le_iff_ne_zero.mpr
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact hFpos I hI
    · exact hnorm I hI
  have hcardNat : F.card ≤ 64 * (N + 1) :=
    (Finset.card_le_card hsub).trans (CompactScaleBridge.idealsUpTo_card_le N)
  have hcard : (F.card : ℝ) ≤ 128 * (N : ℝ) := by
    have hh : (F.card : ℝ) ≤ 64 * ((N : ℝ) + 1) := by exact_mod_cast hcardNat
    linarith
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hdiag := diagonalControl_nonneg sieveCutoff
  have hpv := pvControl_nonneg sieveCutoff
  have hmul := mul_le_mul_of_nonneg_left hcard (mul_nonneg hpv (by positivity : (0 : ℝ) ≤ N))
  unfold initialSieveConstant
  nlinarith [mul_nonneg hdiag (sq_nonneg (N : ℝ)),
    mul_nonneg hpv (show 0 ≤ M by linarith)]

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.IdealQuotients
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

section
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss ConcreteTraceCRT

theorem primaryGenerator_admissible (I : Ideal O) (hI : Admissible I) : primaryGenerator I ≠ 0 :=
  PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors I hI.1
    (fun P hP => (hI.2.2 P hP).1)

theorem primaryGenerator_inj_on_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J) (heq : primaryGenerator I = primaryGenerator J) : I = J := by
  calc
    I = Ideal.span {primaryGenerator I} := (primaryGenerator_spec I (primaryGenerator_admissible I hI)).1.symm
    _ = Ideal.span {primaryGenerator J} := by rw [heq]
    _ = J := (primaryGenerator_spec J (primaryGenerator_admissible J hJ)).1

theorem sieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    sieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  let R := (idealRange M).image primaryGenerator
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => (hF I hI).1
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (hF I hI).2.2 P hP |>.1
  have hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2 := by
    intro i
    obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp i.property
    exact (hF I hI).2.2 i.val hP |>.2
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hz
    rw [primaryGenerator_norm_sq I (primaryGenerator_admissible I (mem_idealRange.mp hI).1)]
    exact (mem_idealRange.mp hI).2
  have hgen : Set.InjOn primaryGenerator (idealRange M) := by
    intro I hI J hJ heq
    exact primaryGenerator_inj_on_admissible (mem_idealRange.mp hI).1 (mem_idealRange.mp hJ).1 heq
  apply FiniteSieveOperator.squared_norm_le_of_energy (matrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 3) =
        ∑ J : F, quadraticRow J.val z * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    rw [quadraticRow_eq F hF J.val J.property z]
    simp only [aext, dif_pos J.property]
    change a J * (idealSexticRow F hFp hFg J.val z) ^ 3 =
      (idealSexticRow F hFp hFg J.val z) ^ 3 * a J
    exact mul_comm _ _
  have he := QuadraticInitialBound.ideal_initial_quadratic_sieve F hFp hFg
    (fun I hI => (hF I hI).2.1) hchar ⌈N⌉₊ hnat hnorm aext M hM R hR
  have heR : (∑ z ∈ R, ‖∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 3‖ ^ 2) =
      ∑ I : idealRange M, ‖∑ J : F, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2 := by
    dsimp only [R]
    rw [Finset.sum_image (fun I hI J hJ heq => hgen hI hJ heq)]
    simp_rw [hinner]
    exact (Finset.sum_coe_sort _ _).symm
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    simp only [aext, dif_pos J.property]
    rfl
  rw [heR, hea] at he
  exact he

end

open ActualEisensteinCubic CompletedGauss

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

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

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap

open MeasureTheory
open scoped BigOperators Classical SchwartzMap

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

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

theorem badPrime_injective : Function.Injective badPrime := by
  have hgood : lambda ∉ (Ideal.span {(2 : O)} : Ideal O) := by
    have hg := cubicTwoIdeal_good
    change lambda ∉ cubicTwoIdeal at hg
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using hg
  intro i j hij
  cases i <;> cases j
  · rfl
  · exfalso
    apply hgood
    have he : (Ideal.span {lambda} : Ideal O) = Ideal.span {(2 : O)} := hij
    rw [← he]
    exact Ideal.subset_span (by simp)
  · exfalso
    apply hgood
    have he : (Ideal.span {(2 : O)} : Ideal O) = Ideal.span {lambda} := hij
    rw [he]
    exact Ideal.subset_span (by simp)
  · rfl

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

open scoped SchwartzMap ContDiff
namespace QuadraticInitialBound

theorem annularSieveBump_eq_one {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) : annularSieveBump t = 1 := by
  apply annularSieveBump.one_of_mem_closedBall
  change dist t (3 / 4) ≤ 1 / 4
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

end QuadraticInitialBound

open scoped BigOperators Classical

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
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge QuadraticSquarefreeKernel

theorem canonical_quadraticRow_square_argument (D : Ideal O) (hD : Admissible D) (a : O) :
    quadraticRow D (a ^ 2) = idealZeroMask D a := by
  rw [pow_two, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_squared D hD]

theorem canonical_quadraticRow_primary_squarefree (D : Ideal O) (hD : Admissible D)
    (A B : Ideal O) :
    quadraticRow D (primaryGenerator (A ^ 2 * B)) =
      idealZeroMask D (primaryGenerator A) * quadraticRow D (primaryGenerator B) := by
  rw [primaryGenerator_mul]
  have hpow : primaryGenerator (A ^ 2) = primaryGenerator A ^ 2 := map_pow primaryGeneratorHom A 2
  rw [hpow, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_square_argument D hD]

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

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
open IdealMobiusDivisorSum

theorem goodSquarefreePart_admissible (I : Ideal O) : Admissible (goodSquarefreePart I) := by
  have hs : goodPrimeSupport I ⊆ IdealMobiusDivisorSum.primeSupport I := Finset.sdiff_subset
  refine ⟨support_product_ne_zero hs, squarefree_support_product hs, ?_⟩
  intro P hP
  change P ∈ UniqueFactorizationMonoid.normalizedFactors (∏ Q ∈ goodPrimeSupport I, Q) at hP
  rw [factors_support_product hs] at hP
  have hp : P ∈ goodPrimeSupport I := hP
  have hprime := support_prime (hs hp)
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  exact (prime_good_iff_not_bad P).mpr (Finset.mem_sdiff.mp hp).2

theorem squarefree_bad_good_product (I : Ideal O) (hI : Squarefree I) :
    (∏ P ∈ badPrimeSupport I, P) * goodSquarefreePart I = I := by
  have hu : badPrimeSupport I ∪ goodPrimeSupport I = IdealMobiusDivisorSum.primeSupport I := by
    ext P
    simp only [badPrimeSupport, goodPrimeSupport, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hd : Disjoint (badPrimeSupport I) (goodPrimeSupport I) := by
    apply Finset.disjoint_left.mpr
    intro P hp hq
    exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2
  rw [goodSquarefreePart, ← Finset.prod_union hd, hu]
  exact squarefree_support_product_self hI

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge

theorem fixedBadPrimes_card : fixedBadPrimes.card = 2 := by
  have hn : (Ideal.span {lambda} : Ideal O) ≠ Ideal.span {(2 : O)} := by
    intro h
    have hb : badPrime false = badPrime true := h
    have := badPrime_injective hb
    cases this
  simp [fixedBadPrimes, hn]

theorem fixedBadPrimes_powerset_card : fixedBadPrimes.powerset.card = 4 := by
  rw [Finset.card_powerset, fixedBadPrimes_card]
  norm_num

theorem goodSquarefreePart_injective_on_sector (I J : Ideal O) (hI : Squarefree I) (hJ : Squarefree J)
    (hs : badPrimeSector I = badPrimeSector J) (hg : goodSquarefreePart I = goodSquarefreePart J) : I = J := by
  have he : badPrimeSupport I = badPrimeSupport J := congrArg Subtype.val hs
  calc
    I = (∏ P ∈ badPrimeSupport I, P) * goodSquarefreePart I := (squarefree_bad_good_product I hI).symm
    _ = (∏ P ∈ badPrimeSupport J, P) * goodSquarefreePart J := by rw [he, hg]
    _ = J := squarefree_bad_good_product J hJ

theorem goodSquarefreePart_norm_le (I : Ideal O) (hI : Squarefree I) :
    Ideal.absNorm (goodSquarefreePart I) ≤ Ideal.absNorm I := by
  have hd : goodSquarefreePart I ∣ I := by
    exact ⟨∏ P ∈ badPrimeSupport I, P, (squarefree_bad_good_product I hI).symm.trans (mul_comm _ _)⟩
  apply Nat.le_of_dvd
  · exact Nat.pos_iff_ne_zero.mpr (fun hn => hI.ne_zero (Ideal.absNorm_eq_zero_iff.mp hn))
  · exact map_dvd Ideal.absNorm hd

theorem goodSquarefreePart_mem_idealRange (I : Ideal O) (hI : Squarefree I) (M : ℝ)
    (hM : (Ideal.absNorm I : ℝ) ≤ M) : goodSquarefreePart I ∈ idealRange M := by
  apply mem_idealRange.mpr
  exact ⟨goodSquarefreePart_admissible I, (Nat.cast_le.mpr (goodSquarefreePart_norm_le I hI)).trans hM⟩

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel UnrestrictedIdealReindex

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

end CanonicalQuadraticSieve

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

open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction

theorem dyadicColumnCoefficient_shell (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (j : Fin (lengthScale + 1)) (a : idealRange N → ℂ) :
    CoefficientOnShell N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a) := by
  intro J hJ
  have he : columnDyadicSector N lengthScale hNL J = j := by
    by_contra hn
    exact hJ (by simp only [dyadicColumnCoefficient, sectorCoefficient, if_neg hn])
  have hs := (column_dyadic_exists N lengthScale hNL J).choose_spec.2
  have hv : (columnDyadicSector N lengthScale hNL J).val = j.val := congrArg Fin.val he
  change (column_dyadic_exists N lengthScale hNL J).choose = j.val at hv
  simpa only [hv] using hs

theorem dyadicColumnCoefficient_energy (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    (∑ j : Fin (lengthScale + 1), ∑ J, ‖dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2) = ∑ J, ‖a J‖ ^ 2 :=
  sectorCoefficient_energy (columnDyadicSector N lengthScale hNL) a

theorem weighted_energy_column_shells {m : Type*} [Fintype m]
    (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (A : Matrix m (idealRange N) ℂ) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i)
    (a : idealRange N → ℂ) :
    (∑ i, v i * ‖∑ J, A i J * a J‖ ^ 2) ≤
      (lengthScale + 1 : ℝ) * ∑ j : Fin (lengthScale + 1), ∑ i,
        v i * ‖∑ J, A i J * dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2 := by
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, dyadicColumnCoefficient] using
    sector_weighted_energy_bound A (columnDyadicSector N lengthScale hNL) a v hv

theorem coefficientAtScale_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell X X (coefficientAtScale N X a) := by
  intro J hJ
  unfold coefficientAtScale at hJ
  split_ifs at hJ with h
  · exact ha ⟨J.val, h⟩ hJ
  · exact (hJ rfl).elim

theorem coefficientAtScale_row_sum (N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) (z : O) :
    (∑ J : idealRange N, quadraticRow J.val z * a J) =
      ∑ J : idealRange X, quadraticRow J.val z * coefficientAtScale N X a J := by
  let f : Ideal O → ℂ := fun I => if h : I ∈ idealRange N then quadraticRow I z * a ⟨I, h⟩ else 0
  have hleft : (∑ J : idealRange N, quadraticRow J.val z * a J) = ∑ I ∈ idealRange N, f I := by
    rw [← Finset.sum_coe_sort (idealRange N) f]
    apply Finset.sum_congr rfl
    intro J _
    simp only [f, dif_pos J.property]
  have hright : (∑ J : idealRange X, quadraticRow J.val z * coefficientAtScale N X a J) =
      ∑ I ∈ idealRange X, f I := by
    rw [← Finset.sum_coe_sort (idealRange X) f]
    apply Finset.sum_congr rfl
    intro J _
    unfold coefficientAtScale
    split_ifs with h <;> simp only [f, h, ↓reduceDIte, mul_zero]
  rw [hleft, hright]
  rcases le_total N X with hNX | hXN
  · apply Finset.sum_subset (idealRange_mono hNX)
    intro I hIX hIN
    simp only [f, dif_neg hIN]
  · symm
    apply Finset.sum_subset (idealRange_mono hXN)
    intro I hIN hIX
    have haI : a ⟨I, hIN⟩ = 0 := by
      by_contra hn
      exact hIX (mem_idealRange.mpr ⟨(mem_idealRange.mp hIN).1, ha ⟨I, hIN⟩ hn⟩)
    simp only [f, dif_pos hIN, haI, mul_zero]

theorem coefficientAtScale_energy (N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) :
    (∑ J : idealRange N, ‖a J‖ ^ 2) = ∑ J : idealRange X, ‖coefficientAtScale N X a J‖ ^ 2 := by
  let f : Ideal O → ℝ := fun I => if h : I ∈ idealRange N then ‖a ⟨I, h⟩‖ ^ 2 else 0
  have hleft : (∑ J : idealRange N, ‖a J‖ ^ 2) = ∑ I ∈ idealRange N, f I := by
    rw [← Finset.sum_coe_sort (idealRange N) f]
    apply Finset.sum_congr rfl
    intro J _
    simp only [f, dif_pos J.property]
  have hright : (∑ J : idealRange X, ‖coefficientAtScale N X a J‖ ^ 2) =
      ∑ I ∈ idealRange X, f I := by
    rw [← Finset.sum_coe_sort (idealRange X) f]
    apply Finset.sum_congr rfl
    intro J _
    unfold coefficientAtScale
    split_ifs with h <;> simp only [f, h, ↓reduceDIte, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [hleft, hright]
  rcases le_total N X with hNX | hXN
  · apply Finset.sum_subset (idealRange_mono hNX)
    intro I hIX hIN
    simp only [f, dif_neg hIN]
  · symm
    apply Finset.sum_subset (idealRange_mono hXN)
    intro I hIN hIX
    have haI : a ⟨I, hIN⟩ = 0 := by
      by_contra hn
      exact hIX (mem_idealRange.mpr ⟨(mem_idealRange.mp hIN).1, ha ⟨I, hIN⟩ hn⟩)
    simp only [f, dif_pos hIN, haI, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem dyadicColumnCoefficient_at_scale_energy (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    (∑ j : Fin (lengthScale + 1), ∑ J : idealRange ((2 : ℝ) ^ j.val),
      ‖coefficientAtScale N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a) J‖ ^ 2) =
        ∑ J : idealRange N, ‖a J‖ ^ 2 := by
  calc
    _ = ∑ j : Fin (lengthScale + 1), ∑ J : idealRange N, ‖dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (coefficientAtScale_energy N _ _
        (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)).symm
    _ = _ := dyadicColumnCoefficient_energy N lengthScale hNL a

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

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FirstCoreCutoff
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

theorem hasSieveExponent_two : HasSieveExponent 2 := by
  intro ε hε
  let C := QuadraticInitialBound.initialSieveConstant
  have hC : 0 < C := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨4 * C, by positivity, ?_⟩
  intro M N hM hN
  have hc : (⌈N⌉₊ : ℝ) ≤ 2 * N := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ N by linarith)
    linarith
  have hc2 : (⌈N⌉₊ : ℝ) ^ 2 ≤ 4 * N ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) ⌈N⌉₊]
  have hmn : 1 ≤ M * N := by nlinarith [mul_le_mul hM hN (by norm_num : (0 : ℝ) ≤ 1) (show 0 ≤ M by linarith)]
  have he : 1 ≤ (M * N) ^ ε := Real.one_le_rpow hmn hε.le
  rw [Real.rpow_two]
  calc
    _ ≤ C * (M + (⌈N⌉₊ : ℝ) ^ 2) := sieveNorm_initial M N hM hN
    _ ≤ 4 * C * (M + N ^ 2) := by nlinarith
    _ ≤ (4 * C) * (M * N) ^ ε * (M + N ^ 2) := by
      nlinarith [show 0 ≤ (4 * C) * (M + N ^ 2) by positivity]

open IdealCoprimeSieveOperator DivisorBlockCauchy

variable {n p : Type*} [Fintype n] [Fintype p]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SeedDefects
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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sector_bad_good_product (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) :
    sectorBadIdeal E * goodSquarefreePart I = I := by
  have hs : badPrimeSupport I = E.val := congrArg Subtype.val hE
  simpa only [hs, sectorBadIdeal] using squarefree_bad_good_product I hI

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical

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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

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

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem idealQuotient_norm_eq (D I : Ideal O) (hD : D≠0) (hDI : D∣I) :
    (Ideal.absNorm (idealQuotient D I):ℝ)=(Ideal.absNorm I:ℝ)/(Ideal.absNorm D:ℝ) := by
  have hn : (Ideal.absNorm D:ℝ)≠0 := by
    exact_mod_cast (show Ideal.absNorm D≠0 from fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  apply (eq_div_iff hn).mpr
  rw [mul_comm,←Nat.cast_mul,←map_mul,idealQuotient_mul hDI]

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

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

theorem hasSieveExponent_one_of_approximation
    (happrox : ∀ η : ℝ, 0<η → ∃ α : ℝ, α≤1+η ∧ HasSieveExponent α) :
    HasSieveExponent 1 := by
  intro ε hε
  have he : 0<ε/2 := by positivity
  obtain ⟨α,hα,h⟩ := happrox (ε/2) he
  obtain ⟨C,hC,hbound⟩ := h (ε/2) he
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0≤M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hNmn : N≤M*N := by nlinarith
  have hQ : 1≤(M*N)^(ε/2) := Real.one_le_rpow hMN he.le
  have hnα : N^α ≤ (M*N)^(ε/2)*N := by
    calc
      _ ≤ N^(1+ε/2) := Real.rpow_le_rpow_of_exponent_le hN hα
      _ = N*N^(ε/2) := by rw [Real.rpow_add hN0,Real.rpow_one]
      _ ≤ N*(M*N)^(ε/2) := by gcongr
      _ = _ := mul_comm _ _
  have hsum : M+N^α ≤ (M*N)^(ε/2)*(M+N) := by
    nlinarith [mul_le_mul_of_nonneg_right hQ hM0]
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+N^α) := hbound M N hM hN
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N)) := by gcongr
    _ = C*(M*N)^ε*(M+N^(1:ℝ)) := by
      rw [Real.rpow_one]
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add (by positivity : 0<M*N)]
        congr 1
        ring
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+N) := by ring
        _ = _ := by rw [hp]

theorem bootstrapExponent_gt_one (n : ℕ) : 1<bootstrapExponent n := by
  unfold bootstrapExponent
  have h : (0:ℝ)<1/((n:ℝ)+1) := by positivity
  linarith

theorem bootstrapExponent_le_two (n : ℕ) : bootstrapExponent n≤2 := by
  have h : 1/((n:ℝ)+1)≤(1:ℝ) := by
    apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold bootstrapExponent
  linarith

theorem bootstrapExponent_step (n : ℕ) :
    bootstrapExponent (n+1) = 2-1/bootstrapExponent n := by
  unfold bootstrapExponent
  push_cast
  field_simp
  ring

theorem hasSieveExponent_one_of_improvement
    (himprove : ∀ α : ℝ, 1<α → α≤2 → HasSieveExponent α → HasSieveExponent (2-1/α)) :
    HasSieveExponent 1 := by
  have hn : ∀ n : ℕ, HasSieveExponent (bootstrapExponent n) := by
    intro n
    induction n with
    | zero => norm_num [bootstrapExponent]; exact hasSieveExponent_two
    | succ n ih =>
      rw [bootstrapExponent_step]
      exact himprove _ (bootstrapExponent_gt_one n) (bootstrapExponent_le_two n) ih
  apply hasSieveExponent_one_of_approximation
  intro η hη
  obtain ⟨n,hnη⟩ := exists_nat_one_div_lt hη
  refine ⟨bootstrapExponent n,?_,hn n⟩
  unfold bootstrapExponent
  linarith

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

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

theorem selectedPoisson_bounds (C M X η : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hMX : M≤X^2) (hη : 0≤η) :
    4≤ selectedPoissonT C M X η ∧ 1≤ selectedPoissonK C M X η ∧
      selectedPoissonK C M X η≤C*(M*X)^(η+2) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hprod : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hprod hη
  have hT : 4≤ selectedPoissonT C M X η := by
    unfold selectedPoissonT
    nlinarith
  have hfrac : 1≤X^2/M := (le_div_iff₀ hM0).mpr (by simpa using hMX)
  have hK : 1≤ selectedPoissonK C M X η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    nlinarith
  refine ⟨hT,hK,?_⟩
  have hXprod : X≤M*X := by nlinarith
  have hfracup : X^2/M≤(M*X)^2 :=
    (div_le_self (sq_nonneg X) hM).trans (pow_le_pow_left₀ hX0.le hXprod 2)
  unfold selectedPoissonK selectedPoissonT
  rw [mul_div_assoc,Real.rpow_add (by positivity : 0<M*X),Real.rpow_two]
  calc
    _ ≤ (C*(M*X)^η)*(M*X)^2 := mul_le_mul_of_nonneg_left hfracup (by positivity)
    _ = _ := by ring

end CanonicalQuadraticSieve

open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Operator
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
theorem operator_conjugate_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    operator (fun i j => star (A i j)) x = conjugateVector (operator A (conjugateVector x)) := by
  ext i
  change (∑ j, star (A i j) * x j) = star (∑ j, A i j * star (x j))
  simp only [star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [DecidableEq m] in
theorem operator_conjugate_norm_le (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [operator_conjugate_apply, norm_conjugateVector]
  simpa only [norm_conjugateVector] using (operator A).le_opNorm (conjugateVector x)

omit [DecidableEq m] in
theorem operator_conjugate_norm (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ = ‖operator A‖ := by
  apply le_antisymm (operator_conjugate_norm_le A)
  simpa only [star_star] using operator_conjugate_norm_le (fun i j => star (A i j))

omit [DecidableEq m] in
theorem energy_le_squaredNorm (A : Matrix m n ℂ) (c : n → ℂ) :
    (∑ i, ‖∑ j, A i j * c j‖ ^ 2) ≤ squaredNorm A * ∑ j, ‖c j‖ ^ 2 := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 c
  have h := (operator A).le_opNorm x
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [squaredNorm, mul_pow, EuclideanSpace.norm_sq_eq, operator_apply, x] using hs

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.GlobalScales
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum CompletedGauss
open QuadraticSquarefreeKernel

theorem liftingPrime_supported : Supported liftingPrime := by
  apply (supported_span_iff liftingPrimeElement).mpr
  have hlam : ShortDraftLatticeCount.qNat lambda=3 := by
    have he : lambda=ActualEisensteinCoordinates.eval (-1) 1 := theta_counter_lambda_eq
    rw [he]
    unfold ShortDraftLatticeCount.qNat
    rw [ShortDraftLatticeCount.coords_eval]
    norm_num [ShortDraftLatticeCount.q]
  have htwo : ShortDraftLatticeCount.qNat (2:O)=4 := by
    have he : (2:O)=ActualEisensteinCoordinates.eval 2 0 := by simp [ActualEisensteinCoordinates.eval]
    rw [he]
    unfold ShortDraftLatticeCount.qNat
    rw [ShortDraftLatticeCount.coords_eval]
    norm_num [ShortDraftLatticeCount.q]
  constructor
  · rintro ⟨z,hz⟩
    have h := congrArg ShortDraftLatticeCount.qNat hz
    rw [liftingPrimeElement_norm,ShortDraftLatticeCount.qNat_mul,hlam] at h
    omega
  · rintro ⟨z,hz⟩
    have h := congrArg ShortDraftLatticeCount.qNat hz
    rw [liftingPrimeElement_norm,ShortDraftLatticeCount.qNat_mul,htwo] at h
    omega

theorem liftedRow_norm (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) :
    (Ideal.absNorm (liftedRow M I hI hIM):ℝ)=(49:ℝ)^liftingExponent M I hI hIM*(Ideal.absNorm I:ℝ) := by
  simp only [liftedRow,map_mul,map_pow,liftingPrime_norm,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [←pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem liftedRow_bounds (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) :
    M<(Ideal.absNorm (liftedRow M I hI hIM):ℝ) ∧
      (Ideal.absNorm (liftedRow M I hI hIM):ℝ)≤49*M := by
  rw [liftedRow_norm]
  exact (exists_lifting_exponent M I hI hIM).choose_spec

theorem liftedRow_squarefreePart (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) : squarefreePart (liftedRow M I hI.1 hIM)=I :=
  (squarePart_mul_squarefree (pow_ne_zero _ liftingPrime_prime.ne_zero) hI.2.1).2

theorem liftedRow_supported (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) : Supported (liftedRow M I hI.1 hIM) := by
  exact (supported_mul_iff _ _).mpr
    ⟨supported_pow (supported_pow liftingPrime_supported _) _,admissible_supported hI⟩

theorem liftedRow_character (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) (J : Ideal O) (hJ : Admissible J)
    (hPJ : IsCoprime liftingPrime J) :
    quadraticRow J (primaryGenerator (liftedRow M I hI.1 hIM)) =
      quadraticRow J (primaryGenerator I) := by
  rw [liftedRow,canonical_quadraticRow_primary_squarefree J hJ,
    idealZeroMask_primary_eq_indicator J _ hJ.1 (supported_pow liftingPrime_supported _),
    if_pos hPJ.pow_left,one_mul]

end CanonicalQuadraticSieve

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

open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss QuadraticSquarefreeKernel

theorem annularLift_injective (M K : ℝ) : Function.Injective (annularLift M K) := by
  intro I J h
  have he := congrArg squarefreePart h
  apply Subtype.ext
  simpa only [annularLift,
    liftedRow_squarefreePart M I.val (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1,
    liftedRow_squarefreePart M J.val (mem_idealRange.mp (Finset.mem_filter.mp J.property).1).1] using he

theorem annularLift_properties (M K : ℝ) (I : squarefreeHighRange M K) :
    Supported (annularLift M K I) ∧ K<(Ideal.absNorm (squarefreePart (annularLift M K I)):ℝ) ∧
      M<(Ideal.absNorm (annularLift M K I):ℝ) ∧ (Ideal.absNorm (annularLift M K I):ℝ)≤49*M := by
  have hi := mem_idealRange.mp (Finset.mem_filter.mp I.property).1
  have hn := liftedRow_bounds M I.val hi.1.1 hi.2
  refine ⟨liftedRow_supported M I.val hi.1 hi.2,?_,hn⟩
  simpa only [annularLift,liftedRow_squarefreePart M I.val hi.1] using (Finset.mem_filter.mp I.property).2

theorem annularLift_row_sum (M N K : ℝ) (I : squarefreeHighRange M K)
    (a : idealRange N → ℂ)
    (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val) :
    (∑J : idealRange N, quadraticRow J.val (primaryGenerator (annularLift M K I))*a J) =
      ∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J := by
  apply Finset.sum_congr rfl
  intro J _
  by_cases hz : a J=0
  · simp only [hz,mul_zero]
  · rw [annularLift,liftedRow_character M I.val
      (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1 _ J.val
      (mem_idealRange.mp J.property).1 (hcop J hz)]

lemma exists_lifted_annular_scale (M x : ℝ) (hM : 0<M) (hx : M<x) (hupper : x≤49*M) :
    ∃j : Fin 7, ((2:ℝ)^j.val*M)/2≤x ∧ x≤(2:ℝ)^j.val*M := by
  have hratio : 1≤x/M := (le_div_iff₀ hM).mpr (by linarith)
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
  have hratioU : x/M≤49 := (div_le_iff₀ hM).mpr hupper
  have hk : k<6 := by
    by_contra hn
    have h6 : 6≤k := by omega
    have hp : (2:ℝ)^6≤(2:ℝ)^k := pow_le_pow_right₀ (by norm_num) h6
    norm_num at hp
    linarith
  refine ⟨⟨k+1,by omega⟩,?_,?_⟩
  · have hl := (le_div_iff₀ hM).mp hlo
    simpa only [pow_succ,mul_assoc,mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using hl
  · exact ((div_lt_iff₀ hM).mp hhi).le

lemma sum_injective_mask_le {ι : Type*} [Fintype ι]
    (f : ι → Ideal O) (hf : Function.Injective f) (S : Finset (Ideal O))
    (v : Ideal O → ℝ) (hv : ∀I, 0≤v I) :
    (∑i, if f i∈S then v (f i) else 0)≤∑I∈S,v I := by
  classical
  rw [←Finset.sum_filter]
  rw [←Finset.sum_image (f := v) (g := f) (by intro i hi j hj he; exact hf he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact (Finset.mem_filter.mp hi).2
  · intro I hI hnot
    exact hv I

theorem squarefreeHigh_energy_le_annuli (M N K : ℝ) (hM : 0<M)
    (a : idealRange N → ℂ) (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val) :
    (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K a := by
  classical
  let E := fun I : Ideal O => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2
  have hE (I : Ideal O) : 0≤E I := sq_nonneg _
  have hlift :
      (∑I : squarefreeHighRange M K, E I.val) = ∑I : squarefreeHighRange M K, E (annularLift M K I) := by
    apply Finset.sum_congr rfl
    intro I _
    dsimp only [E]
    rw [annularLift_row_sum M N K I a hcop]
  change (∑I : squarefreeHighRange M K, E I.val)≤_
  rw [hlift]
  have hpoint (I : squarefreeHighRange M K) : E (annularLift M K I) ≤
      ∑j : Fin 7, if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := by
    have hp := annularLift_properties M K I
    obtain ⟨j,hjlo,hjhi⟩ := exists_lifted_annular_scale M _ hM hp.2.2.1 hp.2.2.2
    have hMj : 0<(2:ℝ)^j.val*M := by positivity
    have hm : annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K :=
      mem_highKernelRange.mpr ⟨hp.1,by linarith,hp.2.1⟩
    have hw : annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)=1 := by
      apply QuadraticInitialBound.annularSieveBump_eq_one
      · exact (le_div_iff₀ hMj).mpr (by linarith)
      · exact (div_le_one hMj).mpr hjhi
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 7)))
      (f := fun j => if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0)
      (fun j _ => by split_ifs; exact mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (hE _); exact le_rfl)
      (Finset.mem_univ j)
    simpa only [hm,ite_true,hw,one_mul] using hh
  calc
    _ ≤ ∑I : squarefreeHighRange M K, ∑j : Fin 7,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 :=
      Finset.sum_le_sum (fun I _ => hpoint I)
    _ = ∑j : Fin 7, ∑I : squarefreeHighRange M K,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [annularHighEnergy,Finset.sum_coe_sort (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)]
      exact sum_injective_mask_le (annularLift M K) (annularLift_injective M K)
        (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)
        (fun I => mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (hE I))

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open FiniteSieveRestriction

theorem liftingQuotientColumn_injective (N : ℝ) : Function.Injective (liftingQuotientColumn N) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  exact idealQuotient_injective_on liftingPrime
    (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2 (congrArg Subtype.val h)

theorem liftingFreeCoefficient_coprime (N : ℝ) (a : idealRange N → ℂ)
    (J : idealRange N) (hJ : liftingFreeCoefficient N a J≠0) : IsCoprime liftingPrime J.val := by
  apply ideals_coprime_of_relprime
  apply liftingPrime_prime.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  exact hJ (by simp only [liftingFreeCoefficient,hd,ite_true])

theorem liftingDividedCoefficient_coprime (N : ℝ) (a : idealRange N → ℂ)
    (J : idealRange N) (hJ : liftingDividedCoefficient N a J≠0) : IsCoprime liftingPrime J.val := by
  classical
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have hdiv := (Finset.mem_filter.mp I.property).2
  have hsf : Squarefree (liftingPrime*idealQuotient liftingPrime I.val.val) := by
    rw [idealQuotient_mul hdiv]
    exact (mem_idealRange.mp I.val.property).1.2.1
  exact ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp hsf).1

theorem liftingDividedCoefficient_row_sum (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    (∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J) =
      ∑J : liftingDivisibleColumns N, quadraticRow (idealQuotient liftingPrime J.val.val) z*a J.val := by
  simpa only [liftingDividedCoefficient,liftingQuotientColumn] using
    extendByZero_matrix Finset.univ (liftingQuotientColumn N)
      (fun J : liftingDivisibleColumns N => a J.val) (fun (_ : Unit) J => quadraticRow J.val z) ()

theorem liftingCoefficient_row_split (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    (∑J : idealRange N, quadraticRow J.val z*a J) =
      (∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J) +
      quadraticRow liftingPrime z*(∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J) := by
  rw [liftingDividedCoefficient_row_sum,Finset.mul_sum,
    Finset.sum_coe_sort (liftingDivisibleColumns N)
      (fun J => quadraticRow liftingPrime z*(quadraticRow (idealQuotient liftingPrime J.val) z*a J))]
  simp only [liftingDivisibleColumns,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hd : liftingPrime∣J.val
  · simp only [hd,ite_true,liftingFreeCoefficient,mul_zero,zero_add]
    rw [quadraticRow_divisor_factor J.val liftingPrime (mem_idealRange.mp J.property).1 hd z]
    ring
  · simp only [hd,ite_false,liftingFreeCoefficient,add_zero]

theorem liftingCoefficient_energy (N : ℝ) (a : idealRange N → ℂ) :
    (∑J : idealRange N, ‖liftingFreeCoefficient N a J‖^2) +
      (∑J : idealRange N, ‖liftingDividedCoefficient N a J‖^2) = ∑J, ‖a J‖^2 := by
  have he := extendByZero_energy Finset.univ (liftingQuotientColumn N)
    (fun J : liftingDivisibleColumns N => a J.val) (liftingQuotientColumn_injective N).injOn
  change (∑J : idealRange N, ‖liftingDividedCoefficient N a J‖^2)=
    ∑J : liftingDivisibleColumns N, ‖a J.val‖^2 at he
  rw [he,Finset.sum_coe_sort (liftingDivisibleColumns N) (fun J => ‖a J‖^2)]
  simp only [liftingDivisibleColumns,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hd : liftingPrime∣J.val <;>
    simp only [liftingFreeCoefficient,hd,ite_true,ite_false,norm_zero,zero_pow (by decide : 2≠0),zero_add,add_zero]

theorem liftingCoefficient_row_energy (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    ‖∑J : idealRange N, quadraticRow J.val z*a J‖^2 ≤
      2*(‖∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J‖^2 +
        ‖∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J‖^2) := by
  rw [liftingCoefficient_row_split]
  let u := ∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J
  let v := ∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J
  change ‖u+quadraticRow liftingPrime z*v‖^2≤2*(‖u‖^2+‖v‖^2)
  have hp : ‖quadraticRow liftingPrime z*v‖≤‖v‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one _ _)
  have hn : ‖u+quadraticRow liftingPrime z*v‖≤‖u‖+‖v‖ := by
    linarith [norm_add_le u (quadraticRow liftingPrime z*v)]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

theorem liftingFreeCoefficient_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N X (liftingFreeCoefficient N a) := by
  intro J hJ
  have hj : a J≠0 := by
    intro hz
    exact hJ (by simp only [liftingFreeCoefficient,hz,ite_self])
  exact ha J hj

theorem liftingDividedCoefficient_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N (X/7) (liftingDividedCoefficient N a) := by
  classical
  intro J hJ
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have he : liftingDividedCoefficient N a (liftingQuotientColumn N I)=a I.val :=
    extendByZero_apply_image _ _ _ (liftingQuotientColumn_injective N).injOn I (Finset.mem_univ I)
  have hn : a I.val≠0 := by rwa [he] at hJ
  have hs := ha I.val hn
  change (X/7)/2<(Ideal.absNorm (idealQuotient liftingPrime I.val.val):ℝ) ∧
    (Ideal.absNorm (idealQuotient liftingPrime I.val.val):ℝ)≤X/7
  rw [idealQuotient_norm_eq liftingPrime I.val.val liftingPrime_prime.ne_zero
    (Finset.mem_filter.mp I.property).2,liftingPrime_norm]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss FiniteSieveOperator

theorem ballQuadraticEnergy_low_high (M N K : ℝ) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      ∑I : squarefreeHighRange M K, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2 := by
  classical
  let E := fun I : Ideal O => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2
  have hs : (idealRange M).filter (fun I => (Ideal.absNorm I:ℝ)≤K) ⊆ idealRange K := by
    intro I hI
    exact mem_idealRange.mpr ⟨(mem_idealRange.mp (Finset.mem_filter.mp hI).1).1,(Finset.mem_filter.mp hI).2⟩
  have hlo : (∑I∈(idealRange M).filter (fun I => (Ideal.absNorm I:ℝ)≤K), E I) ≤
      sieveNorm K N*(∑J, ‖a J‖^2) := by
    calc
      _ ≤ ∑I∈idealRange K,E I := Finset.sum_le_sum_of_subset_of_nonneg hs (fun I hI hnot => sq_nonneg _)
      _ = ballQuadraticEnergy K N a := (Finset.sum_coe_sort (idealRange K) E).symm
      _ ≤ _ := FiniteSieveOperator.energy_bound (matrix K N) a
  change (∑I : idealRange M,E I.val)≤_+(∑I : squarefreeHighRange M K,E I.val)
  rw [Finset.sum_coe_sort (idealRange M) E,
    ←Finset.sum_filter_add_sum_filter_not (idealRange M) (fun I => (Ideal.absNorm I:ℝ)≤K) E]
  rw [Finset.sum_coe_sort (squarefreeHighRange M K) E]
  simp only [not_le,squarefreeHighRange]
  linarith

theorem ballQuadraticEnergy_lifted_annuli (M N K : ℝ) (hM : 0<M) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      2*((∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingFreeCoefficient N a)) +
        ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingDividedCoefficient N a)) := by
  have hlo := ballQuadraticEnergy_low_high M N K a
  have hs : (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      2*((∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2) +
        ∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) := by
    calc
      _ ≤ ∑I : squarefreeHighRange M K, 2*(
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2 +
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) :=
        Finset.sum_le_sum (fun I _ => liftingCoefficient_row_energy N a (primaryGenerator I.val))
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib]
  have hfree := squarefreeHigh_energy_le_annuli M N K hM (liftingFreeCoefficient N a)
    (liftingFreeCoefficient_coprime N a)
  have hdiv := squarefreeHigh_energy_le_annuli M N K hM (liftingDividedCoefficient N a)
    (liftingDividedCoefficient_coprime N a)
  linarith

end

open ActualEisensteinCubic CompletedGauss

theorem ballQuadraticEnergy_mono {M M' N : ℝ} (hM : M≤M') (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a≤ballQuadraticEnergy M' N a := by
  unfold ballQuadraticEnergy
  rw [Finset.sum_coe_sort (idealRange M)
    (fun I => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2),
    Finset.sum_coe_sort (idealRange M')
    (fun I => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (idealRange_mono hM) (fun I hI hnot => sq_nonneg _)

theorem ballQuadraticEnergy_coefficientAtScale (M N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀J, a J≠0 → (Ideal.absNorm J.val:ℝ)≤X) :
    ballQuadraticEnergy M N a=ballQuadraticEnergy M X (coefficientAtScale N X a) := by
  unfold ballQuadraticEnergy
  simp_rw [coefficientAtScale_row_sum N X a ha]

theorem ballQuadraticEnergy_column_shells (M N : ℝ) (lengthScale : ℕ) (hNL : N≤(2:ℝ)^lengthScale)
    (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1:ℝ)*∑j : Fin (lengthScale+1),
      ballQuadraticEnergy M N (dyadicColumnCoefficient N lengthScale hNL j a) := by
  simpa only [one_mul,ballQuadraticEnergy] using
    weighted_energy_column_shells N lengthScale hNL
      (fun I : idealRange M => fun J : idealRange N => quadraticRow J.val (primaryGenerator I.val))
      (fun _ => (1:ℝ)) (fun _ => by norm_num) a

theorem ballQuadraticEnergy_column_shells_at_scale (M N : ℝ) (lengthScale : ℕ) (hNL : N≤(2:ℝ)^lengthScale)
    (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1:ℝ)*∑j : Fin (lengthScale+1),
      ballQuadraticEnergy M ((2:ℝ)^j.val)
        (coefficientAtScale N ((2:ℝ)^j.val) (dyadicColumnCoefficient N lengthScale hNL j a)) := by
  apply (ballQuadraticEnergy_column_shells M N lengthScale hNL a).trans_eq
  apply congrArg (fun x : ℝ => (lengthScale + 1 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro j _
  exact ballQuadraticEnergy_coefficientAtScale M N _ _
    (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)

theorem columnDyadicLength_scale_upper (N : ℝ) (hN : 1≤N) :
    (2:ℝ)^columnDyadicLength N≤2*N := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0≤Real.log N/Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  calc
    _ = (2:ℝ)^((columnDyadicLength N:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2:ℝ)^(Real.log N/Real.log 2+1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil.le
    _ = 2*N := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
      have he : (2:ℝ)^(Real.log N/Real.log 2)=N :=
        Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
      rw [he,mul_comm]

theorem columnDyadicScale_bounds (N : ℝ) (hN : 1≤N) (j : Fin (columnDyadicLength N+1)) :
    1≤(2:ℝ)^j.val ∧ (2:ℝ)^j.val≤2*N := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  exact (pow_le_pow_right₀ (by norm_num) (by omega : j.val≤ columnDyadicLength N)).trans
    (columnDyadicLength_scale_upper N hN)

end

open scoped BigOperators Classical

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

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

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

theorem improved_threshold_reciprocal (α N M : ℝ) (_hα : 0<α) (hN : 0<N) (hM0 : 0<M)
    (hM : N^(2-1/α)≤M) : N^2/M≤N^(1/α) := by
  apply (div_le_iff₀ hM0).mpr
  have he : N^2=N^(2-1/α)*N^(1/α) := by
    rw [←Real.rpow_add hN]
    convert (preTransparency := .instances) (Real.rpow_two N).symm using 1 ; ring_nf
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hN.le (1/α))

theorem improved_threshold_low (α C η N M : ℝ) (hα : 0<α) (hC : 0<C)
    (hN : 0<N) (hM0 : 0<M) (hM : N^(2-1/α)≤M) :
    (selectedPoissonK C M N η)^α≤C ^α*(M*N)^(η*α)*N := by
  have hk : selectedPoissonK C M N η≤C*(M*N)^η*N^(1/α) := by
    unfold selectedPoissonK selectedPoissonT
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (improved_threshold_reciprocal α N M hα hN hM0 hM) (by positivity)
  have hk0 : 0≤ selectedPoissonK C M N η := by
    unfold selectedPoissonK selectedPoissonT
    positivity
  calc
    _ ≤ (C*(M*N)^η*N^(1/α))^α := Real.rpow_le_rpow hk0 hk hα.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤C*(M*N)^η) (by positivity),
        Real.mul_rpow hC.le (by positivity),←Real.rpow_mul (by positivity : 0≤M*N),
        ←Real.rpow_mul hN.le]
      have he : (1/α)*α=1 := by field_simp
      rw [he,Real.rpow_one]

theorem sieveNorm_large_rows (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hlarge : N^2≤M) :
    sieveNorm M N≤5*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤2*N := by
    have h := Nat.ceil_lt_add_one (by linarith : 0≤N)
    linarith
  have hsq : (⌈N⌉₊:ℝ)^2≤4*M := by
    calc
      _ ≤ (2*N)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hceil 2
      _ = 4*N^2 := by ring
      _ ≤ 4*M := by linarith
  have hh := sieveNorm_initial M N hM hN
  have hC := QuadraticInitialBound.initialSieveConstant_pos
  nlinarith

theorem hasSieveExponent_of_threshold_band (β : ℝ) (_hβ1 : 1≤β) (hβ2 : β≤2)
    (hband : ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^β≤M → M≤N^2 → sieveNorm M N≤C*(M*N)^ρ*M) :
    HasSieveExponent β := by
  intro ε hε
  have hρ : 0<ε/3 := by positivity
  obtain ⟨C,hC,hbound⟩ := hband (ε/3) hρ
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨C+5*I,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hpow : 1≤(M*N)^ε := Real.one_le_rpow hMN hε.le
  have hNb : 0≤N^β := Real.rpow_nonneg hN0.le _
  by_cases hlarge : N^2≤M
  · calc
      _ ≤ 5*I*M := sieveNorm_large_rows M N hM hN hlarge
      _ = (5*I)*1*M := by ring
      _ ≤ (C+5*I)*(M*N)^ε*(M+N^β) := by gcongr <;> linarith
  · let R := max M (N^β)
    have hNβsq : N^β≤N^2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hN hβ2
    have hR : 1≤R := hM.trans (le_max_left _ _)
    have hRM : M≤R := le_max_left _ _
    have hRN : N^β≤R := le_max_right _ _
    have hRsq : R≤N^2 := max_le (le_of_not_ge hlarge) hNβsq
    have hb := hbound R N hR hN hRN hRsq
    have hmono := sieveNorm_mono hRM (le_refl N)
    have hN2 : 1≤N^2 := one_le_pow₀ hN
    have hM3 : M≤M^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hM (show (1:ℕ)≤3 by decide)
    have hRN2 : R≤M*N^2 := by
      apply max_le
      · nlinarith
      · exact hNβsq.trans (by nlinarith)
    have hprod : R*N≤(M*N)^3 := by
      calc
        _ ≤ (M*N^2)*N := mul_le_mul_of_nonneg_right hRN2 hN0.le
        _ = M*N^3 := by ring
        _ ≤ M^3*N^3 := mul_le_mul_of_nonneg_right hM3 (by positivity)
        _ = _ := by ring
    have hRprod : (R*N)^(ε/3)≤(M*N)^ε := by
      calc
        _ ≤ ((M*N)^3)^(ε/3) := Real.rpow_le_rpow (by positivity) hprod hρ.le
        _ = _ := by
          rw [←Real.rpow_natCast (M*N) 3,←Real.rpow_mul (by positivity : 0≤M*N)]
          congr 1
          ring
    have hRadd : R≤M+N^β := max_le (by linarith) (by linarith)
    exact hmono.trans (hb.trans (by gcongr ; linarith))

open ActualEisensteinCubic CompletedGauss

theorem hasSieveExponent_of_shell_threshold (β : ℝ) (hβ1 : 1≤β) (hβ2 : β≤2)
    (hshell : ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M X : ℝ,
      1≤M → 1≤X → X^β≤M → ∀a : idealRange X → ℂ, CoefficientOnShell X X a →
      ballQuadraticEnergy M X a≤C*(M*X)^ρ*M*∑J,‖a J‖^2) :
    HasSieveExponent β := by
  apply hasSieveExponent_of_threshold_band β hβ1 hβ2
  intro ε hε
  have hρ : 0<ε/2 := by positivity
  obtain ⟨C,hC,hbound⟩ := hshell (ε/2) hρ
  let lengthScale := 2+1/((ε/2)*Real.log 2)
  have hL : 0<lengthScale := by
    have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [lengthScale]
    positivity
  refine ⟨4*C*8^(ε/2)*lengthScale,by positivity,?_⟩
  intro M N hM hN hMN hMsq
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hprod : 0<M*N := by positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (matrix M N) _ (by positivity)
  intro a
  let a' := fun j : Fin (columnDyadicLength N+1) =>
    coefficientAtScale N ((2:ℝ)^j.val)
      (dyadicColumnCoefficient N (columnDyadicLength N) (columnDyadicLength_cover N) j a)
  have hpart := ballQuadraticEnergy_column_shells_at_scale M N (columnDyadicLength N)
    (columnDyadicLength_cover N) a
  have hj (j : Fin (columnDyadicLength N+1)) :
      ballQuadraticEnergy M ((2:ℝ)^j.val) (a' j) ≤
        (4*C*8^(ε/2)*(M*N)^(ε/2)*M)*∑J,‖a' j J‖^2 := by
    let X := (2:ℝ)^j.val
    have hx := columnDyadicScale_bounds N hN j
    have hβ0 : 0≤β := by linarith
    have hXpow : X^β≤4*M := by
      calc
        _ ≤ (2*N)^β := Real.rpow_le_rpow (by positivity) hx.2 hβ0
        _ = 2^β*N^β := Real.mul_rpow (by norm_num) hN0.le
        _ ≤ 4*N^β := by
          have ht : (2:ℝ)^β≤4 := by
            have ht := Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1:ℝ)≤2) hβ2
            norm_num at ht
            exact ht
          exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hN0.le _)
        _ ≤ 4*M := by linarith
    have hshell' : CoefficientOnShell X X (a' j) :=
      coefficientAtScale_shell N X _ (dyadicColumnCoefficient_shell N _ _ j a)
    have hb := hbound (4*M) X (by linarith) hx.1 hXpow (a' j) hshell'
    have hp : ((4*M)*X)^(ε/2)≤8^(ε/2)*(M*N)^(ε/2) := by
      calc
        _ ≤ (8*(M*N))^(ε/2) := Real.rpow_le_rpow (by positivity) (by nlinarith [hx.2]) hρ.le
        _ = _ := Real.mul_rpow (by norm_num) hprod.le
    apply (ballQuadraticEnergy_mono (by linarith : M≤4*M) (a' j)).trans
    apply hb.trans
    calc
      _ ≤ C*(8^(ε/2)*(M*N)^(ε/2))*(4*M)*∑J,‖a' j J‖^2 := by gcongr
      _ = _ := by ring
  have he : (∑j : Fin (columnDyadicLength N+1), ∑J,‖a' j J‖^2)=∑J,‖a J‖^2 :=
    dyadicColumnCoefficient_at_scale_energy N _ _ a
  have hlen : (columnDyadicLength N+1:ℝ)≤lengthScale*(M*N)^(ε/2) := by
    apply (columnDyadicLength_small_power (ε/2) hρ N hN).trans
    change lengthScale*N^(ε/2)≤lengthScale*(M*N)^(ε/2)
    gcongr
    nlinarith
  change ballQuadraticEnergy M N a≤_
  apply hpart.trans
  calc
    _ ≤ (columnDyadicLength N+1:ℝ)*
        ∑j : Fin (columnDyadicLength N+1),
          (4*C*8^(ε/2)*(M*N)^(ε/2)*M)*∑J,‖a' j J‖^2 := by
      gcongr with j
      exact hj j
    _ = (columnDyadicLength N+1:ℝ)*(4*C*8^(ε/2)*(M*N)^(ε/2)*M)*(∑J,‖a J‖^2) := by
      rw [←Finset.mul_sum,he]
      ring
    _ ≤ (lengthScale*(M*N)^(ε/2))*(4*C*8^(ε/2)*(M*N)^(ε/2)*M)*(∑J,‖a J‖^2) := by gcongr
    _ = _ := by
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2)=(M*N)^ε := by
        rw [←Real.rpow_add hprod]
        congr 1
        ring
      calc
        _ = (4*C*8^(ε/2)*lengthScale)*((M*N)^(ε/2)*(M*N)^(ε/2))*M*(∑J,‖a J‖^2) := by ring
        _ = _ := by rw [hp]

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

theorem fixedCutoffBase_bounds : 4≤fixedCutoffBase ∧ fixedBadNorm≤fixedCutoffBase :=
  ⟨le_max_left _ _,le_max_right _ _⟩

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicLoss
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

theorem HasSieveExponent.ball_selected_high {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤ selectedPoissonK fixedCutoffBase M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      ballQuadraticEnergy M N a ≤
        (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+
          C*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
  obtain ⟨C,hC,hann⟩ := hexp.lifted_annular_selected hα1 hα2 η hη hη1 l A hl hA
  refine ⟨14*C,by positivity,?_⟩
  intro M N hM hN hthreshold hK a ha
  have hf (j : Fin 7) := hann M N hM hN hthreshold hK j 1 (by norm_num) (by norm_num)
    (liftingFreeCoefficient N a) (by simpa only [div_one] using liftingFreeCoefficient_shell N N a ha)
  have hd (j : Fin 7) := hann M N hM hN hthreshold hK j 7 (by norm_num) (by norm_num)
    (liftingDividedCoefficient N a) (liftingDividedCoefficient_shell N N a ha)
  have hsf := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hf j)
  have hsd := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hd j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsf hsd
  have he := liftingCoefficient_energy N a
  have hb := ballQuadraticEnergy_lifted_annuli M N (selectedPoissonK fixedCutoffBase M N η)
    (by linarith) a
  calc
    _ ≤ sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖^2)+
      2*(7*(C*(M*N)^(260*η)*M*∑J,‖liftingFreeCoefficient N a J‖^2)+
        7*(C*(M*N)^(260*η)*M*∑J,‖liftingDividedCoefficient N a J‖^2)) := by linarith
    _ = _ := by
      calc
        _ = sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖^2)+
          (14*C)*(M*N)^(260*η)*M*((∑J,‖liftingFreeCoefficient N a J‖^2)+
            (∑J,‖liftingDividedCoefficient N a J‖^2)) := by ring
        _ = _ := by rw [he]; ring

theorem HasSieveExponent.low_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (c : ℝ) (hc : 4≤ c) :
    ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N → N^(2-1/α)≤M → M≤N^2 →
      sieveNorm (selectedPoissonK c M N η) N≤C*(M*N)^(6*η)*M := by
  obtain ⟨C,hC,hrev⟩ := hexp.reverse η hη
  have hc0 : 0<c := by linarith
  refine ⟨C*c^η*(1+c^α),by positivity,?_⟩
  intro M N hM hN hthreshold hupper
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hNM := improved_threshold_ge_column α N M hα hN hthreshold
  have hNP : N≤M*N := by nlinarith
  have hK := (selectedPoisson_bounds c M N η hc hM hN hupper hη.le).2.1
  have hKP := (selectedPoisson_upper c c M N η hc le_rfl hM hN hη.le hη1).2.2
  have hprod : selectedPoissonK c M N η*N≤ c*(M*N)^4 := by
    calc
      _ ≤ (c*(M*N)^3)*(M*N) := by gcongr
      _ = _ := by ring
  have hsmall : (selectedPoissonK c M N η*N)^η≤ c^η*(M*N)^(4*η) := by
    calc
      _ ≤ (c*(M*N)^4)^η := Real.rpow_le_rpow (by positivity) hprod hη.le
      _ = _ := by
        rw [Real.mul_rpow hc0.le (by positivity)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
  have hmain : (selectedPoissonK c M N η)^α≤ c^α*(M*N)^(2*η)*M := by
    apply (improved_threshold_low α c η N M (by linarith) hc0 hN0 hM0 hthreshold).trans
    have hp : (M*N)^(η*α)≤(M*N)^(2*η) := Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hc0.le _))
      hNM hN0.le (by positivity)
  have hR : 1≤(M*N)^(2*η) := Real.one_le_rpow hP (by positivity)
  have hsum : N+(selectedPoissonK c M N η)^α≤(1+c^α)*(M*N)^(2*η)*M := by
    calc
      _ ≤ M+c^α*(M*N)^(2*η)*M := add_le_add hNM hmain
      _ ≤ (M*N)^(2*η)*M+c^α*(M*N)^(2*η)*M := by
        exact add_le_add (le_mul_of_one_le_left hM0.le hR) le_rfl
      _ = _ := by ring
  have hpowers : (M*N)^(4*η)*(M*N)^(2*η)=(M*N)^(6*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  calc
    _ ≤ C*(selectedPoissonK c M N η*N)^η*(N+(selectedPoissonK c M N η)^α) := hrev _ _ hK hN
    _ ≤ C*(c^η*(M*N)^(4*η))*((1+c^α)*(M*N)^(2*η)*M) := by gcongr
    _ = C*c^η*(1+c^α)*((M*N)^(4*η)*(M*N)^(2*η))*M := by ring
    _ = _ := by rw [hpowers]

end CanonicalQuadraticSieve

open scoped BigOperators Classical

namespace CanonicalQuadraticSieve

theorem sieveNorm_small_columns (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hN28 : N≤28) :
    sieveNorm M N≤785*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤28 := by
    exact_mod_cast (Nat.ceil_le.mpr hN28 : ⌈N⌉₊≤28)
  have hs : (⌈N⌉₊:ℝ)^2≤784 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) ⌈N⌉₊]
  have hc := QuadraticInitialBound.initialSieveConstant_pos
  have hb := sieveNorm_initial M N hM hN
  have ht : M+(⌈N⌉₊:ℝ)^2≤785*M := by linarith
  calc
    _ ≤ QuadraticInitialBound.initialSieveConstant*(M+(⌈N⌉₊:ℝ)^2) := hb
    _ ≤ QuadraticInitialBound.initialSieveConstant*(785*M) := mul_le_mul_of_nonneg_left ht hc.le
    _ = _ := by ring

theorem HasSieveExponent.shell_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) :
    ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^(2-1/α)≤M →
      ∀a : idealRange N → ℂ, CoefficientOnShell N N a →
      ballQuadraticEnergy M N a≤C*(M*N)^ρ*M*∑J,‖a J‖^2 := by
  intro ρ hρ
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : η≤ρ/600 := min_le_right _ _
  have h6 : 6*η≤ρ := by linarith only [hηρ,hη]
  have h260 : 260*η≤ρ := by linarith only [hηρ,hη]
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith only [hh]
  obtain ⟨CH,hCH,hhigh⟩ := hexp.ball_selected_high hα1 hα2 η hη hη1 l l horder horder
  obtain ⟨CL,hCL,hlow⟩ := hexp.low_threshold hα1 hα2 η hη hη1 fixedCutoffBase fixedCutoffBase_bounds.1
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  let C := 790*I+CL+CH
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M N hM hN hthreshold a ha
  have hP : 1≤M*N := by nlinarith only [hM,hN]
  have hPρ : 1≤(M*N)^ρ := Real.one_le_rpow hP hρ.le
  have hE : 0≤∑J,‖a J‖^2 := by positivity
  have hM0 : 0≤M := le_trans zero_le_one hM
  have hscale {x y : ℝ} (hxy : x≤y) :
      x*M*∑J,‖a J‖^2 ≤ y*M*∑J,‖a J‖^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxy hM0) hE
  have hmatrix : ballQuadraticEnergy M N a≤ sieveNorm M N*∑J,‖a J‖^2 :=
    FiniteSieveOperator.energy_bound (matrix M N) a
  by_cases hlarge : N^2≤M
  · have hb := sieveNorm_large_rows M N hM hN hlarge
    calc
      _ ≤ (5*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (5*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 5*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  by_cases hsmall : N≤28
  · have hb := sieveNorm_small_columns M N hM hN hsmall
    calc
      _ ≤ (785*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (785*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 785*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  have hupper : M≤N^2 := le_of_not_ge hlarge
  have hK := (selectedPoisson_bounds fixedCutoffBase M N η fixedCutoffBase_bounds.1 hM hN hupper hη.le).2.1
  have hb := hhigh M N hM (by linarith only [hsmall]) hthreshold hK a ha
  have hlb := hlow M N hM hN hthreshold hupper
  have hp6 : (M*N)^(6*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h6
  have hp260 : (M*N)^(260*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h260
  calc
    _ ≤ (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := hb
    _ ≤ (CL*(M*N)^(6*η)*M+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add hlb le_rfl) hE
    _ ≤ (CL*(M*N)^ρ*M+CH*(M*N)^ρ*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp6 hCL.le) hM0)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp260 hCH.le) hM0)) hE
    _ = (CL+CH)*(M*N)^ρ*M*∑J,‖a J‖^2 := by ring
    _ ≤ _ := hscale (mul_le_mul_of_nonneg_right
      (show CL+CH≤C by dsimp [C]; linarith only [hI])
      (Real.rpow_nonneg (by positivity) _))

theorem HasSieveExponent.improve {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) : HasSieveExponent (2-1/α) := by
  have hα : 0<α := by linarith
  have hfrac : 1/α≤1 := (div_le_one hα).mpr hα1
  have hpos : 0≤1/α := by positivity
  apply hasSieveExponent_of_shell_threshold (2-1/α) (by linarith) (by linarith)
  exact hexp.shell_threshold hα1 hα2

open ActualEisensteinCubic CompletedGauss

theorem hasSieveExponent_one : HasSieveExponent 1 :=
  hasSieveExponent_one_of_improvement (fun _α hα hα2 h => h.improve hα.le hα2)

theorem sieveNorm_sharp :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N →
      sieveNorm M N≤C*(M*N)^ε*(M+N) := by
  simpa only [HasSieveExponent,Real.rpow_one] using hasSieveExponent_one

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.ProductColumns
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
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

theorem product_fiber_card (P : Finset (Ideal O×Ideal O)) (I : Ideal O) (hI : I≠0) :
    (P.filter (fun p => p.1*p.2=I)).card≤(idealDivisors I).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hI).mpr
    rw [←(Finset.mem_filter.mp hp).2]
    exact dvd_mul_right _ _
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hz : p.1≠0 := by intro hz; simp only [hz,zero_mul] at hp'; exact hI hp'.symm
    apply Prod.ext he
    apply mul_left_cancel₀ hz
    rw [hp',he,hq']

end CanonicalQuadraticSieve

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

theorem squarefree_all_column_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hinj : Function.Injective cols) (X K : ℝ)
    (hcols : ∀j,Squarefree (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤X) (a : n → ℂ) :
    (∑k : idealRange K,‖∑j,quadraticRow k.val (primaryGenerator (cols j))*a j‖^2)≤
      4*sieveNorm X K*∑j,‖a j‖^2 := by
  classical
  let sector (E : fixedBadPrimes.powerset) := {j : n // badPrimeSector (cols j)=E}
  have hsector (E : fixedBadPrimes.powerset) :
      (∑k : idealRange K,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2)≤
        sieveNorm X K*∑j : sector E,‖a j.val‖^2 := by
    let good : sector E → Ideal O := fun j => goodSquarefreePart (cols j.val)
    have hg : Function.Injective good := by
      intro i j hij
      apply Subtype.ext
      apply hinj
      exact goodSquarefreePart_injective_on_sector _ _ (hcols i.val).1 (hcols j.val).1
        (i.property.trans j.property.symm) hij
    have hgood (j : sector E) : Admissible (good j) ∧ (Ideal.absNorm (good j):ℝ)≤X :=
      mem_idealRange.mp (goodSquarefreePart_mem_idealRange _ (hcols j.val).1 X (hcols j.val).2)
    let B : Matrix (sector E) (idealRange K) ℂ := fun j k => quadraticRow k.val (primaryGenerator (good j))
    have hB := family_squared_norm_le good (fun k : idealRange K => k.val) hg Subtype.val_injective X K
      hgood (fun k => mem_idealRange.mp k.property)
    change ‖FiniteSieveOperator.operator B‖^2≤ sieveNorm X K at hB
    have hBT : B.conjTranspose=(fun k j => quadraticRow k.val (primaryGenerator (good j))) := by
      ext k j
      exact canonical_quadraticRow_star _ (mem_idealRange.mp k.property).1 _
    have he := FiniteSieveOperator.energy_bound B.conjTranspose (fun j : sector E => a j.val)
    rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
    have hrow (k : idealRange K) :
        (∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val)=
          quadraticRow k.val (primaryGenerator (sectorBadIdeal E))*
          ∑j : sector E,quadraticRow k.val (primaryGenerator (good j))*a j.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hj := sector_bad_good_product (cols j.val) (hcols j.val).1 E j.property
      have hq : quadraticRow k.val (primaryGenerator (cols j.val))=
          quadraticRow k.val (primaryGenerator (sectorBadIdeal E))*quadraticRow k.val (primaryGenerator (good j)) := by
        conv_lhs => rw [←hj]
        rw [primaryGenerator_mul,canonical_quadraticRow_argument_mul _ (mem_idealRange.mp k.property).1]
      rw [hq]
      ring
    have hpoint (k : idealRange K) :
        ‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2≤
          ‖∑j : sector E,quadraticRow k.val (primaryGenerator (good j))*a j.val‖^2 := by
      rw [hrow,norm_mul]
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    exact (Finset.sum_le_sum (fun k _ => hpoint k)).trans
      (he.trans (mul_le_mul_of_nonneg_right hB (by positivity)))
  have hpoint (k : idealRange K) :
      ‖∑j,quadraticRow k.val (primaryGenerator (cols j))*a j‖^2≤
        4*∑E : fixedBadPrimes.powerset,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 := by
    rw [←Fintype.sum_fiberwise (fun j => badPrimeSector (cols j))]
    have hn := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sum_le Finset.univ (fun E : fixedBadPrimes.powerset =>
        ∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val)) 2
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : fixedBadPrimes.powerset => (1:ℝ))
      (fun E : fixedBadPrimes.powerset => ‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖)
    have hcard : Fintype.card fixedBadPrimes.powerset=4 := by
      rw [Fintype.card_coe,fixedBadPrimes_powerset_card]
    apply hn.trans
    simpa [hcard,fixedBadPrimes_card] using hc
  calc
    _ ≤ ∑k : idealRange K,4*∑E : fixedBadPrimes.powerset,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = 4*∑E : fixedBadPrimes.powerset,∑k : idealRange K,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ 4*∑E : fixedBadPrimes.powerset,sieveNorm X K*∑j : sector E,‖a j.val‖^2 := by
      gcongr with E
      exact hsector E
    _ = _ := by
      have he : (∑E : fixedBadPrimes.powerset,∑j : sector E,‖a j.val‖^2)=∑j,‖a j‖^2 :=
        Fintype.sum_fiberwise (fun j => badPrimeSector (cols j)) (fun j => ‖a j‖^2)
      rw [←Finset.mul_sum,he]
      ring

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Ideal
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem idealKernel_norm_le_one (I J : Ideal Eis) : ‖idealKernel I J‖ ≤ 1 := by
  rw [idealKernel, ← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm (primaryGenerator J) I) 2).trans_eq (by norm_num)

theorem mem_idealRange {X : ℝ} {I : Ideal Eis} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.le_floor hN⟩, ha⟩
    intro hz
    exact (primaryGenerator_ne_zero_ideal I ha.2) (Ideal.absNorm_eq_zero_iff.mp hz)

theorem family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal Eis) (cols : n → Ideal Eis)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => idealKernel (cols j) (rows i)) ≤ sieveNorm M N := by
  let r : m → idealRange M := fun i => ⟨rows i, mem_idealRange.mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (idealMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.IdealMasks
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

theorem scaled_product_fiber_card
    (pairs : Finset (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O))
    (B J : Ideal ActualEisensteinCubic.O) (hJ : J ≠ 0) :
    ((pairs.filter (fun p => p.2 * (B * p.1) = J)).card) ≤ (idealDivisors J).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hJ).mpr
    refine ⟨p.2 * B, ?_⟩
    rw [← (Finset.mem_filter.mp hp).2]
    ring
  · intro p hp q hq hpq
    have hep := (Finset.mem_filter.mp hp).2
    have heq := (Finset.mem_filter.mp hq).2
    have hBm : B * p.1 ≠ 0 := by
      intro hz
      apply hJ
      rw [← hep, hz, mul_zero]
    apply Prod.ext hpq
    apply mul_right_cancel₀ hBm
    rw [hep, hpq, heq]

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Gcd
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubic_admissible_of_dvd {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible D := by
  refine ⟨hI.1.squarefree_of_dvd hD, ?_⟩
  obtain ⟨J, he⟩ := hD
  have hp := hI.2
  rw [he, primaryGenerator_mul] at hp
  exact (mul_ne_zero_iff.mp hp).1

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Fibers
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

theorem fiber_energy_bound {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D E : κ → ℝ) (hp : ∀ i ∈ s, p i ∈ t)
    (hE : ∀ j ∈ t, 0 ≤ E j)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    ∑ i ∈ s, w i * E (p i) ≤ ∑ j ∈ t, D j * E j := by
  calc
    ∑ i ∈ s, w i * E (p i) =
        ∑ j ∈ t, ∑ i ∈ s with p i = j, w i * E (p i) :=
      (Finset.sum_fiberwise_of_maps_to hp _).symm
    _ = ∑ j ∈ t, (∑ i ∈ s with p i = j, w i) * E j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ j ∈ t, D j * E j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hD j hj) (hE j hj)

theorem finite_expansion_energy {κ ι : Type*} [DecidableEq ι]
    (rows : Finset κ) (terms : Finset ι) (active : κ → Finset ι)
    (w F : κ → ι → ℂ) (C : ℝ)
    (hsub : ∀ k ∈ rows, active k ⊆ terms)
    (hw : ∀ k ∈ rows, ∀ i ∈ active k, ‖w k i‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((active k).card : ℝ) ≤ C) :
    (∑ k ∈ rows, ‖∑ i ∈ active k, w k i * F k i‖ ^ 2) ≤
      C * ∑ i ∈ terms, ∑ k ∈ rows, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
  have hlocal (k : κ) (hk : k ∈ rows) :
      ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        C * ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
    have hb : ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        ((active k).card : ℝ) * ∑ i ∈ active k, ‖w k i * F k i‖ ^ 2 := by
      calc
        _ ≤ (∑ i ∈ active k, ‖w k i * F k i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := by
          simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
            Finset.sum_mul_sq_le_sq_mul_sq (active k) (fun _ => (1 : ℝ))
              (fun i => ‖w k i * F k i‖)
    have hsum : (∑ i ∈ active k, ‖w k i * F k i‖ ^ 2) ≤
        ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw k hk i hi)
    exact hb.trans (mul_le_mul (hcard k hk) hsum
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (le_trans (Nat.cast_nonneg _) (hcard k hk)))
  calc
    _ ≤ ∑ k ∈ rows, C * ∑ i ∈ active k, ‖F k i‖ ^ 2 :=
      Finset.sum_le_sum hlocal
    _ = C * ∑ k ∈ rows, ∑ i ∈ active k, ‖F k i‖ ^ 2 := by rw [Finset.mul_sum]
    _ = C * ∑ k ∈ rows, ∑ i ∈ terms, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun hi => ⟨hsub k hk hi, hi⟩, And.right⟩
    _ = _ := by rw [Finset.sum_comm]

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Hybrid
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

local notation "Eis" => ActualEisensteinCubic.O

theorem inverseCubicKernel_norm_le_one (P n : Ideal Eis) :
    ‖inverseCubicKernel P n‖ ≤ 1 := by
  simpa only [inverseCubicKernel, norm_star, CubicSieve.idealKernel] using
    CubicSieve.idealKernel_norm_le_one P n

theorem dyadic_normalized_coefficient_energy
    (S : Finset (Ideal Eis)) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ P ∈ S, ‖a P‖ ≤ 1) :
    (∑ P ∈ S, ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2) ≤ 256 := by
  have hL0 : 0 < L := by linarith
  have hP0 (P : Ideal Eis) (hP : P ∈ S) : 0 < (Ideal.absNorm P : ℝ) :=
    hL0.trans_le (hS P hP).1
  have hcount : (S.card : ℝ) ≤ 128 * (2 * L) := by
    apply DescentFiberCost.finite_ideal_count_real S (2 * L) (by linarith)
    · intro P hP hz
      have hn := hP0 P hP
      simp [hz] at hn
    · intro P hP
      exact (hS P hP).2
  have hterm (P : Ideal Eis) (hP : P ∈ S) :
      ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2 ≤ 1 / L := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    calc
      _ ≤ 1 / (Ideal.absNorm P : ℝ) :=
        div_le_div_of_nonneg_right
          (by simpa using pow_le_pow_left₀ (norm_nonneg _) (ha P hP) 2) (hP0 P hP).le
      _ ≤ _ := one_div_le_one_div_of_le hL0 (hS P hP).1
  calc
    _ ≤ ∑ _P ∈ S, (1 / L : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) / L := by simp [div_eq_mul_inv]
    _ ≤ (128 * (2 * L)) / L := div_le_div_of_nonneg_right hcount hL0.le
    _ = 256 := by field_simp; ring

theorem hybridCubicCoefficient_energy
    (R r h t : Ideal Eis) (S : Finset (Ideal Eis)) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ P ∈ S, ‖a (R * P)‖ ≤ 1) :
    (∑ P ∈ S, ‖hybridCubicCoefficient R r h t a P‖ ^ 2) ≤ 256 := by
  apply dyadic_normalized_coefficient_energy S L hL hS
  intro P hP
  by_cases hc : IsCoprime P (h * t)
  · simp only [hc, if_pos, mul_one, norm_mul]
    exact (mul_le_mul (ha P hP) (inverseCubicKernel_norm_le_one P r)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · simp [hc]

theorem hybridColumnCoefficient_norm_le_one (R r c m h : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (hb : ‖beta (r * c) m h‖ ≤ 1) :
    ‖hybridColumnCoefficient R r beta c m h‖ ≤ 1 := by
  simp only [hybridColumnCoefficient, norm_mul]
  have hfirst : ‖beta (r * c) m h‖ *
      ‖CanonicalQuadraticSieve.quadraticRow (R * r)
        (CompletedGauss.primaryGenerator (m * h))‖ ≤ 1 := by
    exact (mul_le_mul hb (CanonicalQuadraticSieve.quadraticRow_norm_le_one _ _)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (mul_le_mul hfirst (inverseCubicKernel_norm_le_one R ((r * c) * m))
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SieveComposition
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators
noncomputable section

theorem bounded_finset_coefficient_sum_sq {C : Type*} (s : Finset C)
    (b f : C → ℂ) (hb : ∀ c ∈ s, ‖b c‖ ≤ 1) :
    ‖∑ c ∈ s, b c * f c‖ ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖f c‖ ^ 2 := by
  classical
  have h := finite_expansion_energy ({()} : Finset Unit) s
    (fun _ => s) (fun _ => b) (fun _ => f) (s.card : ℝ)
    (by simp) (by simpa using hb) (by simp)
  simpa using h

theorem positive_triple_enlarge {M H C : Type*}
    [DecidableEq M] [DecidableEq H] [DecidableEq C]
    (pairs : Finset (M × H)) (cset : M → Finset C)
    (hs : Finset H) (mc : Finset (M × C)) (E : H → M → C → ℝ)
    (hh : ∀ p ∈ pairs, p.2 ∈ hs)
    (hm : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc)
    (hE : ∀ h m c, 0 ≤ E h m c) :
    (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      ∑ h ∈ hs, ∑ u ∈ mc, E h u.1 u.2 := by
  let f : (Σ _p : M × H, C) → H × (M × C) := fun p => (p.1.2, (p.1.1, p.2))
  have hf : Function.Injective f := by
    have hi : Function.LeftInverse
        (fun u : H × (M × C) => (⟨(u.2.1, u.1), u.2.2⟩ : Σ _p : M × H, C)) f := by
      rintro ⟨⟨m, h⟩, c⟩
      rfl
    exact hi.injective
  have hmapped : ((pairs.sigma (fun p => cset p.1)).image f) ⊆ hs ×ˢ mc := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    have hp' := Finset.mem_sigma.mp hp
    exact Finset.mem_product.mpr ⟨hh p.1 hp'.1, hm p.1 hp'.1 p.2 hp'.2⟩
  have hb := Finset.sum_le_sum_of_injOn f hf.injOn hmapped
    (f := fun p : Σ _p : M × H, C => E p.1.2 p.1.1 p.2)
    (g := fun u : H × (M × C) => E u.1 u.2.1 u.2.2)
    (by intros; exact le_rfl) (by intro u _ _; exact hE _ _ _)
  simpa only [Finset.sum_sigma, Finset.sum_product] using hb

theorem column_fiber_sieve {K X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (rows : Finset K) (source : Finset X) (target : Finset Y)
    (φ : X → Y) (q : K → Y → ℂ) (a : X → ℂ) (Q D : ℝ) (hQ : 0 ≤ Q)
    (hφ : ∀ x ∈ source, φ x ∈ target)
    (hfiber : ∀ y ∈ target, ((source.filter (fun x => φ x = y)).card : ℝ) ≤ D)
    (hsieve : ∀ f : Y → ℂ,
      (∑ k ∈ rows, ‖∑ y ∈ target, q k y * f y‖ ^ 2) ≤
        Q * ∑ y ∈ target, ‖f y‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ x ∈ source, q k (φ x) * a x‖ ^ 2) ≤
      Q * D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
  let f : Y → ℂ := fun y => ∑ x ∈ source with φ x = y, a x
  have he (k : K) : (∑ x ∈ source, q k (φ x) * a x) =
      ∑ y ∈ target, q k y * f y := by
    rw [← Finset.sum_fiberwise_of_maps_to hφ]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp only [f]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  have hf := finite_expansion_energy target source
    (fun y => source.filter (fun x => φ x = y)) (fun _ _ => 1) (fun _ => a) D
    (fun _ _ => Finset.filter_subset _ _) (by simp) hfiber
  have hf' : (∑ y ∈ target, ‖f y‖ ^ 2) ≤ D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
    have hrhs : (∑ x ∈ source, ∑ y ∈ target,
        if x ∈ source.filter (fun x => φ x = y) then ‖a x‖ ^ 2 else 0) =
        ∑ x ∈ source, ‖a x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hx, hφ x hx]
    rw [hrhs] at hf
    simpa only [one_mul, f] using hf
  simp_rw [he]
  exact (hsieve f).trans (by
    calc
      _ ≤ Q * (D * ∑ x ∈ source, ‖a x‖ ^ 2) := mul_le_mul_of_nonneg_left hf' hQ
      _ = _ := by ring)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Quadratic
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_squarefree_quadratic_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows cols : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ J ∈ cols, Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X) →
    ∀ a : Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2) ≤
        C * (K * X) ^ ε * (K + X) * ∑ J ∈ cols, ‖a J‖ ^ 2 := by
  obtain ⟨C, hC, hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro K X hK hX rows cols hrows hcols a
  have hf := squarefree_all_column_energy (fun J : cols => J.val) Subtype.val_injective X K
    (fun J => hcols J.val J.property) (fun J => a J.val)
  have hi (k : idealRange K) :
      (∑ J : cols, quadraticRow k.val (primaryGenerator J.val) * a J.val) =
        ∑ J ∈ cols, quadraticRow k.val (primaryGenerator J) * a J :=
    Finset.sum_coe_sort cols (fun J => quadraticRow k.val (primaryGenerator J) * a J)
  simp_rw [hi] at hf
  rw [Finset.sum_coe_sort (idealRange K)
    (fun k => ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2),
    Finset.sum_coe_sort cols (fun J => ‖a J‖ ^ 2)] at hf
  have hr : rows ⊆ idealRange K := fun k hk => mem_idealRange.mpr (hrows k hk)
  have he : (∑ k ∈ rows, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2) ≤
      ∑ k ∈ idealRange K, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hr (by intro k _ _; exact sq_nonneg _)
  apply (he.trans hf).trans
  calc
    _ ≤ 4 * (C * (X * K) ^ ε * (X + K)) * ∑ J ∈ cols, ‖a J‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (hsharp X K hX hK) (by norm_num)
    _ = _ := by rw [mul_comm X K, add_comm X K]; ring

theorem quadratic_squarefree_product_column_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ a : Ideal Eis × Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Cq, hCq, hquad⟩ := finite_squarefree_quadratic_energy (ε / 2) hhalf
  obtain ⟨Cd, hCd, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) hhalf
  refine ⟨Cq * Cd, mul_pos hCq hCd, ?_⟩
  intro K X hK hX rows pairs hrows hpairs a
  let target := pairs.image (fun p => p.1 * p.2)
  have ht (J : Ideal Eis) (hJ : J ∈ target) :
      Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hpairs p hp
  have hfiber (J : Ideal Eis) (hJ : J ∈ target) :
      ((pairs.filter (fun p => p.1 * p.2 = J)).card : ℝ) ≤ Cd * X ^ (ε / 2) := by
    apply (Nat.cast_le.mpr (product_fiber_card pairs J (ht J hJ).1.ne_zero)).trans
    exact (hdiv J (ht J hJ).1.ne_zero).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (ht J hJ).2 hhalf.le) hCd.le)
  have he := column_fiber_sieve rows pairs target (fun p => p.1 * p.2)
    (fun k J => quadraticRow k (primaryGenerator J)) a
    (Cq * (K * X) ^ (ε / 2) * (K + X)) (Cd * X ^ (ε / 2)) (by positivity)
    (fun p hp => Finset.mem_image_of_mem _ hp) hfiber
    (hquad K X hK hX rows target hrows ht)
  apply he.trans
  have hKX : 0 < K * X := mul_pos (by linarith) (by linarith)
  have hpow : (K * X) ^ (ε / 2) * X ^ (ε / 2) ≤ (K * X) ^ ε := by
    calc
      _ ≤ (K * X) ^ (ε / 2) * (K * X) ^ (ε / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hKX.le _)
        exact Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hK) hhalf.le
      _ = _ := by rw [← Real.rpow_add hKX]; congr 1 ; ring
  calc
    _ = (Cq * Cd) * ((K * X) ^ (ε / 2) * X ^ (ε / 2)) * (K + X) *
        ∑ p ∈ pairs, ‖a p‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem quadratic_fixed_factor_energy
    (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
    (hrows : ∀ k ∈ rows, Admissible k) (B : Ideal Eis)
    (a : Ideal Eis × Ideal Eis → ℂ) :
    (∑ k ∈ rows, ‖∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
    ∑ k ∈ rows, ‖∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  have he : (∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p) =
      quadraticRow k (primaryGenerator B) * ∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p := by
    simp only [primaryGenerator_mul,
      canonical_quadraticRow_argument_mul k (hrows k hk), Finset.mul_sum, mul_assoc]
  rw [he]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one k _)

theorem quadratic_squarefree_product_energy_fixed_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal Eis) (a : Ideal Eis × Ideal Eis → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := quadratic_squarefree_product_column_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B a
  exact (quadratic_fixed_factor_energy rows pairs (fun k hk => (hrows k hk).1) B a).trans
    (hb K X hK hX rows pairs hrows hpairs a)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.HybridReduction
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_inverse_cubic_energy
    (Jset Pset : Finset (Ideal Eis)) (N L : ℝ)
    (hJ : ∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N)
    (hP : ∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L)
    (a : Ideal Eis → ℂ) :
    (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2) ≤
      CubicSieve.sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  let A : Matrix Jset Pset ℂ := fun J P => CubicSieve.idealKernel P.val J.val
  have hnorm : CubicSieve.squaredNorm (fun J P => star (A J P)) =
      CubicSieve.squaredNorm A :=
    congrArg (fun z : ℝ => z ^ 2) (CubicSieve.operator_conjugate_norm A)
  have hfamily : CubicSieve.squaredNorm A ≤ CubicSieve.sieveNorm N L :=
    CubicSieve.family_squared_norm_le
      (fun J : Jset => J.val) (fun P : Pset => P.val)
      Subtype.val_injective Subtype.val_injective N L
      (fun J => hJ J.val J.property) (fun P => hP P.val P.property)
  have he := CubicSieve.energy_le_squaredNorm (fun J P => star (A J P)) (fun P => a P.val)
  rw [hnorm] at he
  have he' := he.trans (mul_le_mul_of_nonneg_right hfamily
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hinner (J : Jset) :
      (∑ P : Pset, star (A J P) * a P.val) =
        ∑ P ∈ Pset, a P * inverseCubicKernel P J.val := by
    simp only [A, inverseCubicKernel, CubicSieve.idealKernel, mul_comm]
    exact Finset.sum_coe_sort Pset
      (fun P => a P * star (ConcreteTraceCRT.eisEmbedding
        (CubicJacobiGlobal.idealSymbol P (primaryGenerator J.val))))
  simp_rw [hinner] at he'
  rw [Finset.sum_coe_sort Jset
    (fun J => ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2),
    Finset.sum_coe_sort Pset (fun P => ‖a P‖ ^ 2)] at he'
  exact he'

theorem hybrid_quadratic_reduction (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal Eis) (cset : Ideal Eis → Finset (Ideal Eis))
      (Pset : Finset (Ideal Eis)) (coef : Ideal Eis → Ideal Eis → ℂ)
      (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (Cbound : ℝ),
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * Cbound *
        ∑ p ∈ pairs, ∑ c ∈ cset p.1,
          ‖∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))‖ ^ 2 := by
  obtain ⟨C, hC, hquadratic⟩ := quadratic_squarefree_product_energy_fixed_factor ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B mBad cset Pset coef beta Cbound hcount hbeta
  let F (p : Ideal Eis × Ideal Eis) (c : Ideal Eis) :=
    ∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))
  have he := hquadratic K X hK hX rows pairs hrows hpairs B
    (fun p => ∑ c ∈ cset p.1, beta c p.1 p.2 * F p c)
  apply he.trans
  have hlocal (p : Ideal Eis × Ideal Eis) (hp : p ∈ pairs) :
      ‖∑ c ∈ cset p.1, beta c p.1 p.2 * F p c‖ ^ 2 ≤
        Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
    exact (bounded_finset_coefficient_sum_sq (cset p.1)
      (fun c => beta c p.1 p.2) (F p) (hbeta p hp)).trans
        (mul_le_mul_of_nonneg_right (hcount p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    _ ≤ C * (K * X) ^ ε * (K + X) *
        ∑ p ∈ pairs, Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlocal)
      positivity
    _ = _ := by rw [← Finset.mul_sum]; simp only [F]; ring

theorem cubic_product_row_bound_of_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal Eis × Ideal Eis)) (Jset Pset : Finset (Ideal Eis))
      (mBad : Ideal Eis) (S : ℝ),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ a : Ideal Eis → ℂ,
        (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2) ≤
          S * ∑ P ∈ Pset, ‖a P‖ ^ 2) →
      ∀ a : Ideal Eis → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * inverseCubicKernel P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * S * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨D, hD, ?_⟩
  intro N hN pairs Jset Pset mBad S hmap hJset hcubic a
  let E (J : Ideal Eis) := ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2
  have hfiber (J : Ideal Eis) (hJ : J ∈ Jset) :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤ D * N ^ ε := by
    have hJ0 := (hJset J hJ).1.1.ne_zero
    have hc : ((pairs.filter (fun p => p.2 * (mBad * p.1) = J)).card : ℝ) ≤
        ((IdealMobiusDivisorSum.idealDivisors J).card : ℝ) :=
      Nat.cast_le.mpr (scaled_product_fiber_card pairs mBad J hJ0)
    have hd := (hdiv J hJ0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hJset J hJ).2 hε.le) hD.le)
    exact (by simpa using hc :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤
        ((IdealMobiusDivisorSum.idealDivisors J).card : ℝ)).trans hd
  have hf := fiber_energy_bound pairs Jset (fun p => p.2 * (mBad * p.1))
    (fun _ => 1) (fun _ => D * N ^ ε) E hmap (fun _ _ => sq_nonneg _) hfiber
  simp only [one_mul, ← Finset.mul_sum] at hf
  apply hf.trans
  calc
    _ ≤ (D * N ^ ε) * (S * ∑ P ∈ Pset, ‖a P‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hcubic a) (by positivity)
    _ = _ := by ring

theorem cubic_product_row_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N L : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal Eis × Ideal Eis)) (Jset Pset : Finset (Ideal Eis))
      (mBad : Ideal Eis),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      ∀ a : Ideal Eis → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * inverseCubicKernel P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * CubicSieve.sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hb⟩ := cubic_product_row_bound_of_sieve ε hε
  refine ⟨D, hD, ?_⟩
  intro N L hN pairs Jset Pset mBad hmap hJ hP a
  exact hb N hN pairs Jset Pset mBad (CubicSieve.sieveNorm N L) hmap hJ
    (finite_inverse_cubic_energy Jset Pset N L hJ hP) a

theorem hybrid_fixed_block_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X N L : ℝ, 1 ≤ K → 1 ≤ X → 1 ≤ N →
    ∀ (rows : Finset (Ideal Eis)) (pairs cubicPairs : Finset (Ideal Eis × Ideal Eis))
      (Hset Jset Pset : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal Eis) (cset : Ideal Eis → Finset (Ideal Eis))
      (coef : Ideal Eis → Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
      (Cbound Ebound : ℝ), 0 ≤ Cbound →
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∀ p ∈ pairs, p.2 ∈ Hset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ cubicPairs) →
      (∀ u ∈ cubicPairs, u.2 * (mBad * u.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      (∀ h ∈ Hset, (∑ P ∈ Pset, ‖coef h P‖ ^ 2) ≤ Ebound) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (K * X * N) ^ ε * (K + X) * Cbound * (Hset.card : ℝ) *
        CubicSieve.sieveNorm N L * Ebound := by
  obtain ⟨Cq, hCq, hquad⟩ := hybrid_quadratic_reduction ε hε
  obtain ⟨D, hD, hcube⟩ := cubic_product_row_sieve_norm ε hε
  refine ⟨Cq * D, mul_pos hCq hD, ?_⟩
  intro K X N L hK hX hN rows pairs cubicPairs Hset Jset Pset hrows hpairs
    B mBad cset coef beta Cbound Ebound hCbound hcount hbeta hH hmc hmap hJ hP hcoef
  let E (h m c : Ideal Eis) := ‖∑ P ∈ Pset,
    coef h P * inverseCubicKernel P (c * (mBad * m))‖ ^ 2
  have hnorm : 0 ≤ CubicSieve.sieveNorm N L := sq_nonneg _
  have he := hquad K X hK hX rows pairs hrows hpairs B mBad cset Pset coef beta
    Cbound hcount hbeta
  have hpos := positive_triple_enlarge pairs cset Hset cubicPairs E hH hmc
    (fun _ _ _ => sq_nonneg _)
  have htotal : (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      (Hset.card : ℝ) * (D * N ^ ε * CubicSieve.sieveNorm N L * Ebound) := by
    apply hpos.trans
    calc
      _ ≤ ∑ _h ∈ Hset, D * N ^ ε * CubicSieve.sieveNorm N L * Ebound := by
        apply Finset.sum_le_sum
        intro h hh
        apply (hcube N L hN cubicPairs Jset Pset mBad hmap hJ hP (coef h)).trans
        exact mul_le_mul_of_nonneg_left (hcoef h hh)
          (mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)) hnorm)
      _ = _ := by simp
  apply he.trans
  calc
    _ ≤ (Cq * (K * X) ^ ε * (K + X) * Cbound) *
        ((Hset.card : ℝ) * (D * N ^ ε * CubicSieve.sieveNorm N L * Ebound)) := by
      apply mul_le_mul_of_nonneg_left htotal
      positivity
    _ = _ := by
      rw [Real.mul_rpow (show 0 ≤ K * X by positivity) (show 0 ≤ N by linarith)]
      ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Quotients
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem quotientSupport_nonzero (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, I ≠ 0)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) : J ≠ 0 := by
  have h := hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)
  exact (mul_ne_zero_iff.mp h).2

theorem quotientSupport_quadratic_admissible (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, CanonicalQuadraticSieve.Admissible I)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    CanonicalQuadraticSieve.Admissible J :=
  admissible_of_dvd (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ))
    (dvd_mul_left _ _)

theorem quotientSupport_cubic_admissible (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, CubicSieve.Admissible I)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    CubicSieve.Admissible J :=
  CubicSieve.cubic_admissible_of_dvd
    (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)) (dvd_mul_left _ _)

theorem quotientSupport_norm_le (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (N : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0) (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ N)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    (Ideal.absNorm J : ℝ) ≤ N := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hn : Ideal.absNorm J ≤ Ideal.absNorm (D * J) := by
    apply Nat.le_of_dvd
    · exact Nat.pos_of_ne_zero (fun hz => hS0 _ hDJ (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact map_dvd Ideal.absNorm (dvd_mul_left J D)
  exact (Nat.cast_le.mpr hn).trans (hS _ hDJ)

theorem quotientSupport_shell (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (L : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0)
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    max 1 (L / (Ideal.absNorm D : ℝ)) ≤ (Ideal.absNorm J : ℝ) ∧
      (Ideal.absNorm J : ℝ) ≤ 2 * max 1 (L / (Ideal.absNorm D : ℝ)) := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hnD : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hJ0 := quotientSupport_nonzero D hD S hS0 J hJ
  have hnJ : 1 ≤ (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hJ0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs := hS (D * J) hDJ
  simp only [map_mul, Nat.cast_mul] at hs
  constructor
  · refine max_le hnJ ((div_le_iff₀ hnD).mpr ?_)
    simpa only [mul_comm] using hs.1
  · have hj : (Ideal.absNorm J : ℝ) ≤ 2 * (L / (Ideal.absNorm D : ℝ)) := by
      have hj := (le_div_iff₀ hnD).mpr (show
          (Ideal.absNorm J : ℝ) * (Ideal.absNorm D : ℝ) ≤ 2 * L by
        simpa only [mul_comm] using hs.2)
      simpa only [mul_div_assoc] using hj
    exact hj.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

theorem quotient_hybridCubicCoefficient_energy
    (R r h t : Ideal Eis) (hR : R ≠ 0) (S : Finset (Ideal Eis)) (L : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0)
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ I ∈ S, ‖a I‖ ≤ 1) :
    (∑ P ∈ quotientSupport R S, ‖hybridCubicCoefficient R r h t a P‖ ^ 2) ≤ 256 := by
  apply hybridCubicCoefficient_energy R r h t (quotientSupport R S)
    (max 1 (L / (Ideal.absNorm R : ℝ))) (le_max_left _ _)
  · exact quotientSupport_shell R hR S L hS0 hS
  · intro P hP
    exact ha (R * P) ((mem_quotientSupport R P hR S).mp hP)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.OriginalBlock
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_original_quotient_block_oai (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X N L A H : ℝ,
      1 ≤ K → 1 ≤ X → 1 ≤ N → 1 ≤ A → 1 ≤ H →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
      (cset : Ideal Eis → Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧
        L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
      (∀ p ∈ pairs, p.2 ≠ 0 ∧ (Ideal.absNorm p.2 : ℝ) ≤ H) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1,
        c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A ∧ (r * c) * p.1 ∈ nset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta (r * c) p.1 p.2‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
          (∑ p ∈ pairs, quadraticRow k (primaryGenerator (p.1 * p.2)) *
            (∑ c ∈ cset p.1, hybridColumnCoefficient R r beta c p.1 p.2 *
              (∑ P ∈ quotientSupport R Pset,
                hybridCubicCoefficient R r p.2 t a P * inverseCubicKernel P (c * p.1))))‖ ^ 2) ≤
      C * (K * X * N) ^ ε * (K + X) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C, hC, hblock⟩ := hybrid_fixed_block_sieve_norm ε hε
  refine ⟨C * (128 * 128 * 256), by positivity, ?_⟩
  intro K X N L A H hK hX hN hA hH R r t hR hr rows nset Pset pairs cset a beta
    hrows hn hP ha hpairs hhs hcs hbeta
  let Hset := pairs.image Prod.snd
  let mc := (pairs.image Prod.fst).biUnion fun m => (cset m).image fun c => (m, c)
  have hRr : R * r ≠ 0 := mul_ne_zero hR hr
  have hn0 : ∀ n ∈ nset, n ≠ 0 := fun n hn' => (hn n hn').1.1.ne_zero
  have hP0 : ∀ P ∈ Pset, P ≠ 0 := fun P hP' => (hP P hP').1.1.ne_zero
  have hHcount : (Hset.card : ℝ) ≤ 128 * H := by
    apply DescentFiberCost.finite_ideal_count_real Hset H hH
    · intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      exact (hhs p hp).1
    · intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      exact (hhs p hp).2
  have hcCount : ∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ 128 * A := by
    intro p hp
    exact DescentFiberCost.finite_ideal_count_real (cset p.1) A hA
      (fun c hc => (hcs p hp c hc).1) (fun c hc => (hcs p hp c hc).2.1)
  have hmc : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc := by
    intro p hp c hc
    exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  have hmap : ∀ u ∈ mc, u.2 * (1 * u.1) ∈ quotientSupport r nset := by
    intro u hu
    obtain ⟨m, hm, cu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp cu
    apply (mem_quotientSupport r (c * (1 * p.1)) hr nset).mpr
    simpa only [one_mul, mul_assoc] using (hcs p hp c hc).2.2
  have he := hblock K X N (2 * L) hK hX hN
    (quotientSupport (R * r) rows) pairs mc Hset (quotientSupport r nset)
    (quotientSupport R Pset)
    (fun k hk => ⟨quotientSupport_quadratic_admissible (R * r) hRr rows
        (fun k hk => (hrows k hk).1) k hk,
      quotientSupport_norm_le (R * r) hRr rows K
        (fun k hk => (hrows k hk).1.1) (fun k hk => (hrows k hk).2) k hk⟩)
    hpairs 1 1 cset (fun h => hybridCubicCoefficient R r h t a)
    (hybridColumnCoefficient R r beta) (128 * A) 256 (by positivity) hcCount
    (fun p hp c hc => hybridColumnCoefficient_norm_le_one R r c p.1 p.2 beta (hbeta p hp c hc))
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) hmc hmap
    (fun J hJ => ⟨quotientSupport_cubic_admissible r hr nset (fun n hn' => (hn n hn').1) J hJ,
      quotientSupport_norm_le r hr nset N hn0 (fun n hn' => (hn n hn').2) J hJ⟩)
    (fun P hP' => ⟨quotientSupport_cubic_admissible R hR Pset (fun P hP' => (hP P hP').1) P hP',
      quotientSupport_norm_le R hR Pset (2 * L) hP0 (fun P hP' => (hP P hP').2.2) P hP'⟩)
    (fun h _ => quotient_hybridCubicCoefficient_energy R r h t hR Pset L hP0
      (fun P hP' => (hP P hP').2) a ha)
  simp only [one_mul] at he
  have hsqrt : ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹‖ ^ 2 =
      (Ideal.absNorm R : ℝ)⁻¹ := by
    rw [norm_inv, inv_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [norm_mul, mul_pow, hsqrt]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Nat.cast_nonneg _))).trans
  calc
    _ ≤ (Ideal.absNorm R : ℝ)⁻¹ *
      (C * (K * X * N) ^ ε * (K + X) * (128 * A) * (128 * H) *
        CubicSieve.sieveNorm N (2 * L) * 256) := by
      gcongr
      exact sq_nonneg _
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseMoment.hybrid_original_quotient_block_oai := @OAI.SevenEighths.InverseMoment.hybrid_original_quotient_block_oai
