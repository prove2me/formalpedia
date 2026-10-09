-- Prove2me | solution 1 for OAI.SevenEighths.HeckeInverseAmplification.averaged_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:17:27.076287+00:00
-- url     : https://prove2.me/submissions/85af1481-a5a6-4b85-b998-446a9830842f

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorPresentation
namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.pow {χ : MulChar R ℂ} {I : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (n : ℕ) : FactorsThroughIdeal (χ ^ n) I := by
  rw [factorsThroughIdeal_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply_coe, hχ u hu, one_pow]

end FiniteConductor

end SevenEighths

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
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

namespace CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_convergent
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) : MellinConvergent V s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_hasDerivAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt

end CubicReflectionKernel

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
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

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem mellinLogFamily_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (mellinLogFamily V)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2) • V (Real.exp (-p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).smul
    (hV.comp (Real.contDiff_exp.comp contDiff_snd.neg))

theorem mellinLogFamily_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hv : V (Real.exp (-u)) ≠ 0 := by
    intro hv
    exact hu (by simp [mellinLogFamily, hv])
  have hm := hsupp hv
  have hlow := Real.log_le_log ha hm.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hm.2
  simp only [Real.log_exp] at hlow hhigh
  constructor <;> linarith

theorem mellin_eq_logFamily_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * Complex.I) = 𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero,  sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, Complex.I_im, mul_one, zero_add]
  rfl

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection
namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

theorem primeProduct_ne_zero (s : Finset PrimeIdeal) : primeProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => P.property.ne_zero)

theorem factors_primeProduct (s : Finset PrimeIdeal) :
    normalizedFactors (primeProduct s) = s.val.map Subtype.val := by
  have h := normalizedFactors_prod_of_prime
    (m := s.val.map (fun P : PrimeIdeal => P.val)) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.property)
  simpa only [primeProduct, Finset.prod_eq_multiset_prod] using h

theorem primeSet_primeProduct (s : Finset PrimeIdeal) : primeSet (primeProduct s) = s := by
  ext P
  rw [mem_primeSet]
  simp only [primeSupport, factors_primeProduct, Multiset.mem_toFinset,
    Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨Q,hQ,he⟩
    have : Q=P := Subtype.ext he
    simpa [this] using hQ
  · intro h
    exact ⟨P,h,rfl⟩

theorem primeProduct_injective : Function.Injective primeProduct := by
  intro s t h
  simpa only [primeSet_primeProduct] using congrArg primeSet h

theorem primeProduct_squarefree (s : Finset PrimeIdeal) : Squarefree (primeProduct s) := by
  rw [squarefree_iff_nodup_normalizedFactors (primeProduct_ne_zero s),factors_primeProduct]
  exact s.nodup.map Subtype.val_injective

theorem primeProduct_primeSet (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeProduct (primeSet I) = I := by
  unfold primeProduct primeSet
  rw [Finset.prod_image]
  · change (∏ P ∈ (primeSupport I).attach, (fun Q : Ideal ActualEisensteinCubic.O => Q) P.val) = I
    exact (Finset.prod_attach (primeSupport I) (fun Q : Ideal ActualEisensteinCubic.O => Q)).trans
      (squarefree_support_product_self hI)
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

theorem mobiusPrimeCoeff_nonsquarefree (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : ¬Squarefree I) : mobiusPrimeCoeff w I=0 := by
  simp [mobiusPrimeCoeff,moebius_of_not_squarefree hI]

theorem mobiusPrimeCoeff_primeProduct (w : Ideal ActualEisensteinCubic.O → ℂ) (s : Finset PrimeIdeal) :
    mobiusPrimeCoeff w (primeProduct s) = ∏ P ∈ s, -w P.val := by
  have hm : (moebius (primeProduct s) : ℂ)=(-1:ℂ)^s.card := by
    rw [(primeProduct_squarefree s).moebius_eq,factors_eq_normalizedFactors,
      factors_primeProduct]
    simp
  rw [mobiusPrimeCoeff,hm]
  simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]
  rw [Finset.prod_neg]

theorem mobiusPrimeCoeff_tsum (w : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∑' s : Finset PrimeIdeal, ∏ P ∈ s, -w P.val := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun s => primeProduct s.val)
  · exact primeProduct_injective.comp Subtype.val_injective
  · intro I hI
    have hs : Squarefree I := by
      by_contra hs
      exact hI (mobiusPrimeCoeff_nonsquarefree w I hs)
    have hp : (∏ P ∈ primeSet I, -w P.val) ≠ 0 := by
      rw [←mobiusPrimeCoeff_primeProduct,primeProduct_primeSet I hs]
      exact hI
    exact ⟨⟨primeSet I,hp⟩,primeProduct_primeSet I hs⟩
  · intro s
    exact mobiusPrimeCoeff_primeProduct w s.val

theorem mobiusPrimeCoeff_euler (w : Ideal ActualEisensteinCubic.O → ℂ)
    (hw : Summable (fun P : PrimeIdeal => ‖w P.val‖)) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∏' P : PrimeIdeal, (1-w P.val) := by
  rw [mobiusPrimeCoeff_tsum]
  have hs : Summable (fun P : PrimeIdeal => ‖-w P.val‖) := by simpa using hw
  simpa only [sub_eq_add_neg] using
    (tprod_one_add (summable_finsetProd_of_summable_norm hs)).symm

end

section
open ActualEisensteinCubic
open Filter

lemma prime_norm_pos (P : PrimeIdeal) : (0 : ℝ) < Ideal.absNorm P.val := by
  have h := prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

lemma norm_primeNormPower (P : PrimeIdeal) (s : ℂ) :
    ‖primeNormPower P s‖=(Ideal.absNorm P.val : ℝ)^(-s.re) := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-s)

lemma one_sub_ne_zero {x : ℂ} (hx : ‖x‖<1) : 1-x≠0 := by
  intro h
  have he : x=1 := (sub_eq_zero.mp h).symm
  simp [he] at hx

end

open ActualEisensteinCubic

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O

end SmoothMobiusCorrection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CompletedGauss

section
open Filter MeasureTheory
open scoped Classical BigOperators Topology FourierTransform SchwartzMap ContDiff

lemma compactMellin_vertical_integrable (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin V) σ := by
  have hc : HasCompactSupport (CubicReflectionKernel.mellinLogFamily V σ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (CubicReflectionKernel.mellinLogFamily_support V a b ha hsupp σ)
  have hd : ContDiff ℝ ∞ (CubicReflectionKernel.mellinLogFamily V σ) :=
    (CubicReflectionKernel.mellinLogFamily_smooth V hV).comp (contDiff_const.prodMk contDiff_id)
  let f : 𝓢(ℝ,ℂ) := hc.toSchwartzMap hd
  have hf : Integrable (fun t : ℝ=>(𝓕 f) (t/(2*Real.pi))) := by
    simpa only [div_eq_mul_inv] using
      (𝓕 f).integrable.comp_mul_right' (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  change Integrable (fun t : ℝ=>mellin V ((σ:ℂ)+t*Complex.I))
  have hfcoe : (f:ℝ→ℂ)=CubicReflectionKernel.mellinLogFamily V σ := rfl
  simpa only [CubicReflectionKernel.mellin_eq_logFamily_fourier,
    SchwartzMap.fourier_coe,hfcoe] using hf

theorem compactMellin_inversion (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (σ x : ℝ) (hx : 0<x) :
    V x=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin V ((σ:ℂ)+t*Complex.I) := by
  have hm := mellinInv_mellin_eq σ V hx
    (CubicReflectionKernel.compact_source_mellin_convergent V a b ha hsupp hV σ)
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) hV.continuous.continuousAt
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using hm.symm

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma positive_cpow_vertical_norm (r σ t : ℝ) (hr : 0< r) :
    ‖(r:ℂ)^((σ:ℂ)+t*Complex.I)‖=r^σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_negative_vertical_norm (r σ t : ℝ) (hr : 0< r) :
    ‖(r:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=r^(-σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_vertical_continuous (r σ : ℝ) (hr : 0< r) :
    Continuous (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma positive_cpow_negative_vertical_continuous (r σ : ℝ) (hr : 0< r) :
    Continuous (fun t : ℝ=>(r:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma vertical_power_mul_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0< r) :
    Integrable (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)*M t) := by
  apply (hM.norm.const_mul (r^σ)).mono'
    ((positive_cpow_vertical_continuous r σ hr).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by simp only [Pi.mul_apply,norm_mul,positive_cpow_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0< r) (c : ℂ) :
    Integrable (fun t : ℝ=>c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t) := by
  apply (hM.norm.const_mul (‖c‖*r^(-σ))).mono'
    ((continuous_const.mul (positive_cpow_negative_vertical_continuous r σ hr)).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by
    simp only [Pi.mul_apply,norm_mul,positive_cpow_negative_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integral_norm (M : ℝ→ℂ) (r σ : ℝ) (hr : 0< r) (c : ℂ) :
    (∫t : ℝ,‖c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖)=
      (‖c‖*r^(-σ))*(∫t : ℝ,‖M t‖) := by
  simp only [norm_mul,positive_cpow_negative_vertical_norm r σ _ hr,integral_const_mul]

theorem weighted_vertical_sum_integral {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0< r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (M : ℝ→ℂ) (hM : Integrable M) :
    (∑' i,∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t)=
      ∫t : ℝ,(∑' i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I)))*M t := by
  have hi (i : α) := weighted_vertical_power_integrable M hM (r i) σ (hr i) (c i)
  have hs : Summable (fun i=>∫t : ℝ,‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖) := by
    simp only [weighted_vertical_power_integral_norm M _ σ (hr _) _]
    exact hc.mul_right _
  rw [integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>tsum_mul_right)

lemma positive_quotient_cpow_neg (r X : ℝ) (hr : 0< r) (hX : 0<X) (s : ℂ) :
    ((r/X:ℝ):ℂ)^(-s)=(r:ℂ)^(-s)*(X:ℂ)^s := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hr.le hX.le,
    Complex.cpow_neg,Complex.cpow_neg,div_inv_eq_mul]

theorem weightedMellin_inversion {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0< r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    (∑'i,c i*V (r i/X))=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin V ((σ:ℂ)+t*Complex.I)*(X:ℂ)^((σ:ℂ)+t*Complex.I)*
        (∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let M : ℝ→ℂ := fun t=>(X:ℂ)^((σ:ℂ)+t*Complex.I)*mellin V ((σ:ℂ)+t*Complex.I)
  have hM : Integrable M := vertical_power_mul_integrable _
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) X σ hX
  have hi (i : α) : c i*V (r i/X)=(1/(2*Real.pi):ℂ)*
      ∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t := by
    rw [compactMellin_inversion V a b ha hsupp hV σ _ (div_pos (hr i) hX)]
    rw [←mul_assoc,mul_comm (c i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>by
      dsimp only
      rw [positive_quotient_cpow_neg _ _ (hr i) hX]
      dsimp only [M]
      ring)
  simp_rw [hi]
  rw [tsum_mul_left,weighted_vertical_sum_integral r hr c σ hc M hM]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>by dsimp only [M];ring)

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Theta
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem completed_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inl (by simpa using hs₁))

theorem completed_differentiableAt_of_mean_zero {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (hw : ∑ a, w a = 0) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inr (pair_g₀_eq_zero w hw))

theorem latticeL_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, w a = 0) :
    DifferentiableAt ℂ (latticeL w) s := by
  have hΛ : DifferentiableAt ℂ (completed w) s := by
    rcases hs₁ with hs₁ | hw
    · exact completed_differentiableAt w hs₀ hs₁
    · exact completed_differentiableAt_of_mean_zero w hw hs₀
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul hΛ

theorem regularizedCompleted_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedCompleted w) s := by
  exact (((differentiableAt_id.sub_const 1).mul
    (((pair w).differentiable_Λ₀ s).sub
      ((differentiableAt_id.inv hs₀).mul_const (pair w).f₀))).add_const (pair w).g₀)

theorem regularizedCompleted_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedCompleted w s = (s - 1) * completed w s := by
  unfold regularizedCompleted completed WeakFEPair.Λ
  simp only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl,
    smul_eq_mul, one_div]
  have hsub : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  field_simp
  ring

theorem regularizedLatticeL_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedLatticeL w) s := by
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul
        (regularizedCompleted_differentiableAt w hs₀)

theorem regularizedLatticeL_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedLatticeL w s = (s - 1) * latticeL w s := by
  unfold regularizedLatticeL latticeL
  rw [regularizedCompleted_eq w hs₀ hs₁]
  ring

end SevenEighths.HeckeTheta

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Family
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeFamily

theorem continuedLattice_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, (coefficients χ) a = 0) :
    DifferentiableAt ℂ (continuedLattice χ) s :=
  HeckeTheta.latticeL_differentiableAt (coefficients χ) hs₀ hs₁

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.CharacterAnalytic
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeCharacterAnalytic

theorem continuedLattice_differentiableAt_nonprincipal (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (HeckeFamily.continuedLattice χ) s :=
  HeckeFamily.continuedLattice_differentiableAt χ hs₀
    (Or.inr (coefficients_sum_eq_zero χ hχ))

end SevenEighths.HeckeCharacterAnalytic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.IdealBridge
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeFamily

theorem LFunction_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ χ.residue ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s := by
  apply DifferentiableAt.div_const
  rcases hs₁ with hs₁ | hχ
  · exact continuedLattice_differentiableAt χ hs₀ (Or.inl hs₁)
  · exact HeckeCharacterAnalytic.continuedLattice_differentiableAt_nonprincipal χ hχ hs₀

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealEuler
namespace OAI

namespace SevenEighths.IdealEuler

open ActualEisensteinCubic UniqueFactorizationMonoid
open CompletedGauss (MulFiber mulFiber_moebius_sum)
open SmoothMobiusCorrection (PrimeIdeal)
open scoped BigOperators Classical

noncomputable section

theorem inverseSeries_eq_inv (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s = (series a s)⁻¹ := by
  calc
    _ = (inverseSeries a s * series a s) * (series a s)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (series_ne_zero a ha s hs), mul_one]
    _ = _ := by rw [inverseSeries_mul_series a ha s hs, one_mul]

theorem prime_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun P : PrimeIdeal => ‖weighted a s P.val‖) :=
  (weighted_summable_norm a ha s hs).comp_injective Subtype.val_injective

theorem prime_norm_lt_one (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : ‖weighted a s P.val‖ < 1 := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ < 1
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ < 1
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (ha P.val)).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by have h := SmoothMobiusCorrection.prime_norm_two_le P
        exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)) (by simpa using neg_neg_of_pos hs)

theorem local_factor_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : 1 - weighted a s P.val ≠ 0 :=
  SmoothMobiusCorrection.one_sub_ne_zero (prime_norm_lt_one a ha s hs P)

theorem inverseSeries_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    inverseSeries a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val) := by
  have h := SmoothMobiusCorrection.mobiusPrimeCoeff_euler (weighted a s)
    (prime_summable_norm a ha s hs)
  simpa only [SmoothMobiusCorrection.mobiusPrimeCoeff, primeValueHom_eq, inverseSeries] using h

theorem euler_hasProd (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹) (series a s) := by
  have hm : Multipliable (fun P : PrimeIdeal => 1 - weighted a s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-weighted a s P.val‖) by
        simpa only [norm_neg] using prime_summable_norm a ha s hs)
  have heq : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) = (series a s)⁻¹ :=
    (inverseSeries_euler a ha s hs).symm.trans (inverseSeries_eq_inv a ha s hs)
  have hne : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) ≠ 0 := by
    rw [heq]
    exact inv_ne_zero (series_ne_zero a ha s hs)
  simpa only [heq, inv_inv] using hm.hasProd.inv₀ hne

theorem series_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val)⁻¹ :=
  (euler_hasProd a ha s hs).tprod_eq.symm

theorem deletePrimes_prime (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    deletePrimes S a P.val = if P ∈ S then 0 else a P.val := by
  have hmem : P.val ∈ S.image Subtype.val ↔ P ∈ S := by
    constructor
    · intro hP
      obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP
      exact (Subtype.ext hQP : Q = P) ▸ hQ
    · intro hP
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
  change CanonicalRowCompletion.primeValueHom _ P.val = _
  rw [CanonicalRowCompletion.primeValueHom_prime _ _ P.property]
  simp only [hmem]

theorem deletePrimes_norm_le_one (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) : ∀ I, ‖deletePrimes S a I‖ ≤ 1 := by
  apply CanonicalRowCompletion.primeValueHom_norm_le_one
  intro I
  split_ifs
  · simp only [norm_zero, zero_le_one]
  · exact ha I

theorem deletePrimes_apply (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes S a I = if ∀ P ∈ S, ¬P.val ∣ I then a I else 0 := by
  by_cases ho : ∀ P ∈ S, ¬P.val ∣ I
  · rw [if_pos ho]
    by_cases hI : I = 0
    · subst I
      rw [map_zero, map_zero]
    · change (if I = 0 then 0 else
        ((normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J)).prod) = a I
      simp only [hI, ite_false]
      have hmap : (normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J) =
          (normalizedFactors I).map a := by
        apply Multiset.map_congr rfl
        intro J hJ
        have hnot : J ∉ S.image Subtype.val := by
          intro hmem
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hmem
          exact ho P hP (dvd_of_mem_normalizedFactors hJ)
        simp only [hnot, ite_false]
      rw [hmap, ← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]
  · simp only [ho, ite_false]
    push Not at ho
    obtain ⟨P, hPS, J, hJ⟩ := ho
    rw [hJ, map_mul, deletePrimes_prime]
    simp only [hPS, ite_true, zero_mul]

theorem series_deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    series (deletePrimes S a) s =
      series a s * ∏ P ∈ S, (1 - weighted a s P.val) := by
  have hlocal (P : PrimeIdeal) :
      (1 - weighted (deletePrimes S a) s P.val)⁻¹ =
        (1 - weighted a s P.val)⁻¹ * (if P ∈ S then 1 - weighted a s P.val else 1) := by
    change (1 - deletePrimes S a P.val * normWeight s P.val)⁻¹ = _
    rw [deletePrimes_prime]
    by_cases hP : P ∈ S
    · simp only [hP, ite_true, zero_mul, sub_zero, inv_one]
      exact (inv_mul_cancel₀ (local_factor_ne_zero a ha s (by linarith) P)).symm
    · simp only [hP, ite_false, mul_one]
      rfl
  have hfinite : Multipliable (fun P : PrimeIdeal => if P ∈ S then 1 - weighted a s P.val else 1) := by
    apply multipliable_of_hasFiniteMulSupport
    apply S.finite_toSet.subset
    intro P hP
    by_contra hPS
    change P ∉ S at hPS
    exact hP (by simp only [hPS, ite_false])
  rw [series_euler _ (deletePrimes_norm_le_one S a ha) s hs,
    series_euler a ha s hs]
  simp_rw [hlocal]
  rw [(euler_hasProd a ha s hs).multipliable.tprod_mul hfinite]
  congr 1
  rw [tprod_eq_prod (s := S) (fun P hP => by simp only [hP, ite_false])]
  exact Finset.prod_congr rfl (fun P hP => by simp only [hP, ite_true])

end

end SevenEighths.IdealEuler

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum
namespace OAI

noncomputable section
namespace SevenEighths.HeckeZeroSupremum
open HeckeFamily

theorem zeroRealParts_le_one {x : ℝ} (hx : x ∈ zeroRealParts) : x ≤ 1 := by
  obtain ⟨χ, s, _, _, hz, rfl⟩ := hx
  by_contra h
  exact LFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge h) hz

theorem zeroSet_bddAbove : BddAbove zeroSetWithSentinel := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zeroSet_nonempty : zeroSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem half_le_beta : (1 / 2 : ℝ) ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert _ _)

theorem beta_le_one : beta ≤ 1 := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zero_re_le_beta (χ : Character) {s : ℂ} (hs : 0 < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    s.re ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert_of_mem _ ⟨χ, s, hs, hpole, hz, rfl⟩)

theorem LFunction_ne_zero_of_beta_lt (χ : Character) {s : ℂ}
    (hs : beta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  intro hz
  have hpos : 0 < s.re := lt_trans (by linarith [half_le_beta]) hs
  exact (not_lt_of_ge (zero_re_le_beta χ hpos hpole hz)) hs

end SevenEighths.HeckeZeroSupremum

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Reciprocal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeReciprocal
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem regularizedL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    regularizedL χ s = (s - 1) * LFunction χ s := by
  unfold regularizedL LFunction continuedLattice
  rw [HeckeTheta.regularizedLatticeL_eq _ h0 h1]
  ring

theorem regularizedL_differentiableAt (χ : Character) {s : ℂ} (h0 : s ≠ 0) :
    DifferentiableAt ℂ (regularizedL χ) s :=
  (HeckeTheta.regularizedLatticeL_differentiableAt _ h0).div_const 6

theorem regularizedL_ne_zero (χ : Character) (hχ : χ.residue = 1) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regularizedL χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact regularizedL_ne_zero_at_one χ hχ
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  rw [regularizedL_eq χ h0 h1]
  exact mul_ne_zero (sub_ne_zero.mpr h1)
    (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inl h1))

theorem reciprocal_eq_inv (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    reciprocal χ s = (LFunction χ s)⁻¹ := by
  unfold reciprocal
  split_ifs
  · rw [regularizedL_eq χ h0 h1, div_mul_eq_div_div,
      div_self (sub_ne_zero.mpr h1), one_div]
  · rfl

theorem reciprocal_differentiableAt (χ : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : DifferentiableAt ℂ (reciprocal χ) s := by
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  by_cases hχ : χ.residue = 1
  · have heq : reciprocal χ = fun z => (z - 1) / regularizedL χ z := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (differentiableAt_id.sub_const 1).div
      (regularizedL_differentiableAt χ h0) (regularizedL_ne_zero χ hχ hs)
  · have heq : reciprocal χ = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv
      (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inr hχ))

end SevenEighths.HeckeReciprocal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ReciprocalBound
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeReciprocalBound
open HeckeFamily

theorem normWeight_le_of_re_ge {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (I : Ideal O) :
    ‖CubicEisenstein.fullIdealWeight s I‖ ≤
      ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖ := by
  by_cases hI : I = 0
  · simp [hI, CubicEisenstein.fullIdealWeight]
  · have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
      have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr (Ring.HasFiniteQuotients.finiteQuotient hI))
      exact_mod_cast hpos
    simp only [CubicEisenstein.fullIdealWeight, hI, ite_false]
    have hn : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one hN
    rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hs)

theorem reciprocal_norm_le (χ : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖HeckeReciprocal.reciprocal χ s‖ ≤ bound σ := by
  have hs1 : 1 < s.re := hσ.trans_le hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs1
  have hsp : s ≠ 1 := by intro h; norm_num [h] at hs1
  rw [HeckeReciprocal.reciprocal_eq_inv χ hs0 hsp, LFunction_eq_series χ hs1,
    ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs1]
  have hsum := IdealEuler.inverse_summable_norm (idealCoeff χ)
    (idealCoeff_norm_le_one χ) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖(UniqueFactorizationMonoid.moebius I : ℂ) *
    (idealCoeff χ I * CubicEisenstein.fullIdealWeight s I)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖CubicEisenstein.fullIdealWeight s I‖ := by
      apply (mul_le_of_le_one_left (by positivity)
        (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)
    _ ≤ _ := normWeight_le_of_re_ge hs I

end SevenEighths.HeckeReciprocalBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.StripActual
namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set MeasureTheory
namespace SevenEighths.HeckeStripActual
open HeckeFamily HeckePrimitive

variable (c : O) [NeZero c]

theorem LFunction_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖LFunction η s‖ ≤ HeckeReciprocalBound.bound σ := by
  have hs1 := hσ.trans_le hs
  rw [LFunction_eq_series η hs1, IdealEuler.series]
  have hsum := IdealEuler.weighted_summable_norm (idealCoeff η) (idealCoeff_norm_le_one η) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖idealCoeff η I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I)).trans
    (HeckeReciprocalBound.normWeight_le_of_re_ge hs I)

end SevenEighths.HeckeStripActual

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

theorem coefficient_norm_le (χ : Character) (inverse : Bool) (I : Ideal O) :
    ‖coefficient χ inverse I‖ ≤ 1 := by
  cases inverse
  · exact idealCoeff_norm_le_one χ I
  · change ‖(UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      (idealCoeff_norm_le_one χ I)

theorem series_eq_tsum (χ : Character) (inverse : Bool) {s : ℂ} (hs : 1 < s.re) :
    series χ inverse s =
      ∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, coefficient χ inverse I.val *
      CubicEisenstein.fullIdealWeight s I.val) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    apply tsum_subtype_eq_of_support_subset
      (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I)
    intro I hI hi
    subst I
    exact hI (by
      change coefficient χ inverse 0 * CubicEisenstein.fullIdealWeight s 0 = 0
      rw [coefficient_zero, zero_mul])
  have hc : (∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s)) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    rw [← he]
    apply tsum_congr
    intro I
    have hI : I.val ≠ 0 := I.property
    rw [CubicEisenstein.fullIdealWeight, if_neg hI]
    simp only [norm, Complex.ofReal_natCast]
  rw [hc]
  cases inverse
  · exact LFunction_eq_series χ hs
  · have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
    change HeckeReciprocal.reciprocal χ s = _
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1, LFunction_eq_series χ hs,
      ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs]
    apply tsum_congr
    intro I
    simp only [coefficient,  ite_true, IdealEuler.weighted,
      IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    ring

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicMellin
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem twisted_coefficient_summable (χ : Character) (inverse : Bool) (c σ freq : ℝ)
    (hc : 1 < c+σ) :
    Summable (fun I : NonzeroIdeal => ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c)) := by
  have hf := (CubicEisenstein.fullIdealWeight_summable_norm ((c+σ : ℝ) : ℂ)
    (by simpa using hc)).comp_injective (Subtype.val_injective : Function.Injective
      (fun I : NonzeroIdeal => I.val))
  apply hf.of_nonneg_of_le (fun I => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_pos I).le _))
  intro I
  have hI : I.val ≠ 0 := I.property
  change ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c) ≤
    ‖CubicEisenstein.fullIdealWeight ((c+σ : ℝ) : ℂ) I.val‖
  rw [CubicEisenstein.fullIdealWeight, if_neg hI]
  change ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c) ≤
    ‖(norm I : ℂ)^(-((c+σ : ℝ) : ℂ))‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp only [Complex.neg_re, Complex.ofReal_re]
  unfold twistedCoefficient
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re, shift_re]
  calc
    _ = ‖coefficient χ inverse I.val‖ * (norm I)^(-(c+σ)) := by
      rw [mul_assoc, ← Real.rpow_add (norm_pos I)]
      congr 2
      ring
    _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg (norm_pos I).le _)
      (coefficient_norm_le χ inverse I.val)

theorem twisted_series_eq (χ : Character) (inverse : Bool) (σ freq : ℝ)
    {s : ℂ} (hs : 1 < (s+shift σ freq).re) :
    (∑' I : NonzeroIdeal, twistedCoefficient χ inverse σ freq I*(norm I : ℂ)^(-s)) =
      series χ inverse (s+shift σ freq) := by
  rw [series_eq_tsum χ inverse hs]
  apply tsum_congr
  intro I
  unfold twistedCoefficient
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_pos I).ne')]
  congr 2
  ring

theorem polynomial_eq_weighted (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0 < D) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(shift σ freq-(1/2 : ℂ)) *
        ∑' I : NonzeroIdeal, twistedCoefficient χ inverse σ freq I * W (norm I/D) := by
  have he (I : NonzeroIdeal) : summand χ inverse W D σ freq I =
      (D : ℂ)^(shift σ freq) * (twistedCoefficient χ inverse σ freq I * W (norm I/D)) := by
    unfold summand twistedCoefficient
    rw [CompletedGauss.positive_quotient_cpow_neg _ _ (norm_pos I) hD]
    ring
  unfold polynomial
  simp_rw [he]
  rw [tsum_mul_left, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 2
  ring

theorem polynomial_mellin (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hWs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (D c σ freq : ℝ) (hD : 0 < D) (hc : 1 < c+σ) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
      mellin W ((c : ℂ)+t*Complex.I) *
        (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) *
          series χ inverse (((c : ℂ)+t*Complex.I)+shift σ freq) := by
  rw [polynomial_eq_weighted χ inverse W D σ freq hD]
  rw [CompletedGauss.weightedMellin_inversion norm norm_pos
    (twistedCoefficient χ inverse σ freq) c (twisted_coefficient_summable χ inverse c σ freq hc)
    W a b ha hWs hW D hD]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [twisted_series_eq χ inverse σ freq (by simpa using hc)]
  have he : (D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I) =
      (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
    congr 1
    ring
  calc
    _ = mellin W ((c : ℂ)+t*Complex.I) *
        ((D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I)) *
          series χ inverse (((c : ℂ)+t*Complex.I)+shift σ freq) := by ring
    _ = _ := by rw [he]

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicContour
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem series_norm_le (χ : Character) (inverse : Bool) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤ s.re) :
    ‖series χ inverse s‖ ≤ HeckeReciprocalBound.bound b := by
  cases inverse
  · exact HeckeStripActual.LFunction_norm_le χ hb hs
  · exact HeckeReciprocalBound.reciprocal_norm_le χ hb hs

theorem series_differentiableAt_right (χ : Character) (inverse : Bool) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hs) (Or.inl (by intro h; norm_num [h] at hs))
  · exact HeckeReciprocal.reciprocal_differentiableAt χ
      (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one hs)

theorem integrand_differentiableAt (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (series χ inverse) (s+shift σ freq)) :
    DifferentiableAt ℂ (integrand χ inverse W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (shift σ freq))

theorem integrand_norm (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ inverse W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ inverse (s+shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem integrand_vertical_integrable (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (hc : 1<c+σ) :
    Integrable (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_right χ inverse (by simpa using hc))).continuousAt.comp
    fun_prop
  have hm := (CompletedGauss.compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*HeckeReciprocalBound.bound (c+σ))).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [integrand_norm χ inverse W D σ freq hD]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (series_norm_le χ inverse hc (by simp))
  positivity

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Set Complex
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDyadic HeckeDetectorFourier

lemma polynomial_eq_finite (χ : Character) (inverse : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (S : Finset (Ideal O))
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ J∈S,
        coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
          (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq) := by
  unfold polynomial
  congr 1
  let f : Ideal O→ℂ := fun J => coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
    (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)
  have hf : Function.support f ⊆ {J : Ideal O | J≠0} := by
    intro J hJ hzero
    subst J
    apply hJ
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have he := tsum_subtype_eq_of_support_subset hf
  change (∑' J : {J : Ideal O // J≠0}, f J.val)=_
  apply he.trans
  apply tsum_eq_sum
  intro J hJ
  by_cases hj : J=0
  · subst J
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have hw : W ((J.absNorm : ℝ)/D)=0 := by
    by_contra hw
    exact hJ (hcover J hj hw)
  simp [f,hw]

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowwise
namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory Set
namespace SevenEighths.HeckeDetectorRowwise

theorem norm_sq_le_anchor_integral (F F' : ℝ→ℂ)
    (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ x, HasDerivAt F (F' x) x) {a b x : ℝ} (hx : x∈Icc a b) :
    ‖F x‖^2≤‖F a‖^2+∫ t in a..b, (‖F t‖^2+‖F' t‖^2) := by
  let G : ℝ→ℝ := fun t => ‖F t‖^2+‖F' t‖^2
  have hG : Continuous G := (hF.norm.pow 2).add (hF'.norm.pow 2)
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hx.1
    (hF.norm.pow 2).continuousOn
    (fun t ht => (hd t).norm_sq.hasDerivWithinAt)
    (hG.continuousOn.integrableOn_Icc)
    (fun t ht => show 2*inner (𝕜:=ℝ) (F t) (F' t)≤G t by
      dsimp [G]
      have hc := real_inner_le_norm (F t) (F' t)
      change (F' t * (starRingEnd ℂ) (F t)).re ≤ ‖F t‖*‖F' t‖ at hc
      nlinarith [sq_nonneg (‖F t‖-‖F' t‖)])
  simp only [Pi.pow_apply] at hh
  have hm := intervalIntegral.integral_mono_interval (μ:=volume) (le_refl a) hx.1 hx.2
    (Filter.Eventually.of_forall (fun t => show 0≤G t by dsimp [G]; positivity))
    (hG.intervalIntegrable a b)
  change ‖F x‖^2≤‖F a‖^2+∫ t in a..b, G t
  linarith

theorem rowwise_energy {ι : Type*} (rows : Finset ι) (F F' : ι→ℝ→ℂ)
    (hF : ∀ i∈rows, Continuous (F i)) (hF' : ∀ i∈rows, Continuous (F' i))
    (hd : ∀ i∈rows, ∀ x, HasDerivAt (F i) (F' i x) x)
    (a b E : ℝ) (hab : a≤b) (choice : ι→ℝ)
    (hc : ∀ i∈rows, choice i∈Icc a b)
    (henergy : ∀ t∈Icc a b, ∑ i∈rows, ‖F i t‖^2≤E)
    (henergy' : ∀ t∈Icc a b, ∑ i∈rows, ‖F' i t‖^2≤E) :
    ∑ i∈rows, ‖F i (choice i)‖^2≤(1+2*(b-a))*E := by
  have hg (i : ι) (hi : i∈rows) :
      Continuous (fun t => ‖F i t‖^2+‖F' i t‖^2) :=
    ((hF i hi).norm.pow 2).add ((hF' i hi).norm.pow 2)
  have hs := Finset.sum_le_sum (fun i hi =>
    norm_sq_le_anchor_integral (F i) (F' i) (hF i hi) (hF' i hi) (hd i hi) (hc i hi))
  rw [Finset.sum_add_distrib,←intervalIntegral.integral_finsetSum
    (fun i hi => (hg i hi).intervalIntegrable a b)] at hs
  have hm : (∫ t in a..b, ∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤(b-a)*(2*E) := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hab
      ((continuous_finsetSum rows (fun i hi => hg i hi)).intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)
      (fun t ht => show (∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤2*E by
        rw [Finset.sum_add_distrib]
        linarith [henergy t ht,henergy' t ht])
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have ha := henergy a ⟨le_refl a,hab⟩
  nlinarith

end SevenEighths.HeckeDetectorRowwise

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily UniqueFactorizationMonoid

theorem rowMap_norm (p : FreeRow×NonzeroIdeal) :
    (Ideal.span {rowMap p}).absNorm=(Ideal.span {p.1.val}).absNorm*p.2.val.absNorm^6 := by
  rw [rowMap_span,map_mul,map_pow]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationColumn
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_reciprocal_identity (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    {s : ℂ} (hs : 1<s.re) :
    series χ true s=(1-idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-s))*series ψ true s := by
  have hL : LFunction ψ s=LFunction χ s*(1-idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-s)) := by
    rw [LFunction_eq_series ψ hs,LFunction_eq_series χ hs,hm,
      IdealEuler.series_deletePrimes {P} (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs]
    simp only [Finset.prod_singleton]
    change IdealEuler.series (idealCoeff χ) s *
      (1-idealCoeff χ P.val*CubicEisenstein.fullIdealWeight s P.val)=_
    rw [CubicEisenstein.fullIdealWeight,if_neg P.property.ne_zero]
  have h0 : s≠0 := by intro h; norm_num [h] at hs
  have h1 : s≠1 := by intro h; norm_num [h] at hs
  simp only [series,ite_true,HeckeReciprocal.reciprocal_eq_inv χ h0 h1,
    HeckeReciprocal.reciprocal_eq_inv ψ h0 h1]
  have hχ := LFunction_ne_zero_of_one_lt_re χ hs
  have hψ := LFunction_ne_zero_of_one_lt_re ψ hs
  apply (mul_right_cancel₀ hψ)
  rw [mul_assoc,inv_mul_cancel₀ hψ,mul_one,hL]
  rw [←mul_assoc,inv_mul_cancel₀ hχ,one_mul]

lemma rescaled_power (D N : ℝ) (hD : 0<D) (hN : 0<N) (w : ℂ) :
    (D : ℂ)^(w-(1/2 : ℂ))*(N : ℂ)^(-w)=
      (N : ℂ)^(-(1/2 : ℂ))*((D/N : ℝ) : ℂ)^(w-(1/2 : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hD hN).ne')]
  rw [←Complex.ofReal_log hD.le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log (div_pos hD hN).le,Real.log_div hD.ne' hN.ne']
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem prime_column_identity (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0<D) :
    polynomial χ true W D σ freq=polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*
        polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq := by
  let N : ℝ := P.val.absNorm
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc : 1<(2-σ)+σ := by linarith
  have he (t : ℝ) : integrand χ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I)=
      integrand ψ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I)-
      (idealCoeff χ P.val*(N : ℂ)^(-(1/2 : ℂ)))*
        integrand ψ true W (D/N) σ freq (((2-σ : ℝ) : ℂ)+t*I) := by
    let w : ℂ := (((2-σ : ℝ) : ℂ)+t*I)+_root_.OAI.SevenEighths.HeckeDyadic.shift σ freq
    have hw : 1<w.re := by dsimp [w]; simp
    have hr := prime_reciprocal_identity χ ψ P hm hw
    have hp := rescaled_power D N hD hN w
    unfold integrand
    change mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*series χ true w=_
    rw [hr]
    change mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*
      ((1-idealCoeff χ P.val*(N : ℂ)^(-w))*series ψ true w)=_
    calc
      _ = mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*series ψ true w-
          idealCoeff χ P.val*mellin W _*((D : ℂ)^(w-(1/2 : ℂ))*(N : ℂ)^(-w))*series ψ true w := by ring
      _ = _ := by rw [hp]; ring
  have hI := integrand_vertical_integrable ψ true W a b ha hWs hW D (2-σ) σ freq hD hc
  have hJ := integrand_vertical_integrable ψ true W a b ha hWs hW (D/N) (2-σ) σ freq (div_pos hD hN) hc
  rw [polynomial_mellin χ true W a b ha hWs hW D (2-σ) σ freq hD hc,
    polynomial_mellin ψ true W a b ha hWs hW D (2-σ) σ freq hD hc,
    polynomial_mellin ψ true W a b ha hWs hW (D/(P.val.absNorm : ℝ)) (2-σ) σ freq (div_pos hD hN) hc]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I))=_
  simp_rw [he]
  rw [integral_sub hI (hJ.const_mul _),integral_const_mul]
  change _=(1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand ψ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I))-
    idealCoeff χ P.val*(N : ℂ)^(-(1/2 : ℂ))*
      ((1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand ψ true W (D/N) σ freq (((2-σ : ℝ) : ℂ)+t*I)))
  ring

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationMask
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve hiding O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem row_coeff_zero_unsupported (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (J : Ideal O) (hJ : ¬Supported J) :
    idealCoeff χ J=0 := by
  by_cases hz : J=0
  · subst J
    exact map_zero _
  let n := ConcretePrimeRowBridge.idealGenerator J
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero J hz
  have hs : Ideal.span {n}=J := ConcretePrimeRowBridge.span_idealGenerator J
  rw [←hs,idealCoeff_span χ hn,heq]
  exact rowTwist_zero_of_not_supported (elementHom η) m f z n hmLam hm2 (hs ▸ hJ)

theorem prime_coprime_iff (P : SmoothMobiusCorrection.PrimeIdeal) (J : Ideal O) :
    IsCoprime J P.val ↔ ¬P.val∣J := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  rw [isCoprime_comm,Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint,
    ←Ideal.dvd_iff_le]

theorem amplified_row_prime_mask (η χ ψ : Character) (m f z a : O)
    (P : SmoothMobiusCorrection.PrimeIdeal) (hspan : Ideal.span {a}=P.val)
    (hχ : ∀ n : O, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hψ : ∀ n : O, elementCoeff ψ n=rowTwist (elementHom η) m f (z*a^6) n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) :
    idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ) := by
  ext J
  rw [IdealEuler.deletePrimes_apply]
  simp only [Finset.mem_singleton,forall_eq]
  by_cases hs : Supported J
  · rw [idealCoeff_eq_row η ψ m f (z*a^6) hψ,
      show m^6*f^4*(z*a^6)=(m^6*f^4*z)*a^6 by ring,
      idealRowHom_argument_mul,idealRowHom_sixth_mask a J hs,hspan,prime_coprime_iff]
    by_cases hd : P.val∣J
    · simp [hd]
    · simp only [hd,not_false_eq_true,ite_true,mul_one]
      exact (idealCoeff_eq_row η χ m f z hχ J).symm
  · rw [row_coeff_zero_unsupported η ψ m f (z*a^6) hψ hmLam hm2 J hs,
      row_coeff_zero_unsupported η χ m f z hχ hmLam hm2 J hs]
    simp

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_column_energy (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ true W D σ freq‖^2≤
      2*(‖polynomial ψ true W D σ freq‖^2+
        ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖^2) := by
  have hN : (1 : ℝ)≤P.val.absNorm := by
    exact_mod_cast (show 1≤P.val.absNorm from (SmoothMobiusCorrection.prime_norm_two_le P).trans' (by norm_num))
  have hNp : (0 : ℝ)<P.val.absNorm := by linarith
  have hc : ‖idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
    rw [norm_mul]
    have hh : ‖(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
      change ‖((P.val.absNorm : ℝ) : ℂ)^(-(1/2 : ℂ))‖≤1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNp]
      norm_num
      exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (idealCoeff_norm_le_one χ P.val)).trans hh
  rw [prime_column_identity χ ψ P hm W a b ha hWs hW D σ freq hD]
  have hn := norm_sub_le (polynomial ψ true W D σ freq)
    (idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)
  rw [norm_mul] at hn
  have hb := mul_le_of_le_one_left
    (norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)) hc
  nlinarith [norm_nonneg (polynomial ψ true W D σ freq),
    norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    norm_nonneg (polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    sq_nonneg (‖polynomial ψ true W D σ freq‖-
      ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖)]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeRowClosure
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem RowData.amplified_prime_mask (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) :
    idealCoeff (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))=
      IdealEuler.deletePrimes {P} (idealCoeff (data.character u)) := by
  exact amplified_row_prime_mask data.η (data.character u)
    (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) data.m data.f u.val
    (ConcretePrimeRowBridge.idealGenerator P.val) P
    (ConcretePrimeRowBridge.span_idealGenerator P.val)
    (data.character_spec u) (data.character_spec (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))
    data.lambda_dvd data.two_dvd

theorem RowData.prime_energy (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial (data.character u) true W D σ freq‖^2≤
      2*(‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq‖^2+
        ‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq‖^2) :=
  prime_column_energy _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScale
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeDetectorRowwise

theorem scaleProfile_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    Continuous (scaleProfile W) := by
  have hd := hW.continuous_deriv (by simp)
  unfold scaleProfile
  fun_prop

theorem scaleSum_continuous (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ W S) (scaleSum χ (scaleProfile W) S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert (preTransparency := .instances) ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert (preTransparency := .instances) ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ true J) using 1
    · rfl
    · change coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        coefficient χ true J*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert (preTransparency := .instances) hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [scaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [scaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

theorem scale_normalization (l : ℝ) :
    ((Real.exp l : ℝ) : ℂ)^(-(1/2 : ℂ))=Complex.exp (-(l : ℂ)/2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos l).ne'),
    ←Complex.ofReal_log (Real.exp_pos l).le,Real.log_exp]
  congr 1
  ring

theorem scaleSum_eq_polynomial (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ W S l=polynomial χ true W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ true W (Real.exp l) 0 0 S hc,scale_normalization]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_self,neg_zero,Complex.cpow_zero,mul_one]
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwise
open ConcretePrimeRowBridge hiding O

theorem scaleSupport_cover (W : ℝ→ℂ) (a b upper l : ℝ) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hl : l≤upper) :
    ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈scaleSupport upper b := by
  intro J hJ hw
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hh := (div_le_iff₀ (Real.exp_pos l)).mp (hWs hw).2
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hl) hb
  have hn : (J.absNorm : ℝ)≤Real.exp upper*b := by nlinarith
  exact_mod_cast hn.trans (Nat.le_ceil _)

theorem rowwise_scales {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (a b : ℝ) (hb : 0≤b) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (lo hi E : ℝ) (hlh : lo≤hi) (l : ι→ℝ)
    (hl : ∀ i∈rows, l i∈Icc lo hi)
    (h0 : ∀ t∈Icc lo hi, ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤E)
    (h1 : ∀ t∈Icc lo hi, ∑ i∈rows,
      ‖polynomial (χ i) true (scaleProfile W) (Real.exp t) 0 0‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp (l i)) 0 0‖^2≤(1+2*(hi-lo))*E := by
  let S := scaleSupport hi b
  have hsp := scaleProfile_support W a b hWs
  have eq0 (i : ι) (t : ℝ) (ht : t∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) W S t (scaleSupport_cover W a b hi t hb hWs ht.2)
  have eq1 (i : ι) (t : ℝ) (ht : t∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) (scaleProfile W) S t
      (scaleSupport_cover (scaleProfile W) a b hi t hb hsp ht.2)
  have hh := rowwise_energy rows (fun i => scaleSum (χ i) W S)
    (fun i => scaleSum (χ i) (scaleProfile W) S)
    (fun i hi => scaleSum_continuous (χ i) W S hW.continuous)
    (fun i hi => scaleSum_continuous (χ i) (scaleProfile W) S (scaleProfile_continuous W hW))
    (fun i hi t => scaleSum_deriv (χ i) W S (hW.differentiable (by simp)) t)
    lo hi E hlh l hl
    (fun t ht => by simpa only [eq0 _ t ht] using h0 t ht)
    (fun t ht => by simpa only [eq1 _ t ht] using h1 t ht)
  convert (preTransparency := .instances) hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [eq0 i (l i) (hl i hi)]

theorem exists_scale_majorant {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (a b : ℝ) (hb : 0≤b) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (lo hi E : ℝ) (hlh : lo≤hi)
    (h0 : ∀ t∈Icc lo hi, ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤E)
    (h1 : ∀ t∈Icc lo hi, ∑ i∈rows,
      ‖polynomial (χ i) true (scaleProfile W) (Real.exp t) 0 0‖^2≤E) :
    ∃ B : ι→ℝ, (∀ i, 0≤B i) ∧
      (∀ i, ∀ t∈Icc lo hi, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤B i) ∧
      (∑ i∈rows, B i)≤(1+2*(hi-lo))*E := by
  let S := scaleSupport hi b
  have hm (i : ι) : ∃ t∈Icc lo hi, ∀ u∈Icc lo hi,
      ‖scaleSum (χ i) W S u‖^2≤‖scaleSum (χ i) W S t‖^2 := by
    exact isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlh)
      ((scaleSum_continuous (χ i) W S hW.continuous).norm.pow 2).continuousOn
  choose t ht hmax using hm
  refine ⟨fun i => ‖polynomial (χ i) true W (Real.exp (t i)) 0 0‖^2,
    fun i => sq_nonneg _,?_,?_⟩
  · intro i u hu
    have hh := hmax i u hu
    rw [scaleSum_eq_polynomial (χ i) W S u (scaleSupport_cover W a b hi u hb hWs hu.2),
      scaleSum_eq_polynomial (χ i) W S (t i) (scaleSupport_cover W a b hi (t i) hb hWs (ht i).2)] at hh
    exact hh
  · exact rowwise_scales rows χ W a b hb hWs hW lo hi E hlh t (fun i hi => ht i) h0 h1

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationAggregate
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem primeRowMap_injective : Function.Injective primeRowMap := by
  intro p q hpq
  have he : rowMap (p.1,⟨p.2.val,p.2.property.ne_zero⟩)=
      rowMap (q.1,⟨q.2.val,q.2.property.ne_zero⟩) := congrArg Subtype.val hpq
  have hh := rowMap_injective he
  apply Prod.ext
  · exact congrArg (fun r : FreeRow×NonzeroIdeal => r.1) hh
  · apply Subtype.ext
    exact congrArg (fun r : FreeRow×NonzeroIdeal => r.2.val) hh

theorem primeRowMap_norm_bound (p : FreeRow×PrimeIdeal) (U V : ℝ)
    (hU : (Ideal.span {p.1.val}).absNorm≤U) (hV : (p.2.val.absNorm : ℝ)≤V) :
    ((Ideal.span {((primeRowMap p).val)}).absNorm : ℝ)≤U*V^6 := by
  have hn := rowMap_norm (p.1,⟨p.2.val,p.2.property.ne_zero⟩)
  change ((Ideal.span {rowMap (p.1,⟨p.2.val,p.2.property.ne_zero⟩)}).absNorm : ℝ)≤_
  rw [hn,Nat.cast_mul,Nat.cast_pow]
  exact mul_le_mul hU (pow_le_pow_left₀ (Nat.cast_nonneg _) hV 6)
    (by positivity) ((Nat.cast_nonneg _).trans hU)

theorem averaged_energy_oai (data : RowData) (rows : Finset FreeRow) (primes : Finset PrimeIdeal)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D U V E : ℝ) (hD : 0<D) (hV : 1≤V)
    (hrows : ∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U)
    (hprimes : ∀ P∈primes, (P.val.absNorm : ℝ)≤V)
    (hraw0 : ∀ R : Finset NonzeroElement,
      (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
      ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true W (Real.exp l) 0 0‖^2≤E)
    (hraw1 : ∀ R : Finset NonzeroElement,
      (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
      ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true (scaleProfile W) (Real.exp l) 0 0‖^2≤E) :
    (primes.card : ℝ)*∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤
      4*(1+2*Real.log V)*E := by
  let R := (rows×ˢprimes).image primeRowMap
  have hR : ∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6 := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hu,hP⟩ := Finset.mem_product.mp hp
    exact primeRowMap_norm_bound p U V (hrows p.1 hu) (hprimes p.2 hP)
  have hl : Real.log D-Real.log V≤Real.log D := by linarith [Real.log_nonneg hV]
  obtain ⟨B,hB,hmajor,henergy⟩ := exists_scale_majorant R data.character W a b hb hWs hW
    (Real.log D-Real.log V) (Real.log D) E hl (hraw0 R hR) (hraw1 R hR)
  have hamp (u : FreeRow) (hu : u∈rows) (P : PrimeIdeal) (hP : P∈primes) :
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤4*B (primeRowMap (u,P)) := by
    have hN : (1 : ℝ)≤P.val.absNorm := by
      exact_mod_cast (show 1≤P.val.absNorm from (SmoothMobiusCorrection.prime_norm_two_le P).trans' (by norm_num))
    have hNp : (0 : ℝ)<P.val.absNorm := by linarith
    have hlog : Real.log (P.val.absNorm : ℝ)≤Real.log V :=
      Real.log_le_log hNp (hprimes P hP)
    have hDV : Real.log (D/(P.val.absNorm : ℝ))∈Icc (Real.log D-Real.log V) (Real.log D) := by
      rw [Real.log_div hD.ne' hNp.ne']
      constructor <;> linarith [Real.log_nonneg hN]
    have hbase := hmajor (primeRowMap (u,P)) (Real.log D) ⟨hl,le_refl _⟩
    have hlow := hmajor (primeRowMap (u,P)) (Real.log (D/(P.val.absNorm : ℝ))) hDV
    rw [Real.exp_log hD] at hbase
    rw [Real.exp_log (div_pos hD hNp)] at hlow
    have hh := data.prime_energy ⟨u.val,u.property.1⟩ P W a b ha hWs hW D 0 0 hD
    change ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤
      2*(‖polynomial (data.character (primeRowMap (u,P))) true W D 0 0‖^2+
        ‖polynomial (data.character (primeRowMap (u,P))) true W (D/(P.val.absNorm : ℝ)) 0 0‖^2) at hh
    linarith
  have hs : (primes.card : ℝ)*∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤4*∑ v∈R, B v := by
    calc
      _ = ∑ p∈rows×ˢprimes,
          ‖polynomial (data.character ⟨p.1.val,p.1.property.1⟩) true W D 0 0‖^2 := by
        rw [Finset.sum_product]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        change (primes.card : ℝ) *
          ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2 =
          ∑ _P∈primes, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p∈rows×ˢprimes, 4*B (primeRowMap p) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hu,hP⟩ := Finset.mem_product.mp hp
        exact hamp p.1 hu p.2 hP
      _ = _ := by
        dsimp [R]
        rw [Finset.mul_sum,Finset.sum_image]
        exact fun p hp q hq h => primeRowMap_injective h
  have hh := mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ)≤4)
  nlinarith

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.HeckeInverseAmplification.averaged_energy_oai := @OAI.SevenEighths.HeckeInverseAmplification.averaged_energy_oai
