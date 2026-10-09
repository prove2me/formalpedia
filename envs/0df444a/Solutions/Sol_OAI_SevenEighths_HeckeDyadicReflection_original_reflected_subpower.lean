-- Prove2me | solution 1 for OAI.SevenEighths.HeckeDyadicReflection.original_reflected_subpower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:38:40.710301+00:00
-- url     : https://prove2.me/submissions/00e36a62-894b-48af-b7a2-3bdda510188c

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B016
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorPresentation
namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.bot (χ : MulChar R ℂ) : FactorsThroughIdeal χ ⊥ := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
  rw [hu1, map_one]

end FiniteConductor

namespace ConductorPresentation

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]
  [Module.Free ℤ A] [Module.Finite ℤ A]

theorem exists_primitive_presentation (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hMK, hbotK, hK, hprimitive, hnorm, hmask⟩ :=
    exists_primitive_presentation_above_quotient M χ ⊥ (FactorsThroughIdeal.bot χ)
  refine ⟨K, φ, hMK, hK, hprimitive, ?_, hmask⟩
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hnorm

end

end ConductorPresentation

end SevenEighths

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Continuation
namespace OAI

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace SevenEighths.Continuation

theorem product_identity_on_halfPlane (a b : ℝ) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | a < s.re})
    (hM : AnalyticOnNhd ℂ M {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (heq : ∀ s : ℂ, max a b < s.re → L s * M s = W s) :
    Set.EqOn (fun s => L s * M s) W {s : ℂ | a < s.re} := by
  let z : ℂ := (max a b + 1 : ℝ)
  have hz : a < z.re := by dsimp [z]; linarith [le_max_left a b]
  have hz' : max a b < z.re := by dsimp [z]; simp
  have hev : (fun s => L s * M s) =ᶠ[𝓝 z] W := by
    filter_upwards [(Complex.isOpen_re_gt (max a b)).mem_nhds hz'] with s hs
    exact heq s hs
  exact (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
    (convex_halfSpace_re_gt a).isPreconnected hz hev

end SevenEighths.Continuation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.EulerFactors
namespace OAI

namespace SevenEighths.EulerFactors

noncomputable section

theorem norm_term_lt_one {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : ‖a * (N : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N),
    Complex.neg_re]
  calc
    ‖a‖ * N ^ (-s.re) ≤ 1 * N ^ (-s.re) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by linarith) _)
    _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hN (neg_neg_of_pos hs)

theorem factor_ne_zero {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : factor N a s ≠ 0 := by
  intro h
  have heq : a * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hlt := norm_term_lt_one hN ha hs
  rw [heq, norm_one] at hlt
  exact (lt_irrefl _ hlt)

theorem differentiable_factor {N : ℝ} (hN : 0 < N) (a : ℂ) :
    Differentiable ℂ (factor N a) := by
  exact (differentiable_const (1 : ℂ)).sub ((differentiable_const a).mul
    (differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))))

theorem deletedProduct_ne_zero {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : deletedProduct S N a s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact factor_ne_zero (hN p hp) (ha p hp) hs

theorem differentiable_deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 0 < N p) :
    Differentiable ℂ (deletedProduct S N a) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Differentiable ℂ (fun _ : ℂ => (1 : ℂ))
    exact differentiable_const _
  | @insert p S hp ih =>
    have hpN := hN p (Finset.mem_insert_self p S)
    have hSN : ∀ q ∈ S, 0 < N q := fun q hq => hN q (Finset.mem_insert_of_mem hq)
    have heq : deletedProduct (insert p S) N a =
        fun s => factor (N p) (a p) s * deletedProduct S N a s := by
      funext s
      simp only [deletedProduct, Finset.prod_insert hp]
    rw [heq]
    exact (differentiable_factor hpN (a p)).mul (ih hSN)

end

end SevenEighths.EulerFactors

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

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

namespace CubicReflectionKernel

theorem Gamma_vertical_conj (a u : ℝ) :
    Complex.Gamma ((a : ℂ) - u * Complex.I) =
      star (Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  change _ = (starRingEnd ℂ) (Complex.Gamma ((a : ℂ) + u * Complex.I))
  rw [← Complex.Gamma_conj]
  congr 1
  simp [sub_eq_add_neg]

end CubicReflectionKernel

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
namespace CubicReflectionKernel

theorem betaIntegral_ofReal (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) = (realBeta a b : ℂ) := by
  rw [Complex.betaIntegral, realBeta, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  push_cast
  rfl

theorem norm_betaIntegral_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ realBeta u.re v.re := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
  simp

theorem realBeta_eq_Gamma (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realBeta a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← betaIntegral_ofReal]
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
  rw [← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

theorem Gamma_ratio_eq_beta (z : ℂ) (d : ℝ) (hz : 0 < z.re) (hd : 0 < d) :
    Complex.Gamma z / Complex.Gamma (z + d) =
      Complex.betaIntegral z d / Complex.Gamma d := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hz (by simpa using hd)]
  have hdn : Complex.Gamma (d : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hd)
  field_simp

theorem Gamma_vertical_ratio_bound (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
      Complex.Gamma ((a : ℂ) + t * Complex.I + d)‖ ≤
      Real.Gamma a / Real.Gamma (a + d) := by
  rw [Gamma_ratio_eq_beta _ d (by simpa using ha) hd, norm_div]
  have hg := Real.Gamma_pos_of_pos hd
  have hb := norm_betaIntegral_le ((a : ℂ) + t * Complex.I) (d : ℂ)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] at hb
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    _ ≤ realBeta a d / Real.Gamma d := div_le_div_of_nonneg_right hb hg.le
    _ = _ := by rw [realBeta_eq_Gamma a d ha hd]; field_simp

theorem inverse_Gamma_shift (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ k ∈ Finset.range n, (z + k)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n),
      Finset.prod_range_succ]
    push_cast
    ring_nf

theorem Gamma_shifted_pair_bound (a σ t : ℝ) (n : ℕ)
    (ha : 0 < a + σ) (hd : 0 < (n : ℝ) - 2 * σ) :
    ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)‖ ≤
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) := by
  have hb := Gamma_vertical_ratio_bound (a + σ) ((n : ℝ) - 2 * σ) t ha hd
  have hn : ((a + σ : ℝ) : ℂ) + t * Complex.I =
      (a : ℂ) + (σ + t * Complex.I) := by push_cast; ring
  have hdp : ((a + σ : ℝ) : ℂ) + t * Complex.I + ((n : ℝ) - 2 * σ : ℝ) =
      ((a - σ + n : ℝ) : ℂ) + t * Complex.I := by push_cast; ring
  have hdm : (a : ℂ) - (σ + t * Complex.I) + n =
      ((a - σ + n : ℝ) : ℂ) - t * Complex.I := by push_cast; ring
  have hr : a + σ + ((n : ℝ) - 2 * σ) = a - σ + n := by ring
  rw [hdp, hn, hr] at hb
  rw [hdm, Gamma_vertical_conj, norm_div, norm_star]
  simpa only [norm_div] using hb

theorem norm_Gamma_shift_factor (z : ℂ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (z + k)‖ ≤ (‖z‖ + n) ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _k ∈ Finset.range n, (‖z‖ + n) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact norm_nonneg _
      · intro k hk
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
        exact (norm_add_le _ _).trans (by simpa using add_le_add_left hk' ‖z‖)
    _ = _ := by simp

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

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

section
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

lemma prod_primeSet {M : Type*} [CommMonoid M] (I : Ideal ActualEisensteinCubic.O) (f : Ideal ActualEisensteinCubic.O→M) :
    (∏P∈primeSet I,f P.val)=∏P∈primeSupport I,f P := by
  unfold primeSet
  rw [Finset.prod_image]
  · exact Finset.prod_attach (primeSupport I) f
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Theta
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.FamilySeries
namespace OAI

noncomputable section
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem latticeL_eq_of_coefficients_right {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (hcoeff : ∀ n, periodicCoeff w n = periodicCoeff v n)
    {s : ℂ} (hs : 1 < s.re) : latticeL w s = latticeL v s := by
  have hw := latticeL_hasSum w hs
  simp_rw [hcoeff] at hw
  exact hw.unique (latticeL_hasSum v hs)

theorem latticeL_eq_of_coefficients {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (hcoeff : ∀ n, periodicCoeff w n = periodicCoeff v n)
    {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) : latticeL w s = latticeL v s := by
  have hwa : AnalyticOnNhd ℂ (regularizedLatticeL w) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (regularizedLatticeL_differentiableAt w
      (by intro h; simp [h] at hz)).differentiableWithinAt
  have hva : AnalyticOnNhd ℂ (regularizedLatticeL v) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (regularizedLatticeL_differentiableAt v
      (by intro h; simp [h] at hz)).differentiableWithinAt
  have hident := Continuation.product_identity_on_halfPlane 0 1
    (regularizedLatticeL w) (fun _ => 1) (regularizedLatticeL v)
    hwa analyticOnNhd_const hva (by
      intro z hz
      have hz' : 1 < z.re := by simpa using hz
      have hz₀ : z ≠ 0 := by intro h; norm_num [h] at hz'
      have hz₁ : z ≠ 1 := by intro h; norm_num [h] at hz'
      simp only [mul_one, regularizedLatticeL_eq w hz₀ hz₁,
        regularizedLatticeL_eq v hz₀ hz₁,
        latticeL_eq_of_coefficients_right w v hcoeff hz']) hs
  have hs₀ : s ≠ 0 := by intro h; simp [h] at hs
  simp only [mul_one, regularizedLatticeL_eq w hs₀ hs₁,
    regularizedLatticeL_eq v hs₀ hs₁] at hident
  exact mul_left_cancel₀ (sub_ne_zero.mpr hs₁) hident
end SevenEighths.HeckeTheta

namespace SevenEighths.HeckeFamily
open EisensteinTheta

theorem continuedLattice_eq_of_elementCoeff_eq (χ ψ : Character)
    (hχψ : ∀ z, elementCoeff χ z = elementCoeff ψ z)
    {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    continuedLattice χ s = continuedLattice ψ s := by
  apply HeckeTheta.latticeL_eq_of_coefficients (coefficients χ) (coefficients ψ) _ hs hs₁
  intro n
  simp only [periodicCoeff_eq_elementCoeff, hχψ]

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealCharacter
namespace OAI

namespace SevenEighths.IdealCharacter

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

section Principal

variable [IsDomain A] [IsPrincipalIdealRing A]

theorem ofResidue_finite_deletion (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I =
      ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  rw [ofResidue_source_mask M K χ φ hχ hφ hmask, ofResidue_one]
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true, ite_self, mul_zero]
  · simp only [hI, ite_false]
    split_ifs <;> simp only [one_mul, zero_mul]

section Primitive

variable [Infinite A] [Module.Free ℤ A] [Module.Finite ℤ A]

theorem exists_primitive_associate (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      (∀ I : Ideal A, ofResidue M χ hχ I =
        if IsCoprime I M then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I =
        ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  obtain ⟨K, φ, hMK, hK, hprimitive, hnorm, hmask⟩ := exists_primitive_presentation M χ
  have hφ : UnitInvariant K φ := by
    intro u
    have h := hmask (u : A)
    simpa only [hχ u, u.isUnit.map (Ideal.Quotient.mk M), ite_true] using h.symm
  exact ⟨K, φ, hφ, hMK, hK, hprimitive, hnorm,
    ofResidue_source_mask M K χ φ hχ hφ hmask,
    ofResidue_finite_deletion M K χ φ hχ hφ hmask⟩

end Primitive

end Principal

end

end SevenEighths.IdealCharacter

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

theorem deletePrimes_primeSet_apply (M : Ideal O) (hM : M ≠ 0)
    (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes (SmoothMobiusCorrection.primeSet M) a I =
      if IsCoprime I M then a I else 0 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
    exact (ite_self _).symm
  have heq : (∀ P ∈ SmoothMobiusCorrection.primeSet M, ¬P.val ∣ I) ↔ IsCoprime I M := by
    rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hI hM]
    constructor
    · intro h
      apply Finset.disjoint_left.mpr
      intro P hPI hPM
      have hp : Prime P := IdealMobiusDivisorSum.support_prime hPM
      exact h ⟨P, hp⟩ (SmoothMobiusCorrection.mem_primeSet M ⟨P, hp⟩ |>.mpr hPM)
        (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPI))
    · intro h P hPM hPI
      exact Finset.disjoint_left.mp h
        (Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hI).mpr ⟨P.property, hPI⟩))
        ((SmoothMobiusCorrection.mem_primeSet M P).mp hPM)
  simpa only [heq] using deletePrimes_apply (SmoothMobiusCorrection.primeSet M) a I

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

theorem series_of_coprime_mask (M : Ideal O) (hM : M ≠ 0)
    (a b : Ideal O →*₀ ℂ) (hb : ∀ I, ‖b I‖ ≤ 1)
    (hmask : ∀ I, a I = if IsCoprime I M then b I else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = series b s *
      ∏ P ∈ SmoothMobiusCorrection.primeSet M, (1 - weighted b s P.val) := by
  have heq : a = deletePrimes (SmoothMobiusCorrection.primeSet M) b := by
    ext I
    rw [deletePrimes_primeSet_apply M hM, hmask]
  rw [heq]
  exact series_deletePrimes _ b hb s hs

end

end SevenEighths.IdealEuler

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.IdealOperations
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeFamily

theorem exists_primitive_character (χ : Character) :
    ∃ ψ : Character,
      χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  obtain ⟨M, φ, hφ, hM, hM₀, hprim, hnorm, hmask, _⟩ :=
    IdealCharacter.exists_primitive_associate χ.modulus χ.residue χ.unit_trivial
  exact ⟨Character.ofResidue M hM₀ φ hφ, hM, hprim, hnorm, hmask⟩

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Conjugation
namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex
namespace SevenEighths.HeckeFamily

theorem idealTerm_inverse_conj (χ : Character) (s : ℂ) (J : Ideal O) :
    idealTerm χ.inverse s J=conj (idealTerm χ (conj s) J) := by
  by_cases hJ : J=0
  · subst J
    simp only [idealTerm,map_zero,zero_div]
  have hN : (0 : ℝ)<J.absNorm := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hpow := Complex.cpow_conj ((J.absNorm : ℝ) : ℂ) (conj s)
    (by rw [Complex.arg_ofReal_of_nonneg hN.le]; exact Real.pi_ne_zero.symm)
  simp only [conj_ofReal, conj_conj] at hpow
  unfold idealTerm
  rw [idealCoeff_inverse_conj,map_div₀]
  congr 1

theorem LFunction_inverse_conj (χ : Character) (hχ : χ.residue≠1) (s : ℂ) :
    LFunction χ.inverse s=conj (LFunction χ (conj s)) := by
  have hi : χ.inverse.residue≠1 := by
    change χ.residue⁻¹≠1
    simpa only [ne_eq,inv_eq_one] using hχ
  have hA := LFunction_entire_nonprincipal χ.inverse hi
  have hB : Differentiable ℂ (fun z => conj (LFunction χ (conj z))) := by
    intro z
    simpa only [Function.comp_def,conj_conj] using
      (LFunction_entire_nonprincipal χ hχ (conj z)).conj_conj
  have he : LFunction χ.inverse=(fun z => conj (LFunction χ (conj z))) := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hA).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hB) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    rw [LFunction_eq_ideal_tsum χ.inverse hz,LFunction_eq_ideal_tsum χ (by simpa using hz),conj_tsum]
    exact tsum_congr (idealTerm_inverse_conj χ z)
  exact congr_fun he s

end SevenEighths.HeckeFamily

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

end SevenEighths.HeckeReciprocal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFiniteDeletion
open HeckeFamily HeckeReciprocal

theorem factors_eq (M : Ideal O) (ψ : Character) (s : ℂ) :
    factors M ψ s = ∏ P ∈ SmoothMobiusCorrection.primeSet M,
      (1 - IdealEuler.weighted (idealCoeff ψ) s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, IdealEuler.weighted, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, IdealEuler.normWeight, CubicEisenstein.fullIdealWeight,
    P.property.ne_zero, ite_false, Complex.ofReal_natCast]

theorem factors_differentiable (M : Ideal O) (ψ : Character) :
    Differentiable ℂ (factors M ψ) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := SmoothMobiusCorrection.prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

theorem factors_ne_zero (M : Ideal O) (ψ : Character) {s : ℂ} (hs : 0 < s.re) :
    factors M ψ s ≠ 0 := by
  apply EulerFactors.deletedProduct_ne_zero _ _ _ _ _ hs
  · intro P _
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)
  · intro P _
    exact idealCoeff_norm_le_one ψ P.val

theorem LFunction_eq_of_mask_right (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rw [LFunction_eq_series χ hs, LFunction_eq_series ψ hs, factors_eq]
  exact IdealEuler.series_of_coprime_mask χ.modulus χ.modulus_ne_bot
    _ _ (idealCoeff_norm_le_one ψ) hmask s hs

theorem regularizedL_analytic (χ : Character) :
    AnalyticOnNhd ℂ (regularizedL χ) {s : ℂ | 0 < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
  intro s hs
  exact (regularizedL_differentiableAt χ (by intro h; simp [h] at hs)).differentiableWithinAt

theorem regularizedL_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    regularizedL χ s = regularizedL ψ s * factors χ.modulus ψ s := by
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (regularizedL ψ) (factors χ.modulus ψ) (regularizedL χ)
    (regularizedL_analytic ψ) hf (regularizedL_analytic χ) _ hs
  intro z hz
  have hz' : 1 < z.re := by simpa using hz
  have h0 : z ≠ 0 := by intro h; norm_num [h] at hz'
  have h1 : z ≠ 1 := by intro h; norm_num [h] at hz'
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1,
    LFunction_eq_of_mask_right χ ψ hmask hz']
  ring

theorem regularizedL_one_ne_zero_iff (χ : Character) :
    regularizedL χ 1 ≠ 0 ↔ χ.residue = 1 := by
  constructor
  · intro h
    by_contra hχ
    rw [regularizedL_at_one,
      HeckeTheta.pair_g₀_eq_zero _ (HeckeCharacterAnalytic.coefficients_sum_eq_zero χ hχ),
      mul_zero, zero_div] at h
    exact h rfl
  · exact regularizedL_ne_zero_at_one χ

theorem principal_iff_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0) :
    χ.residue = 1 ↔ ψ.residue = 1 := by
  rw [← regularizedL_one_ne_zero_iff χ, ← regularizedL_one_ne_zero_iff ψ,
    regularizedL_eq_of_mask χ ψ hmask (by norm_num : 0 < (1 : ℂ).re),
    mul_ne_zero_iff, and_iff_left (factors_ne_zero χ.modulus ψ (by norm_num))]

end SevenEighths.HeckeFiniteDeletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DeletionBounds
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDeletionBounds
open HeckeFamily

theorem constant_pow_primeSupport_bound (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Ideal O, M ≠ ⊥ →
      K^(IdealMobiusDivisorSum.primeSupport M).card ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max K 1)
  have hn0 : 0 < (n : ℝ) := by linarith [le_max_right K 1]
  have hKpow : K ≤ (2 : ℝ)^n := by
    have hn2 : (n : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast (show n < 2^n from Nat.lt_two_pow_self).le
    linarith [le_max_left K 1]
  obtain ⟨C, hC, hbound⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/(n : ℝ)) (div_pos hε hn0)
  refine ⟨C ^n, by positivity, ?_⟩
  intro M hM
  calc
    _ ≤ ((2 : ℝ)^n)^(IdealMobiusDivisorSum.primeSupport M).card :=
      pow_le_pow_left₀ hK hKpow _
    _ = ((2 : ℝ)^(IdealMobiusDivisorSum.primeSupport M).card)^n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (C*(M.absNorm : ℝ)^(ε/(n : ℝ)))^n :=
      pow_le_pow_left₀ (by positivity) (hbound M hM) n
    _ = C ^n*(M.absNorm : ℝ)^ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), div_mul_cancel₀ _ hn0.ne']

theorem localBound_pos {σ : ℝ} (hσ : 0 < σ) : 0 < localBound σ := by
  unfold localBound
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))

theorem term_bound {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖a*(N : ℂ)^(-s)‖ ≤ (2 : ℝ)^(-σ) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha).trans
  apply (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by linarith : -s.re ≤ -σ)).trans
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)

theorem factor_bounds {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖EulerFactors.factor N a s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor N a s)⁻¹‖ ≤ localBound σ := by
  have hδ : (2 : ℝ)^(-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hδ0 : 0 ≤ (2 : ℝ)^(-σ) := Real.rpow_nonneg (by norm_num) _
  have ht := term_bound hσ hN ha hs
  have hl : 1-(2 : ℝ)^(-σ) ≤ ‖EulerFactors.factor N a s‖ := by
    have hh := norm_sub_le (1-a*(N : ℂ)^(-s)) (-a*(N : ℂ)^(-s))
    have he : (1-a*(N : ℂ)^(-s))-(-a*(N : ℂ)^(-s)) = 1 := by ring
    rw [he, norm_one, neg_mul, norm_neg] at hh
    change 1-(2 : ℝ)^(-σ) ≤ ‖1-a*(N : ℂ)^(-s)‖
    linarith
  constructor
  · apply (norm_sub_le _ _).trans
    rw [norm_one]
    apply (add_le_add (le_refl 1) ht).trans
    unfold localBound
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr
    nlinarith [sq_nonneg ((2 : ℝ)^(-σ))]
  · rw [norm_inv]
    exact (inv_le_inv₀ (by linarith : 0 < ‖EulerFactors.factor N a s‖)
      (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr hl

theorem factors_bound_pow (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card ∧
    ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
  have hfactor (P : SmoothMobiusCorrection.PrimeIdeal) :
      ‖EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s)⁻¹‖ ≤ localBound σ :=
    factor_bounds hσ (by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
      (idealCoeff_norm_le_one ψ P.val) hs
  have he : (∏ P ∈ SmoothMobiusCorrection.primeSet M, localBound σ) =
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
    rw [SmoothMobiusCorrection.prod_primeSet M (fun _ => localBound σ)]
    simp
  constructor
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [norm_prod, ← he]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).1)
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [← Finset.prod_inv_distrib, norm_prod, ← he]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).2)

theorem factors_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O), M ≠ ⊥ → ∀ (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := constant_pow_primeSupport_bound (localBound σ) ε
    (localBound_pos hσ).le hε
  refine ⟨2*C, by positivity, ?_⟩
  intro M hM ψ s hs
  obtain ⟨h1, h2⟩ := factors_bound_pow σ hσ M ψ hs
  have h := hb M hM
  nlinarith

theorem radical_ne_zero (M : Ideal O) : radical M ≠ 0 :=
  SmoothMobiusCorrection.primeProduct_ne_zero _

theorem factors_radical (M : Ideal O) (ψ : Character) (s : ℂ) :
    HeckeFiniteDeletion.factors (radical M) ψ s = HeckeFiniteDeletion.factors M ψ s := by
  unfold HeckeFiniteDeletion.factors radical
  rw [SmoothMobiusCorrection.primeSet_primeProduct]

theorem factors_radical_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*((radical M).absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := factors_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s hs
  simpa only [factors_radical] using hb (radical M) (radical_ne_zero M) ψ s hs

theorem factor_bound_any_re {N : ℝ} (hN : 2 ≤ N) {a s : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖EulerFactors.factor N a s‖ ≤ 2*N^(max (-s.re) 0) := by
  have hn : 1 ≤ N := by linarith
  have ht : ‖a*(N : ℂ)^(-s)‖ ≤ N^(-s.re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha
  have hpow : N^(-s.re) ≤ N^(max (-s.re) 0) :=
    Real.rpow_le_rpow_of_exponent_le hn (le_max_left _ _)
  have h1 : 1 ≤ N^(max (-s.re) 0) := Real.one_le_rpow hn (le_max_right _ _)
  have hb := norm_sub_le (1 : ℂ) (a*(N : ℂ)^(-s))
  rw [norm_one] at hb
  change ‖1-a*(N : ℂ)^(-s)‖ ≤ _
  linarith

theorem factors_bound_any_re (M : Ideal O) (ψ : Character) (s : ℂ) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card *
        ((radical M).absNorm : ℝ)^(max (-s.re) 0) := by
  unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ P ∈ SmoothMobiusCorrection.primeSet M,
        2*(P.val.absNorm : ℝ)^(max (-s.re) 0) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro P _
      exact factor_bound_any_re (show (2 : ℝ) ≤ (P.val.absNorm : ℝ) by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
        (idealCoeff_norm_le_one ψ P.val)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
      simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]

theorem primeSet_card (M : Ideal O) :
    (SmoothMobiusCorrection.primeSet M).card =
      (IdealMobiusDivisorSum.primeSupport M).card := by
  unfold SmoothMobiusCorrection.primeSet
  rw [Finset.card_image_iff.mpr ?_, Finset.card_attach]
  intro P hP Q hQ h
  exact Subtype.ext (congrArg (fun R : SmoothMobiusCorrection.PrimeIdeal => R.val) h)

theorem factors_any_re_subpower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
        C*((radical M).absNorm : ℝ)^(max (-s.re) 0 + ε) := by
  obtain ⟨C, hC, hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s
  have hR : 0 < ((radical M).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))
  have hc : (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card ≤ C*((radical M).absNorm : ℝ)^ε := by
    have h := hb (radical M) (radical_ne_zero M)
    rw [← primeSet_card, radical, SmoothMobiusCorrection.primeSet_primeProduct] at h
    exact h
  apply (factors_bound_any_re M ψ s).trans
  calc
    _ ≤ (C*((radical M).absNorm : ℝ)^ε)*((radical M).absNorm : ℝ)^(max (-s.re) 0) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [Real.rpow_add hR]; ring

end SevenEighths.HeckeDeletionBounds

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.MellinIdentity
namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace SevenEighths.HeckeMellinIdentity

theorem scaled_eq (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (A : ℝ) (hA : 0 < A)
    (hright : ∀ s : ℂ, 1 < s.re → P.Λ s = (A : ℂ)^(-s) * Q.Λ s)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    P.Λ s = (A : ℂ)^(-s) * Q.Λ s := by
  have hd : Differentiable ℂ (fun z : ℂ => (A : ℂ)^(-z) * regularized Q z) :=
    ((differentiable_id.neg).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))).mul (regularized_entire Q)
  have he : regularized P = fun z : ℂ => (A : ℂ)^(-z) * regularized Q z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularized_entire P)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : z ≠ 1 := by intro h; norm_num [h] at hz
    rw [regularized_eq P hP hz0 hz1, regularized_eq Q hQ hz0 hz1, hright z hz]
    ring
  have heq := congr_fun he s
  rw [regularized_eq P hP h0 h1, regularized_eq Q hQ h0 h1] at heq
  apply mul_left_cancel₀ (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  calc
    s * (s - 1) * P.Λ s = (A : ℂ)^(-s) * (s * (s-1) * Q.Λ s) := heq
    _ = s * (s-1) * ((A : ℂ)^(-s) * Q.Λ s) := by ring

theorem eq_of_f (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (hf : ∀ t : ℝ, 0 < t → P.f t = Q.f t) (hf₀ : P.f₀ = Q.f₀)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : P.Λ s = Q.Λ s := by
  have h := scaled_eq P Q hP hQ 1 zero_lt_one (fun z hz => by
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
    rw [← (P.hasMellin (by rwa [hP])).2, ← (Q.hasMellin (by rwa [hQ])).2]
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hf t ht, hf₀]) h0 h1
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using h

end SevenEighths.HeckeMellinIdentity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Primitive
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckePrimitive
open HeckeFamily

variable (c : O) [NeZero c]

theorem pair_completed_eq_right (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (hs : 1 < s.re) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s := by
  let w := coefficients (character c χ hu)
  have h := (pair c χ hu hp).hasMellin hs
  calc
    (pair c χ hu hp).Λ s =
        mellin (fun t => HeckeTheta.theta w (scale c * t) - w (0,0)) s := h.2.symm
    _ = (scale c : ℂ) ^ (-s) * mellin (fun t => HeckeTheta.theta w t - w (0,0)) s :=
      by simpa only [smul_eq_mul] using
        mellin_comp_mul_left (fun t => HeckeTheta.theta w t - w (0,0)) s (scale_pos c)
    _ = (scale c : ℂ) ^ (-s) * HeckeTheta.completed w s := by
      congr 1
      rw [← (HeckeTheta.pair_hasMellin w hs).2]
      unfold mellin
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [HeckeTheta.theta_eq_pair w ht, HeckeTheta.pair_f₀]

theorem pair_completed_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s :=
  HeckeMellinIdentity.scaled_eq (pair c χ hu hp)
    (HeckeTheta.pair (coefficients (character c χ hu))) rfl (HeckeTheta.pair_k _)
    (scale c) (scale_pos c) (fun _ hs => pair_completed_eq_right c χ hu hp hs) h0 h1

theorem symm_completed_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (pair c χ hu hp).symm.Λ s =
      (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv).Λ s := by
  apply HeckeMellinIdentity.eq_of_f (pair c χ hu hp).symm
    (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv) rfl rfl _ rfl h0 h1
  intro t _
  change (pair c χ hu hp).g t = _
  rw [pair_g, pair_f]

theorem completedL_functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedL c χ hu hp (1-s) = TraceCharacter.normalizedGauss c χ *
      completedL c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv s := by
  have h := (pair c χ hu hp).functional_equation s
  change (pair c χ hu hp).Λ (1-s) = TraceCharacter.normalizedGauss c χ *
    (pair c χ hu hp).symm.Λ s at h
  rw [symm_completed_eq c χ hu hp h0 h1] at h
  unfold completedL
  rw [h]
  ring

theorem completedL_eq_gamma_mul_LFunction (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s = (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) *
      Complex.Gamma s * LFunction (character c χ hu) s := by
  unfold completedL
  rw [pair_completed_eq c χ hu hp h0 h1]
  unfold LFunction continuedLattice HeckeTheta.latticeL
  simp only [Complex.cpow_neg]
  have hπ : (Real.pi : ℂ)^s ≠ 0 := by
    exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [Real.pi_ne_zero])
  field_simp

end SevenEighths.HeckePrimitive

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ThetaRegularity
namespace OAI

noncomputable section

open scoped BigOperators Classical Topology
open Filter Asymptotics

namespace SevenEighths.ThetaRegularity

open ActualEisensteinCubic ConcreteTraceCRT GaussianTheta

theorem lattice_gap (z : O) (hz : z ≠ 0) : 1 ≤ ‖eisEmbedding z‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {z}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hz)

variable (c : O) [NeZero c]

end SevenEighths.ThetaRegularity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Strip
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter Asymptotics Set MeasureTheory

namespace SevenEighths.HeckeStrip

theorem completionScale_pos (Q : ℝ) (hQ : 0 < Q) : 0 < completionScale Q := by
  unfold completionScale
  positivity

end SevenEighths.HeckeStrip
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

theorem conductor_ge_one : 1 ≤ conductor c := by
  unfold conductor
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {c}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact NeZero.ne c)

theorem completionScale_eq_inv :
    HeckeStrip.completionScale (conductor c) = (Real.pi * scale c)⁻¹ := by
  have hn : 0 < ‖ConcreteTraceCRT.eisEmbedding c‖ := by
    have h := ThetaRegularity.lattice_gap c (NeZero.ne c)
    nlinarith [norm_nonneg (ConcreteTraceCRT.eisEmbedding c)]
  unfold HeckeStrip.completionScale conductor scale GaussianTheta.parameter
  rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (norm_nonneg _)]
  field_simp

theorem completionScale_cpow (s : ℂ) :
    (HeckeStrip.completionScale (conductor c) : ℂ)^s =
      (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) := by
  rw [completionScale_eq_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (mul_nonneg Real.pi_pos.le (scale_pos c).le),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (scale_pos c).le,
    mul_inv_rev]
  simp only [Complex.cpow_neg]

theorem completedL_eq_standard (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s =
      (HeckeStrip.completionScale (conductor c) : ℂ)^s * Complex.Gamma s *
        LFunction (character c χ hu) s := by
  rw [completedL_eq_gamma_mul_LFunction c χ hu hp h0 h1 hΓ, completionScale_cpow]

theorem pair_strong (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) :
    IsStrongFEPair (pair c χ hu hp) := by
  constructor
  · exact HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal (character c χ hu) hχ
  · apply HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal
      (character c χ⁻¹ (inverse_unit_trivial c χ hu))
    change χ⁻¹ ≠ 1
    simpa only [ne_eq, inv_eq_one] using hχ

theorem LFunction_eq_uncompleted (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) (s : ℂ) :
    LFunction (character c χ hu) s =
      (HeckeStrip.completionScale (conductor c) : ℂ)^(-s) * (Complex.Gamma s)⁻¹ *
        completedL c χ hu hp s := by
  let a := HeckeStrip.completionScale (conductor c)
  have ha : 0 < a := HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))
  have hL := LFunction_entire_nonprincipal (character c χ hu) hχ
  have hΛ : Differentiable ℂ (completedL c χ hu hp) :=
    (pair_strong c χ hu hp hχ).differentiable_Λ.div_const 6
  have hR : Differentiable ℂ (fun z : ℂ => (a : ℂ)^(-z) * (Complex.Gamma z)⁻¹ *
      completedL c χ hu hp z) :=
    (((differentiable_id.neg).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      Complex.differentiable_one_div_Gamma).mul hΛ
  have he : LFunction (character c χ hu) = fun z : ℂ => (a : ℂ)^(-z) *
      (Complex.Gamma z)⁻¹ * completedL c χ hu hp z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hL).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hR) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have h0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have h1 : z ≠ 1 := by intro h; norm_num [h] at hz
    have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    rw [completedL_eq_standard c χ hu hp h0 h1 hΓ]
    have haz : (a : ℂ)^z ≠ 0 := (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [ha.ne'])
    change LFunction (character c χ hu) z = (a : ℂ)^(-z) * (Complex.Gamma z)⁻¹ *
      ((a : ℂ)^z * Complex.Gamma z * LFunction (character c χ hu) z)
    rw [Complex.cpow_neg]
    field_simp
  exact congr_fun he s

end SevenEighths.HeckeStripActual

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Presentation
namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckePresentation
open HeckeFamily

theorem principalResidue_primitive (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) :
    FiniteFourier.IsPrimitiveOnIdeals (principalResidue η) :=
  CharacterTransport.primitive_pullback (quotientEquiv η) η.residue hp

private theorem pullback_one {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    CharacterTransport.pullback e (1 : MulChar S ℂ) = 1 := by
  apply MulChar.ext'
  intro x
  rw [CharacterTransport.pullback_apply]
  by_cases hx : IsUnit x
  · have hxe : IsUnit (e x) := hx.map e.toMonoidHom
    rw [MulChar.one_apply hxe, MulChar.one_apply hx]
  · have he : ¬ IsUnit (e x) := by
      intro h
      apply hx
      simpa using h.map e.symm.toMonoidHom
    rw [MulChar.map_nonunit _ he, MulChar.map_nonunit _ hx]

theorem principalResidue_ne_one (η : Character) (hη : η.residue ≠ 1) :
    principalResidue η ≠ 1 := by
  intro h
  have he := congrArg (CharacterTransport.pullback (quotientEquiv η).symm) h
  rw [principalResidue, CharacterTransport.pullback_symm, pullback_one] at he
  exact hη he

theorem LFunction_principalCharacter (η : Character) (hη : η.residue ≠ 1) (s : ℂ) :
    LFunction (principalCharacter η) s = LFunction η s := by
  have hp : (principalCharacter η).residue ≠ 1 := principalResidue_ne_one η hη
  have ha := LFunction_entire_nonprincipal (principalCharacter η) hp
  have hb := LFunction_entire_nonprincipal η hη
  have he : LFunction (principalCharacter η) = LFunction η := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr ha).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hb) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    unfold LFunction
    congr 1
    apply continuedLattice_eq_of_elementCoeff_eq _ _ (principalCharacter_elementCoeff η)
      (by linarith) (by intro h; norm_num [h] at hz)
  exact congr_fun he s

end SevenEighths.HeckePresentation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicReflection
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Complex
namespace SevenEighths.HeckeDyadicReflection
open HeckeFamily HeckePrimitive HeckeStripActual

variable (c : O) [NeZero c]

theorem functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O))=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    {s : ℂ} (hs : s.re<1) :
    LFunction (character c χ hu) s = TraceCharacter.normalizedGauss c χ *
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) *
      (Complex.Gamma (1-s)/Complex.Gamma s) *
      LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by
  by_cases h0 : s=0
  · subst s
    rw [LFunction_eq_uncompleted c χ hu hp hχ]
    simp
  have h1 : s≠1 := by intro h; norm_num [h] at hs
  have hs0 : 1-s≠0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs1 : 1-s≠1 := by intro h; apply h0; linear_combination -h
  have hΓ : Complex.Gamma (1-s)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have he := completedL_functional_equation c χ hu hp hs0 hs1
  rw [sub_sub_cancel] at he
  rw [LFunction_eq_uncompleted c χ hu hp hχ,he,
    completedL_eq_standard c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv hs0 hs1 hΓ]
  have ha : ((HeckeStrip.completionScale (conductor c)) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (HeckeStrip.completionScale_pos _
      (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))).ne'
  have hpow : (HeckeStrip.completionScale (conductor c) : ℂ)^(-s)*
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-s)=
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) := by
    rw [←Complex.cpow_add _ _ ha]
    congr 1
    ring
  rw [div_eq_mul_inv]
  calc
    _ = TraceCharacter.normalizedGauss c χ *
        ((HeckeStrip.completionScale (conductor c) : ℂ)^(-s)*
          (HeckeStrip.completionScale (conductor c) : ℂ)^(1-s)) *
        (Complex.Gamma (1-s)*(Complex.Gamma s)⁻¹) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by ring
    _ = _ := by rw [hpow]

theorem gamma_real_ratio_bound : ∃ C : ℝ, 0<C ∧
    ∀ x ∈ Icc (-(1/10 : ℝ)) (1/2), Real.Gamma (1-x)/Real.Gamma (x+2)≤C := by
  have hcont : ContinuousOn (fun x : ℝ => Real.Gamma (1-x)/Real.Gamma (x+2))
      (Icc (-(1/10 : ℝ)) (1/2)) := by
    intro x hx
    have hnum : DifferentiableAt ℝ Real.Gamma (1-x) :=
      Real.differentiableAt_Gamma (by intro n hn; have hnn := Nat.cast_nonneg (α:=ℝ) n; linarith [hx.2])
    have hden : DifferentiableAt ℝ Real.Gamma (x+2) :=
      Real.differentiableAt_Gamma (by intro n hn; have hnn := Nat.cast_nonneg (α:=ℝ) n; linarith [hx.1])
    exact ((hnum.continuousAt.comp (g := Real.Gamma) (f := fun y : ℝ => 1-y) (show ContinuousAt (fun y : ℝ => 1-y) x by fun_prop)).div
      (hden.continuousAt.comp (g := Real.Gamma) (f := fun y : ℝ => y+2) (show ContinuousAt (fun y : ℝ => y+2) x by fun_prop))
      (Real.Gamma_pos_of_pos (show 0<x+2 by linarith [hx.1])).ne').continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (le_abs_self _).trans ((hC x hx).trans (by linarith [le_abs_self C]))

theorem gamma_ratio_strip_bound : ∃ C : ℝ, 0<C ∧ ∀ s : ℂ,
    -(1/10 : ℝ)≤ s.re → s.re≤1/2 →
    ‖Complex.Gamma (1-s)/Complex.Gamma s‖≤C*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hreal⟩ := gamma_real_ratio_bound
  refine ⟨C,hC,?_⟩
  intro s hl hr
  have hb := CubicReflectionKernel.Gamma_shifted_pair_bound
    (1/2) (1/2-s.re) (-s.im) 2 (by linarith) (by norm_num; linarith)
  have hnum : ((1/2 : ℝ) : ℂ)+((1/2-s.re : ℝ)+(-s.im)*I)=1-s := by
    apply Complex.ext <;> simp; ring
  have hden : ((1/2 : ℝ) : ℂ)-((1/2-s.re : ℝ)+(-s.im)*I)+(2 : ℕ)=s+2 := by
    apply Complex.ext <;> simp
  simp only [ofReal_neg] at hb
  rw [hnum,hden] at hb
  have hreal' := hreal s.re ⟨hl,hr⟩
  have hb' : ‖Complex.Gamma (1-s)/Complex.Gamma (s+2)‖≤C := by
    apply hb.trans
    convert (preTransparency := .instances) hreal' using 1; congr 1 <;> ring_nf
  have heq : Complex.Gamma (1-s)/Complex.Gamma s =
      (∏ k ∈ Finset.range 2, (s+k))*(Complex.Gamma (1-s)/Complex.Gamma (s+2)) := by
    rw [div_eq_mul_inv,CubicReflectionKernel.inverse_Gamma_shift s 2]
    simp only [Nat.cast_ofNat,div_eq_mul_inv]
    ring
  have hs : ‖s‖≤1+|s.im| := by
    have hsr : |s.re|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hn := Complex.norm_le_abs_re_add_abs_im s
    linarith
  have hf := CubicReflectionKernel.norm_Gamma_shift_factor s 2
  norm_num only [Nat.cast_ofNat] at hf
  have hf' : ‖∏ k ∈ Finset.range 2,(s+k)‖≤(3+|s.im|)^2 :=
    hf.trans (pow_le_pow_left₀ (by positivity) (show ‖s‖+2≤3+|s.im| by linarith) 2)
  rw [heq,norm_mul]
  exact (mul_le_mul hf' hb' (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem completionScale_rpow_le {Q x : ℝ} (hQ : 0<Q) (hx : 0≤x) :
    HeckeStrip.completionScale Q ^ x≤Q^(x/2) := by
  have hs3 : Real.sqrt 3≤2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hscale : HeckeStrip.completionScale Q≤Real.sqrt Q := by
    unfold HeckeStrip.completionScale
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤3)]
    apply (div_le_iff₀ (by positivity : 0<2*Real.pi)).mpr
    nlinarith [Real.sqrt_nonneg Q,Real.pi_gt_three]
  calc
    _ ≤ (Real.sqrt Q)^x := Real.rpow_le_rpow
      (HeckeStrip.completionScale_pos Q hQ).le hscale hx
    _ = _ := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hQ.le]
      congr 1
      ring

theorem primitive_reflected_bound : ∃ C : ℝ, 0<C ∧
    ∀ (c : O) [NeZero c] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O))=1)
      (_hp : FiniteFourier.IsPrimitiveOnIdeals χ), χ≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤ s.re → s.re≤1/2 →
    ‖LFunction (character c χ hu) s‖≤
      C*(conductor c)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)‖ := by
  obtain ⟨C,hC,hgamma⟩ := gamma_ratio_strip_bound
  refine ⟨C,hC,?_⟩
  intro c _ χ hu hp hχ s hl hr
  rw [functional_equation c χ hu hp hχ (by linarith),norm_mul,norm_mul,norm_mul,
    TraceCharacter.normalizedGauss_norm c χ hp,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (HeckeStrip.completionScale_pos _
      (lt_of_lt_of_le zero_lt_one (conductor_ge_one c)))]
  have hscale := completionScale_rpow_le
    (lt_of_lt_of_le zero_lt_one (conductor_ge_one c)) (show 0≤1-2*s.re by linarith)
  have he : (1-2*s).re=1-2*s.re := by simp
  rw [he]
  have he' : (1-2*s.re)/2=1/2-s.re := by ring
  rw [he'] at hscale
  calc
    _ ≤ ((conductor c)^(1/2-s.re)*(C*(3+|s.im|)^2))*
        ‖LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul hscale (hgamma s hl hr)
        (norm_nonneg _) (Real.rpow_nonneg (by exact_mod_cast (conductor_ge_one c).trans' zero_le_one) _))
        (norm_nonneg _)
    _ = _ := by ring

end SevenEighths.HeckeDyadicReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedFamily
namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set
namespace SevenEighths.HeckeDyadicReflection
open HeckeFamily HeckePresentation HeckeFiniteDeletion

theorem family_reflected_bound : ∃ C : ℝ, 0<C ∧ ∀ η : Character,
    FiniteFourier.IsPrimitiveOnIdeals η.residue → η.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤ s.re → s.re≤1/2 →
    ‖LFunction η s‖≤C*(η.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
      ‖LFunction η (1-conj s)‖ := by
  obtain ⟨C,hC,hbound⟩ := primitive_reflected_bound
  refine ⟨C,hC,?_⟩
  intro η hp hη s hl hr
  have h := hbound (generator η) (principalResidue η) (principalResidue_unit η)
    (principalResidue_primitive η hp) (principalResidue_ne_one η hη) s hl hr
  have hi : HeckePrimitive.character (generator η) (principalResidue η)⁻¹
      (HeckePrimitive.inverse_unit_trivial (generator η) (principalResidue η) (principalResidue_unit η)) =
      (principalCharacter η).inverse := rfl
  rw [hi,LFunction_inverse_conj (principalCharacter η) (principalResidue_ne_one η hη),
    norm_conj,map_sub,map_one] at h
  change ‖LFunction (principalCharacter η) s‖≤_ at h
  rw [LFunction_principalCharacter η hη,LFunction_principalCharacter η hη] at h
  simpa only [HeckeStripActual.conductor,span_generator] using h

theorem LFunction_eq_of_mask_entire (χ ψ : Character) (hχ : χ.residue≠1)
    (hmask : ∀ J : Ideal O, idealCoeff χ J=
      if IsCoprime J χ.modulus then idealCoeff ψ J else 0) (s : ℂ) :
    LFunction χ s=LFunction ψ s*factors χ.modulus ψ s := by
  have hψ : ψ.residue≠1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have ha := LFunction_entire_nonprincipal χ hχ
  have hb : Differentiable ℂ (fun z => LFunction ψ z*factors χ.modulus ψ z) :=
    (LFunction_entire_nonprincipal ψ hψ).mul (factors_differentiable _ _)
  have he : LFunction χ=(fun z => LFunction ψ z*factors χ.modulus ψ z) := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr ha).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hb) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    exact LFunction_eq_of_mask_right χ ψ hmask hz
  exact congr_fun he s

theorem original_reflected_bound : ∃ C : ℝ, 0<C ∧ ∀ χ ψ : Character,
    FiniteFourier.IsPrimitiveOnIdeals ψ.residue → χ.residue≠1 →
    (∀ J : Ideal O, idealCoeff χ J=
      if IsCoprime J χ.modulus then idealCoeff ψ J else 0) →
    ∀ s : ℂ, -(1/10 : ℝ)≤ s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤C*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
      ‖LFunction χ (1-conj s)‖*
      (‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖) := by
  obtain ⟨C,hC,hbound⟩ := family_reflected_bound
  refine ⟨C,hC,?_⟩
  intro χ ψ hp hχ hmask s hl hr
  have hψ : ψ.residue≠1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have h := hbound ψ hp hψ s hl hr
  have hd : factors χ.modulus ψ (1-conj s)≠0 := factors_ne_zero _ _ (by simp; linarith)
  have he : LFunction ψ (1-conj s)=LFunction χ (1-conj s)*(factors χ.modulus ψ (1-conj s))⁻¹ := by
    rw [LFunction_eq_of_mask_entire χ ψ hχ hmask]
    field_simp
  rw [he,norm_mul] at h
  rw [LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (C*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        (‖LFunction χ (1-conj s)‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖))*
          ‖factors χ.modulus ψ s‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

theorem original_reflected_subpower_oai (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ χ : Character, χ.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤ s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤C*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*
      ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
      (3+|s.im|)^2*‖LFunction χ (1-conj s)‖ := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_bound
  obtain ⟨Cl,hCl,hleft⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound ε hε
  obtain ⟨Cr,hCr,hright⟩ := HeckeDeletionBounds.factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Cg*Cl*Cr,by positivity,?_⟩
  intro χ hχ s hl hr
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hR : 0<((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (HeckeDeletionBounds.radical_ne_zero χ.modulus))
  have hd₁ := hleft χ.modulus ψ s
  have hd₂ : ‖(factors χ.modulus ψ (1-conj s))⁻¹‖≤
      Cr*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε := by
    have h := hright χ.modulus ψ (1-conj s) (by simp; linarith)
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans h
  have hd : ‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖≤
      (Cl*Cr)*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε) := by
    calc
      _ ≤ (Cl*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε))*
          (Cr*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) :=
        mul_le_mul hd₁ hd₂ (norm_nonneg _) (mul_nonneg hCl.le (Real.rpow_nonneg hR.le _))
      _ = _ := by
        have he : ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε)*
            ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε =
            ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε) := by
          rw [←Real.rpow_add hR]
          congr 1
          ring
        calc
          _ = (Cl*Cr)*(((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε)*
              ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) := by ring
          _ = _ := by rw [he]
  have hQ' : (ψ.modulus.absNorm : ℝ)^(1/2-s.re)≤(χ.modulus.absNorm : ℝ)^(1/2-s.re) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by linarith)
  calc
    _ ≤ Cg*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction χ (1-conj s)‖*
        (‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖) :=
      hreflect χ ψ hp hχ hmask s hl hr
    _ ≤ Cg*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction χ (1-conj s)‖*
        ((Cl*Cr)*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)) := by
      apply mul_le_mul _ hd (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      gcongr
    _ = _ := by ring

end SevenEighths.HeckeDyadicReflection

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.HeckeDyadicReflection.original_reflected_subpower_oai := @OAI.SevenEighths.HeckeDyadicReflection.original_reflected_subpower_oai
