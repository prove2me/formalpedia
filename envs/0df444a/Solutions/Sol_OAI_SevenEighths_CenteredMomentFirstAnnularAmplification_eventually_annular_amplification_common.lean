-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFirstAnnularAmplification.eventually_annular_amplification_common
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:51:47.378529+00:00
-- url     : https://prove2.me/submissions/9b2a81ad-6023-4b37-b2d1-b510465bbe68

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Theorems.Thm_OAI_SevenEighths_CenteredMomentAmplificationRadicalChoice_eventually_original_amplification_common

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

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

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

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

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

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Physical
namespace OAI

noncomputable section

open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbeCompleted ProbeRow

local notation "O" => ActualEisensteinCubic.O

theorem sexticGauss_coefficient_mk (s : O) (a : O) :
    idealRowHom (GaussianShiftedPartition.representative s
      (Ideal.Quotient.mk (Ideal.span {s}) a)) (Ideal.span {s}) =
      idealRowHom a (Ideal.span {s}) := by
  apply idealRowHom_congr_mod
  apply Ideal.Quotient.eq.mp
  exact GaussianShiftedPartition.representative_spec _ _

attribute [local irreducible] markedPhysicalProbe

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Fourier
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFourier
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation

theorem residueGauss_supported_mk (d : O)
    (hd : CanonicalQuadraticSieve.Supported (Ideal.span {d})) (h : O) :
    residueGauss d (supported_element_ne_zero d hd) (supportedModulusCharacter d hd)
      (Ideal.Quotient.mk _ h) = ProbePhysical.sexticGauss d (supported_element_ne_zero d hd) h := by
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [supportedModulusCharacter_mk, ProbePhysical.sexticGauss_coefficient_mk]

end SevenEighths.CenteredMomentFourier
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.GaussEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentGaussEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentFourier
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem gaussRow_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => gaussRow a ha z * star (gaussRow b hb z) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  let P : Residue (a * b) → ℂ := fun x =>
    normalizedResidueGauss a (supported_element_ne_zero a ha)
      (supportedModulusCharacter a ha) (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (normalizedResidueGauss b (supported_element_ne_zero b hb)
      (supportedModulusCharacter b hb) (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) P
  simpa only [P, frequencyReduction_mk, normalizedResidueGauss,
    residueGauss_supported_mk, scaledRadialTest_apply, gaussRow] using hs

theorem gaussPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : O) :
    ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [gaussPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gaussEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  exact (hasSum_sum (fun i _ =>
    (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

end SevenEighths.CenteredMomentGaussEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Wiener
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

attribute [fun_prop] Real.continuous_fourierChar

attribute [fun_prop] measurable_coe_nnreal_ennreal

theorem Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSmoothedWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem gaussEnergy_hasSum_re {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ‖gaussPolynomial S a ha c z‖^2*
      (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (gaussEnergy S a ha c U K).re := by
  have hs := Complex.hasSum_re (gaussEnergy_summable S a ha c U K hK).hasSum
  simpa only [gaussEnergy,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hs

end SevenEighths.CenteredMomentSmoothedWindowEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

theorem annulus_bounds (x : ℝ) : 0 ≤ annulus x ∧ annulus x ≤ 1 := by
  by_cases hx : x ≤ 1/4
  · rw [annulus_zero_low x hx]; constructor <;> norm_num
  have hm := cutoff_antitone (show x ≤ 2*x by linarith)
  have h₁ := cutoff_bounds x
  have h₂ := cutoff_bounds (2*x)
  unfold annulus
  constructor <;> linarith

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

theorem dyadicWeight_bounds (n : ℤ) (q : ℝ) :
    0 ≤ dyadicWeight n q ∧ dyadicWeight n q ≤ 1 := annulus_bounds _

theorem dyadicWeight_outside_pair (q : ℝ) (k : ℤ)
    (hlo : dyadicScale k ≤ q) (hhi : q < dyadicScale (k+1))
    (n : ℤ) (hn : n ∉ ({k+1,k+2} : Finset ℤ)) : dyadicWeight n q=0 := by
  have hn₁ : n ≠ k+1 := by simpa using fun h => hn (by simp [h])
  have hn₂ : n ≠ k+2 := by simpa using fun h => hn (by simp [h])
  by_cases hnk : n ≤ k
  · exact dyadicWeight_zero_high n q ((zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnk).trans hlo)
  · have hkn : k+3 ≤ n := by omega
    have hmono : dyadicScale (k+3) ≤ dyadicScale n :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
    have he : dyadicScale (k+3)=4*dyadicScale (k+1) := by
      rw [show k+3=(k+1)+1+1 by omega,dyadicScale_add,dyadicScale_add]
      ring
    apply dyadicWeight_zero_low
    rw [he] at hmono
    linarith

theorem dyadicWeight_partition (q : ℝ) (hq : 0 < q) : ∑' n,dyadicWeight n q=1 := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
  rw [tsum_eq_sum (s := {k+1,k+2}) (dyadicWeight_outside_pair q k hlo hhi)]
  change dyadicScale k ≤ q at hlo
  change q < dyadicScale (k+1) at hhi
  have hk : k+1 ≠ k+2 := by omega
  rw [Finset.sum_pair hk]
  simp only [dyadicWeight,annulus]
  have h₁ : 2*(q/dyadicScale (k+1))=q/dyadicScale k := by
    rw [dyadicScale_add]; field_simp
  have h₂ : 2*(q/dyadicScale (k+2))=q/dyadicScale (k+1) := by
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]; field_simp
  rw [h₁,h₂,cutoff_zero _ ((le_div_iff₀ (dyadicScale_pos k)).mpr (by simpa using hlo))]
  have hs : q/dyadicScale (k+2) ≤ 1/2 := by
    apply (div_le_iff₀ (dyadicScale_pos (k+2))).mpr
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]
    linarith
  rw [cutoff_one _ hs]
  ring

theorem annulus_pos (x : ℝ) (hlo : 1/4 < x) (hhi : x < 1) : 0 < annulus x := by
  by_cases hx : x ≤ 1/2
  · rw [annulus,cutoff_one x hx]
    have h := Real.smoothTransition.lt_one_of_lt_one (by linarith : 2-2*(2*x) < 1)
    exact sub_pos.mpr h
  · rw [annulus,cutoff_zero (2*x) (by linarith),sub_zero]
    exact Real.smoothTransition.pos_of_pos (by linarith)

theorem dyadicWeight_support_eq (n : ℤ) :
    Function.support (dyadicWeight n)=Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  apply Set.Subset.antisymm (dyadicWeight_support n)
  intro q hq
  apply ne_of_gt
  apply annulus_pos
  · apply (lt_div_iff₀ (dyadicScale_pos n)).mpr
    linarith [hq.1]
  · exact (div_lt_one (dyadicScale_pos n)).mpr hq.2

theorem dyadicWeight_tsupport_eq (n : ℤ) :
    tsupport (dyadicWeight n)=Set.Icc (dyadicScale n/4) (dyadicScale n) := by
  rw [tsupport,dyadicWeight_support_eq,closure_Ioo]
  linarith [dyadicScale_pos n]

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.Profiles
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentEnergyProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalSource
open CenteredMomentScaleSupremum

lemma annulusTemplate_apply (x:ℝ):annulusTemplate.profile x=(CenteredMomentSectorLocalization.annulus x:ℂ):=rfl

end SevenEighths.CenteredMomentEnergyProfiles

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DyadicCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.CenteredMomentDyadicCount
open CenteredMomentSectorLocalization

lemma logb_dyadicScale (n : ℤ) : Real.logb 2 (dyadicScale n)=(n:ℝ) := by
  rw [dyadicScale,←Real.rpow_intCast,Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num)]

lemma mem_indices_iff_scale (a b : ℝ) (ha : 0<a) (hb : 0<b) (n : ℤ) :
    n∈indices a b ↔ a≤dyadicScale n ∧ dyadicScale n≤4*b := by
  rw [indices,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  rw [←logb_dyadicScale n]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(Real.logb_le_logb (by norm_num) ha (dyadicScale_pos n)).mp h1,
      (Real.logb_le_logb (by norm_num) (dyadicScale_pos n) (by positivity)).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨Real.logb_le_logb_of_le (by norm_num) ha h1,
      Real.logb_le_logb_of_le (by norm_num) (dyadicScale_pos n) h2⟩

lemma mem_indices_iff_whole_support (a b : ℝ) (ha : 0<a) (hab : a≤b) (n : ℤ) :
    n∈indices a b ↔ ∃q∈Icc a b,q∈tsupport (dyadicWeight n) := by
  rw [mem_indices_iff_scale a b ha (ha.trans_le hab) n]
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨max a (dyadicScale n/4),⟨le_max_left _ _,max_le hab (by linarith)⟩,?_⟩
    rw [dyadicWeight_tsupport_eq]
    exact ⟨le_max_right _ _,max_le hlo (by linarith [dyadicScale_pos n])⟩
  · rintro ⟨q,hq,hq'⟩
    have hh := dyadicWeight_tsupport n hq'
    exact ⟨hq.1.trans hh.2,by linarith [hq.2,hh.1]⟩

lemma support_indices (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b)
    (n : ℤ) (hne : dyadicWeight n q≠0) : n∈indices a b :=
  (mem_indices_iff_whole_support a b ha (hq.1.trans hq.2) n).mpr
    ⟨q,hq,subset_tsupport _ hne⟩

lemma logb_four_mul (b : ℝ) (hb : 0<b) :
    Real.logb 2 (4*b)=2+Real.logb 2 b := by
  rw [Real.logb_mul (by norm_num) hb.ne']
  congr 1
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem indices_card_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ((indices a b).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have hb := ha.trans_le hab
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha hab
  have hu := Int.ceil_lt_add_one (Real.logb 2 a)
  have hl := Int.sub_one_lt_floor (Real.logb 2 (4*b))
  have he := logb_four_mul b hb
  have hle : ⌈Real.logb 2 a⌉≤⌊Real.logb 2 (4*b)⌋+1 := by
    have hh : (⌈Real.logb 2 a⌉:ℝ)≤(⌊Real.logb 2 (4*b)⌋:ℝ)+1 := by linarith
    exact_mod_cast hh
  have hcard := Int.card_Icc_of_le _ _ hle
  have hcard' : ((indices a b).card:ℝ)=(⌊Real.logb 2 (4*b)⌋:ℝ)+1-(⌈Real.logb 2 a⌉:ℝ) := by
    exact_mod_cast hcard
  rw [hcard',Real.logb_div hb.ne' ha.ne']
  linarith [Int.floor_le (Real.logb 2 (4*b)),Int.le_ceil (Real.logb 2 a)]

lemma dyadic_partition_on_interval (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b) :
    (∑n∈indices a b,dyadicWeight n q)=1 := by
  rw [←dyadicWeight_partition q (ha.trans_le hq.1)]
  symm
  apply tsum_eq_sum
  intro n hn
  by_contra hne
  exact hn (support_indices a b q ha hq n hne)

end SevenEighths.CenteredMomentDyadicCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

lemma weight_bounds (x:ℝ):0≤weight x ∧ weight x≤1:=by
  have h₁:=cutoff_bounds (x/2)
  have h₂:=cutoff_bounds (4*x)
  unfold weight
  constructor
  · exact mul_nonneg h₁.1 (sub_nonneg.mpr h₂.2)
  · exact (mul_le_mul_of_nonneg_left (sub_le_self _ h₂.1) h₁.1).trans
      (by simpa only [mul_one] using h₁.2)

lemma weight_one (x:ℝ)(hx:1/4≤x)(hx':x≤1):weight x=1:=by
  rw [weight,cutoff_one (x/2) (by linarith),cutoff_zero (4*x) (by linarith)]
  norm_num

lemma profile_apply (x:ℝ):profile x=(weight x:ℂ):=rfl
lemma profile_nonneg (x:ℝ):0≤(profile x).re:=(weight_bounds x).1
lemma profile_le_one (x:ℝ):(profile x).re≤1:=(weight_bounds x).2
lemma profile_one (x:ℝ)(hx:1/4≤x)(hx':x≤1):profile x=1:=by
  rw [profile_apply,weight_one x hx hx'];rfl

lemma bands_scale (H:ℝ)(hH:0<H)(j:ℤ)(hj:j∈bands H):
    H/8≤dyadicScale j ∧ dyadicScale j≤8*H:=by
  have h:=(mem_indices_iff_scale (H/8) (2*H) (by positivity) (by positivity) j).mp hj
  constructor
  · exact h.1
  · linarith [h.2]

lemma bands_card (H:ℝ)(hH:0<H):((bands H).card:ℝ)≤7:=by
  have h:=indices_card_bound (H/8) (2*H) (by positivity) (by linarith)
  have he:(2*H)/(H/8)=16:=by field_simp;ring
  rw [he,show (16:ℝ)=(2:ℝ)^4 by norm_num,Real.logb_pow] at h
  norm_num [Real.logb_self_eq_one] at h
  change ((indices (H/8) (2*H)).card:ℝ)≤7
  exact_mod_cast h

lemma weighted_partition (H q:ℝ)(hH:0<H):
    (profile (q/H)).re=(∑j∈bands H,dyadicWeight j q)*(profile (q/H)).re:=by
  by_cases h:weight (q/H)=0
  · simp only [profile_apply,Complex.ofReal_re,h,mul_zero]
  · have hx:=weight_support h
    have hq:q∈Set.Icc (H/8) (2*H):=⟨by linarith [(le_div_iff₀ hH).mp hx.1],
      (div_le_iff₀ hH).mp hx.2⟩
    rw [bands,dyadic_partition_on_interval (H/8) (2*H) q (by positivity) hq]
    exact (one_mul _).symm

end SevenEighths.CenteredMomentFirstAnnularMajorant

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAnnularEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentFirstAnnularMajorant CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentSmoothedWindowEnergy
local notation "O"=>HeckeFamily.O

variable {α:Type*}

lemma dyadic_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(j:ℤ):Summable (fun z:O=>dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2):=by
  have hs:=gaussEnergy_hasSum_re S a ha c CenteredMomentEnergyProfiles.annulusTemplate.profile
    (dyadicScale j) (dyadicScale_pos j)
  simpa only [CenteredMomentEnergyProfiles.annulusTemplate_apply,Complex.ofReal_re,
    dyadicWeight,normValue_eq_embedding,mul_comm] using hs.summable

lemma weighted_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    Summable (fun z:O=>‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  simpa only [normValue_eq_embedding] using (gaussEnergy_hasSum_re S a ha c profile H hH).summable

theorem energy_partition (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    (gaussEnergy S a ha c profile H).re=
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  have hs:=weighted_summable S a ha c H hH
  have hj (j:ℤ):Summable (fun z:O=>dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=by
    apply hs.of_nonneg_of_le
    · intro z
      exact mul_nonneg (dyadicWeight_bounds j _).1 (mul_nonneg (sq_nonneg _) (profile_nonneg _))
    · intro z
      exact mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (profile_nonneg _)) (dyadicWeight_bounds j _).2
  have he (z:O):‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re=
      ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
    rw [←Finset.sum_mul]
    calc
      _=‖gaussPolynomial S a ha c z‖^2*
          ((∑j∈bands H,dyadicWeight j (normValue z))*(profile (normValue z/H)).re):=by
        rw [←weighted_partition H (normValue z) hH]
      _=_:=by ring
  have hsum:=gaussEnergy_hasSum_re S a ha c profile H hH
  rw [←hsum.tsum_eq]
  simp_rw [←normValue_eq_embedding]
  calc
    _ = ∑'z:O, ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re) :=
      tsum_congr he
    _ = _ := Summable.tsum_finsetSum (fun j _=>hj j)

theorem energy_le_dyadic (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    (gaussEnergy S a ha c profile H).re≤
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=by
  rw [energy_partition S a ha c H hH]
  apply Finset.sum_le_sum
  intro j hj
  have hs:=dyadic_summable S a ha c j
  have hdom (z:O):dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)≤
      dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg _) (profile_le_one _))
      (dyadicWeight_bounds j _).1
  have hl:Summable (fun z:O=>dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=
    hs.of_nonneg_of_le (fun z=>mul_nonneg (dyadicWeight_bounds j _).1
      (mul_nonneg (sq_nonneg _) (profile_nonneg _))) hdom
  exact hl.tsum_le_tsum hdom hs

end SevenEighths.CenteredMomentFirstAnnularEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAnnularGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentFirstAnnularGeometry
open CenteredMomentSectorLocalization CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAnnularEnergy CenteredMomentGaussEnergy CanonicalQuadraticSieve

local notation "O"=>HeckeFamily.O

lemma retained_of_scale_le (j:ℤ)(R:ℝ)(h:dyadicScale j≤R):Retained R j:=by
  refine ⟨dyadicScale j/2, by exact div_pos (dyadicScale_pos j) (by norm_num), by linarith [dyadicScale_pos j], ?_⟩
  apply subset_closure
  change dyadicWeight j (dyadicScale j/2)≠0
  have he:(dyadicScale j/2)/dyadicScale j=(1/2:ℝ):=by
    field_simp [ne_of_gt (dyadicScale_pos j)]
  rw [dyadicWeight,he,annulus,cutoff_one _ (by norm_num)]
  norm_num [cutoff_zero]

lemma bands_retained (H R:ℝ)(hH:0<H)(hR:8*H≤R)(j:ℤ)(hj:j∈bands H):
    Retained R j:=retained_of_scale_le j R ((bands_scale H hH j hj).2.trans hR)

lemma bands_log_cap (H Z A:ℝ)(hH:0<H)(hZ:1<Z)(hcap:8*H≤Z^A)
    (j:ℤ)(hj:j∈bands H):Real.logb Z (dyadicScale j)≤A:=by
  have he:Real.logb Z (Z^A)=A:=Real.logb_rpow (by positivity) (ne_of_gt hZ)
  rw [←he]
  exact Real.logb_le_logb_of_le hZ (dyadicScale_pos j) ((bands_scale H hH j hj).2.trans hcap)

lemma bands_nonempty (H:ℝ)(hH:0<H):(bands H).Nonempty:=by
  by_contra hn
  have he:bands H=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
  have hp:=weighted_partition H (H/2) hH
  have hr:(H/2)/H=(1/2:ℝ):=by field_simp
  rw [hr,profile_one _ (by norm_num) (by norm_num),he] at hp
  norm_num at hp

theorem common_bound {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(H B:ℝ)(hH:0<H)(hB:0≤B)
    (hb:∀j∈bands H,(∑' z : O, dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2)≤B):
    (gaussEnergy S a ha c profile H).re≤7*B:=by
  apply (energy_le_dyadic S a ha c H hH).trans
  calc
    _≤∑j∈bands H,B:=Finset.sum_le_sum hb
    _=((bands H).card:ℝ)*B:=by simp
    _≤7*B:=mul_le_mul_of_nonneg_right (bands_card H hH) hB

theorem common_bound_auto {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(H B:ℝ)(hH:0<H)
    (hb:∀j∈bands H,(∑' z : O, dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2)≤B):
    (gaussEnergy S a ha c profile H).re≤7*B:=by
  obtain ⟨j,hj⟩:=bands_nonempty H hH
  have hB:0≤B:=(tsum_nonneg (fun z=>mul_nonneg (dyadicWeight_bounds j _).1 (sq_nonneg _))).trans (hb j hj)
  exact common_bound S a ha c H B hH hB hb

end SevenEighths.CenteredMomentFirstAnnularGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAnnularAmplification
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAnnularAmplification
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O

local instance instDecidableEqSumFinOfNatNat_solutions_r1356f5_1 {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
theorem eventually_annular_amplification_common_oai {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T d cLog : ℝ),0<T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi →
          8*H0≤Z^Mmax →
          (gaussEnergy Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            CenteredMomentFirstAnnularMajorant.profile H0).re≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentAmplificationRadicalChoice.eventually_original_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta (32*Csec) xi reserve
    hsigma hloss hM hb hgap (by linarith) hxi hreserve] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩:=hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have hsec' :32*Tsec≤(32*Csec)*firstNominalScale I J E K X:=by nlinarith
  have hfreq:8*H0≤frequencyRadius (32*Tsec) Z xi:=by
    unfold frequencyRadius at houter ⊢
    nlinarith
  have hbnd:=CenteredMomentFirstAnnularGeometry.common_bound_auto Finset.univ
    (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) H0 _ hH0 (fun j hj=>
      henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
        I J E hE K X (32*Tsec) hK hX hsec' j
        (CenteredMomentFirstAnnularGeometry.bands_retained H0 _ hH0 hfreq j hj)
        (CenteredMomentFirstAnnularGeometry.bands_log_cap H0 Z Mmax hH0 hZ hcap j hj))
  convert (preTransparency := .instances) hbnd using 1 ; ring

end SevenEighths.CenteredMomentFirstAnnularAmplification

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentFirstAnnularAmplification.eventually_annular_amplification_common_oai.{u_1} := @OAI.SevenEighths.CenteredMomentFirstAnnularAmplification.eventually_annular_amplification_common_oai.{u_1}
