-- Prove2me | solution 1 for OAI.SevenEighths.DetectorDictionaryInverseRawInitialEnergy.raw_rows_le_initial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:04:37.331065+00:00
-- url     : https://prove2.me/submissions/8a5df5fa-526c-445d-8c2e-ef4dac3743b7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Overlap
namespace OAI

namespace SevenEighths.InverseMoment

open UniqueFactorizationMonoid

section Moebius

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]

theorem moebius_squarefree_sq {P : M} (hP : Squarefree P) :
    moebius P ^ 2 = 1 := by
  rw [hP.moebius_eq, ← pow_mul, mul_comm _ 2, pow_mul]
  norm_num

theorem moebius_overlap_recovery {n P : M} (hnP : IsRelPrime n P)
    (hP : Squarefree P) : moebius n = moebius (n * P) * moebius P := by
  rw [hnP.moebius_mul, mul_assoc, ← pow_two, moebius_squarefree_sq hP, mul_one]

theorem moebius_character_overlap (ψ : M →* ℂ) {j n₀ P₀ : M}
    (hjn : IsRelPrime j n₀) (hnP : IsRelPrime n₀ P₀) (hP : Squarefree P₀) :
    (moebius (j * n₀) : ℂ) * ψ (j * n₀) * ψ (j * P₀) =
      (moebius j : ℂ) * (moebius P₀ : ℂ) * (moebius (n₀ * P₀) : ℂ) *
        ψ j ^ 2 * ψ (n₀ * P₀) := by
  have hμ : (moebius n₀ : ℂ) = (moebius (n₀ * P₀) : ℂ) * (moebius P₀ : ℂ) := by
    exact_mod_cast moebius_overlap_recovery hnP hP
  rw [hjn.moebius_mul, Int.cast_mul, map_mul, map_mul, map_mul, hμ]
  ring

end Moebius

end SevenEighths.InverseMoment

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

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem finiteSquarefreeRow_pair_radial_summable
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun u : O =>
      (star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u) *
        W (‖eisEmbedding u‖ ^ 2 / scale)) := by
  have hW : Summable (fun u : O => ‖W (‖eisEmbedding u‖ ^ 2 / scale)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W scale hscale)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun u => norm_nonneg _) _ hW
  intro u
  simp only [norm_mul, norm_star]
  calc
    ‖finiteSquarefreeRow P hgood S u‖ * ‖finiteSquarefreeRow P hgood T u‖ *
        ‖W (‖eisEmbedding u‖ ^ 2 / scale)‖ ≤
      1 * 1 * ‖W (‖eisEmbedding u‖ ^ 2 / scale)‖ := by
        gcongr
        · exact finiteSquarefreeRow_norm_le_one P hgood S u
        · exact finiteSquarefreeRow_norm_le_one P hgood T u
    _ = _ := by ring

private theorem norm_sq_finite_row_sum {β : Type*}
    (C : Finset β) (a r : β → ℂ) :
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

theorem finiteSquarefreeRow_smoothed_mean_square_summable
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (C : Finset β) (support : β → Finset ι) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun u : O => W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖∑ n ∈ C, a n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) : ℂ)) := by
  have hs := summable_sum (s := C) (fun n hn =>
    summable_sum (s := C) (fun m hm =>
      (finiteSquarefreeRow_pair_radial_summable P hgood (support n) (support m)
        W scale hscale).mul_left (star (a n) * a m)))
  apply hs.congr
  intro u
  rw [norm_sq_finite_row_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

end ActualEisensteinCubic

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialOverlap
namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum
open UniqueFactorizationMonoid

namespace SevenEighths.InverseInitialOverlap

theorem mem_original {S : Finset (Ideal O)} {P j n : Ideal O} :
    n ∈ original S P j ↔ n ∈ S ∧ Squarefree n ∧ gcd n P = j := by
  simp only [original, Finset.mem_filter]

theorem residual_mul {P j : Ideal O} (hj : j ∣ P) : j * residual P j = P :=
  idealQuotient_mul hj

theorem residual_squarefree {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) :
    Squarefree (residual P j) :=
  hP.squarefree_of_dvd (idealQuotient_dvd hj)

theorem quotient_mul_cancel {D H : Ideal O} (hD : D ≠ 0) :
    idealQuotient D (D * H) = H :=
  mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D H))

theorem column_properties {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hn : Squarefree n) (hg : gcd n P = j) :
    Squarefree (column P j n) ∧ IsCoprime (column P j n) j ∧
      residual P j ∣ column P j n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hHP : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have hHj := hHP.mono (dvd_refl _) hj
  have hHP0 := hHP.mono (dvd_refl _) (idealQuotient_dvd hj)
  have hJP0 : IsCoprime j (residual P j) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (j * residual P j) by rw [residual_mul hj]; exact hP)).1
  refine ⟨squarefree_mul_iff.mpr ⟨hHP0.isRelPrime,
    hn.squarefree_of_dvd (idealQuotient_dvd hjn), residual_squarefree hP hj⟩,
    hHj.mul_left hJP0.symm, dvd_mul_left _ _⟩

theorem reconstruct_column {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hg : gcd n P = j) : reconstruct P j (column P j n) = n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hP0 := (residual_squarefree hP hj).ne_zero
  unfold reconstruct column
  rw [mul_comm (idealQuotient j n), quotient_mul_cancel hP0, idealQuotient_mul hjn]

theorem reconstruct_properties {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hc : Squarefree c) (hcj : IsCoprime c j) (hPc : residual P j ∣ c) :
    Squarefree (reconstruct P j c) ∧ gcd (reconstruct P j c) P = j := by
  let H := idealQuotient (residual P j) c
  have hHc : H ∣ c := idealQuotient_dvd hPc
  have hHj : IsCoprime H j := hcj.mono hHc (dvd_refl _)
  have hHP0 : IsCoprime H (residual P j) :=
    (ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (residual P j * H) by rw [idealQuotient_mul hPc]; exact hc)).1).symm
  have hHP : IsCoprime H P := by
    rw [← residual_mul hj]
    exact hHj.mul_right hHP0
  exact ⟨squarefree_mul_iff.mpr ⟨hHj.symm.isRelPrime,
    hP.squarefree_of_dvd hj, hc.squarefree_of_dvd hHc⟩,
    gcd_mul_of_coprime_divisor j H P hj hHP⟩

theorem column_reconstruct {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) : column P j (reconstruct P j c) = c := by
  have hj0 : j ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero hj
  unfold column reconstruct
  rw [quotient_mul_cancel hj0, mul_comm, idealQuotient_mul hPc]

theorem mem_columns {S : Finset (Ideal O)} {P j c : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    c ∈ columns S P j ↔ Squarefree c ∧ IsCoprime c j ∧
      residual P j ∣ c ∧ reconstruct P j c ∈ S := by
  constructor
  · intro hc
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hnS, hn, hg⟩ := mem_original.mp hn
    obtain ⟨hcs, hcj, hPc⟩ := column_properties hP hj hn hg
    exact ⟨hcs, hcj, hPc, by rwa [reconstruct_column hP hj hg]⟩
  · rintro ⟨hc, hcj, hPc, hnS⟩
    obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hc hcj hPc
    exact Finset.mem_image.mpr ⟨reconstruct P j c,
      mem_original.mpr ⟨hnS, hn, hg⟩, column_reconstruct hP hj hPc⟩

theorem column_injOn (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    Set.InjOn (column P j) (original S P j) := by
  intro n hn m hm he
  have hn' := reconstruct_column hP hj (mem_original.mp hn).2.2
  have hm' := reconstruct_column hP hj (mem_original.mp hm).2.2
  rw [← hn', ← hm', he]

theorem reconstruct_mul_residual {P j c : Ideal O} (hPc : residual P j ∣ c) :
    reconstruct P j c * residual P j = j * c := by
  unfold reconstruct
  rw [mul_assoc, mul_comm (idealQuotient _ _), idealQuotient_mul hPc]

theorem norm_reconstruct {P j c : Ideal O} (hPc : residual P j ∣ c) :
    Ideal.absNorm (reconstruct P j c) * Ideal.absNorm (residual P j) =
      Ideal.absNorm j * Ideal.absNorm c := by
  simpa only [map_mul] using congrArg Ideal.absNorm (reconstruct_mul_residual hPc)

theorem cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) (X : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / X =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c /
        ((Ideal.absNorm (residual P j) : ℝ) * X) := by
  have h0 : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hn : (Ideal.absNorm (reconstruct P j c) : ℝ) =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c / Ideal.absNorm (residual P j) := by
    apply (eq_div_iff h0).mpr
    exact_mod_cast norm_reconstruct hPc
  rw [hn, div_div]

theorem sum_reconstruct (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (F : Ideal O → ℂ) :
    (∑ n ∈ original S P j, F n) =
      ∑ c ∈ columns S P j, F (reconstruct P j c) := by
  rw [columns, Finset.sum_image (column_injOn S hP hj)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [reconstruct_column hP hj (mem_original.mp hn).2.2]

theorem coefficient_identity (ψ : Ideal O →* ℂ) {P j n : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (hn : Squarefree n) (hg : gcd n P = j) :
    (moebius n : ℂ) * ψ n * ψ P =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2 *
        ((moebius (column P j n) : ℂ) * ψ (column P j n)) := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hH : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have h := InverseMoment.moebius_character_overlap ψ
    (hH.mono (dvd_refl _) hj).symm.isRelPrime
    (hH.mono (dvd_refl _) (idealQuotient_dvd hj)).isRelPrime
    (residual_squarefree hP hj)
  rw [idealQuotient_mul hjn, idealQuotient_mul hj] at h
  change (moebius n : ℂ) * ψ n * ψ P = _
  rw [h]
  unfold column residual
  ring

theorem polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ original S P j,
      (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / X)) =
    ((moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * X)) := by
  rw [sum_reconstruct S hP hj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨hcs, hcj, hPc, _⟩ := (mem_columns hP hj).mp hc
  obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hcs hcj hPc
  rw [coefficient_identity ψ hP hj hn hg, column_reconstruct hP hj hPc,
    cutoff_argument hP hj hPc]
  ring

theorem sum_original_partition (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (F : Ideal O → ℂ) :
    (∑ n ∈ S.filter Squarefree, F n) =
      ∑ j ∈ idealDivisors P, ∑ n ∈ original S P j, F n := by
  have hmap : ∀ n ∈ S.filter Squarefree, gcd n P ∈ idealDivisors P := by
    intro n _
    exact (mem_idealDivisors hP.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)
  have h := Finset.sum_fiberwise_of_maps_to hmap F
  simpa only [original, Finset.filter_filter] using h.symm

theorem scaled_cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / Z ^ r =
      (((Ideal.absNorm j : ℝ) / Z ^ G) *
        ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
        ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G)) := by
  have hnorm : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hscale : Z ^ G * Z ^ (r + z - 2 * G) = Z ^ r * Z ^ (z - G) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  rw [cutoff_argument hP hj hPc]
  rw [div_mul_div_comm, div_div_eq_mul_div]
  field_simp [hnorm, (Real.rpow_pos_of_pos hZ r).ne',
    (Real.rpow_pos_of_pos hZ G).ne',
    (Real.rpow_pos_of_pos hZ (r + z - 2 * G)).ne',
    (Real.rpow_pos_of_pos hZ (z - G)).ne']
  linear_combination ((Ideal.absNorm j : ℝ) * Ideal.absNorm c) * hscale

theorem normalization_split {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    Z ^ (-(r + z) / 2) = Z ^ (-G) * Z ^ (-(r + z - 2 * G) / 2) := by
  rw [← Real.rpow_add hZ]
  congr 1
  ring

theorem normalized_polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ original S P j,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
      (Z ^ (-G) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G) / 2) : ℝ) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
  rw [polynomial_fixed_overlap S hP hj ψ a W, normalization_split hZ r z G,
    Complex.ofReal_mul]
  have hs : (∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * Z ^ r))) =
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hPc := ((mem_columns hP hj).mp hc).2.2.1
    rw [← cutoff_argument hP hj hPc, scaled_cutoff_argument hP hj hPc hZ]
  rw [hs]
  ring

theorem normalized_polynomial_all_overlaps (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S.filter Squarefree,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  rw [sum_original_partition S hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact normalized_polynomial_fixed_overlap S hP
    ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W hZ r z (G j)

theorem sum_moebius_filter (S : Finset (Ideal O)) (F : Ideal O → ℂ) :
    (∑ n ∈ S, (moebius n : ℂ) * F n) =
      ∑ n ∈ S.filter Squarefree, (moebius n : ℂ) * F n := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnf
  have hns : ¬ Squarefree n := fun h => hnf (Finset.mem_filter.mpr ⟨hn, h⟩)
  simp only [moebius_of_not_squarefree hns, Int.cast_zero, zero_mul]

theorem original_normalized_polynomial (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  have hf := sum_moebius_filter S (fun n =>
    ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r))
  simp only [← mul_assoc] at hf
  rw [hf]
  exact normalized_polynomial_all_overlaps S hP ψ a W hZ r z G

end SevenEighths.InverseInitialOverlap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialPoissonBridge
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialPoissonBridge
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open UniqueFactorizationMonoid InverseInitialOverlap
local notation "Eis" => ActualEisensteinCubic.O

theorem idealRowHom_eq_idealSexticRow
    (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I)
    {I : Ideal Eis} (hI : I ∈ F) (u : Eis) :
    idealRowHom u I = idealSexticRow F (pool_positive F hF) (pool_good F hF) I u := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  conv_lhs => rw [← idealSupport_product_eq F hI (hF I hI).2.1]
  rw [map_prod]
  change (∏ q ∈ idealSupport F I, idealRowHom u q.val) =
    ∏ q ∈ idealSupport F I, CompletedGauss.actualSextic q.val (primePool_good F (pool_good F hF) q)
      (Ideal.Quotient.mk q.val u)
  apply Finset.prod_congr rfl
  intro q hq
  exact idealRowHom_prime u q.val (primePool_good F (pool_good F hF) q)

theorem indexed_smoothed_summable {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * idealRowHom u (L c)‖^2 : ℝ)) := by
  let F := C.image L
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
    exact hL c hc
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he (u : Eis) : (∑ c ∈ C, A c*idealRowHom u (L c)) =
      ∑ c ∈ C, A c*idealSexticRow F (pool_positive F hF) (pool_good F hF) (L c) u := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_image.mpr ⟨c,hc,rfl⟩)]
  simpa only [he,idealSexticRow] using finiteSquarefreeRow_smoothed_mean_square_summable
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF))
    C (fun c => idealSupport F (L c)) A Φ Y hY

theorem supported_of_dvd {I J : Ideal Eis} (hI : Supported I) (hJI : J ∣ I) : Supported J := by
  obtain ⟨K,rfl⟩ := hJI
  exact (supported_mul_iff J K).mp hI |>.1

theorem columns_admissible (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n)
    {c : Ideal Eis} (hc : c ∈ columns S P j) : Admissible c := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hnS,hns,hg⟩ := mem_original.mp hn
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hs := (supported_mul_iff (idealQuotient j n) (residual P j)).mpr
    ⟨supported_of_dvd (hS n hnS hns) (idealQuotient_dvd hjn),
     supported_of_dvd (admissible_supported hP) (idealQuotient_dvd hj)⟩
  exact ⟨hs.1,(column_properties hP.2.1 hj hns hg).1,hs.2⟩

theorem masked_columns_admissible (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n)
    {c : Ideal Eis} (hc : c ∈ columns S P j) : Admissible (j*c) := by
  have hjA := admissible_of_dvd hP hj
  have hcA := columns_admissible S hP hj hS hc
  have hs := (supported_mul_iff j c).mpr ⟨admissible_supported hjA,admissible_supported hcA⟩
  exact ⟨hs.1,squarefree_mul_iff.mpr
    ⟨((mem_columns hP.2.1 hj).mp hc).2.1.symm.isRelPrime,hjA.2.1,hcA.2.1⟩,hs.2⟩

theorem norm_idealRowHom_four_eq_two (I : Ideal Eis) (hI : Admissible I) (u : Eis) :
    ‖idealRowHom u I‖^4 = ‖idealRowHom u I‖^2 := by
  let F : Finset (Ideal Eis) := {I}
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have he : J=I := Finset.mem_singleton.mp hJ
    simpa only [he] using hI
  rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_singleton_self I)]
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he := congrArg norm (finiteSquarefreeRow_self_pair
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF)) (idealSupport F I) u)
  simp only [norm_mul,norm_star,←pow_two] at he
  change ‖idealSexticRow F (pool_positive F hF) (pool_good F hF) I u‖^2 = _ at he
  have hp : ∀ x : ℝ, x^4=(x^2)^2 := by intro x; ring
  rw [hp,he]
  unfold rowCoprimeMask
  split_ifs <;> norm_num

theorem heckeIdealCharacter_apply (η : Ideal Eis →* ℂ) (u : Eis) (I : Ideal Eis) :
    heckeIdealCharacter η u I = η I * idealRowHom u I := rfl

theorem originalFixedPolynomial_eq (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j ∣ P) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) (u : Eis) :
    originalFixedPolynomial S P j η a W Z r z u =
      overlapPrefactor P j η Z r z G * (idealRowHom u j)^2 *
        rowPolynomial (columns S P j) (overlapResidualCoefficient P j η a W Z r z G) u := by
  have he := normalized_polynomial_fixed_overlap S hP hj (heckeIdealCharacter η u) a W hZ r z G
  change originalFixedPolynomial S P j η a W Z r z u = _ at he
  rw [he]
  simp only [heckeIdealCharacter_apply,
    rowPolynomial,overlapPrefactor,overlapResidualCoefficient,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem maskedResidual_eq (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (A : Ideal Eis → ℂ) (u : Eis) :
    (∑ c ∈ columns S P j, A c*idealRowHom u (j*c)) =
      idealRowHom u j * rowPolynomial (columns S P j) A u := by
  simp only [map_mul,rowPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

lemma norm_sq_square_factor (r s : ℂ) (h : ‖r‖^4=‖r‖^2) :
    ‖r^2*s‖^2=‖r*s‖^2 := by
  calc
    _ = ‖r‖^4*‖s‖^2 := by simp only [norm_mul,norm_pow]; ring
    _ = ‖r*s‖^2 := by rw [h,norm_mul,mul_pow]

theorem originalFixedPolynomial_norm_sq (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) (u : Eis) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 =
      ‖overlapPrefactor P j η Z r z G‖^2 *
        ‖∑ c ∈ columns S P j, overlapResidualCoefficient P j η a W Z r z G c *
          idealRowHom u (j*c)‖^2 := by
  rw [originalFixedPolynomial_eq S hP.2.1 hj η a W hZ r z G,
    maskedResidual_eq,mul_assoc,norm_mul,mul_pow]
  congr 1
  exact norm_sq_square_factor _ _ (norm_idealRowHom_four_eq_two j (admissible_of_dvd hP hj) u)

lemma norm_rpow_half_sq {Z : ℝ} (hZ : 0 < Z) (D : ℝ) :
    ‖((Z^(-D/2) : ℝ) : ℂ)‖^2=Z^(-D) := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
    ←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1
  norm_num

theorem original_fixed_overlap_smoothed_summable
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) := by
  have hs := (indexed_smoothed_summable (columns S P j) (fun c => j*c)
    (fun c hc => masked_columns_admissible S hP hj hS hc)
    (overlapResidualCoefficient P j η a W Z r z G) Φ Y hY).mul_left
      ((‖overlapPrefactor P j η Z r z G‖^2 : ℝ) : ℂ)
  apply hs.congr
  intro u
  rw [originalFixedPolynomial_norm_sq S hP hj η a W hZ r z G,Complex.ofReal_mul]
  ring

theorem original_normalized_polynomial_hecke_rows
    (S : Finset (Ideal Eis)) {P : Ideal Eis} (hP : Squarefree P)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal Eis → ℝ) (u : Eis) :
    (Z^(-(r+z)/2) : ℝ) * (∑ n ∈ S,
      (moebius n : ℂ)*heckeIdealCharacter η u n*heckeIdealCharacter η u P*
        a n*W ((Ideal.absNorm n : ℝ)/Z^r)) =
      ∑ j ∈ IdealMobiusDivisorSum.idealDivisors P,
        overlapPrefactor P j η Z r z (G j) * (idealRowHom u j)^2 *
          rowPolynomial (columns S P j)
            (overlapResidualCoefficient P j η a W Z r z (G j)) u := by
  rw [original_normalized_polynomial S hP (heckeIdealCharacter η u) a W hZ r z G]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [heckeIdealCharacter_apply,rowPolynomial,overlapPrefactor,
    overlapResidualCoefficient,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem indexed_conjugate_smoothed_summable {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * star (idealRowHom u (L c))‖^2 : ℝ)) := by
  have he (u : Eis) : (∑ c ∈ C, A c * star (idealRowHom u (L c))) =
      star (∑ c ∈ C, star (A c) * idealRowHom u (L c)) := by
    simp only [star_sum,star_mul,star_star,mul_comm]
  simpa only [he,norm_star] using
    indexed_smoothed_summable C L hL (fun c => star (A c)) Φ Y hY

theorem residual_normalized_smoothed_summable
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) := by
  have hs := (indexed_conjugate_smoothed_summable (columns S P j) (fun c => c)
    (fun c hc => columns_admissible S hP hj hS hc)
    (overlapResidualCoefficient P j η a W Z r z G) Φ Y hY).mul_left
      ((Z^(-(r+z-2*G)) : ℝ) : ℂ)
  apply hs.congr
  intro u
  rw [residualNormalizedPolynomial,norm_mul,mul_pow,norm_rpow_half_sq hZ,Complex.ofReal_mul]
  ring

end SevenEighths.InverseInitialPoissonBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialConjugateEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialConjugateEnergy
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss ConcreteTraceCRT
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialRayAttachment
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem overlapResidualCoefficient_conjugate (P j : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (c : Ideal O) :
    overlapResidualCoefficient P j (conjugateIdealCharacter η)
        (fun I => star (a I)) (fun x => star (W x)) Z r z G c =
      star (overlapResidualCoefficient P j η a W Z r z G c) := by
  simp [overlapResidualCoefficient, star_mul, mul_comm, mul_left_comm, mul_assoc]

theorem star_conjugatedResidual (S : Finset (Ideal O)) (P j : Ideal O)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : O) :
    star (conjugatedResidual S P j η a W Z r z G u) =
      (Z^(-(r+z-2*G)/2) : ℝ) *
        rowPolynomial (columns S P j) (overlapResidualCoefficient P j η a W Z r z G) u := by
  unfold conjugatedResidual residualNormalizedPolynomial
  simp_rw [overlapResidualCoefficient_conjugate]
  simp [rowPolynomial, mul_comm]

theorem originalFixedPolynomial_eq_conjugatedResidual (S : Finset (Ideal O))
    {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (u : O) :
    originalFixedPolynomial S P j η a W Z r z u =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * (Z^(-G) : ℝ) *
        η j^2 * (idealRowHom u j)^2 * star (conjugatedResidual S P j η a W Z r z G u) := by
  rw [originalFixedPolynomial_eq S hP hj η a W hZ r z G,
    star_conjugatedResidual]
  unfold overlapPrefactor
  ring

theorem originalFixedPolynomial_norm_sq_conjugatedResidual (S : Finset (Ideal O))
    {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (u : O) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 =
      Z^(-2*G) * ‖η j‖^4 * ‖idealRowHom u j‖^4 *
        ‖conjugatedResidual S P j η a W Z r z G u‖^2 := by
  rw [originalFixedPolynomial_eq_conjugatedResidual S hP hj η a W hZ r z G]
  have hjn : ‖(moebius j : ℂ)‖=1 := by simp [(hP.squarefree_of_dvd hj).moebius_eq]
  have hpn : ‖(moebius (residual P j) : ℂ)‖=1 := by simp [(residual_squarefree hP hj).moebius_eq]
  have hp : (Z^(-G))^2=Z^(-2*G) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    ring
  simp only [norm_mul,norm_pow,norm_star,hjn,hpn,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ (-G)),mul_pow]
  rw [hp]
  ring

theorem admissible_row_four_le_one (I : Ideal O) (hI : Admissible I) (u : O) :
    ‖idealRowHom u I‖^4 ≤ 1 := by
  have he := norm_idealRowHom_four_eq_two I hI u
  have hs : 0≤‖idealRowHom u I‖^2 := sq_nonneg _
  have ht : ‖idealRowHom u I‖^4=(‖idealRowHom u I‖^2)^2 := by ring
  rw [ht] at he ⊢
  nlinarith

theorem originalFixedPolynomial_norm_sq_le (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z) (r z G : ℝ) (u : O) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 ≤
      Z^(-2*G) * ‖η j‖^4 * ‖conjugatedResidual S P j η a W Z r z G u‖^2 := by
  rw [originalFixedPolynomial_norm_sq_conjugatedResidual S hP.2.1 hj η a W hZ r z G]
  have hm := admissible_row_four_le_one j (admissible_of_dvd hP hj) u
  have hz := (Real.rpow_pos_of_pos hZ (-2*G)).le
  nlinarith [mul_nonneg hz (pow_nonneg (norm_nonneg (η j)) 4),
    mul_nonneg (mul_nonneg hz (pow_nonneg (norm_nonneg (η j)) 4))
      (sq_nonneg ‖conjugatedResidual S P j η a W Z r z G u‖)]

theorem finite_weighted_triangle {α β : Type*} (J : Finset α) (R : Finset β)
    (w : β → ℝ) (hw : ∀ u,0≤w u) (F : α → β → ℂ) :
    (∑ u ∈ R,w u * ‖∑ j ∈ J,F j u‖^2) ≤
      (∑ j ∈ J,Real.sqrt (∑ u ∈ R,w u*‖F j u‖^2))^2 := by
  let v (j : α) : EuclideanSpace ℂ R :=
    WithLp.toLp 2 (fun u => (Real.sqrt (w u) : ℂ)*F j u)
  have hv (j : α) : ‖v j‖^2=∑ u ∈ R,w u*‖F j u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [v,norm_mul,mul_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw _)]
    exact Finset.sum_coe_sort R (fun u => w u*‖F j u‖^2)
  have hsum : ‖∑ j ∈ J,v j‖^2=∑ u ∈ R,w u*‖∑ j ∈ J,F j u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_sum,Finset.sum_apply,v,←Finset.mul_sum,norm_mul,mul_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hw _)]
    exact Finset.sum_coe_sort R (fun u => w u*‖∑ j ∈ J,F j u‖^2)
  have hs := norm_sum_le J v
  have hn (j : α) : ‖v j‖=Real.sqrt (∑ u ∈ R,w u*‖F j u‖^2) := by
    rw [←hv,Real.sqrt_sq (norm_nonneg _)]
  have hh := pow_le_pow_left₀ (norm_nonneg _) hs 2
  simpa only [hsum,hn] using hh

theorem weighted_overlap_triangle {α β : Type*} (J : Finset α)
    (w : β → ℝ) (hw : ∀ u,0≤w u) (F : α → β → ℂ)
    (hs : ∀ j∈J,Summable (fun u => w u*‖F j u‖^2)) :
    Summable (fun u => w u*‖∑ j∈J,F j u‖^2) ∧
      (∑' u,w u*‖∑ j∈J,F j u‖^2) ≤
        (∑ j∈J,Real.sqrt (∑' u,w u*‖F j u‖^2))^2 := by
  have hn (u : β) : 0≤w u*‖∑ j∈J,F j u‖^2 := mul_nonneg (hw u) (sq_nonneg _)
  have hb (R : Finset β) : (∑ u∈R,w u*‖∑ j∈J,F j u‖^2) ≤
      (∑ j∈J,Real.sqrt (∑' u,w u*‖F j u‖^2))^2 := by
    refine (finite_weighted_triangle J R w hw F).trans ?_
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
    apply Finset.sum_le_sum
    intro j hj
    apply Real.sqrt_le_sqrt
    exact (hs j hj).sum_le_tsum R (fun u _ => mul_nonneg (hw u) (sq_nonneg _))
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

theorem radialWeight_nonneg (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) (u : O) : 0≤ radialWeight Φ Y u :=
  hΦ _ (div_nonneg (sq_nonneg _) hY.le)

theorem original_energy_summable (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖originalFixedPolynomial S P j η a W Z r z u‖^2) := by
  have hs := original_fixed_overlap_smoothed_summable S hP hj hS η a W hZ r z G Φ Y hY
  simpa only [radialWeight,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] using (Complex.hasSum_re hs.hasSum).summable

theorem conjugatedResidual_energy_summable (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖conjugatedResidual S P j η a W Z r z G u‖^2) := by
  have hs := residual_normalized_smoothed_summable S hP hj hS (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) hZ r z G Φ Y hY
  simpa only [radialWeight,conjugatedResidual,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using (Complex.hasSum_re hs.hasSum).summable

theorem original_smoothed_contraction (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) :
    smoothedEnergy Φ Y (originalFixedPolynomial S P j η a W Z r z) ≤
      Z^(-2*G)*‖η j‖^4 * smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z G) := by
  unfold smoothedEnergy
  rw [←tsum_mul_left]
  apply (original_energy_summable S hP hj hS η a W hZ r z G Φ hY).tsum_le_tsum _
    ((conjugatedResidual_energy_summable S hP hj hS η a W hZ r z G Φ hY).mul_left _)
  intro u
  have hh := mul_le_mul_of_nonneg_left
    (originalFixedPolynomial_norm_sq_le S hP hj η a W hZ r z G u)
    (radialWeight_nonneg Φ hΦ hY u)
  convert (preTransparency := .instances) hh using 1
  ring

theorem sqrt_overlap_prefactor {Z : ℝ} (hZ : 0<Z) (G : ℝ) (ηj : ℂ) (E : ℝ) :
    Real.sqrt (Z^(-2*G)*‖ηj‖^4*E) = Z^(-G)*‖ηj‖^2*Real.sqrt E := by
  have hz : (Z^(-G))^2=Z^(-2*G) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    ring
  have hp : Z^(-2*G)*‖ηj‖^4=(Z^(-G)*‖ηj‖^2)^2 := by
    rw [mul_pow,hz]
    ring
  rw [hp,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]

theorem originalTotalPolynomial_eq_sectors (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z : ℝ) (G : Ideal O → ℝ) (u : O) :
    originalTotalPolynomial S P η a W Z r z u =
      ∑ j∈idealDivisors P,originalFixedPolynomial S P j η a W Z r z u := by
  unfold originalTotalPolynomial
  rw [original_normalized_polynomial_hecke_rows S hP η a W hZ r z G]
  apply Finset.sum_congr rfl
  intro j hj
  exact (originalFixedPolynomial_eq S hP ((mem_idealDivisors hP.ne_zero).mp hj)
    η a W hZ r z (G j) u).symm

theorem original_smoothed_overlap_triangle (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖originalTotalPolynomial S P η a W Z r z u‖^2) ∧
    Real.sqrt (smoothedEnergy Φ Y (originalTotalPolynomial S P η a W Z r z)) ≤
      ∑ j∈idealDivisors P,Z^(-G j)*‖η j‖^2*
        Real.sqrt (smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z (G j))) := by
  have hjd (j : Ideal O) (hj : j∈idealDivisors P) : j∣P := (mem_idealDivisors hP.1).mp hj
  have hs := weighted_overlap_triangle (idealDivisors P) (radialWeight Φ Y)
    (radialWeight_nonneg Φ hΦ hY) (fun j => originalFixedPolynomial S P j η a W Z r z)
    (fun j hj => original_energy_summable S hP (hjd j hj) hS η a W hZ r z (G j) Φ hY)
  simp_rw [←originalTotalPolynomial_eq_sectors S hP.2.1 η a W hZ r z G] at hs
  refine ⟨hs.1,?_⟩
  have hb := Real.sqrt_le_sqrt hs.2
  rw [Real.sqrt_sq (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))] at hb
  refine hb.trans (Finset.sum_le_sum (fun j hj => ?_))
  have hc := Real.sqrt_le_sqrt (original_smoothed_contraction S hP (hjd j hj) hS
    η a W hZ r z (G j) Φ hΦ hY)
  rwa [sqrt_overlap_prefactor hZ] at hc

end SevenEighths.InverseInitialConjugateEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawGeometry
namespace OAI

noncomputable section
namespace SevenEighths.DetectorDictionaryInverseRawGeometry
open InverseMoment InverseInitialCanonicalState

theorem capacityGap_pos (c : ℝ) (hc : 0<c) : 0<capacityGap c :=
  div_pos hc (by linarith)

theorem raw_log_capacity (H D c : ℝ) (hH : 1<H) (hD : 1≤D) (hc : 0<c)
    (hcap : D^(1+c)≤H) :
    0≤Real.logb H D ∧ Real.logb H D≤1-capacityGap c ∧
    2*Real.logb H D≤3-capacityGap c ∧ H^(Real.logb H D)=D := by
  have hHp : 0<H:=zero_lt_one.trans hH
  have hDp : 0<D:=zero_lt_one.trans_le hD
  have hlogH : 0<Real.log H:=Real.log_pos hH
  have hh:=Real.log_le_log (Real.rpow_pos_of_pos hDp (1+c)) hcap
  rw [Real.log_rpow hDp] at hh
  have hr : Real.logb H D≤1/(1+c) := by
    unfold Real.logb
    apply (le_div_iff₀ (by linarith : 0<1+c)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hlogH).mpr
    simpa only [mul_div_assoc,mul_comm,mul_left_comm,one_mul] using hh
  have he : 1/(1+c)=1-capacityGap c := by
    unfold capacityGap
    field_simp
    ring
  have hg:=(capacityGap_pos c hc).le
  exact ⟨div_nonneg (Real.log_nonneg hD) hlogH.le,hr.trans_eq he,
    by linarith [hr.trans_eq he],Real.rpow_logb hHp (ne_of_gt hH) hDp⟩

end SevenEighths.DetectorDictionaryInverseRawGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialRawDictionary
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeRowClosure
open InverseInitialPoissonBridge InverseInitialConjugateEnergy
open ConcretePrimeRowBridge CompletedGauss UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem finite_source_cover (W : ℝ → ℂ) (D b : ℝ) (hD : 0<D)
    (hW : ∀x,W x≠0 → x≤b) (I : Ideal O) (hI : I≠0)
    (hi : W ((I.absNorm:ℝ)/D)≠0) : I∈idealsUpTo ⌈D*b⌉₊ := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩
  have hb := (div_le_iff₀ hD).mp (hW _ hi)
  have hn : (I.absNorm:ℝ)≤(⌈D*b⌉₊:ℝ) := by
    calc
      (I.absNorm:ℝ)≤D*b := by simpa only [mul_comm] using hb
      _≤(⌈D*b⌉₊:ℝ) := Nat.le_ceil _
  exact_mod_cast hn

theorem normalization_eq (Z r : ℝ) (hZ : 0<Z) :
    ((Z^r:ℝ):ℂ)^(-(1/2:ℂ))=((Z^(-r/2):ℝ):ℂ) := by
  have he : (-(1/2:ℂ))=((-(1/2:ℝ)):ℂ) := by norm_num
  calc
    _ = (((Z^r)^(-(1/2:ℝ)):ℝ):ℂ) := by
      simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,
        Complex.ofReal_ofNat] using (Complex.ofReal_cpow
          (Real.rpow_nonneg hZ.le r) (-(1/2:ℝ))).symm
    _ = _ := ?_
  rw [←Real.rpow_mul hZ.le]
  congr 2
  ring

theorem fixedBase_row (η χ : Character) (m f z : O)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I=fixedBase η m f I*CanonicalRowCompletion.idealRowHom z I := by
  rw [HeckeRowClosure.idealCoeff_eq_row η χ m f z hrow,
    CanonicalRowCompletion.idealRowHom_argument_mul]
  change idealCoeff η I*(CanonicalRowCompletion.idealRowHom (m^6*f^4) I*
    CanonicalRowCompletion.idealRowHom z I)=
    (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*f^4) I)*
    CanonicalRowCompletion.idealRowHom z I
  ring

end SevenEighths.InverseInitialRawDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDetectorSource
namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexConjugate
namespace SevenEighths.InverseInitialDetectorSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open InverseInitialRawDictionary InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

theorem baseCharacter_coeff (data : RowData) (I : Ideal O) :
    idealCoeff (baseCharacter data) I=fixedBase data.η data.m data.f I := by
  rw [HeckeRowClosure.idealCoeff_eq_row data.η (baseCharacter data) data.m data.f 1
    (data.character_spec ⟨1,one_ne_zero⟩),mul_one]
  rfl

end SevenEighths.InverseInitialDetectorSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedSource
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedSource
open InverseInitialOverlap
local notation "O"=>ActualEisensteinCubic.O

theorem quotient_properties {P j n:Ideal O}(hn:Squarefree n)(hg:gcd n P=j):
    Squarefree (idealQuotient j n) ∧ IsCoprime (idealQuotient j n) P ∧
      j*idealQuotient j n=n := by
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  exact ⟨hn.squarefree_of_dvd (idealQuotient_dvd hjn),by
    rw [←hg];exact squarefree_quotient_gcd_coprime n P hn,idealQuotient_mul hjn⟩

theorem reconstruct_properties {P j c:Ideal O}(hP:Squarefree P)(hj:j∣P)
    (hc:Squarefree c)(hcp:IsCoprime c P):
    Squarefree (j*c) ∧ gcd (j*c) P=j := by
  exact ⟨squarefree_mul_iff.mpr ⟨(hcp.mono (dvd_refl _) hj).symm.isRelPrime,
    hP.squarefree_of_dvd hj,hc⟩,gcd_mul_of_coprime_divisor j c P hj hcp⟩

theorem mem_columns {S:Finset (Ideal O)}{P j c:Ideal O}
    (hP:Squarefree P)(hj:j∣P):
    c∈columns S P j ↔ Squarefree c ∧ IsCoprime c P ∧ j*c∈S := by
  constructor
  · intro hc
    obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
    obtain ⟨hnS,hns,hng⟩:=mem_original.mp hn
    obtain ⟨hcs,hcp,he⟩:=quotient_properties hns hng
    exact ⟨hcs,hcp,he.symm ▸ hnS⟩
  · rintro ⟨hcs,hcp,hnS⟩
    obtain ⟨hns,hng⟩:=reconstruct_properties hP hj hcs hcp
    refine Finset.mem_image.mpr ⟨j*c,mem_original.mpr ⟨hnS,hns,hng⟩,?_⟩
    exact quotient_mul_cancel (ne_zero_of_dvd_ne_zero hP.ne_zero hj)

theorem sum_reconstruct (S:Finset (Ideal O)){P j:Ideal O}
    (_hP:Squarefree P)(_hj:j∣P)(f:Ideal O→ℂ):
    (∑n∈original S P j,f n)=∑c∈columns S P j,f (j*c) := by
  rw [columns,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2]
  · intro n hn n' hn' he
    have h1:=(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2
    have h2:=(quotient_properties (mem_original.mp hn').2.1 (mem_original.mp hn').2.2).2.2
    rw [←h1,←h2,he]

theorem cutoff_argument (j c:Ideal O)(X:ℝ):
    ((j*c).absNorm:ℝ)/X=(c.absNorm:ℝ)/(X/(j.absNorm:ℝ)) := by
  rw [map_mul,Nat.cast_mul,div_div_eq_mul_div]
  ring

theorem coefficient_identity (ψ:Ideal O→*ℂ){P j c:Ideal O}
    (hj:j∣P)(hcp:IsCoprime c P):
    (moebius (j*c):ℂ)*ψ (j*c)=(moebius j:ℂ)*ψ j*((moebius c:ℂ)*ψ c) := by
  rw [((hcp.mono (dvd_refl _) hj).symm.isRelPrime).moebius_mul,Int.cast_mul,map_mul]
  ring

theorem polynomial_slice (S:Finset (Ideal O)){P j:Ideal O}
    (hP:Squarefree P)(hj:j∣P)(ψ:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(X:ℝ):
    (∑n∈original S P j,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ((moebius j:ℂ)*ψ j)*∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  rw [sum_reconstruct S hP hj,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [coefficient_identity ψ hj ((mem_columns hP hj).mp hc).2.1,cutoff_argument]
  ring

theorem polynomial_decomposition (S:Finset (Ideal O)){P:Ideal O}(hP:Squarefree P)
    (ψ:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(X:ℝ):
    (∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ∑j∈idealDivisors P,((moebius j:ℂ)*ψ j)*
      ∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have hs:(∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
      ∑n∈S.filter Squarefree,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hs:Squarefree n
    · rw [if_pos hs]
    · simp only [if_neg hs,moebius_of_not_squarefree hs,Int.cast_zero,zero_mul]
  rw [hs,sum_original_partition S hP]
  apply Finset.sum_congr rfl
  intro j hj
  exact polynomial_slice S hP ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W X

end SevenEighths.InverseInitialExcludedSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedPolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge
open InverseInitialExcludedSource IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

theorem prime_product_squarefree (S:Finset (Ideal O))(hS:∀P∈S,Prime P):
    Squarefree (∏P∈S,P) := by
  have hz:(∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)
  apply (squarefree_iff_nodup_normalizedFactors hz).mpr
  have he:normalizedFactors (∏P∈S,P)=S.val:=by
    simpa using normalizedFactors_prod_of_prime (m:=S.val) (fun P hP=>hS P hP)
  rw [he]
  exact S.nodup

theorem deleted_coefficient_product (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(I:Ideal O):
    idealCoeff (χ.excludePrimes S hS) I=
      if IsCoprime I (∏P∈S,P) then idealCoeff χ I else 0 := by
  rw [idealCoeff_excludePrimes,IsCoprime.prod_right_iff]
  congr 1

theorem residual_source (χ:Character)(S A:Finset (Ideal O))(hS:∀P∈S,Prime P)
    {j:Ideal O}(hj:j∣∏P∈S,P)(W:ℝ→ℂ)(X:ℝ)
    (hcover:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A):
    (∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff χ c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))))=
    ∑'c:Ideal O,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have hP:=prime_product_squarefree S hS
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hj
  symm
  calc
    _ = ∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
      apply tsum_eq_sum
      intro c hc
      by_cases hcs:Squarefree c
      · by_cases hcp:IsCoprime c (∏P∈S,P)
        · have hw:W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ)))=0:=by
            by_contra hw
            apply hc
            apply (mem_columns hP hj).mpr
            refine ⟨hcs,hcp,hcover (j*c) (mul_ne_zero hj0 hcs.ne_zero) ?_⟩
            rwa [cutoff_argument]
          rw [hw,mul_zero]
        · rw [deleted_coefficient_product,if_neg hcp,mul_zero,zero_mul]
      · rw [moebius_of_not_squarefree hcs,Int.cast_zero,zero_mul,zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [deleted_coefficient_product,if_pos ((mem_columns hP hj).mp hc).2.1]

theorem source_decomposition (χ:Character)(S A:Finset (Ideal O))(hS:∀P∈S,Prime P)
    (W:ℝ→ℂ)(X:ℝ)(hcover:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A):
    (∑I∈A,(moebius I:ℂ)*idealCoeff χ I*W ((I.absNorm:ℝ)/X))=
    ∑j∈idealDivisors (∏P∈S,P),((moebius j:ℂ)*idealCoeff χ j)*
      ∑'c:Ideal O,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have he:=polynomial_decomposition A (prime_product_squarefree S hS)
    (idealCoeff χ).toMonoidHom (fun _=>1) W X
  simp only [mul_one] at he
  trans ∑j∈idealDivisors (∏P∈S,P),((moebius j:ℂ)*idealCoeff χ j)*
    ∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff χ c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ)))
  · exact he
  apply Finset.sum_congr rfl
  intro j hj
  rw [residual_source χ S A hS ((mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj) W X hcover]

theorem polynomial_all_ideals (χ:Character)(W:ℝ→ℂ)(X σ t:ℝ):
    polynomial χ true W X σ t=(X:ℂ)^(-(1/2:ℂ))*
      ∑'I:Ideal O,(moebius I:ℂ)*idealCoeff χ I*
        (W ((I.absNorm:ℝ)/X)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(-_root_.OAI.SevenEighths.HeckeDyadic.shift σ t)) := by
  unfold polynomial
  congr 1
  let f:Ideal O→ℂ:=fun I=>(moebius I:ℂ)*idealCoeff χ I*
    (W ((I.absNorm:ℝ)/X)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(-_root_.OAI.SevenEighths.HeckeDyadic.shift σ t))
  have hf:Function.support f⊆{I:Ideal O|I≠0}:=by
    intro I hi hz
    subst I
    exact hi (by simp only [f,map_zero,mul_zero,zero_mul])
  have he:=tsum_subtype_eq_of_support_subset hf
  calc
    _=∑'I:{I:Ideal O//I≠0},f I.val:=by
      apply tsum_congr
      intro I
      simp only [summand,coefficient,ite_true,HeckeDyadic.norm,f]
      ring
    _=_:=he

theorem scale_normalization (X n:ℝ)(hX:0<X)(hn:0<n):
    (n:ℂ)^(-(1/2:ℂ))*((X/n:ℝ):ℂ)^(-(1/2:ℂ))=(X:ℂ)^(-(1/2:ℂ)) := by
  rw [←Complex.mul_cpow_ofReal_nonneg hn.le (div_pos hX hn).le,
    ←Complex.ofReal_mul,mul_div_cancel₀ _ hn.ne']

theorem inverse_polynomial_decomposition (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(W:ℝ→ℂ)(X σ t b:ℝ)(hX:0<X)
    (hW:∀x,W x≠0→x≤b):
    polynomial χ true W X σ t=
    ∑j∈idealDivisors (∏P∈S,P),
      ((moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ)))*
        polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t := by
  let A:=ConcretePrimeRowBridge.idealsUpTo ⌈X*b⌉₊
  let V:ℝ→ℂ:=fun x=>W x*(x:ℂ)^(-_root_.OAI.SevenEighths.HeckeDyadic.shift σ t)
  have hc:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A:=
    InverseInitialRawDictionary.finite_source_cover W X b hX hW
  have hcv:∀I:Ideal O,I≠0→V ((I.absNorm:ℝ)/X)≠0→I∈A:=by
    intro I hi hv
    apply hc I hi
    intro hw
    exact hv (by simp [V,hw])
  rw [polynomial_eq_finite χ true W X σ t A hc]
  have hsource:=source_decomposition χ S A hS V X hcv
  have hfinite:(∑I∈A,coefficient χ true I*W ((I.absNorm:ℝ)/X)*
      (((I.absNorm:ℝ)/X:ℝ):ℂ)^(-_root_.OAI.SevenEighths.HeckeDyadic.shift σ t))=
      ∑I∈A,(moebius I:ℂ)*idealCoeff χ I*V ((I.absNorm:ℝ)/X):=by
    apply Finset.sum_congr rfl
    intro I hi
    simp only [coefficient,ite_true,V]
    ring
  rw [hfinite,hsource,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd: j∣∏P∈S,P:=(mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj
  have hj0:j≠0:=ne_zero_of_dvd_ne_zero (prime_product_squarefree S hS).ne_zero hjd
  have hjpos:0<(j.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  rw [polynomial_all_ideals]
  have hn:=scale_normalization X (j.absNorm:ℝ) hX hjpos
  simp only [Complex.ofReal_natCast] at hn
  dsimp only [V]
  rw [←hn]
  ring

end SevenEighths.InverseInitialExcludedPolynomial

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedOverlap
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedOverlap
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open HeckeFamily InverseInitialExcludedPolynomial
local notation "O"=>ActualEisensteinCubic.O

theorem deleted_zero_outside (χ:Character)(E:Finset (Ideal O))
    (hE:∀Q∈E,Prime Q)(I:Ideal O)(hn:¬outside E I):
    idealCoeff (χ.excludePrimes E hE) I=0 := by
  rw [idealCoeff_excludePrimes]
  apply if_neg
  intro hc
  apply hn
  intro Q hQ hd
  have hu:IsUnit Q:=(hc Q hQ).isRelPrime hd (dvd_refl Q)
  exact (hE Q hQ).not_isUnit hu

end SevenEighths.InverseInitialExcludedOverlap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawInitialGates
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialRayAttachment InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap InverseInitialExcludedPolynomial
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge UniqueFactorizationMonoid IdealMobiusDivisorSum
open DetectorDictionaryInverseRawGeometry
local notation "O"=>HeckeFamily.O

theorem actual_row_fixed_base (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff (data.character u) I=idealCoeff (baseCharacter data) I*idealRowHom u.val I:=by
  rw [baseCharacter_coeff]
  exact fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u) I

theorem actual_deleted_row (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) I=
      idealCoeff (deletedBase data) I*idealRowHom u.val I:=by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,idealCoeff_excludePrimes,actual_row_fixed_base]
  split_ifs <;> simp

theorem completeCutoff_tree (H b Btree cap:ℝ):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ):=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem completeCutoff_columns (H b Btree cap D n:ℝ)(hb:0≤b)(hD:0≤D)
    (hDH:D≤H)(hn:1≤n):b*(D/n)≤(completeCutoff H b Btree cap:ℝ):=by
  have hn0:0<n:=zero_lt_one.trans_le hn
  have hdn:D/n≤D:=(div_le_iff₀ hn0).mpr (le_mul_of_one_le_right hD hn)
  exact (mul_le_mul_of_nonneg_left (hdn.trans hDH) hb).trans
    ((le_max_right _ _).trans (Nat.le_ceil _))

theorem excluded_divisor_norm (data:RowData)(j:Ideal O)
    (hj:j∈idealDivisors (∏P∈excluded data,P)):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤((∏P∈excluded data,P).absNorm:ℝ):=by
  have hP:Squarefree (∏P∈excluded data,P):=
    prime_product_squarefree _ (reflectionExcludedPrimes_prime (basePeriod data))
  have hd: j∣∏P∈excluded data,P:=(mem_idealDivisors hP.ne_zero).mp hj
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hd
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)) (map_dvd Ideal.absNorm hd)

theorem deleted_row_complete_polynomial (data:RowData)(u:NonzeroElement)
    (W:ℝ→ℂ)(H r sigma freq b:ℝ)(hH:0<H)
    (hW:∀x,W x≠0→x≤b)(Dpool:ℕ)(hbudget:b*H^r≤(Dpool:ℝ)):
    polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (H^r) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (InitialMeanSquare.outsideSquarefreeIdeals (excluded data) Dpool) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H r 0 u.val:=by
  let χ:=(data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (excluded data) Dpool
  have hs:(∑'I:Ideal O,(moebius I:ℂ)*idealCoeff χ I*
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)))=
      ∑I∈F,(moebius I:ℂ)*idealCoeff χ I*
        (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)):=by
    apply tsum_eq_sum
    intro I hn
    by_cases hsq:Squarefree I
    · by_cases hout:outside (excluded data) I
      · by_cases hw:W ((I.absNorm:ℝ)/H^r)=0
        · simp only [hw,zero_mul,mul_zero]
        · have hN:(I.absNorm:ℝ)≤(Dpool:ℝ):=
            ((div_le_iff₀ (Real.rpow_pos_of_pos hH r)).mp (hW _ hw)).trans hbudget
          have hmem:I∈F:=by
            apply Finset.mem_filter.mpr
            refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,hout⟩,hsq⟩
            · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero)
            · exact_mod_cast hN
          exact False.elim (hn hmem)
      · have hz:=deleted_zero_outside (data.character u) (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data)) I hout
        simp only [χ,hz,mul_zero,zero_mul]
    · simp only [moebius_of_not_squarefree hsq,Int.cast_zero,zero_mul]
  rw [polynomial_all_ideals,hs,normalization_eq H r hH]
  unfold InverseInitialConjugateEnergy.originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [actual_deleted_row]
  simp only [twistedProfile,InverseInitialPoissonBridge.heckeIdealCharacter_apply]
  change (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq)) =
    (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq))
  ring

theorem raw_complete_pool (data:RowData)(H D c b Btree cap:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcap:D^(1+c)≤H)(hb:0≤b)
    (W:ℝ→ℂ)(hW:∀x,W x≠0→x≤b):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ) ∧
    ∀j∈idealDivisors (∏P∈excluded data,P),∀u:NonzeroElement,∀sigma freq:ℝ,
      polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W
        (D/(j.absNorm:ℝ)) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (InitialMeanSquare.outsideSquarefreeIdeals (excluded data)
          (completeCutoff H b Btree cap)) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0 u.val:=by
  refine ⟨completeCutoff_tree _ _ _ _,?_⟩
  intro j hj u sigma freq
  have hn:= (excluded_divisor_norm data j hj).1
  have hH0:0<H:=zero_lt_one.trans hH
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hex:=Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0)
  obtain ⟨_,hr,_,heD⟩:=raw_log_capacity H D c hH hD hc hcap
  have hDH:D≤H:=by
    calc
      D=H^(Real.logb H D):=heD.symm
      _≤H^1:=Real.rpow_le_rpow_of_exponent_le hH.le
        (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _
  have hbudget:b*H^(Real.logb H (D/(j.absNorm:ℝ)))≤
      (completeCutoff H b Btree cap:ℝ):=by
    rw [hex]
    exact completeCutoff_columns H b Btree cap D _ hb hD0.le hDH hn
  simpa only [hex] using deleted_row_complete_polynomial data u W H
    (Real.logb H (D/(j.absNorm:ℝ))) sigma freq b hH0 hW _ hbudget

end SevenEighths.DetectorDictionaryInverseRawInitialGates

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedEnergy
open HeckeFamily HeckeDyadic InverseInitialExcludedPolynomial
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

theorem deletionWeight_norm_le_one (χ:Character){j:Ideal O}(hj:j≠0):
    ‖deletionWeight χ j‖≤1 := by
  have hn:1≤(j.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj)
  have hp:0<(j.absNorm:ℝ):=lt_of_lt_of_le zero_lt_one hn
  have hw:‖(j.absNorm:ℂ)^(-(1/2:ℂ))‖≤1:=by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp]
    apply Real.rpow_le_one_of_one_le_of_nonpos hn
    norm_num
  dsimp [deletionWeight]
  rw [norm_mul,norm_mul]
  calc
    _≤1*1:=mul_le_mul
      (by simpa only [one_mul] using (mul_le_mul (CubicEisenstein.norm_ideal_moebius_le_one j)
        (idealCoeff_norm_le_one χ j) (norm_nonneg _) zero_le_one)) hw
      (norm_nonneg _) (by positivity)
    _=1:=one_mul _

theorem marked_pointwise (χ:Character)(S:Finset (Ideal O))(hS:∀P∈S,Prime P)
    (W:ℝ→ℂ)(X σ t b:ℝ)(hX:0<X)(hW:∀x,W x≠0→x≤b)(mark:ℂ):
    ‖polynomial χ true W X σ t*mark‖^2≤
    ((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖^2 := by
  rw [inverse_polynomial_decomposition χ S hS W X σ t b hX hW,Finset.sum_mul]
  have hn:‖∑j∈idealDivisors (∏P∈S,P),
      ((moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ)))*
        polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖≤
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖:=by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro j hj
    change ‖deletionWeight χ j*polynomial _ _ _ _ _ _*mark‖≤_
    rw [mul_assoc,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply deletionWeight_norm_le_one χ
    exact ne_zero_of_dvd_ne_zero (prime_product_squarefree S hS).ne_zero
      ((mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj)
  have hh:=Finset.sum_mul_sq_le_sq_mul_sq (idealDivisors (∏P∈S,P))
    (fun _=>(1:ℝ)) (fun j=>‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr hn |>.trans
    hh

theorem marked_family {ι:Type*}(rows:Finset ι)(χ:ι→Character)
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(W:ℝ→ℂ)(X σ t b:ℝ)
    (hX:0<X)(hW:∀x,W x≠0→x≤b)(mark:ι→ℂ)(weight:ι→ℝ)
    (hw:∀u∈rows,0≤weight u):
    (∑u∈rows,weight u*‖polynomial (χ u) true W X σ t*mark u‖^2)≤
      ((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),∑u∈rows,weight u*
        ‖polynomial ((χ u).excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark u‖^2 := by
  calc
    _≤∑u∈rows,weight u*(((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial ((χ u).excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark u‖^2):=by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (marked_pointwise (χ u) S hS W X σ t b hX hW (mark u)) (hw u hu)
    _=_:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro u hu
      ring

end SevenEighths.InverseInitialExcludedEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialEnergy
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseRawInitialEnergy
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRawDictionary InverseInitialExcludedPolynomial InverseInitialExcludedEnergy
open DetectorDictionaryInverseRawInitialGates CanonicalQuadraticSieve ConcreteTraceCRT
open ActualEisensteinCubic IdealMobiusDivisorSum CanonicalRowCompletion CanonicalCoefficientClass
local notation "O"=>HeckeFamily.O

private theorem admissible_one : Admissible (1:Ideal O) := by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

theorem deleted_rows_le_initial
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data:RowData)(W:ℝ→ℂ)(H D c b Btree cap sigma freq:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcapacity:D^(1+c)≤H)(hb:0≤b)
    (hW:∀x,W x≠0→x≤b)
    (j:Ideal O)(hj:j∈idealDivisors (∏P∈excluded data,P))
    (rows:Finset NonzeroElement)(hrows:∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H):
    (∑u∈rows,‖polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (D/(j.absNorm:ℝ)) sigma freq‖^2)
      ≤ smoothedEnergy Φ H (initialFunction data W H b Btree cap D sigma freq j) := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (excluded data) (completeCutoff H b Btree cap)
  let f:=initialFunction data W H b Btree cap D sigma freq j
  have hFa:∀I∈F,Admissible I:=InitialMeanSquare.outsideSquarefree_admissible _ _
    (reflectionExcludedPrimes_bad (basePeriod data))
  have hs:Summable (fun u:O=>radialWeight Φ H u*‖f u‖^2):=
    (original_smoothed_overlap_triangle F admissible_one
      (fun I hI _=>admissible_supported (hFa I hI))
      (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) (twistedProfile W sigma freq)
      (zero_lt_one.trans hH) (Real.logb H (D/(j.absNorm:ℝ))) 0 (fun _=>0)
      Φ (fun x _=>hΦ x) (zero_lt_one.trans hH)).1
  have he (u:NonzeroElement)(hu:u∈rows):
      ‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W (D/(j.absNorm:ℝ)) sigma freq‖^2=
        radialWeight Φ H u.val*‖f u.val‖^2:=by
    have hn:‖eisEmbedding u.val‖^2/H∈Set.Icc (0:ℝ) 1:=by
      refine ⟨div_nonneg (sq_nonneg _) (zero_lt_one.trans hH).le,?_⟩
      apply (div_le_one (zero_lt_one.trans hH)).mpr
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    rw [(raw_complete_pool data H D c b Btree cap hH hD hc hcapacity hb W hW).2 j hj u sigma freq]
    change ‖f u.val‖^2=(Φ (‖eisEmbedding u.val‖^2/H)).re*‖f u.val‖^2
    rw [hone _ hn,Complex.one_re,one_mul]
  calc
    _=∑u∈rows,radialWeight Φ H u.val*‖f u.val‖^2:=Finset.sum_congr rfl he
    _=∑u∈rows.image Subtype.val,radialWeight Φ H u*‖f u‖^2:=by
      rw [Finset.sum_image (fun a _ b _ hab=>Subtype.val_injective hab)]
    _≤∑'u:O,radialWeight Φ H u*‖f u‖^2:=hs.sum_le_tsum _
      (fun u _=>mul_nonneg (hΦ _) (sq_nonneg _))
    _=_:=rfl

theorem raw_rows_le_initial_oai
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data:RowData)(W:ℝ→ℂ)(H D c b Btree cap sigma freq:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcapacity:D^(1+c)≤H)(hb:0≤b)
    (hW:∀x,W x≠0→x≤b)
    (rows:Finset NonzeroElement)(hrows:∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H):
    (∑u∈rows,‖polynomial (data.character u) true W D sigma freq‖^2)≤
      ((idealDivisors (∏P∈excluded data,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded data,P),
          smoothedEnergy Φ H (initialFunction data W H b Btree cap D sigma freq j) := by
  have hd:=marked_family rows data.character (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data)) W D sigma freq b
    (zero_lt_one.trans_le hD) hW (fun _=>1) (fun _=>1) (by intros;norm_num)
  simp only [mul_one,one_mul] at hd
  apply hd.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  exact deleted_rows_le_initial Φ hΦ hone data W H D c b Btree cap sigma freq
    hH hD hc hcapacity hb hW j hj rows hrows

end SevenEighths.DetectorDictionaryInverseRawInitialEnergy

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.DetectorDictionaryInverseRawInitialEnergy.raw_rows_le_initial_oai := @OAI.SevenEighths.DetectorDictionaryInverseRawInitialEnergy.raw_rows_le_initial_oai
