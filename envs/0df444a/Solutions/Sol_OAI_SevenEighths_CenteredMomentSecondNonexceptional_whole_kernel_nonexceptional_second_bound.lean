-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentSecondNonexceptional.whole_kernel_nonexceptional_second_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:50:05.729341+00:00
-- url     : https://prove2.me/submissions/8767e10b-e0b4-4e06-abf5-d391ed30a7b0

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorBounds
namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

section QuotientBounds

variable {R : Type*} [CommRing R]

theorem quotient_inf_card_le_mul (I J : Ideal R) [Finite (R ⧸ I)] [Finite (R ⧸ J)] :
    Nat.card (R ⧸ I ⊓ J) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) := by
  let f : R ⧸ I ⊓ J →+* (R ⧸ I) × (R ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

end QuotientBounds

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]
  [Module.Free ℤ A] [Module.Finite ℤ A]

theorem absNorm_inf_le_mul (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    (I ⊓ J).absNorm ≤ I.absNorm * J.absNorm := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    quotient_inf_card_le_mul I J

end

end SevenEighths.FiniteConductor

end OAI
end

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation
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

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

open FirstPassCubeLabels

lemma weighted_schwartz_integrable (b : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  simpa using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J

end JointLogSeparation

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ResidueCharacter
namespace OAI

namespace SevenEighths.ResidueCharacter

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

theorem finite_quotient_inf (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    Finite (A ⧸ I ⊓ J) := by
  let f : A ⧸ I ⊓ J →+* (A ⧸ I) × (A ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  apply Finite.of_injective f
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
    Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩

end

end SevenEighths.ResidueCharacter

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

theorem exists_primitive_product_associate (M N : Ideal A)
    [Finite (A ⧸ M)] [Finite (A ⧸ N)]
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ⊓ N ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ M.absNorm * N.absNorm ∧
      (∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        if IsCoprime I (M ⊓ N) then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        ofResidue (M ⊓ N) 1 (one_unitInvariant (M ⊓ N)) I * ofResidue K φ hφ I := by
  let : Finite (A ⧸ M ⊓ N) := ResidueCharacter.finite_quotient_inf M N
  obtain ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm, hmask, hdelete⟩ :=
    exists_primitive_associate (M ⊓ N) (ResidueCharacter.product M N χ ψ)
      (ResidueCharacter.product_global_units M N χ ψ hχ hψ)
  refine ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm.trans (absNorm_inf_le_mul M N), ?_, ?_⟩
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hmask I)
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hdelete I)

end Primitive

end Principal

end

end SevenEighths.IdealCharacter

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Operations
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem elementCoeff_inverse (χ : Character) (z : O) :
    elementCoeff χ.inverse z = (elementCoeff χ z)⁻¹ := by
  exact MulChar.inv_apply_eq_inv' _ _

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.IdealOperations
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeFamily

theorem exists_primitive_product_character (χ ψ : Character) :
    ∃ ρ : Character,
      χ.modulus ⊓ ψ.modulus ≤ ρ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ρ.residue ∧
      ρ.modulus.absNorm ≤ χ.modulus.absNorm * ψ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I * idealCoeff ψ I =
        if IsCoprime I (χ.modulus ⊓ ψ.modulus) then idealCoeff ρ I else 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  obtain ⟨M, φ, hφ, hM, hM₀, hprim, hnorm, hmask, _⟩ :=
    IdealCharacter.exists_primitive_product_associate χ.modulus ψ.modulus
      χ.residue ψ.residue χ.unit_trivial ψ.unit_trivial
  exact ⟨Character.ofResidue M hM₀ φ hφ, hM, hprim, hnorm, hmask⟩

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.UnitRows
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeUnitRows
open HeckeFamily CanonicalUnitEuler CanonicalRowCompletion
open ActualEisensteinCubic CubicRamified ConcreteTraceCRT
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
local notation "ω" => HeckeFamily.omega
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem supported_unit_thirty_six (n : O) (hn : Supported (Ideal.span {n})) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(36 : O)}) n) := by
  have hs := (supported_span_iff n).mp hn
  have hneg2 : IsCoprime (-2 : O) n := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using hs.2)
  have h2 : IsCoprime n (2 : O) := (hneg2.of_isCoprime_of_dvd_left ⟨-1, by ring⟩).symm
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n hs.1).symm
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, Ideal.isCoprime_span_singleton_iff]
  convert (preTransparency := .instances) (h2.pow_right : IsCoprime n ((2 : O)^2)).mul_right h9 using 1 ; norm_num

theorem elementCoeff_character (u : Oˣ) (n : O) :
    elementCoeff (character u) n = unitSupplement u n := by
  rw [character, HeckeRowClosure.elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · change 0 = if Supported (Ideal.span {n}) then _ else 0
    rw [if_neg (fun hs => hn (supported_unit_thirty_six n hs))]

end SevenEighths.HeckeUnitRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Mask
namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMask
open ActualEisensteinCubic IdealMobiusDivisorSum
open UniqueFactorizationMonoid

theorem ideal_coprime_mobius (I R : Ideal O) (hR : R ≠ 0) :
    (if IsCoprime I R then (1 : ℂ) else 0) =
      ∑ D ∈ idealDivisors R, if D ∣ I then (moebius D : ℂ) else 0 := by
  let G : Ideal O := R ⊔ I
  have hG : G ≠ 0 := by
    intro hz
    apply hR
    apply le_antisymm _ bot_le
    exact le_sup_left.trans_eq hz
  have hdiv : (idealDivisors R).filter (fun D => D ∣ I) = idealDivisors G := by
    ext D
    simp only [Finset.mem_filter, mem_idealDivisors hR, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G, sup_comm]

end SevenEighths.CenteredMomentMask
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonSupport
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

lemma coprime_mul_dvd_iff (d a n : A) (h : IsCoprime d a) :
    d * a ∣ n ↔ d ∣ n ∧ a ∣ n := by
  constructor
  · intro hn
    exact ⟨(dvd_mul_right d a).trans hn, (dvd_mul_left a d).trans hn⟩
  · rintro ⟨hd, ha⟩
    exact h.mul_dvd hd ha

theorem full_product_congruence (D E a b n : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b) :
    (D * a) * (E * b) ∣ n ↔ D * E ∣ n ∧ a ∣ n ∧ b ∣ n := by
  have heq : (D * a) * (E * b) = (D * E) * (a * b) := by ring
  rw [heq, coprime_mul_dvd_iff _ _ _ (ha.mul_right hb), coprime_mul_dvd_iff _ _ _ hab]

lemma residue_eq_zero_iff_dvd (d n : A) :
    Ideal.Quotient.mk (Ideal.span {d}) n = 0 ↔ d ∣ n := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem full_congruence_split (D E a b x y j : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b) :
    (D * a) * (E * b) ∣ (E * b) * x - (D * a) * y - j ↔
      (D * E ∣ E * (b * x) - D * (a * y) - j) ∧
      Ideal.Quotient.mk (Ideal.span {a}) (E * b * x) = Ideal.Quotient.mk _ j ∧
      Ideal.Quotient.mk (Ideal.span {b}) (D * a * y) = Ideal.Quotient.mk _ (-j) := by
  rw [full_product_congruence D E a b _ ha hb hab]
  have hzeroa : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  have hzerob : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  have heq : (E * b) * x - (D * a) * y - j = E * (b * x) - D * (a * y) - j := by ring
  refine and_congr (by rw [heq]) (and_congr ?_ ?_)
  · rw [← residue_eq_zero_iff_dvd]
    simp only [map_sub, map_mul, hzeroa, mul_zero, zero_mul, sub_zero]
    exact sub_eq_zero
  · rw [← residue_eq_zero_iff_dvd]
    simp only [map_sub, map_mul, hzerob, mul_zero, zero_mul, zero_sub, map_neg]
    constructor <;> intro h <;> linear_combination -h

theorem sum_residual_constraints
    {X Y S T : Type*} [Fintype X] [Fintype Y] [CommRing S] [CommRing T]
    [Fintype S] [Fintype T]
    (p : X → Y → Prop) [∀ x y, Decidable (p x y)]
    (f : X → ℂ) (g : Y → ℂ) (α : S → ℂ) (β : T → ℂ)
    (a : Sˣ) (b : Tˣ) (j : S) (k : T) :
    (∑ x : X × S, ∑ y : Y × T,
      if p x.1 y.1 ∧ (a : S) * x.2 = j ∧ (b : T) * y.2 = k
      then (f x.1 * α x.2) * star (g y.1 * β y.2) else 0) =
    (∑ x : X, ∑ y : Y, if p x y then f x * star (g y) else 0) *
      α ((↑a⁻¹ : S) * j) * star (β ((↑b⁻¹ : T) * k)) := by
  have ha (x : S) : (a : S) * x = j ↔ x = (↑a⁻¹ : S) * j := by
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  have hb (y : T) : (b : T) * y = k ↔ y = (↑b⁻¹ : T) * k := by
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  simp only [Fintype.sum_prod_type, ha, hb]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : p x y
  · simp only [h, true_and, star_mul]
    simp [ite_and, Finset.sum_ite_eq', mul_assoc, mul_left_comm, mul_comm]
  · simp [h]

theorem fullCorrelation_unit_change
    {X Y R : Type*} [CommRing X] [CommRing Y] [CommRing R]
    [Fintype X] [Fintype Y]
    (left : X → R) (right : Y → R) (χ : MulChar X ℂ) (ψ : MulChar Y ℂ)
    (u : Xˣ) (v : Yˣ) (j : R) :
    fullCorrelation (fun x => left ((u : X) * x)) (fun y => right ((v : Y) * y)) χ ψ j =
      χ (↑u⁻¹ : X) * star (ψ (↑v⁻¹ : Y)) * fullCorrelation left right χ ψ j := by
  have hχ (x : X) : χ x = χ (↑u⁻¹ : X) * χ ((u : X) * x) := by
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  have hψ (y : Y) : ψ y = ψ (↑v⁻¹ : Y) * ψ ((v : Y) * y) := by
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  unfold fullCorrelation
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv u.mulLeft
  intro x
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv v.mulLeft
  intro y
  simp only [Units.mulLeft_apply]
  by_cases h : left ((u : X) * x) - right ((v : Y) * y) = j
  · simp only [h, ite_true]
    rw [hχ x, hψ y, star_mul]
    ring
  · simp only [h, ite_false, mul_zero]

lemma character_unit_inverse {X : Type*} [CommRing X] [Fintype X]
    (χ : MulChar X ℂ) (u : Xˣ) : χ (↑u⁻¹ : X) = star (χ (u : X)) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]

theorem scaledCommonCorrelation_eq (D E a b : A)
    (hDb : IsCoprime D b) (hEa : IsCoprime E a)
    [Fintype (Residue D)] [Fintype (Residue E)]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ) (j : A) :
    scaledCommonCorrelation D E a b χD χE j =
      star (χD (Ideal.Quotient.mk _ b)) * χE (Ideal.Quotient.mk _ a) *
        fullModulusCorrelation D E χD χE j := by
  have h := fullCorrelation_unit_change
    (scaledResidue D E (D * E) rfl) (scaledResidue E D (D * E) (mul_comm _ _))
    χD χE (residueUnit D b hDb) (residueUnit E a hEa) (Ideal.Quotient.mk _ j)
  simpa only [residueUnit_coe, character_unit_inverse, star_star,
    scaledCommonCorrelation, fullModulusCorrelation] using h

theorem fullModulusCorrelation_extract (D E a b : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (χDa : MulChar (Residue (D * a)) ℂ) (χEb : MulChar (Residue (E * b)) ℂ)
    (hχDa : ∀ x : A, χDa (Ideal.Quotient.mk _ x) =
      χD (Ideal.Quotient.mk _ x) * χa (Ideal.Quotient.mk _ x))
    (hχEb : ∀ x : A, χEb (Ideal.Quotient.mk _ x) =
      χE (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x)) (j : A) :
    let α := residueUnit a (E * b) (((IsCoprime.mul_left_iff.mp ha).2.symm).mul_right hab)
    let β := residueUnit b (D * a) (((IsCoprime.mul_left_iff.mp hb).1.symm).mul_right hab.symm)
    fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      scaledCommonCorrelation D E a b χD χE j *
        χa ((↑α⁻¹ : Residue a) * Ideal.Quotient.mk _ j) *
        star (χb ((↑β⁻¹ : Residue b) * Ideal.Quotient.mk _ (-j))) := by
  dsimp only
  let e₁ := principalCRT D a (IsCoprime.mul_left_iff.mp ha).1
  let e₂ := principalCRT E b (IsCoprime.mul_left_iff.mp hb).2
  let α := residueUnit a (E * b) (((IsCoprime.mul_left_iff.mp ha).2.symm).mul_right hab)
  let β := residueUnit b (D * a) (((IsCoprime.mul_left_iff.mp hb).1.symm).mul_right hab.symm)
  let p := fun x : Residue D => fun y : Residue E =>
    scaledResidue D E (D * E) rfl (Ideal.Quotient.mk _ b * x) -
      scaledResidue E D (D * E) (mul_comm _ _) (Ideal.Quotient.mk _ a * y) =
        Ideal.Quotient.mk _ j
  have hextract : fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      ∑ x : Residue D × Residue a, ∑ y : Residue E × Residue b,
        if p x.1 y.1 ∧ (α : Residue a) * x.2 = Ideal.Quotient.mk _ j ∧
          (β : Residue b) * y.2 = Ideal.Quotient.mk _ (-j)
        then (χD x.1 * χa x.2) * star (χE y.1 * χb y.2) else 0 := by
    unfold fullModulusCorrelation fullCorrelation
    apply Fintype.sum_equiv e₁.toEquiv
    intro x
    apply Fintype.sum_equiv e₂.toEquiv
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [e₁, e₂, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, principalCRT_mk,
      hχDa, hχEb, p, α, β, residueUnit_coe, ← map_mul]
    rw [scaledResidue_congruence, scaledResidue_congruence,
      full_congruence_split D E a b x y j ha hb hab]
    split_ifs <;> rfl
  rw [hextract, sum_residual_constraints]
  rfl

theorem fullModulusCorrelation_complete_support (D E a b : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (χDa : MulChar (Residue (D * a)) ℂ) (χEb : MulChar (Residue (E * b)) ℂ)
    (hχDa : ∀ x : A, χDa (Ideal.Quotient.mk _ x) =
      χD (Ideal.Quotient.mk _ x) * χa (Ideal.Quotient.mk _ x))
    (hχEb : ∀ x : A, χEb (Ideal.Quotient.mk _ x) =
      χE (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x)) (j : A) :
    fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      fullModulusCorrelation D E χD χE j *
        (χE (Ideal.Quotient.mk _ a) * star (χa (Ideal.Quotient.mk _ E))) *
        (χb (Ideal.Quotient.mk _ D) * star (χD (Ideal.Quotient.mk _ b))) *
        (χb (Ideal.Quotient.mk _ a) * star (χa (Ideal.Quotient.mk _ b))) *
        χa (Ideal.Quotient.mk _ j) * star (χb (Ideal.Quotient.mk _ (-j))) := by
  rw [fullModulusCorrelation_extract D E a b ha hb hab χD χE χa χb χDa χEb hχDa hχEb j]
  rw [scaledCommonCorrelation_eq D E a b (IsCoprime.mul_left_iff.mp hb).1
    (IsCoprime.mul_left_iff.mp ha).2 χD χE j]
  simp only [map_mul, character_unit_inverse, residueUnit_coe, star_mul, star_star]
  ring

end SevenEighths.CenteredMomentCommonSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupportedCorrelation
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentCommonSupport

theorem supportedModulusCharacter_mul (d a : O)
    (hd : Supported (Ideal.span {d})) (ha : Supported (Ideal.span {a})) (x : O) :
    supportedModulusCharacter (d * a) (supported_mul_elements d a hd ha) (Ideal.Quotient.mk _ x) =
      supportedModulusCharacter d hd (Ideal.Quotient.mk _ x) *
        supportedModulusCharacter a ha (Ideal.Quotient.mk _ x) := by
  simp only [supportedModulusCharacter_mk, ← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma sexticReciprocityPhase_symm (a b : O) :
    sexticReciprocityPhase a b = sexticReciprocityPhase b a := by
  exact congrArg (fun z : ℤ => (z : ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

theorem supported_opposite_phase (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcop : IsCoprime a b) [Fintype (Residue a)] :
    idealRowHom a (Ideal.span {b}) * star (idealRowHom b (Ideal.span {a})) =
      sexticReciprocityPhase a b := by
  rw [idealRowHom_primary_reciprocity b a hpb hpa hb ha,
    sexticReciprocityPhase_symm b a, mul_assoc]
  have hunit := isUnit_residue_of_coprime a b hcop
  have hn := (supportedModulusCharacter a ha).apply_ne_zero_iff.mpr hunit
  change idealRowHom b (Ideal.span {a}) ≠ 0 at hn
  have heq : idealRowHom b (Ideal.span {a}) * star (idealRowHom b (Ideal.span {a})) = 1 := by
    change supportedModulusCharacter a ha (Ideal.Quotient.mk _ b) *
      star (supportedModulusCharacter a ha (Ideal.Quotient.mk _ b)) = 1
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
    exact mul_inv_cancel₀ hn
  rw [heq, mul_one]

theorem supported_complete_common_support (D E a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))] (j : O) :
    supportedCorrelation (D * a) (E * b)
      (supported_mul_elements D a hD ha) (supported_mul_elements E b hE hb) j =
      supportedCorrelation D E hD hE j * sexticReciprocityPhase a E *
        star (sexticReciprocityPhase b D) * sexticReciprocityPhase a b *
        idealRowHom j (Ideal.span {a}) * star (idealRowHom (-j) (Ideal.span {b})) := by
  unfold supportedCorrelation
  rw [fullModulusCorrelation_complete_support D E a b hcopA hcopB hab
    (supportedModulusCharacter D hD) (supportedModulusCharacter E hE)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)
    (supportedModulusCharacter (D * a) (supported_mul_elements D a hD ha))
    (supportedModulusCharacter (E * b) (supported_mul_elements E b hE hb))
    (supportedModulusCharacter_mul D a hD ha) (supportedModulusCharacter_mul E b hE hb) j]
  simp only [supportedModulusCharacter_mk]
  rw [supported_opposite_phase a E ha hE hpa hpE (IsCoprime.mul_left_iff.mp hcopA).2.symm,
    supported_opposite_phase D b hD hb hpD hpb (IsCoprime.mul_left_iff.mp hcopB).1,
    supported_opposite_phase a b ha hb hpa hpb hab,
    sexticReciprocityPhase_symm D b, star_sexticReciprocityPhase]

theorem actual_complete_common_support (D E a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (hab : IsCoprime a b)
    (j : O) :
    actualCorrelation (D * a) (E * b)
      (supported_mul_elements D a hD ha) (supported_mul_elements E b hE hb) j =
      completeSupportExtension D E hD hE j a b := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero D hD)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero E hE)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero a ha)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero b hb)
  let := ConcreteTraceCRT.finite_quotient_span
    (mul_ne_zero (supported_element_ne_zero D hD) (supported_element_ne_zero a ha))
  let := ConcreteTraceCRT.finite_quotient_span
    (mul_ne_zero (supported_element_ne_zero E hE) (supported_element_ne_zero b hb))
  let : Fintype (Residue D) := Fintype.ofFinite _
  let : Fintype (Residue E) := Fintype.ofFinite _
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (D * a)) := Fintype.ofFinite _
  let : Fintype (Residue (E * b)) := Fintype.ofFinite _
  exact supported_complete_common_support D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB hab j

end SevenEighths.CenteredMomentSupportedCorrelation
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Smooth
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentSmooth
open FourierBridge EisensteinSchwartzPoisson

theorem whole_kernel_separation (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
        ∫ t : ℝ, separatedKernel V ρ x u v t * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  let U : Fin 4 → ℝ → ℂ := ![V 0, V 1, rootWindow (V 2), rootWindow (V 3)]
  let a : Fin 4 → ℝ := ![1, 1, -1, -1]
  have hU : ∀ i y, U i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i
    · exact hV 0 y hy
    · exact hV 1 y hy
    · apply hV 2 y
      intro hz
      exact hy (by simp [U, rootWindow, hz])
    · apply hV 3 y
      intro hz
      exact hy (by simp [U, rootWindow, hz])
  obtain ⟨C, hC, hs⟩ := paperRadialFourier_log_separation_envelope W U a M hM hU A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  refine ⟨b, ?_, hi, hm, hp⟩
  intro ρ x u v
  have h := hb ![ρ, x, u, v]
  simpa [U, a, wholeKernel, separatedKernel, rowPhase, columnPhase,
    Fin.prod_univ_succ, Fin.sum_univ_succ, sub_eq_add_neg, mul_assoc, add_assoc] using h

lemma separated_integrable (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (ρ x u v : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ => c * separatedKernel V ρ x u v t * b t) := by
  let K : ℝ := ‖c‖ * ‖V 0 ρ‖ * ‖V 1 x‖ * ‖rootWindow (V 2) u‖ * ‖rootWindow (V 3) v‖
  apply (b.integrable.norm.const_mul K).mono'
  · have hρ := logPhase_continuous_left ρ
    have hx := logPhase_continuous_left x
    have hu := logPhase_continuous_left (-u)
    have hv := logPhase_continuous_left (-v)
    exact (by unfold separatedKernel rowPhase columnPhase; fun_prop : Continuous (fun t : ℝ =>
      c * separatedKernel V ρ x u v t * b t)).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [separatedKernel, rowPhase, columnPhase, norm_mul, logPhase_norm, mul_one]
    dsimp only [K]
    ring_nf
    exact le_rfl

theorem finite_pair_separation {α β : Type*}
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
      ∫ t : ℝ, separatedKernel V ρ x u v t * b t)
    (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (ρ x : ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, (c i * star (d j)) * wholeKernel W V R ρ x (u i) (v j)) =
      ∫ t : ℝ, rowPhase V ρ x t *
        (∑ i ∈ S, c i * columnPhase (V 2) (u i) t) *
        (∑ j ∈ T, star (d j) * columnPhase (V 3) (v j) t) * b t := by
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∫ t : ℝ,
        (c i * star (d j)) * separatedKernel V ρ x (u i) (v j) t * b t := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsep, ← integral_const_mul]
      congr 1
      funext t
      ring
    _ = ∫ t : ℝ, ∑ i ∈ S, ∑ j ∈ T,
        (c i * star (d j)) * separatedKernel V ρ x (u i) (v j) t * b t := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum T
        (fun j _ => separated_integrable b V ρ x (u i) (v j) (c i * star (d j))))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ =>
        separated_integrable b V ρ x (u i) (v j) (c i * star (d j)))]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [Finset.sum_mul, Finset.mul_sum, separatedKernel]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem whole_product_pair_separation (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ {α β : Type*} (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
        (u : α → ℝ) (v : β → ℝ) (ρ x : ℝ),
        (∑ i ∈ S, ∑ j ∈ T, (c i * star (d j)) * wholeKernel W V R ρ x (u i) (v j)) =
          ∫ t : ℝ, rowPhase V ρ x t *
            (∑ i ∈ S, c i * columnPhase (V 2) (u i) t) *
            (∑ j ∈ T, star (d j) * columnPhase (V 3) (v j) t) * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨C, hC, hs⟩ := whole_kernel_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  exact ⟨b, fun S T c d u v ρ x => finite_pair_separation W V R b hb S T c d u v ρ x,
    hi, hm, hp⟩

open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentSmooth
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Cauchy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentCauchy
open CenteredMomentSmooth FourierBridge

theorem bounded_row_cauchy {κ : Type*} (rows : Finset κ)
    (w A B : κ → ℂ) (hw : ∀ k ∈ rows, ‖w k‖ ≤ 1) :
    ‖∑ k ∈ rows, w k * A k * B k‖ ≤
      Real.sqrt (∑ k ∈ rows, ‖A k‖ ^ 2) * Real.sqrt (∑ k ∈ rows, ‖B k‖ ^ 2) := by
  calc
    _ ≤ ∑ k ∈ rows, ‖w k * A k * B k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ rows, ‖A k‖ * ‖B k‖ := Finset.sum_le_sum fun k hk => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg _) (hw k hk)) (norm_nonneg _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt rows _ _

lemma paired_columns_integrable {α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (ρ x : ℝ)
    (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (z : ℂ) :
    Integrable (fun t : ℝ => z * (rowPhase V ρ x t *
      leftColumn S c (V 2) u t * rightColumn T d (V 3) v t * b t)) := by
  have hi := integrable_finsetSum S (fun i _ => integrable_finsetSum T
    (fun j _ => separated_integrable b V ρ x (u i) (v j) (z * c i * star (d j))))
  convert (preTransparency := .instances) hi using 1
  funext t
  simp only [leftColumn, rightColumn, Finset.mul_sum, Finset.sum_mul, separatedKernel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem common_density_cauchy {κ α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (rows : Finset κ) (S : Finset α) (T : Finset β)
    (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
    (ρ x : κ → ℝ) (η : κ → ℂ)
    (hη : ∀ k ∈ rows, ‖η k‖ ≤ 1)
    (hV₀ : ∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) (hV₁ : ∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1)
    (E : ℝ) (_hE : 0 ≤ E) (J : ℕ)
    (henergy : ∀ t : ℝ,
      Real.sqrt (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn T (d k) (V 3) v t‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) :
    ‖∑ k ∈ rows, η k * ∫ t : ℝ, rowPhase V (ρ k) (x k) t *
      leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t‖ ≤
      E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
  have hrow (k : κ) (hk : k ∈ rows) (t : ℝ) : ‖η k * rowPhase V (ρ k) (x k) t‖ ≤ 1 := by
    rw [norm_mul, rowPhase, norm_mul, norm_mul, norm_mul, logPhase_norm, logPhase_norm, mul_one, mul_one]
    exact (mul_le_of_le_one_left (by positivity) (hη k hk)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hV₀ k hk)).trans (hV₁ k hk))
  have hpoint (t : ℝ) :
      ‖∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ ≤
        E * ((1 + ‖t‖) ^ J * ‖b t‖) := by
    have hs := bounded_row_cauchy rows (fun k => η k * rowPhase V (ρ k) (x k) t)
      (fun k => leftColumn S (c k) (V 2) u t) (fun k => rightColumn T (d k) (V 3) v t)
      (fun k hk => hrow k hk t)
    have he : (∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)) =
        (∑ k ∈ rows, (η k * rowPhase V (ρ k) (x k) t) *
          leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t) * b t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hs.trans (henergy t)) (norm_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) :=
    JointLogSeparation.weighted_schwartz_integrable b J
  calc
    _ = ‖∫ t : ℝ, ∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ := by
      congr 1
      rw [integral_finsetSum _ (fun k _ =>
        paired_columns_integrable b V (ρ k) (x k) S T (c k) (d k) u v (η k))]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul]
    _ ≤ ∫ t : ℝ, E * ((1 + ‖t‖) ^ J * ‖b t‖) :=
      norm_integral_le_of_norm_le (hi.const_mul E) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

theorem whole_kernel_row_estimate (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {κ α β : Type*} (rows : Finset κ) (S : Finset α) (T : Finset β)
        (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : κ → ℝ) (η : κ → ℂ),
      (∀ k ∈ rows, ‖η k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ, Real.sqrt (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn T (d k) (V 3) v t‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) →
      (1 + R) ^ A * ‖∑ k ∈ rows, η k *
        (∑ i ∈ S, ∑ j ∈ T, (c k i * star (d k j)) *
          wholeKernel W V R (ρ k) (x k) (u i) (v j))‖ ≤ C * E := by
  obtain ⟨C, hC, hs⟩ := whole_product_pair_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR κ α β rows S T c d u v ρ x η hη hV₀ hV₁ E hE he
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  have hid (k : κ) := hb S T (c k) (d k) u v (ρ k) (x k)
  simp_rw [hid]
  have hcs := common_density_cauchy b V rows S T c d u v ρ x η hη hV₀ hV₁ E hE J he
  change (1 + R) ^ A * ‖∑ k ∈ rows, η k * ∫ t : ℝ,
    rowPhase V (ρ k) (x k) t * leftColumn S (c k) (V 2) u t *
      rightColumn T (d k) (V 3) v t * b t‖ ≤ _
  calc
    _ ≤ (1 + R) ^ A * (E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = E * ((1 + R) ^ A * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ ≤ E * C := mul_le_mul_of_nonneg_left hm hE
    _ = _ := mul_comm _ _

end SevenEighths.CenteredMomentCauchy
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FixedRay
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open RayFourExpansion CenteredMomentPrimary HeckeFamily HeckeRowClosure
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem supported_rayMask (a : O) (ha : Supported (Ideal.span {a})) : rayMask a = 1 := by
  rw [rayMask, if_pos (CenteredMomentCommonSupport.isUnit_residue_of_coprime
    4 a (supported_coprime_four a ha))]

theorem phaseTable_mk (D E a b : O) :
    phaseTable D E (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) =
      sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
        sexticReciprocityPhase a b := by
  simp only [phaseTable, QuadraticGaussRay.residueQuotientFour_mk,
    sexticReciprocityPhase, star_intCast]

theorem phaseTable_norm (D E : O) (r s : RayRing) : ‖phaseTable D E r s‖ ≤ 1 := by
  unfold phaseTable QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> norm_num

theorem phaseTable_expansion (D E a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
        sexticReciprocityPhase a b =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable D E) χ ξ * rayCharacter χ a * rayCharacter ξ b := by
  have h := pair_phase_expansion (phaseTable D E) a b
  simpa only [supported_rayMask a ha, supported_rayMask b hb, one_mul,
    phaseTable_mk] using h

theorem phaseTable_mass (D E : O) :
    (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖) ≤ 256 := by
  simpa only [mul_one] using pairCoeff_sum_norm_le (phaseTable D E) 1
    (fun u v => phaseTable_norm D E u v)

theorem completeSupportExtension_separated (D E h a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    completeSupportExtension D E hD hE h a b =
      actualCorrelation D E hD hE h *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          pairCoeff (phaseTable D E) χ ξ *
            (rayCharacter χ a * idealRowHom h (Ideal.span {a})) *
            (rayCharacter ξ b * star (idealRowHom (-h) (Ideal.span {b}))) := by
  rw [completeSupportExtension]
  have he := phaseTable_expansion D E a b ha hb
  calc
    _ = actualCorrelation D E hD hE h *
        (sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
          sexticReciprocityPhase a b) *
        idealRowHom h (Ideal.span {a}) * star (idealRowHom (-h) (Ideal.span {b})) := by ring
    _ = _ := by
      rw [he]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      ring

end SevenEighths.CenteredMomentFixedRay

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.MobiusRegroup
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentMobiusRegroup
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

theorem mobius_on_pool {β : Type*} (T : Finset β) (B : β → Ideal O)
    (hB : ∀ j ∈ T, B j ≠ 0) (j : β) (hj : j ∈ T) (I : Ideal O) :
    (if IsCoprime I (B j) then (1 : ℂ) else 0) =
      ∑ D ∈ divisorPool T B, if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
  rw [ideal_coprime_mobius I (B j) (hB j hj)]
  have hsub : idealDivisors (B j) ⊆ divisorPool T B :=
    fun D hD => Finset.mem_biUnion.mpr ⟨j,hj,hD⟩
  calc
    _ = ∑ D ∈ idealDivisors (B j), if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      simp only [(mem_idealDivisors (hB j hj)).mp hD, and_true]
    _ = _ := Finset.sum_subset hsub (by
      intro D hD hn
      have hnd : ¬ D ∣ B j := fun hd => hn ((mem_idealDivisors (hB j hj)).mpr hd)
      simp only [hnd, and_false, ite_false])

theorem finite_pair_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → Ideal O) (B : β → Ideal O) (hB : ∀ j ∈ T, B j ≠ 0)
    (F : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if IsCoprime (A i) (B j) then F i j else 0) =
      ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T, if D ∣ A i ∧ D ∣ B j then F i j else 0 := by
  have ht (i : α) (j : β) (hj : j ∈ T) :
      (if IsCoprime (A i) (B j) then F i j else 0) =
        ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
          (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
    have hm := congrArg (fun z : ℂ => z * F i j) (mobius_on_pool T B hB j hj (A i))
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_mul, mul_ite, mul_zero] using hm
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact ht i j hj
    _ = _ := by
      simp_rw [Finset.sum_comm (s := T) (t := divisorPool T B)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro D hD
      simp only [Finset.mul_sum]

open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation

theorem finite_correlation_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a i - 1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b j - 1)
    (hcopA : ∀ i, IsCoprime (D * E) (a i)) (hcopB : ∀ j, IsCoprime (D * E) (b j))
    (h : O) (c : α → ℂ) (d : β → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}), (moebius L : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T,
          if L ∣ Ideal.span {a i} ∧ L ∣ Ideal.span {b j} then
            completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K i j
          else 0 := by
  have he (i : α) (j : β) :
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j =
      if IsCoprime (Ideal.span {a i}) (Ideal.span {b j}) then
        completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K i j else 0 := by
    rw [Ideal.isCoprime_span_singleton_iff]
    by_cases hab : IsCoprime (a i) (b j)
    · rw [if_pos hab, if_pos hab, actual_complete_common_support D E (a i) (b j)
        hD hE (ha i) (hb j) hpD hpE (hpa i) (hpb j) (hcopA i) (hcopB j) hab]
    · simp only [if_neg hab, zero_mul]
  simp_rw [he]
  exact finite_pair_mobius S T (fun i => Ideal.span {a i}) (fun j => Ideal.span {b j})
    (fun j _ => (hb j).1) _

end SevenEighths.CenteredMomentMobiusRegroup

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RowNorm
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRowNorm
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

theorem row_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O =>
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) (pairResidue a b ha hb)
  simpa only [pairResidue_mk, scaledRadialTest_apply] using h

theorem rowPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ) (z : O) :
    ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (idealRowHom z (Ideal.span {a i}) * star (idealRowHom z (Ideal.span {a j}))) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [rowPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end SevenEighths.CenteredMomentRowNorm

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ChildAssembly
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentMobiusRegroup CenteredMomentRowNorm RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem rayCharacter_inverse_star (χ : RayCharacter) (a : O) :
    star (rayCharacter (χ⁻¹) a) = rayCharacter χ a := by
  change star ((χ⁻¹) (Ideal.Quotient.mk _ a)) = χ (Ideal.Quotient.mk _ a)
  rw [MulChar.star_apply', inv_inv]

theorem divisor_pair_separation {α β : Type*} (L : Ideal O) (a : α → O) (b : β → O)
    (c : α → ℂ) (d : β → ℂ) (D E h : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (i : α) (j : β) (K : ℂ) :
    (if L ∣ Ideal.span {a i} ∧ L ∣ Ideal.span {b j} then
      completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K else 0) =
      actualCorrelation D E hD hE h *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          pairCoeff (phaseTable D E) χ ξ *
            ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
              star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) * K := by
  by_cases hi : L ∣ Ideal.span {a i}
  · by_cases hj : L ∣ Ideal.span {b j}
    · simp only [hi,hj,and_self,ite_true,divisorCoefficient,star_mul,rayCharacter_inverse_star]
      rw [completeSupportExtension_separated D E h (a i) (b j) hD hE (ha i) (hb j)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    · simp only [hi,hj,and_false,ite_false,divisorCoefficient,ite_true,zero_mul,star_zero,
        mul_zero,Finset.sum_const_zero]
  · simp only [hi,false_and,ite_false,divisorCoefficient,zero_mul,Finset.sum_const_zero,mul_zero]

theorem pair_ray_fubini {α β γ δ : Type*} [Fintype γ] [Fintype δ]
    (S : Finset α) (T : Finset β) (A : γ → δ → ℂ)
    (L : α → γ → ℂ) (R : β → δ → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, ∑ χ : γ, ∑ ξ : δ, A χ ξ * (L i χ * R j ξ) * K i j) =
      ∑ χ : γ, ∑ ξ : δ, A χ ξ * ∑ i ∈ S, ∑ j ∈ T, (L i χ * R j ξ) * K i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := S)]
  simp_rw [Finset.sum_comm (s := S) (t := Finset.univ)]
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem finite_correlation_children {α β : Type*} (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a i - 1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b j - 1)
    (hcopA : ∀ i, IsCoprime (D * E) (a i)) (hcopB : ∀ j, IsCoprime (D * E) (b j))
    (h : O) (c : α → ℂ) (d : β → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) * actualCorrelation D E hD hE h *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
            pairCoeff (phaseTable D E) χ ξ *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
                  star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) * K i j := by
  rw [finite_correlation_mobius S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB h c d K]
  apply Finset.sum_congr rfl
  intro L hL
  simp_rw [divisor_pair_separation L a b c d D E h hD hE ha hb]
  simp_rw [← Finset.mul_sum (s := T), ← Finset.mul_sum (s := S)]
  rw [pair_ray_fubini]
  ring

end SevenEighths.CenteredMomentChildAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalPair
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentExceptionalPair
open HeckeFamily CenteredExceptionalProfile CenteredMomentChildRows CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem fixed_primitive_product (χ ψ τ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hψ : Q ≤ ψ.modulus) (hτ : Q ≤ τ.modulus) :
    ∃ ρ : Character, FiniteFourier.IsPrimitiveOnIdeals ρ.residue ∧
      Q ≤ ρ.modulus ∧ InducedBy (χ.product τ) ρ := by
  obtain ⟨ρ,hmod,hprim,hnorm,hmask⟩ := exists_primitive_product_character ψ τ
  refine ⟨ρ,hprim,(le_inf hψ hτ).trans hmod,?_⟩
  intro I
  by_cases hI : I = 0
  · simp only [hI,idealCoeff_zero,ite_self]
  by_cases hc : IsCoprime I (χ.product τ).modulus
  · have hn := (idealCoeff_ne_zero_iff (χ.product τ) I).mpr ⟨hI,hc⟩
    rw [idealCoeff_product] at hn
    have hχ := (idealCoeff_ne_zero_iff χ I).mp (left_ne_zero_of_mul hn) |>.2
    have he : idealCoeff χ I = idealCoeff ψ I := by rw [h I,if_pos hχ]
    have hnψ : idealCoeff (ψ.product τ) I ≠ 0 := by
      rw [idealCoeff_product,← he]
      exact hn
    have hcψ := (idealCoeff_ne_zero_iff (ψ.product τ) I).mp hnψ |>.2
    change IsCoprime I (ψ.modulus ⊓ τ.modulus) at hcψ
    rw [if_pos hc,idealCoeff_product,he,hmask I,if_pos hcψ]
  · have hz : idealCoeff (χ.product τ) I = 0 := by
      by_contra hn
      exact hc ((idealCoeff_ne_zero_iff (χ.product τ) I).mp hn).2
    rw [hz,if_neg hc]

theorem fixedInducingRow_of_product (η₁ η₂ τ : Character) (Q : Ideal O)
    (m A z₁ z₂ : O) (hτ : Q ≤ τ.modulus)
    (he : ∀ n, rowTwist (HeckeRowClosure.elementHom η₂) m 1 (A*z₂) n =
      rowTwist (HeckeRowClosure.elementHom η₁) m 1 (A*z₁) n * elementCoeff τ n)
    (hx : FixedInducingRow η₁ Q m A z₁) : FixedInducingRow η₂ Q m A z₂ := by
  obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hx
  obtain ⟨ρ,hρ,hQρ,hindρ⟩ := fixed_primitive_product χ ψ τ hind Q hQ hτ
  refine ⟨χ.product τ,ρ,hρ,hindρ,hQρ,?_⟩
  intro n
  rw [elementCoeff_product,hrow n,he n]

theorem childCharacter_ratio (η : Character) (χ ξ : RayCharacter) (n : O) :
    elementCoeff (childCharacter η ξ) n =
      elementCoeff (childCharacter η χ) n * elementCoeff (rayRatio χ ξ) n := by
  simp only [childCharacter,rayRatio,elementCoeff_product,elementCoeff_inverse]
  by_cases hn : IsUnit (Ideal.Quotient.mk (Ideal.span {(12 : O)}) n)
  · have hχ : elementCoeff (primaryRayCharacter χ) n ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr hn
    field_simp
  · have hz (ψ : RayCharacter) : elementCoeff (primaryRayCharacter ψ) n = 0 :=
      MulChar.map_nonunit _ hn
    rw [hz χ,hz ξ]
    ring

theorem reflectionRatio_modulus (χ ξ : RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)}) : Q ≤ (reflectionRatio χ ξ).modulus := by
  change Q ≤ ((Ideal.span {(12 : O)}) ⊓ (Ideal.span {(12 : O)})) ⊓ Ideal.span {(36 : O)}
  refine le_inf (le_inf ?_ ?_) ?_
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨2,by norm_num⟩)

end SevenEighths.CenteredMomentExceptionalPair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalReflection
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentExceptionalReflection
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CenteredMomentChildRows
open CenteredMomentFixedRay CenteredMomentExceptionalPair RayFourExpansion
open CanonicalRowCompletion CanonicalQuadraticSieve CanonicalUnitEuler
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem child_rows_zero_off_support (η : Character) (χ ξ : RayCharacter)
    (m A z n : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : ¬Supported (Ideal.span {n})) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n = 0 ∧
      rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n = 0 := by
  exact ⟨rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
    rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn⟩

theorem child_row_reflection (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) (n : O) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n *
        elementCoeff (reflectionRatio χ ξ) n := by
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 (A*(-z)) n hn,
      rowTwist_extract_sixth_mask _ m 1 (A*z) n hn]
    simp only [one_pow, one_mul]
    change elementCoeff (childCharacter η ξ) n * coprimalityMask m n *
        idealRowHom (A*(-z)) (Ideal.span {n}) =
      (elementCoeff (childCharacter η χ) n * coprimalityMask m n *
        idealRowHom (A*z) (Ideal.span {n})) * elementCoeff (reflectionRatio χ ξ) n
    rw [childCharacter_ratio, reflectionRatio, elementCoeff_product,
      HeckeUnitRows.elementCoeff_character]
    have hu : unitSupplement (-1 : Oˣ) n = idealRowHom (-1) (Ideal.span {n}) := by
      change (if Supported (Ideal.span {n}) then
        idealRowHom ((-1 : Oˣ) : O) (Ideal.span {n}) else 0) = _
      rw [if_pos hn]
      rfl
    rw [hu, show A*(-z) = (-1)*(A*z) by ring, idealRowHom_argument_mul]
    ring
  · obtain ⟨hleft, hright⟩ := child_rows_zero_off_support η χ ξ m A z n hmLam hm2 hn
    rw [hleft, hright, zero_mul]

theorem fixedInducingRow_reflected (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hex : FixedInducingRow (childCharacter η χ) Q m A z) :
    FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  exact fixedInducingRow_of_product (childCharacter η χ) (childCharacter η ξ)
    (reflectionRatio χ ξ) Q m A z (-z) (reflectionRatio_modulus χ ξ Q hQ)
    (child_row_reflection η χ ξ m A z hmLam hm2) hex

theorem fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    FixedInducingRow (childCharacter η χ) Q m A z ↔
      FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  constructor
  · exact fixedInducingRow_reflected η χ ξ Q hQ m A z hmLam hm2
  · intro hex
    simpa only [neg_neg] using
      fixedInducingRow_reflected η ξ χ Q hQ m A (-z) hmLam hm2 hex

theorem not_fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    (¬FixedInducingRow (childCharacter η χ) Q m A z) ↔
      ¬FixedInducingRow (childCharacter η ξ) Q m A (-z) :=
  not_congr (fixedInducingRow_reflection_iff η χ ξ Q hQ m A z hmLam hm2)

end SevenEighths.CenteredMomentExceptionalReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PlainEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentPlainEnergy
open CanonicalQuadraticSieve CenteredMomentRowNorm ConcreteTraceCRT
open CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

theorem rowEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖rowPolynomial S a c z‖^2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖^2/K)) := by
  have hs (i j : α) := (row_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [rowPolynomial_norm_sq,Finset.sum_mul,mul_assoc]
  exact (hasSum_sum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

end SevenEighths.CenteredMomentPlainEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PlainChildEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentPlainChildEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm CenteredMomentPlainEnergy CenteredMomentCauchy
open CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem leftColumn_eq_rowPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    leftColumn S (fun i => c i * idealRowHom z (Ideal.span {a i})) V u t =
      rowPolynomial S a (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn rowPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rightColumn_eq_star_rowPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    rightColumn S (fun i => c i * idealRowHom z (Ideal.span {a i})) V u t =
      star (rowPolynomial S a (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, rowPolynomial, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SevenEighths.CenteredMomentPlainChildEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RestrictedEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRestrictedEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm
open CenteredMomentPlainEnergy CenteredMomentPlainChildEnergy CenteredMomentCauchy CenteredMomentSmooth
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

theorem restricted_summable {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => if keep z then
      ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0) := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c W K hK).hasSum
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  exact hs.summable.indicator {z | keep z}

theorem finite_energy_le_restricted {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep z)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c z‖^2) ≤ restrictedEnergy keep S a c W K := by
  calc
    _ ≤ ∑ z ∈ rows, if keep z then
        ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0 := by
      apply Finset.sum_le_sum
      intro z hz
      rw [if_pos (hkeep z hz)]
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows
      (by intro z hz; split_ifs; exact mul_nonneg (sq_nonneg _) (hW z); exact le_rfl)
      (restricted_summable keep S a ha c W K hK).hasSum

theorem finite_negative_energy_le_restricted {α : Type*} (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep (-z))
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c (-z)‖^2) ≤ restrictedEnergy keep S a c W K := by
  have he := finite_energy_le_restricted keep S a ha c W K hK (rows.image Neg.neg)
    (by intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz; exact hkeep w hw) hW
    (by intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa only [map_neg,norm_neg] using hmajor w hw)
  rwa [Finset.sum_image (fun x hx y hy hxy => neg_injective hxy)] at he

theorem nonexceptional_reflection (η : HeckeFamily.Character)
    (χ ξ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    nonexceptional η χ Q m A₀ z ↔ nonexceptional η ξ Q m A₀ (-z) := by
  unfold nonexceptional
  rw [neg_ne_zero]
  exact and_congr Iff.rfl (CenteredMomentExceptionalReflection.not_fixedInducingRow_reflection_iff
    η χ ξ Q hQ m A₀ z hmLam hm2)

theorem nonexceptional_ray_independent (η : HeckeFamily.Character)
    (χ ξ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    nonexceptional η χ Q m A₀ z ↔ nonexceptional η ξ Q m A₀ z := by
  have h₁ := nonexceptional_reflection η χ ξ Q hQ m A₀ z hmLam hm2
  have h₂ := nonexceptional_reflection η ξ ξ Q hQ m A₀ (-z) hmLam hm2
  simpa only [neg_neg] using h₁.trans h₂

theorem whole_kernel_restricted_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (_ha : ∀ i, Supported (Ideal.span {a i}))
        (_hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ) (keep₁ keep₂ : O → Prop),
      (∀ z ∈ rows, keep₁ z) → (∀ z ∈ rows, keep₂ (-z)) →
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (restrictedEnergy keep₁ S a (fun i => c i * columnPhase (V 2) (u i) t) U K) ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (restrictedEnergy keep₂ T b (fun j => d j * star (columnPhase (V 3) (v j) t)) U K) ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * idealRowHom z (Ideal.span {a i})) * star (d j * idealRowHom (-z) (Ideal.span {b j}))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η keep₁ keep₂ hkeep₁ hkeep₂ hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * idealRowHom z (Ideal.span {a i}))
    (fun z j => d j * idealRowHom (-z) (Ideal.span {b j})) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_restricted keep₁ S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hkeep₁ hU hmajor).trans (hleft t)
  have hR' := (finite_negative_energy_le_restricted keep₂ T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hkeep₂ hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial S a (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial T b (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_rowPolynomial, rightColumn_eq_star_rowPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentRestrictedEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondDescent
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondDescent
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentPlainChildEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

private theorem weighted_norm_sum {α : Type*} (S : Finset α) (a f : α → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (B : α → ℝ)
    (hB : ∀ i ∈ S, r*‖f i‖ ≤ B i) :
    r*‖∑ i ∈ S, a i*f i‖ ≤ ∑ i ∈ S, ‖a i‖*B i := by
  calc
    _ ≤ r*∑ i ∈ S, ‖a i*f i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _ = ∑ i ∈ S, ‖a i‖*(r*‖f i‖) := by simp only [Finset.mul_sum,norm_mul]; congr 1; funext i; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem finite_ray_divisor_bound (L : Finset (Ideal O)) (D E : O)
    (F : Ideal O → RayCharacter → RayCharacter → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (B₁ B₂ : Ideal O → ℝ)
    (hB₁ : ∀ I ∈ L, 0 ≤ B₁ I) (hB₂ : ∀ I ∈ L, 0 ≤ B₂ I)
    (hF : ∀ I ∈ L, ∀ χ ξ, r*‖F I χ ξ‖ ≤ C*(B₁ I*B₂ I)) :
    r*‖∑ I ∈ L, (UniqueFactorizationMonoid.moebius I : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ * F I χ ξ‖ ≤
      (256*C)*∑ I ∈ L, ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖*(B₁ I*B₂ I) := by
  have he (I : Ideal O) (hI : I ∈ L) :
      r*‖∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable D E) χ ξ*F I χ ξ‖ ≤ (256*C)*(B₁ I*B₂ I) := by
    calc
      _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff (phaseTable D E) χ ξ‖*(C*(B₁ I*B₂ I)) := by
        have h := weighted_norm_sum Finset.univ (fun _ : RayCharacter => (1 : ℂ))
          (fun χ => ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ*F I χ ξ) r hr
          (fun χ => ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖*(C*(B₁ I*B₂ I)))
          (fun χ _ => weighted_norm_sum Finset.univ _ _ r hr _ (fun ξ _ => hF I hI χ ξ))
        simpa only [one_mul,norm_one] using h
      _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖)*
          (C*(B₁ I*B₂ I)) := by simp only [Finset.sum_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (phaseTable_mass D E)
          (mul_nonneg hC (mul_nonneg (hB₁ I hI) (hB₂ I hI)))
        convert (preTransparency := .instances) h using 1 ; ring
  have h := weighted_norm_sum L (fun I => (UniqueFactorizationMonoid.moebius I : ℂ))
    (fun I => ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ*F I χ ξ)
    r hr (fun I => (256*C)*(B₁ I*B₂ I)) he
  convert (preTransparency := .instances) h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

end SevenEighths.CenteredMomentSecondDescent

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondScaled
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondScaled
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentPlainChildEnergy RayFourExpansion
open CenteredMomentSecondDescent CenteredMomentProductCRT CenteredMomentUnequal CenteredMomentPartition
local notation "O" => ActualEisensteinCubic.O

theorem divisorCoefficient_moving {α : Type*} (L : Ideal O) (A : O) (a : α → O)
    (c : α → ℂ) (χ : RayCharacter) (i : α) :
    divisorCoefficient L a (movingCoefficient A a c) χ i =
      divisorCoefficient L a c χ i*idealRowHom A (Ideal.span {a i}) := by
  unfold divisorCoefficient movingCoefficient
  split_ifs <;> ring

theorem actual_scaled_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (D E A₀ : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda^2 ∣ D-1)
    (hpE : ConcretePrimeRowBridge.goodLambda^2 ∣ E-1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1)
    (hcopA : ∀ i, IsCoprime (D*E) (a i)) (hcopB : ∀ j, IsCoprime (D*E) (b j))
    (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (K : O → α → β → ℂ) :
    (∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
        else 0) * (c i*star (d j))*K z i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ *
            ∑ z ∈ rows, (q z*actualCorrelation D E hD hE (A₀*z)) *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i})) *
                  star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j}))) * K z i j := by
  simp_rw [finite_correlation_children S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -(A₀*z)=A₀*(-z) by ring]
  simp only [idealRowHom_argument_mul,divisorCoefficient_moving,star_mul]
  ring

end SevenEighths.CenteredMomentSecondScaled

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondNonexceptional
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptional
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth RayFourExpansion
open CenteredMomentSecondDescent CenteredMomentSecondScaled CenteredMomentRestrictedEnergy
local notation "O" => ActualEisensteinCubic.O

theorem whole_kernel_nonexceptional_second_bound_oai (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E A₀ : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2 ∣ D-1) →
      (ConcretePrimeRowBridge.goodLambda^2 ∣ E-1) →
      (∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) →
      (∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η₀ : HeckeFamily.Character) (χ₀ : RayCharacter)
        (Q : Ideal O) (m : O),
      (Q ≤ Ideal.span {(72:O)}) → (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ z ∈ rows, nonexceptional η₀ χ₀ Q m A₀ z) →
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE (A₀*z)‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (nonexceptional η₀ χ Q m A₀) S a (fun i => divisorCoefficient L a (movingCoefficient A₀ a c) χ i*columnPhase (V 2) (u i) t) U K) ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (nonexceptional η₀ ξ Q m A₀) T b (fun j => divisorCoefficient L b (movingCoefficient A₀ b d) ξ j*star (columnPhase (V 3) (v j) t)) U K) ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_restricted_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x η₀ χ₀ Q m hQ hmLam hm2 hrows hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (movingCoefficient A₀ a c) χ) (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE (A₀*z))
    (nonexceptional η₀ χ Q m A₀) (nonexceptional η₀ (ξ⁻¹) Q m A₀)
    (fun z hz => (nonexceptional_ray_independent η₀ χ₀ χ Q hQ m A₀ z hmLam hm2).mp (hrows z hz))
    (fun z hz => (nonexceptional_reflection η₀ χ₀ (ξ⁻¹) Q hQ m A₀ z hmLam hm2).mp (hrows z hz)) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentSecondNonexceptional

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.CenteredMomentSecondNonexceptional.whole_kernel_nonexceptional_second_bound_oai.{u_1, u_2} := @OAI.SevenEighths.CenteredMomentSecondNonexceptional.whole_kernel_nonexceptional_second_bound_oai.{u_1, u_2}
