-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentDetectorPlainExceptional.retained_positive_energy_le_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:21:45.740962+00:00
-- url     : https://prove2.me/submissions/74b48c05-27a6-44f6-920f-afcd7c234ff6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

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

namespace QuadraticMainBoundary
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open QuadraticSquarefreeKernel

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

end QuadraticMainBoundary

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFamily

attribute [local instance] OAI.SevenEighths.HeckeFamily.instIsPrincipalIdealRingO_solutions
theorem elementCoeff_refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) (n : O) :
    elementCoeff (η.refineModulus M hM hle) n =
      if IsUnit (Ideal.Quotient.mk M n) then elementCoeff η n else 0 :=
  ResidueCharacter.inflate_mk hle η.residue n

end SevenEighths.HeckeFamily

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

theorem annular_ideal_sum_summable (χ : Ideal O → ℂ) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    Summable (fun I : Ideal O => χ I * W ((Ideal.absNorm I : ℝ) / X)) := by
  apply summable_of_hasFiniteSupport
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b * X))).subset
  intro I hI
  have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
    intro hz
    exact hI (by simp only [hz, mul_zero])
  have hn : (Ideal.absNorm I : ℝ) ≤ b * X := (div_le_iff₀ hX).mp (hs hw)
  exact_mod_cast hn.trans (Nat.le_ceil (b * X))

end SevenEighths.CenteredMomentMask
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Extraction
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentExtraction
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist

theorem idealRectangle_extract (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ I J : Ideal O) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J) =
      idealRectangle W₁ W₂
        (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
        (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J := by
  simp only [idealRectangle, map_mul, Nat.cast_mul, div_div_eq_mul_div]
  congr 2 <;> congr 1 <;> ring

end SevenEighths.CenteredMomentExtraction
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeExpansion
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExpansion
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

theorem rowTwistedSum_eq_weight (η : Character) (m A z : O) (t : ℝ) (W : ℝ → ℂ) (X : ℝ) :
    rowTwistedSum η m A z W t X =
      ∑' I : Ideal O, rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) := rfl

theorem rowSlot_eq_weight (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) :
    rowSlot η m A z S β t = ∑ P ∈ S, β P*rowWeight η m A z t P := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro P hP
  simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
  ring

theorem actual_hecke_rectangle_sum
    (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      rowTwistedSum η m A z W₁ t X₁ * rowTwistedSum η m A z W₂ t X₂ -
        rowTwistedSum η m A z W₁ t Y₁ * rowTwistedSum η m A z W₂ t Y₂ := by
  let w := rowWeight η m A z t
  let f₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal O) :
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [map_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal O) : (∑' J : Ideal O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal O, f₂ J) - g₁ I * (∑' J : Ideal O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [rowTwistedSum_eq_weight]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem live_slot_product (η : Character) (m A z : O) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (t : ℝ) :
    (∏ i,rowSlot η m A z (S i) (β i) t) =
      ∑ v : (i : ι) → S i, (∏ i,β i (v i))*rowWeight η m A z t (∏ i,(v i:Ideal O)) := by
  have hs (i : ι) : rowSlot η m A z (S i) (β i) t =
      ∑ P : S i, β i P*rowWeight η m A z t P := by
    rw [rowSlot_eq_weight]
    exact (Finset.sum_coe_sort (S i) (fun P => β i P*rowWeight η m A z t P)).symm
  simp_rw [hs]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_prod,← Finset.prod_mul_distrib]

theorem actual_slot_rectangle_sum (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
       ∏ i,rowSlot η m A z (S i) (β i) t := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        rowWeight η m A z t (∏ i,(v i:Ideal O))*
          (rowWeight η m A z t (I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
    simp only [map_mul]; ring
  simp_rw [ht,tsum_mul_left]
  rw [actual_hecke_rectangle_sum η m A z t W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂,
    live_slot_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end SevenEighths.CenteredMomentHeckeExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRawEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalized_norm_sq (T : ℝ) (hT : 0 < T) (x : ℂ) :
    ‖(Real.sqrt T:ℂ)⁻¹*x‖^2=‖x‖^2/T := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,
    Real.sq_sqrt hT.le]
  ring

end SevenEighths.CenteredMomentDivisorRawEnergy

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentRowNorm HeckeFamily CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_split (η : Character) (m A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I = rowWeight η m A 1 t I*idealRowHom z I := by
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) =
    ((idealCoeff η I*idealRowHom (m^6*(A*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*idealRowHom z I
  rw [mul_one,← mul_assoc,idealRowHom_argument_mul]
  ring

theorem rowWeight_zero_of_not_supported (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) (I : Ideal O) (hI : ¬Supported I) :
    rowWeight η m A z t I=0 := by
  by_cases h0 : I=0
  · rw [h0,map_zero]
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I h0
  have hs : Ideal.span {n}=I := span_idealGenerator I
  have hz := rowTwist_zero_of_not_supported (HeckeRowClosure.elementHom η) m 1 (A*z) n
    hmLam hm2 (hs ▸ hI)
  have he : rowTwist (HeckeRowClosure.elementHom η) m 1 (A*z) n =
      idealCoeff η I*idealRowHom (m^6*(A*z)) I := by
    change elementCoeff η n*idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n})=_
    rw [one_pow,mul_one,hs,← idealCoeff_span η hn,hs]
  rw [he] at hz
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=0
  rw [hz,zero_mul]

end SevenEighths.CenteredMomentSourceRow

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondHeightFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentChildRows CenteredMomentChildAssembly
open CenteredMomentSecondScaled RayFourExpansion ConcretePrimeRowBridge ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem fixedBadMask_coprime (n : O) (hn : Supported (Ideal.span {n})) :
    IsCoprime fixedBadMask n := by
  have hl := PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
    ((supported_span_iff n).mp hn).1
  have h2 := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have htwo : IsCoprime (2:O) n := h2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  exact hl.mul_left htwo

theorem heightCoeff_eq_fixed_rowWeight (τ : Character) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff τ t I=rowWeight τ fixedBadMask 1 1 t I := by
  have hc : IsCoprime (Ideal.span {fixedBadMask}) I := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
  have hs := idealRowHom_sixth_mask fixedBadMask I hI
  rw [if_pos hc.symm] at hs
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff τ I*idealRowHom (fixedBadMask^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))
  simp only [mul_one,hs]

end SevenEighths.CenteredMomentSecondHeightFamily

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
open CenteredMomentPlainEnergy CenteredMomentCauchy CenteredMomentSmooth
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

end SevenEighths.CenteredMomentRestrictedEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceMask
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CompletedGauss UniqueFactorizationMonoid ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma coprime_support_iff (I R : Ideal O) (hR : R≠0) :
    (∀P∈primeSupport R,IsCoprime I P) ↔ IsCoprime I R := by
  constructor
  · intro h
    have aux : ∀s : Multiset (Ideal O),(∀P∈s,IsCoprime I P)→IsCoprime I s.prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _; simpa using (isCoprime_one_right : IsCoprime I 1)
      | @cons a s ih =>
        intro hs
        rw [Multiset.prod_cons]
        exact (hs a (Multiset.mem_cons_self _ _)).mul_right
          (ih (fun P hP=>hs P (Multiset.mem_cons_of_mem hP)))
    rw [←Ideal.prod_normalizedFactors_eq_self hR]
    exact aux _ (fun P hP=>h P (Multiset.mem_toFinset.mpr hP))
  · intro h P hP
    exact h.of_isCoprime_of_dvd_right (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))

lemma excluded_ideal (χ : Character) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I=if IsCoprime I R then idealCoeff χ I else 0 := by
  simp only [excluded,idealCoeff_excludePrimes,coprime_support_iff I R hR]

lemma excluded_element (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      if IsCoprime (Ideal.span {n}) R then elementCoeff χ n else 0 := by
  by_cases hn : n=0
  · subst n
    have hh : elementCoeff (excluded χ R) 0=0 := by
      rw [excluded,Character.excludePrimes,elementCoeff_refineModulus,hχ0]
      split_ifs <;> rfl
    rw [hh,hχ0]
    split_ifs <;> rfl
  · rw [←idealCoeff_span _ hn,excluded_ideal χ R hR,idealCoeff_span χ hn]

lemma excluded_element_generator (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      if IsCoprime n (idealGenerator R) then elementCoeff χ n else 0 := by
  rw [excluded_element χ hχ0 R hR]
  conv_lhs => rw [←span_idealGenerator R,Ideal.isCoprime_span_singleton_iff]

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O

lemma NaturalRow.ideal {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff F.character I=idealCoeff η I*idealRowHom (fixedBadMask^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η F.character fixedBadMask 1 z F.element I

lemma NaturalRow.element_zero {η : Character} {z : O} (F : NaturalRow η z) :
    elementCoeff F.character 0=0 := by
  rw [F.element]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (Ideal.span {(0:O)})=0
  rw [Ideal.span_singleton_zero]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (0:Ideal O)=0
  rw [(idealRowHom (fixedBadMask^6*1^4*z)).map_zero,mul_zero]

lemma NaturalRow.masked_element {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded F.character R) n=
      rowTwist (elementHom η) (fixedBadMask*idealGenerator R) 1 z n := by
  rw [excluded_element_generator F.character F.element_zero R hR,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask (idealGenerator R) 1 z n
      (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

lemma NaturalRow.masked_ideal {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded F.character R) I=
      idealCoeff η I*idealRowHom ((fixedBadMask*idealGenerator R)^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η (excluded F.character R)
    (fixedBadMask*idealGenerator R) 1 z (F.masked_element R hR) I

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RestrictedDomain
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentRowNorm CenteredMomentRestrictedEnergy CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

theorem source_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*CanonicalRowCompletion.idealRowHom z I := by
  unfold rowPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*CanonicalRowCompletion.idealRowHom z I)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2]

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentRestrictedDomain

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRectangle
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangle
open ActualEisensteinCubic HeckeFamily CenteredMomentHeckeExpansion CenteredMomentRectangle
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentExtraction CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentRemainingBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem pack_product (v : ι→Ideal O) (I J : Ideal O) :
    finiteTupleProduct (pack v I J)=(∏ i,v i)*I*J := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,pack_slot,Fin.prod_univ_two,
    pack_left,pack_right,mul_assoc]

theorem sum_tuplePool (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (f : Tuple ι→ℂ) :
    (∑ v∈tuplePool slots S₁ S₂,f v)=
      ∑ v : (∀ i,slots i),∑ I : S₁,∑ J : S₂,f (pack (fun i=>v i) I J) := by
  rw [← Finset.sum_coe_sort (tuplePool slots S₁ S₂) f]
  have he := (tuplePoolEquiv slots S₁ S₂).symm.sum_comp (fun v : tuplePool slots S₁ S₂=>f v)
  change (∑ x : ((∀ i,slots i)×S₁×S₂),f (pack (fun i=>x.1 i) x.2.1 x.2.2))=
    (∑ v : tuplePool slots S₁ S₂,f v) at he
  simpa only [Fintype.sum_prod_type] using he.symm

theorem finite_column_regroup (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (w : Ideal O→ℂ) :
    (∑ I∈finiteColumns S,finiteColumnCoefficient S β I*w I)=
      ∑ v∈S,β v*w (finiteTupleProduct v) := by
  simp only [finiteColumnCoefficient,Finset.sum_mul]
  calc
    _ = ∑ I∈finiteColumns S,∑ v∈S.filter (fun v=>finiteTupleProduct v=I),
        β v*w (finiteTupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

theorem rectangle_zero_left (S₁ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (I J : Ideal O) (hI : I∉S₁) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)=0 := by
  have hx : W₁ ((Ideal.absNorm (B₁*I):ℝ)/X₁)=0 := by
    by_contra hn;exact hI (h I (Or.inl hn))
  have hy : W₁ ((Ideal.absNorm (B₁*I):ℝ)/Y₁)=0 := by
    by_contra hn;exact hI (h I (Or.inr hn))
  simp only [idealRectangle,hx,hy,zero_mul,sub_self]

theorem rectangle_zero_right (S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h : PlainCoverage S₂ W₂ B₂ X₂ Y₂) (I J : Ideal O) (hJ : J∉S₂) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)=0 := by
  have hx : W₂ ((Ideal.absNorm (B₂*J):ℝ)/X₂)=0 := by
    by_contra hn;exact hJ (h J (Or.inl hn))
  have hy : W₂ ((Ideal.absNorm (B₂*J):ℝ)/Y₂)=0 := by
    by_contra hn;exact hJ (h J (Or.inr hn))
  simp only [idealRectangle,hx,hy,mul_zero,sub_self]

theorem finite_plain_rectangle (S₁ S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂)
    (f : Ideal O→Ideal O→ℂ) :
    (∑ I : S₁,∑ J : S₂,f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J))=
      ∑' I : Ideal O,∑' J : Ideal O,f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) := by
  symm
  rw [tsum_eq_sum (s := S₁)]
  · rw [← Finset.sum_coe_sort S₁ (fun I=>∑' J : Ideal O,
      f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J))]
    apply Finset.sum_congr rfl
    intro I hI
    rw [tsum_eq_sum (s := S₂)]
    · exact (Finset.sum_coe_sort S₂ _).symm
    · intro J hJ
      rw [rectangle_zero_right S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₂ I J hJ,mul_zero]
  · intro I hI
    simp only [rectangle_zero_left S₁ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ I _ hI,mul_zero,tsum_zero]

theorem source_polynomial_eq_full_masked_rectangle (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (tuplePool slots S₁ S₂),
      finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      fullMaskedRectangle η m A z t slots ν (fun i I=>Wslot i ((Ideal.absNorm I:ℝ)/P i))
        R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [finite_column_regroup,sum_tuplePool]
  unfold fullMaskedRectangle
  apply Finset.sum_congr rfl
  intro v hv
  rw [← finite_plain_rectangle S₁ S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ h₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [profileCoefficient,pack_product,pack_slot,pack_left,pack_right]
  ring

theorem fullMaskedRectangle_modulus_one [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot 1 L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ =
      CenteredMomentDivisorRowEnergy.maskedRectangle η m A z t slots
        (fun i I=>ν i I*Wslot i I) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) := by
  simp only [fullMaskedRectangle,CenteredMomentDivisorRowEnergy.maskedRectangle,
    isCoprime_one_right,ite_true,one_mul,idealRectangle_extract]
  apply Finset.sum_congr (by ext; simp)
  intro v hv
  rfl

theorem source_polynomial_eq_maskedRectangle [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (tuplePool slots S₁ S₂),
      finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient 1 ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      CenteredMomentDivisorRowEnergy.maskedRectangle η m A z t slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) :=
  (source_polynomial_eq_full_masked_rectangle η m A z t slots S₁ S₂ 1 L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂).trans
    (fullMaskedRectangle_modulus_one η m A z t slots ν _ L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)

end SevenEighths.CenteredMomentSourceRectangle

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceRectangleMask
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSourceRectangle
open CenteredMomentDivisorRowEnergy CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_ideal_mask (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (R I : Ideal O) :
    (if IsCoprime I R then (1:ℂ) else 0)*rowWeight η m A z t I=
      rowWeight η (m*idealGenerator R) A z t I := by
  by_cases hI : Supported I
  · have hm : (m*idealGenerator R)^6*(A*z)=(idealGenerator R)^6*(m^6*(A*z)) := by ring
    change (if IsCoprime I R then (1:ℂ) else 0)*
      ((idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))=
      (idealCoeff η I*idealRowHom ((m*idealGenerator R)^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)
    rw [hm,idealRowHom_argument_mul ((idealGenerator R)^6) (m^6*(A*z)) I,
      idealRowHom_sixth_mask (idealGenerator R) I hI,span_idealGenerator]
    ring
  · rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hI,
      rowWeight_zero_of_not_supported η (m*idealGenerator R) A z t
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) I hI,mul_zero]

theorem fullMaskedRectangle_eq_maskedRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂=
      maskedRectangle η (m*idealGenerator R) A z t slots
        (fun i I=>ν i I*Wslot i I) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) := by
  unfold fullMaskedRectangle maskedRectangle
  apply Finset.sum_congr (by ext;simp)
  intro v hv
  congr 1
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [idealRectangle_extract]
  rw [mul_right_comm (if IsCoprime _ R then (1:ℂ) else 0) _,rowWeight_ideal_mask η m A z t hmLam hm2]
  ring

theorem source_polynomial_eq_maskedRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈CenteredMomentSourceMass.finiteColumns (tuplePool slots S₁ S₂),
      CenteredMomentSourceMass.finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (CenteredMomentSourceProfileMass.profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      maskedRectangle η (m*idealGenerator R) A z t slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) :=
  (source_polynomial_eq_full_masked_rectangle η m A z t slots S₁ S₂ R L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂).trans
    (fullMaskedRectangle_eq_maskedRectangle η m A z t hmLam hm2 slots ν _ R L W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂)

end SevenEighths.CenteredMomentSourceRectangleMask

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangleEnergy
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedDomain CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSourceRectangle
open CenteredMomentSourceRectangleMask CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained
local notation "O" => ActualEisensteinCubic.O

theorem height_source_row (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S=>β I*heightCoeff η t I) z=
      ∑ I∈S,β I*rowWeight η fixedBadMask 1 z t I := by
  rw [source_rowPolynomial S (fun I=>β I*heightCoeff η t I) z]
  calc
    _ = ∑ I∈supportedColumns S,β I*rowWeight η fixedBadMask 1 z t I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp hI).2,
        rowWeight_split η fixedBadMask 1 z t I]
      ring
    _ = _ := Finset.sum_filter_of_ne (fun I hI hn => by
      by_contra hs
      apply hn
      rw [rowWeight_zero_of_not_supported η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hs,mul_zero])

end SevenEighths.CenteredMomentSourceRectangleEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.UncenteredTerminal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentUncenteredTerminal
open HeckeFamily CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

lemma comparisonScale_pos (b : ℝ) : 0<comparisonScale b := by
  have hb : 0< max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  unfold comparisonScale
  positivity

theorem comparison_first_zero (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (B I : Ideal O) (hB : B≠0) :
    W ((Ideal.absNorm (B*I):ℝ)/comparisonScale b)=0 := by
  by_contra h
  have ht := hs h
  by_cases hI : I=0
  · simp only [hI,mul_zero,map_zero,Nat.cast_zero,zero_div,Set.mem_Icc] at ht
    linarith [ht.1]
  have hn : 1≤(Ideal.absNorm (B*I):ℝ) :=
    QuadraticMainBoundary.norm_one_le (mul_ne_zero hB hI)
  have hmax : 1≤ max 1 b := le_max_left _ _
  have hb : b≤ max 1 b := le_max_right _ _
  have harg : (Ideal.absNorm (B*I):ℝ)/comparisonScale b=
      (Ideal.absNorm (B*I):ℝ)*(2*max 1 b) := by
    simp [comparisonScale,div_eq_mul_inv]
  rw [harg] at ht
  have hupper := ht.2
  nlinarith

theorem profileCoefficient_eq_uncentered {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ : ℝ) (ha₁ : 0<a₁)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (X₁ X₂ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (hB₁ : B₁≠0) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ (comparisonScale b₁) Y₂ B₁ B₂ s=
      uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ s := by
  funext v
  simp only [profileCoefficient,idealRectangle,
    comparison_first_zero W₁ a₁ b₁ ha₁ hs₁ B₁ (v (Sum.inr 0)) hB₁,
    zero_mul,sub_zero,uncenteredProfileCoefficient]

end SevenEighths.CenteredMomentUncenteredTerminal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainSource
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentAddedZeroUniform
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleMask
open CenteredMomentUncenteredTerminal CenteredMomentHeckeExpansion
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentDivisorRowEnergy
open CenteredMomentRetainedEnergy CenteredMomentRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma comparison_row_zero (η : Character) (m A z : O) (t : ℝ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) :
    rowTwistedSum η m A z W t (comparisonScale b)=0 := by
  rw [rowTwistedSum_eq_weight]
  calc
    _ = ∑' _I : Ideal O, (0:ℂ) := by
      apply tsum_congr
      intro I
      have h := comparison_first_zero W a b ha hs 1 I one_ne_zero
      simpa only [one_mul,mul_zero] using congrArg (fun v : ℂ=>rowWeight η m A z t I*v) h
    _ = 0 := tsum_zero

theorem complete_source_polynomial (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    (∑ I∈finiteColumns (completePool slots b₁ b₂ X₁ X₂),
      finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
        (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1) I *
          rowWeight η m A z t I)=
      (rowTwistedSum η (m*idealGenerator R) A z W₁ t X₁*
        rowTwistedSum η (m*idealGenerator R) A z W₂ t X₂)*
        ∏ i,rowSlot η (m*idealGenerator R) A z (slots i)
          (fun I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t := by
  let : DecidableEq (ι⊕Fin 2) := Classical.decEq _
  have hs₁' : Function.support W₁⊆Set.Iic b₁ := fun x hx=>(hs₁ hx).2
  have hs₂' : Function.support W₂⊆Set.Iic b₂ := fun x hx=>(hs₂ hx).2
  have hy₁ := comparisonScale_pos b₁
  have hy₂ := div_pos (mul_pos hX₁ hX₂) hy₁
  have hc₁ := plainSupportPool_coverage W₁ b₁ X₁ (comparisonScale b₁)
    (support_zero W₁ a₁ b₁ ha₁ hs₁) hs₁' hX₁ hy₁
  have hc₂ := plainSupportPool_coverage W₂ b₂ X₂ (X₁*X₂/comparisonScale b₁)
    (support_zero W₂ a₂ b₂ ha₂ hs₂) hs₂' hX₂ hy₂
  have he := source_polynomial_eq_maskedRectangle η m A z t hmLam hm2 slots _ _ R 1
    ν Wslot P W₁ W₂ X₁ X₂ (comparisonScale b₁) (X₁*X₂/comparisonScale b₁) 1 1 hc₁ hc₂
  rw [profileCoefficient_eq_uncentered R ν Wslot P W₁ W₂ a₁ b₁ ha₁ hs₁
    X₁ X₂ (X₁*X₂/comparisonScale b₁) 1 1 1 one_ne_zero] at he
  simp only [map_one,Nat.cast_one,div_one] at he
  unfold completePool
  rw [he]
  have hr := actual_slot_rectangle_sum η (m*idealGenerator R) A z slots
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t W₁ W₂ b₁ b₂
    X₁ X₂ (comparisonScale b₁) (X₁*X₂/comparisonScale b₁) hs₁' hs₂' hX₁ hX₂ hy₁ hy₂
  simp only [maskedRectangle,one_dvd,ite_true,one_mul]
  rw [hr,comparison_row_zero η (m*idealGenerator R) A z t W₁ a₁ b₁ ha₁ hs₁,
    zero_mul,sub_zero]

theorem positiveSlotRow_eq_complete_source (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    positiveSlotRow η (m*idealGenerator R) A z W₁ W₂ slots
      (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹*
      ∑ I∈finiteColumns (completePool slots b₁ b₂ X₁ X₂),
        finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
          (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1) I *
            rowWeight η m A z t I := by
  rw [complete_source_polynomial η m A z t hmLam hm2 slots R ν Wslot P W₁ W₂
    a₁ b₁ a₂ b₂ X₁ X₂ ha₁ ha₂ hs₁ hs₂ hX₁ hX₂]
  rfl

end SevenEighths.CenteredMomentDetectorPlainSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentHeckeHeight CenteredMomentPrimeSlot HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ProbeHighRowFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma rowMaskElement_eq_fixed : rowMaskElement=fixedBadMask := by
  unfold rowMaskElement fixedBadMask
  exact mul_comm _ _

lemma excluded_one_ideal (χ : Character) (I : Ideal O) :
    idealCoeff (excluded χ 1) I=idealCoeff χ I := by
  simp only [excluded_ideal χ 1 one_ne_zero,isCoprime_one_right,ite_true]

lemma natural_unit_mask_coefficient {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff η I*CanonicalRowCompletion.idealRowHom ((fixedBadMask*idealGenerator 1)^6*z) I=
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (fixedBadMask^6*z) I := by
  rw [←F.masked_ideal 1 one_ne_zero,excluded_one_ideal,F.ideal]

lemma natural_unit_mask_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator 1) 1 z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂ := by
  simp only [positiveSlotRow,rowTwistedSum,rowSlot,one_mul,natural_unit_mask_coefficient F]

variable {M : Ideal O} [NeZero M]
variable {H : Subgroup (O⧸M)ˣ} (hH : RayOrthogonality.globalUnits M≤H)
variable {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

theorem detector_row_eq_source (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(u:FreeRow)(hU:0<U):
    detectorPositiveRow F η selected j k σ t u=
      (Real.sqrt ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):ℂ)⁻¹*
      ∑I∈finiteColumns (fiberPool F selected),fiberCoefficient F η selected j k σ t I*
        CenteredMomentHeckeExpansion.rowWeight η fixedBadMask 1 u.val 0 I:=by
  have he:=positiveSlotRow_eq_complete_source η fixedBadMask 1 u.val 0
    (dvd_mul_right _ _) (dvd_mul_left _ _)
    (fun s:selected=>primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=>idealCoeff η.inverse) (fun s:selected=>slotWindow F s.val)
    (fun s:selected=>U^(F.widths s.val)) (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
  rw [natural_unit_mask_positive (CenteredMomentNaturalRowSource.naturalRow η u.val u.property.1)] at he
  unfold detectorPositiveRow
  rw [rowMaskElement_eq_fixed]
  exact he

end SevenEighths.CenteredMomentDetectorPlainFiberSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorPlainExceptional
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainExceptional
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

theorem retained_positive_energy_le_source_oai
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0<U)
    (hkeep:∀u∈F.rows,keep u.val):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2)≤
      retainedSourceEnergy keep F η selected j k σ t Φ:=by
  let Q:=finiteColumns (fiberPool F selected)
  let c:=fun I:supportedColumns Q=>fiberCoefficient F η selected j k σ t I*heightCoeff η 0 I
  let rows:Finset O:=F.rows.image Subtype.val
  have ht:0<(U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val):=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos hU _))
  have he (u:FreeRow):
      ‖detectorPositiveRow F η selected j k σ t u‖^2=
      ‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
    rw [detector_row_eq_source F η selected j k σ t u hU,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
    congr 1
    exact congrArg (fun w : ℂ=>‖w‖^2)
      (height_source_row η 0 Q (fiberCoefficient F η selected j k σ t) u.val).symm
  have hb:=finite_energy_le_restricted keep Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
    (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      exact hkeep u hu) (fun z=>hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖eisEmbedding u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=>Subtype.val_injective hxy)]
    _≤_:=div_le_div_of_nonneg_right hb ht.le

variable {Δ:ℝ}{D:Parameters.HighData Δ}

end SevenEighths.CenteredMomentDetectorPlainExceptional

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.CenteredMomentDetectorPlainExceptional.retained_positive_energy_le_source_oai.{u_1, u_2} := @OAI.SevenEighths.CenteredMomentDetectorPlainExceptional.retained_positive_energy_le_source_oai.{u_1, u_2}
