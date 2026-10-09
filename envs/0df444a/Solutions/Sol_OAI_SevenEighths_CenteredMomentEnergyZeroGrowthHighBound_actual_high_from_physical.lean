-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyZeroGrowthHighBound.actual_high_from_physical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:27:55.722699+00:00
-- url     : https://prove2.me/submissions/3603cccb-4fa0-49d5-9e2e-469ff39959df

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroReferenceLiveBounded_balanced_reference_live
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroUnbalancedOriginal_original_unbalanced_from_zero_low
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstSourceReduction_original_first_physical_reduction

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

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Twist
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTwist
open ActualEisensteinCubic EisensteinSchwartzPoisson
open CenteredMomentLattice

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

end SevenEighths.CenteredMomentTwist
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

theorem finite_hecke_sum_eq_rowPolynomial (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    (∑ I∈S,c I*rowWeight η m A z t I) =
      rowPolynomial Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) z := by
  have he : (∑ I∈S,c I*rowWeight η m A z t I) =
      ∑ I∈supportedColumns S,c I*rowWeight η m A z t I := by
    symm
    apply Finset.sum_filter_of_ne
    intro I hI hn
    by_contra hs
    exact hn (by rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hs,mul_zero])
  rw [he,← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*rowWeight η m A z t I)]
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,rowWeight_split]
  ring

theorem finiteHeckeEnergy_eq (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy η m A t S c W K =
      rowEnergy Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) W K := by
  unfold finiteHeckeEnergy rowEnergy
  simp_rw [finite_hecke_sum_eq_rowPolynomial η m A _ t hmLam hm2 S c]

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstTailAggregate
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) (hI : I≠0) : ‖rowWeight η m A z t I‖≤1 := by
  have hp := norm_real_imaginary_power (Ideal.absNorm I:ℝ) t (norm_pos I hI)
  norm_cast at hp
  change ‖(idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)‖≤1
  rw [norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η I)).trans (idealRowHom_norm _ _)

end SevenEighths.CenteredMomentFirstTailAggregate

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAbsoluteEnergy
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one_all (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) : ‖rowWeight η m A z t I‖ ≤ 1 := by
  by_cases hI : I=0
  · subst I
    rw [map_zero,norm_zero]
    norm_num
  · exact CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A z t I hI

theorem radial_norm_summable (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖Φ (‖eisEmbedding z‖^2/K)‖) := by
  simpa only [scaledRadialTest_apply] using
    actual_eisenstein_summable_norm (scaledRadialTest Φ K hK)

theorem finite_hecke_polynomial_norm (η : Character) (m A z : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    ‖∑ I∈S,c I*rowWeight η m A z t I‖ ≤ ∑ I∈S,‖c I‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)

theorem finite_hecke_energy_summable (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun z : O => (∑ I∈S,‖c I‖)^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
      (norm_nonneg _)
  · exact (radial_norm_summable Φ K hK).mul_left _

end SevenEighths.CenteredMomentAbsoluteEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PositiveSummability
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentPositiveSummability
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceMass
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile CenteredMomentDivisorRetained
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction CenteredMomentDivisorAllocation
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O

lemma plain_finite_norm (η:Character) (m A z:O) (t:ℝ) (W:ℝ→ℂ) (b X:ℝ)
    (hs:Function.support W⊆Set.Iic b) (hX:0<X) :
    ‖rowTwistedSum η m A z W t X‖≤∑I∈idealBall (b*X),‖W ((Ideal.absNorm I:ℝ)/X)‖ := by
  rw [rowTwistedSum_eq_weight,tsum_eq_sum (s:=idealBall (b*X)) ?_]
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)
  · intro I hI
    by_cases h0:I=0
    · subst I
      simp only [map_zero,zero_mul]
    · have hw:W ((Ideal.absNorm I:ℝ)/X)=0 := by
        by_contra hn
        have hh:=hs hn
        have hbound:(Ideal.absNorm I:ℝ)≤b*X:=(div_le_iff₀ hX).mp hh
        exact hI ((mem_idealBall _ _).mpr ⟨h0,hbound⟩)
      rw [hw,mul_zero]

lemma slot_finite_norm (η:Character) (m A z:O) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) :
    ‖rowSlot η m A z S β t‖≤∑I∈S,‖β I‖ := by
  rw [rowSlot_eq_weight]
  exact finite_hecke_polynomial_norm η m A z t S β

lemma bounded_radial_summable (F:O→ℂ) (B:ℝ) (hF:∀z,‖F z‖≤B)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (f:=fun z:O=>B^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    split_ifs
    · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hF z) 2)
        (Complex.abs_re_le_norm _) (abs_nonneg _) (sq_nonneg _)
    · simp only [norm_zero]
      positivity
  · exact (radial_norm_summable Φ K hK).mul_left _

lemma product_bounded {ι:Type*} [Fintype ι]
    (η:Character) (m A:O) (t:ℝ) (c:ℂ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) :
    ∃B:ℝ,∀z:O,‖c*((rowTwistedSum η m A z W₁ t X₁*
      rowTwistedSum η m A z W₂ t X₂)*∏i,rowSlot η m A z (S i) (β i) t)‖≤B := by
  refine ⟨‖c‖*((∑I∈idealBall (b₁*X₁),‖W₁ ((Ideal.absNorm I:ℝ)/X₁)‖)*
    (∑I∈idealBall (b₂*X₂),‖W₂ ((Ideal.absNorm I:ℝ)/X₂)‖)*
    ∏i,∑I∈S i,‖β i I‖),?_⟩
  intro z
  rw [norm_mul,norm_mul,norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul
  · exact mul_le_mul (plain_finite_norm η m A z t W₁ b₁ X₁ hs₁ hX₁)
      (plain_finite_norm η m A z t W₂ b₂ X₂ hs₂ hX₂) (norm_nonneg _) (by positivity)
  · exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>slot_finite_norm η m A z t (S i) (β i))
  · positivity
  · positivity

end SevenEighths.CenteredMomentPositiveSummability

end

end OAI
end

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Sobolev
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace trunc

theorem nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

end trunc
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}

end SevenEighths.CenteredMomentFiniteProfileExceptional

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBandMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

lemma profile_control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(hst:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyBandMonotonicity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSourceInputTailUniform.instDecidableEqSumFinOfNatNat_solutions
omit [DecidableEq ι] in
lemma plainControl_nonneg (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)):0≤plainControl s W₁ W₂:=by
  unfold plainControl
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _=>(s.M_ge_one i).trans' zero_le_one))
    (apply_nonneg _ _)) (apply_nonneg _ _)

end SevenEighths.CenteredMomentSourceInputTailUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.OriginalSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleMask
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentHeckeHeight
open CenteredMomentDivisorRowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentPositiveSummability CenteredMomentPlainEnergy CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyOriginalSource.energyOriginalSourceDecidableSum
omit [DecidableEq ι] in
lemma input_tuplePool (s : Input ι) :
    Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
  ext v
  simp only [Fintype.mem_piFinset,tuplePool,tuplePools,Input.pools]

lemma input_polynomial_difference (s : Input ι) (R : Ideal O) (z : O) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I)=
    (rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.X₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.X₂-
     rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.Y₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.Y₂)*
        ∏i,rowSlot s.η (fixedBadMask*idealGenerator R) 1 z (s.slots i)
          (s.toData.coefficient i) s.t := by
  unfold coefficient
  rw [input_tuplePool]
  rw [source_polynomial_eq_maskedRectangle s.η fixedBadMask 1 z s.t
    (dvd_mul_right _ _) (dvd_mul_left _ _) s.slots s.plain₁ s.plain₂ R 1
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 s.coverage₁ s.coverage₂]
  simp only [map_one,Nat.cast_one,div_one,maskedRectangle,one_dvd,ite_true,one_mul]
  exact actual_slot_rectangle_sum s.η (fixedBadMask*idealGenerator R) 1 z s.slots
    s.toData.coefficient s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos

lemma normalized_input_difference (s : Input ι) (R : Ideal O) (z : O) :
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.X₁ s.X₂-
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂=
    (Real.sqrt (CenteredMomentAmplificationChildInput.volume s):ℂ)⁻¹*
      ∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I := by
  rw [input_polynomial_difference]
  unfold positiveSlotRow CenteredMomentAmplificationChildInput.volume
  rw [s.same_product]
  ring

omit [DecidableEq ι] in
lemma input_energy_hasSum (s : Input ι) (R : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O=>
      ‖∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I‖^2*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy s.η fixedBadMask 1 s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R 1) Φ K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable Finset.univ
    (sourceGenerator (finiteColumns (Fintype.piFinset s.pools))) (sourceGenerator_supported _)
    (fun I=>coefficient s R 1 I*rowWeight s.η fixedBadMask 1 1 s.t I) Φ K hK).hasSum
  change HasSum _ (rowEnergy _ _ _ Φ K).re at hs
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  simpa only [finiteHeckeEnergy_eq s.η fixedBadMask 1 s.t (dvd_mul_right _ _) (dvd_mul_left _ _),
    finite_hecke_sum_eq_rowPolynomial s.η fixedBadMask 1 _ s.t (dvd_mul_right _ _) (dvd_mul_left _ _)] using hs

omit [DecidableEq ι] in
lemma input_positive_summable (s : Input ι) (R : Ideal O) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K X₁ X₂ : ℝ) (hK : 0<K) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    Summable (fun z : O=>if keep z then
      ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t X₁ X₂‖^2*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB⟩ := product_bounded s.η (fixedBadMask*idealGenerator R) 1 s.t
    (Real.sqrt (X₁*X₂*∏i,s.P i):ℂ)⁻¹ s.W₁ s.W₂ s.b₁ s.b₂ X₁ X₂
    s.support₁ s.support₂ hX₁ hX₂ s.slots s.toData.coefficient
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem positive_energy_comparison (s : Input ι) (R : Ideal O)
    (r : CenteredMomentRadialEligibleEnergy.Radial) :
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
      s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
    2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R 1) r.profile r.scale‖ / CenteredMomentAmplificationChildInput.volume s+
    2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
      s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale := by
  let V := CenteredMomentAmplificationChildInput.volume s
  have hV : 0<V := CenteredMomentAmplificationChildInput.volume_pos s
  let f : O→ℝ := fun z=>
    (‖∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I‖^2*
      (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re)/V
  let g : O→ℝ := fun z=>if r.keep z then
    ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂‖^2*
      (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0
  have hf := (input_energy_hasSum s R r.profile r.scale r.scale_pos).div_const V
  have hg := input_positive_summable s R r.keep r.profile r.scale s.Y₁ s.Y₂
    r.scale_pos s.Y₁_pos s.Y₂_pos
  have hfn (z : O) : 0≤f z := div_nonneg (mul_nonneg (sq_nonneg _) (r.nonneg z)) hV.le
  have hgn (z : O) : 0≤g z := by
    dsimp only [g]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (r.nonneg z)
    · rfl
  unfold CenteredMomentInductionEnergy.energy
  apply Real.tsum_le_of_sum_le (fun z=>by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (r.nonneg z)
    · rfl)
  intro rows
  have hp (z : O) :
      (if r.keep z then
        ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.X₁ s.X₂‖^2*
          (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0) ≤ 2*f z+2*g z := by
    by_cases hk : r.keep z
    · let x := positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t s.X₁ s.X₂
      let y := positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t s.Y₁ s.Y₂
      have hn : ‖x‖≤‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
      have hsq : ‖x‖^2≤2*‖x-y‖^2+2*‖y‖^2 := by
        have hh := pow_le_pow_left₀ (norm_nonneg x) hn 2
        nlinarith [sq_nonneg (‖x-y‖-‖y‖)]
      dsimp only [x,y] at hsq
      rw [normalized_input_difference,CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hV] at hsq
      have hh := mul_le_mul_of_nonneg_right hsq (r.nonneg z)
      dsimp only [f,g]
      rw [if_pos hk,if_pos hk]
      convert (preTransparency := .instances) hh using 1 ; ring
    · rw [if_neg hk]
      exact add_nonneg (mul_nonneg (by norm_num) (hfn z)) (mul_nonneg (by norm_num) (hgn z))
  have hb := Finset.sum_le_sum (fun z (_:z∈rows)=>hp z)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at hb
  have hs := sum_le_hasSum rows (fun z _=>hfn z) hf
  have ht := sum_le_hasSum rows (fun z _=>hgn z) hg.hasSum
  have he := div_le_div_of_nonneg_right
    (Complex.re_le_norm (finiteHeckeEnergy s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale)) hV.le
  change ∑z∈rows,f z≤_ at hs
  change ∑z∈rows,g z≤∑'z,g z at ht
  change _≤2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale‖/V+2*∑'z,g z
  rw [mul_div_assoc]
  linarith

end SevenEighths.CenteredMomentEnergyOriginalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FixedRadialSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyFixedRadialSource
open HeckeFamily CenteredMomentSourceRow CenteredMomentAbsoluteEnergy CenteredMomentHeckeExpansion
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

lemma norm_le_diagonalControl (Φ:𝓢(ℝ,ℂ))(x:ℝ):‖Φ x‖≤diagonalControl Φ:=by
  have hs:SchwartzMap.seminorm ℝ 0 0 Φ≤
      (Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ:=by
    exact Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ)
      (by simp : (0,0)∈Finset.Iic (2,0))) Φ
  apply (SchwartzMap.norm_le_seminorm ℝ Φ x).trans
  apply hs.trans
  unfold diagonalControl
  exact le_mul_of_one_le_left (by positivity) (by nlinarith [Real.pi_nonneg])

theorem exists_fixed_bump (b:ℝ)(_hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ (∀x,(Ψ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) b,Ψ x=1):=by
  have hsub:Set.Icc (0:ℝ) b⊆Set.Ioo (-1) (b+1):=by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v:ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv:ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf:ContDiff ℝ ∞ f).pow 2)
  have hsupp:Function.support v⊆Set.Icc (-1) (b+1):=by
    intro x hx
    have hn:x∈Function.support f:=by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  let Ψ:𝓢(ℝ,ℂ):=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp).toSchwartzMap hv
  refine ⟨Ψ,hsupp,?_,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

theorem finite_energy_domination (b:ℝ)(Ψ:𝓢(ℝ,ℂ))
    (hΨ:∀x,0≤(Ψ x).re)(hone:∀x∈Set.Icc (0:ℝ) b,Ψ x=1)
    (Φ:𝓢(ℝ,ℂ))(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic b)
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (K:ℝ)(hK:0<K):
    ‖finiteHeckeEnergy η m A t S c Φ K‖≤
      diagonalControl Φ*‖finiteHeckeEnergy η m A t S c Ψ K‖:=by
  have hΦ:∀x:ℝ,0≤x→‖Φ x‖≤diagonalControl Φ*(Ψ x).re:=by
    intro x hx
    by_cases h:Φ x=0
    · rw [h,norm_zero]
      exact mul_nonneg (diagonalControl_nonneg Φ) (hΨ x)
    · rw [hone x ⟨hx,hs h⟩,Complex.one_re,mul_one]
      exact norm_le_diagonalControl Φ x
  have hsumΦ:=finite_hecke_energy_summable η m A t S c Φ K hK
  have hsumΨ:=finite_hecke_energy_summable η m A t S c Ψ K hK
  have hre:HasSum (fun z:O=>‖∑I∈S,c I*rowWeight η m A z t I‖^2*
      (Ψ (‖eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy η m A t S c Ψ K).re:=by
    have hh:=Complex.hasSum_re hsumΨ.hasSum
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      finiteHeckeEnergy] using hh
  calc
    _≤∑'z:O,‖((‖∑I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)‖:=norm_tsum_le_tsum_norm hsumΦ.norm
    _≤∑'z:O,diagonalControl Φ*(‖∑I∈S,c I*rowWeight η m A z t I‖^2*
      (Ψ (‖eisEmbedding z‖^2/K)).re):=by
      apply hsumΦ.norm.tsum_le_tsum _ (hre.summable.mul_left _)
      intro z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (hΦ _ (by positivity)) (sq_nonneg _)).trans_eq (by ring)
    _=diagonalControl Φ*(finiteHeckeEnergy η m A t S c Ψ K).re:=by
      rw [tsum_mul_left,hre.tsum_eq]
    _≤_:=mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (diagonalControl_nonneg Φ)

theorem fixed_source (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀Φ:𝓢(ℝ,ℂ),Function.support (Φ:ℝ→ℂ)⊆Set.Iic b→
      ∀(η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)(K:ℝ),0<K→
      ‖finiteHeckeEnergy η m A t S c Φ K‖≤
        diagonalControl Φ*‖finiteHeckeEnergy η m A t S c Ψ K‖:=by
  obtain ⟨Ψ,hs,hn,_,hone⟩:=exists_fixed_bump b hb
  exact ⟨Ψ,hs,hn,fun Φ hΦ η m A t S c K hK=>finite_energy_domination b Ψ hn hone Φ hΦ η m A t S c K hK⟩

end SevenEighths.CenteredMomentEnergyFixedRadialSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FixedRadialEntry
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFixedRadialEntry
open ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSourceMass CenteredMomentSourceRectangleMask
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialSource CenteredMomentSourceRow
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentRadialEligibleEnergy
open CenteredMomentEnergyZeroComparison CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyFixedRadialEntry.instDecidableEqSumFinOfNatNat_solutions
theorem original_comparison (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀s:Input ι,∀R:Ideal O,∀r:Radial,
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic b→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*QuadraticInitialBound.diagonalControl r.profile*
        ‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) Ψ r.scale‖/volume s+
      2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale :=by
  obtain ⟨Ψ,hs,hn,hh⟩:=fixed_source b hb
  refine ⟨Ψ,hs,hn,?_⟩
  intro s R r hr
  apply (positive_energy_comparison s R r).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (volume_pos s).le
  have h:=mul_le_mul_of_nonneg_left
    (hh r.profile hr s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.scale r.scale_pos)
    (by norm_num : (0:ℝ)≤2)
  simpa only [mul_assoc] using h

end SevenEighths.CenteredMomentEnergyFixedRadialEntry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFixedRadialReduction
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildInput
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyFixedRadialEntry
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputFirstRemainder
open CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

local instance instDecidableEqSumFinOfNatNat_solutions_r1e74a6_1 : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum
theorem actual_original_reduction (bΦ:ℝ)(hbΦ:0<bΦ)
    (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,
      0<Cdiag ∧ 0<Ctail ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(R:Ideal O)(r:Radial),Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ→
      volume s≤Z^B→(r.scale)⁻¹≤Z^B→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
      2*diagonalControl r.profile*(
        physicalMass s R 1 fixedBadMask 1 Ψ r.scale Z ξ/volume s+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^(-saving))+
      2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale:=by
  obtain ⟨Ψ,hs,hn,hentry⟩:=original_comparison (ι:=ι) bΦ hbΦ
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=
    original_first_physical_reduction hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Ψ,hs,hn,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  have hsource:=hz.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi fixedBadMask 1
    (dvd_mul_right _ _) (dvd_mul_left _ _) R 1 Ψ r.scale r.scale_pos hV hK
  have hpos:=hentry s R r hr
  have hdom:=mul_le_mul_of_nonneg_left hsource
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg r.profile))
  apply hpos.trans
  apply add_le_add _ le_rfl
  simpa only [mul_div_assoc, CenteredMomentAmplificationChildInput.volume,
    CenteredMomentExceptionalAmplitudePair.volume] using hdom
end SevenEighths.CenteredMomentEnergyFixedRadialReduction

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.PhysicalEntry
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPhysicalEntry
open HeckeFamily CenteredMomentEnergyOriginalSource CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentSecondHeightFamily CenteredMomentExceptionalAmplitudePair
open CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma natural_inverse_scale {Z Bmask bΦ:ℝ} (state:NaturalState Z Bmask bΦ)
    (B:ℝ)(hB:0≤B):state.radial.scale⁻¹≤Z^B:=by
  have hscale:1≤ state.radial.scale:=by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  exact (inv_le_one_of_one_le₀ hscale).trans (Real.one_le_rpow state.base_ge_one hB)

end SevenEighths.CenteredMomentEnergyPhysicalEntry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ReferenceState
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceState
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyState
open CenteredMomentRadialEligibleEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

lemma comparison_second_power (Z M X₁ X₂:ℝ)(hZ:1<Z)(hX₁:0<X₁)(hX₂:0<X₂):
    comparisonSecond Z M X₁ X₂=Z^(Real.logb Z (X₁*X₂)-M/4):=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (mul_pos hX₁ hX₂)]
  rfl

end SevenEighths.CenteredMomentEnergyReferenceState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ReferenceLowBranchGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
local notation "O"=>HeckeFamily.O

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X):=by
  by_cases h:1≤X
  · rw [length,max_eq_right h,max_eq_right (Real.logb_nonneg hZ h)]
  · have hx:X≤1:=le_of_not_ge h
    have hl:Real.logb Z X≤0:=by
      simpa using Real.logb_le_logb_of_le hZ hX hx
    rw [length,max_eq_left hx,Real.logb_one,max_eq_left hl]

end SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetric
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetric
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionPower
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem balanced_four_scale_gates (Z width X₁ X₂:ℝ)(hZ:1<Z)(hwidth:0<width)
    (hX₁:0<X₁)(hX₂:0<X₂)
    (hshort:width/4≤ min (length Z X₁) (length Z X₂)):
    Z^(width/4)≤X₁ ∧ Z^(width/4)≤X₂ ∧
    Z^(width/4)≤ comparisonFirst Z width ∧
    Z^(width/4)≤ comparisonSecond Z width X₁ X₂ ∧
    length Z X₁+length Z X₂=Real.logb Z (X₁*X₂):=by
  have h₁:width/4≤length Z X₁:=hshort.trans (min_le_left _ _)
  have h₂:width/4≤length Z X₂:=hshort.trans (min_le_right _ _)
  have hraw (X:ℝ)(hX:0<X)(h:width/4≤length Z X):
      length Z X=Real.logb Z X ∧ width/4≤Real.logb Z X:=by
    have he:=CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX
    have hp:0<Real.logb Z X:=by
      by_contra hn
      rw [he,max_eq_left (le_of_not_gt hn)] at h
      linarith
    refine ⟨he.trans (max_eq_right hp.le),?_⟩
    rwa [he,max_eq_right hp.le] at h
  obtain ⟨he₁,hr₁⟩:=hraw X₁ hX₁ h₁
  obtain ⟨he₂,hr₂⟩:=hraw X₂ hX₂ h₂
  refine ⟨?_,?_,le_refl _,?_,?_⟩
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₁] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₁
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₂] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₂
  · rw [comparison_second_power Z width X₁ X₂ hZ hX₁ hX₂,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · rw [he₁,he₂,Real.logb_mul hX₁.ne' hX₂.ne']

variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetric

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceInputTailUniform CenteredMomentFirstReferenceEnergy
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
lemma slot_product_le (s:Input ι)(N:ℕ)(C:ℝ)(hC:1≤C)
    (hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C): (∏i,s.M i)≤C ^N := by
  calc
    _≤∏_i:ι,C:=Finset.prod_le_prod (fun i _=>(s.M_ge_one i).trans' zero_le_one) (fun i _=>hM i)
    _=C ^(Fintype.card ι):=by simp
    _≤C ^N:=pow_le_pow_right₀ hC hN

omit [DecidableEq ι] in
lemma plain_control_le {a b:ℝ}(s:Input ι)(p:Profiles a b)(S:Finset (ℕ×ℕ))
    (N:ℕ)(C:ℝ)(hC:1≤C)(hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C):
    plainControl s (p.profile 0) (p.profile 1)≤C ^N*p.control (insert (0,0) S) := by
  have h0 (i:Fin 2):SchwartzMap.seminorm ℝ 0 0 (p.profile i)≤
      sourceControl (insert (0,0) S) (p.profile i):=
    Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
      (s:=insert (0,0) S) (i:=(0,0)) (x:=p.profile i) (Finset.mem_insert_self _ _)
  have hpair:=mul_le_mul (h0 0) (h0 1) (apply_nonneg _ _) (sourceControl_nonneg _ _)
  have hh:=mul_le_mul (slot_product_le s N C hC hN hM) hpair
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (pow_nonneg (by linarith) _)
  simpa only [plainControl,Profiles.control,mul_assoc] using hh

omit [DecidableEq ι] in
lemma plain_control_sq_le {a b:ℝ}(s:Input ι)(p:Profiles a b)(S:Finset (ℕ×ℕ))
    (N:ℕ)(C:ℝ)(hC:1≤C)(hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C):
    (plainControl s (p.profile 0) (p.profile 1))^2≤C ^(2*N)*(p.control (insert (0,0) S))^2 := by
  have hh:=pow_le_pow_left₀ (plainControl_nonneg _ _ _) (plain_control_le s p S N C hC hN hM) 2
  simpa only [mul_pow,←pow_mul,Nat.mul_comm N 2] using hh

local notation "O"=>HeckeFamily.O
end SevenEighths.CenteredMomentEnergyOriginalProfileControl

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroReferencePhysical
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O

local instance instDecidableEqSumFinOfNatNat_solutions_r1e74a6_2 : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _
lemma balanced_volume {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    CenteredMomentAmplificationChildInput.volume (balancedInput s p ha t X₁ X₂ hX₁ hX₂)=X₁*X₂:=by
  simp only [CenteredMomentAmplificationChildInput.volume,
    balancedInput,naturalInput,completeInput,naturalData,Finset.univ_eq_empty,Finset.prod_empty,mul_one]

end SevenEighths.CenteredMomentEnergyZeroReferencePhysical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroReferencePhysicalBounded
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePhysicalBounded
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceLiveBounded CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyZeroReferencePhysical

local instance instDecidableEqSumFinOfNatNat_solutions_r1e74a6_3 : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _
theorem actual_positive_source_entry (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤ rho/100 ∧Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),X₁*X₂≤Z^B →
      5*s.width/6≤length Z X₁+length Z X₂ →
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t X₁ X₂≤
        2*diagonalControl s.radial.profile*(
          physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)+
          Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
          Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
        2*C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=balanced_reference_live
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=Fin 0) bΦ hbΦ (fun _=>1) a b B εdiag ξ saving (by simp) ha (by linarith) hB hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hV hlarge
  rcases hz.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge with hzero|hreference
  · exact Or.inl hzero
  · right
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (by simp) s.puncture s.radial s.radial_support
      (by rw [balanced_volume];exact hV) (natural_inverse_scale s B hB)
    change s.plainEnergy p t X₁ X₂≤_+2*s.plainEnergy p t
      (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) at hphysical
    rw [balanced_volume] at hphysical
    dsimp only [inp] at hphysical
    linarith only [hphysical,hreference]

end SevenEighths.CenteredMomentEnergyZeroReferencePhysicalBounded

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroGrowthHighBound
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthHighBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyOriginalProfileControl
local notation "O"=>HeckeFamily.O

local instance instDecidableEqSumFinOfNatNat_solutions_r1e74a6_4 : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _
lemma low_restrict (Q:Ideal O)(a b bΦ Bmask L L' Mcap e Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(K:ℝ)(hZ:1≤Z)(hL:L'≤L)
    (h:ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K):
    ZeroLowAt Q a b bΦ Bmask L' Mcap e Z degree S K:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ hL
  exact h s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hp) (hc₂.trans hp) hl

theorem actual_high_from_physical_oai
    (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass:ℝ),
      0≤e→0≤K→0≤Cmass→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      ZeroLowAt Q a b bΦ Bmask (Mcap+Bmask+rho/100) Mcap e Z degree S K→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q→ rho≤ s.width→s.width≤Mcap→
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),X₁*X₂≤Z^B→
      5*s.width/6≤length Z X₁+length Z X₂→
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      ((Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
          Cmass*(p.control Smass)^2*(1+|t|)^Jmass*
            Z^(max s.width (length Z X₁+length Z X₂)+emass))→
      s.plainEnergy p t X₁ X₂≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^Jout*Z^(max s.width (length Z X₁+length Z X₂)+efinal):=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuCap,hLu,hLuCap,huStage⟩:=
    CenteredMomentEnergyZeroUnbalancedOriginal.original_unbalanced_from_zero_low
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirCap,hLr,hLrCap,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrStage⟩:=
    CenteredMomentEnergyZeroReferencePhysicalBounded.actual_positive_source_entry
      a b bΦ rho ε Mcap Bmask B εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Ju,Uu,Cu,hCu,huBound⟩:=huStage S
  obtain ⟨Jr,Ur,Cr,hCr,hrBound⟩:=hrStage S
  let U:Finset (ℕ×ℕ):=insert (0,0) (Smass∪Uu∪Ur)
  let Jout:ℕ:=Jmass+Ju+Jr
  let P:ℝ:=1
  let D:ℝ:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ctail*P*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤P:=by norm_num [P]
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];positivity
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [huBound,hrBound] with Z hZu hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow s hQ hwidthLo hwidth p t X₁ X₂ hX₁ hX₂ hvolume hlarge
  dsimp only
  intro hphysical
  let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
  have hlowU:=low_restrict Q a b bΦ Bmask _ Lu Mcap e Z degree S K hZ.1.le hLuCap hlow
  have hlowR:=low_restrict Q a b bΦ Bmask _ Lr Mcap e Z degree S K hZ.1.le hLrCap hlow
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:0≤ s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|:=by exact le_add_of_nonneg_right (abs_nonneg t)
  let Mout:ℝ:=max s.width (length Z X₁+length Z X₂)
  have hwm:s.width≤Mout:=le_max_left _ _
  let F:ℝ:=(p.control U)^2*(1+|t|)^Jout*Z^(Mout+efinal)
  have hF:0≤F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤Jout)(hej:ej≤efinal):
      (p.control Sj)^2*(1+|t|)^jj*Z^(s.width+ej)≤F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (add_le_add hwm hej)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤Jout:=by dsimp [Jout];omega
  have hjr:Jr≤Jout:=by dsimp [Jout];omega
  have hjm:Jmass≤Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1)≤Cfixed*(K+Cmass+1):=by
    have hCuC : Cu ≤ Cfixed := by
      dsimp only [Cfixed]
      linarith only [hCr, hD, hT]
    exact mul_le_mul hCuC (by linarith only [hCmass])
      (by linarith only [hK]) hCfixed.le
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
  · have hunbalanced:=hZu.2 e Q degree K he hK hlowU s hQ hwidthLo hwidth
      p t X₁ X₂ hX₁ hX₂ hshort hlarge
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hfour':=balanced_four_scale_gates Z s.width X₁ X₂ hZ.1 (hrho.trans_le hwidthLo)
      hX₁ hX₂ (le_of_not_ge hshort)
    have hfour:Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂:=
      ⟨hfour'.1,hfour'.2.1,hfour'.2.2.1,hfour'.2.2.2.1⟩
    rcases hZ.2 e Q degree K he hK hlowR s hQ hwidthLo hwidth p t X₁ X₂ hX₁ hX₂
      hvolume hlarge with hzero|hsource
    · rw [hzero]
      positivity
    have hmass:=hphysical hfour
    have hmEnv:(p.control Smass)^2*(1+|t|)^Jmass*Z^(Mout+emass)≤F:=by
      have hp:=profile_control_mono p hm
      have hp0:=p.control_nonneg Smass
      have hj:=pow_le_pow_right₀ hbase hjm
      have hx:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show Mout+emass≤Mout+efinal by linarith only [hmassFinal])
      dsimp [F]
      gcongr
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        (X₁*X₂)≤Cmass*F:=by
      apply hmass.trans
      convert (preTransparency := .instances) mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤P*(p.control U)^2:=by
      have hc:=plain_control_sq_le inp p U 0 1 (by norm_num) (by simp) (by intro i;exact Fin.elim0 i)
      have h00:(0,0)∈U:=Finset.mem_insert_self _ _
      simpa only [P,Finset.insert_eq_of_mem h00,one_pow,one_mul] using hc
    have hheight1:1≤(1+|t|)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤efinal):s.radial.scale*Z^x≤Z^(Mout+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by have hh:=hwm;unfold NaturalState.width at hh;linarith only [hh, hx, s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤ c)(hA:0≤A)(hx:x≤efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤ c*P*A*F:=by
      calc
        _≤ c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
        _≤ c*(P*(p.control U)^2)*A*Z^(Mout+efinal):=by gcongr;exact hscalePower x hx
        _≤ c*P*A*F:=by
          dsimp [F]
          nlinarith only [mul_nonneg (show 0≤ c*P*A*(p.control U)^2*Z^(Mout+efinal) by positivity)
            (sub_nonneg.mpr hheight1)]
    have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) hdiagFinal
    have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) htailFinal
    have hrEnv:=henv Ur Jr (e+ε) hr hjr hefinal
    have href:=mul_le_mul_of_nonneg_left hrEnv (show 0≤2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
    have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
      (show 0≤2*diagonalControl s.radial.profile by positivity)
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu, hCr, hD, hT, hK, hCmass, mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _≤Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+|t|)^Jout*Z^(Mout+efinal)
    dsimp [D,T,F] at hsum href hfinish
    change _≤_ at hsum
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+|t|)^Jr*Z^(s.width+(e+ε)))≤_ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+|t|)^Jr*Z^(s.width+e+ε)≤_
    have hex:s.width+e+ε=s.width+(e+ε):=by ring
    rw [hex]
    nlinarith only [hsum,href,hfinish]

end SevenEighths.CenteredMomentEnergyZeroGrowthHighBound

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentEnergyZeroGrowthHighBound.actual_high_from_physical_oai := @OAI.SevenEighths.CenteredMomentEnergyZeroGrowthHighBound.actual_high_from_physical_oai
