-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentRadialPointwiseUniform.actual_uniform_divisor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:43:20.197215+00:00
-- url     : https://prove2.me/submissions/861e2f21-3924-4521-aa73-985f41574c9c

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Mask
namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMask
open ActualEisensteinCubic IdealMobiusDivisorSum
open UniqueFactorizationMonoid

theorem tsum_ideal_divisible (D : Ideal O) (hD : D ≠ 0) (f : Ideal O → ℂ) :
    (∑' I : Ideal O, if D ∣ I then f I else 0) =
      ∑' J : Ideal O, f (D * J) := by
  let F : Ideal O → ℂ := fun I => if D ∣ I then f I else 0
  have hrange : Function.support F ⊆ Set.range (fun J : Ideal O => D * J) := by
    intro I hI
    have hd : D ∣ I := by
      by_contra hn
      exact hI (by simp only [F, if_neg hn])
    obtain ⟨J, hJ⟩ := hd
    exact ⟨J, hJ.symm⟩
  have ht := (mul_right_injective₀ hD).tsum_eq hrange
  calc
    _ = ∑' J : Ideal O, F (D * J) := ht.symm
    _ = _ := by
      apply tsum_congr
      intro J
      simp only [F, dvd_mul_right, ite_true]

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeSlots
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeSlots
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem row_twisted_coefficient_norm (η : Character) (m A z : O) (t : ℝ)
    (P : Ideal O) (hP : P ≠ 0) :
    ‖(idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t)‖ ≤ 1 := by
  have hn : 0 < (Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  rw [norm_mul, norm_mul, show (Ideal.absNorm P:ℂ)=((Ideal.absNorm P:ℝ):ℂ) by simp,
    norm_real_imaginary_power _ t hn, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η P)).trans
    (CanonicalRowCompletion.idealRowHom_norm _ _)

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentHeckeSlots

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

theorem common_extracted_slot_rectangle (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)) =
      rowWeight η m A z t (B₁*B₂)*
        ∑ v : (i : ι) → S i, (∏ i,β i (v i))*
          ∑' I : Ideal O, ∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
              idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
                (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) =
      rowWeight η m A z t (B₁*B₂)*
        (rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
            (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J) := by
    rw [CenteredMomentExtraction.idealRectangle_extract]
    simp only [map_mul]
    ring
  simp_rw [ht,tsum_mul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end SevenEighths.CenteredMomentHeckeExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorAllocation
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorAllocation
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem prime_complement (P : Ideal O) (hP : Prime P) (s : Finset ι) (v : ι → Ideal O) :
    (∏ i ∈ s, (1-(if P ∣ v i then (1:ℂ) else 0))) =
      if P ∣ ∏ i ∈ s,v i then 0 else 1 := by
  by_cases h : P ∣ ∏ i ∈ s,v i
  · rw [if_pos h]
    obtain ⟨i,hi,hd⟩ := (hP.dvd_finsetProd_iff v).mp h
    exact Finset.prod_eq_zero hi (by simp only [if_pos hd,sub_self])
  · rw [if_neg h]
    apply Finset.prod_eq_one
    intro i hi
    have hd : ¬P∣v i := fun hh => h ((hP.dvd_finsetProd_iff v).mpr ⟨i,hi,hh⟩)
    simp only [if_neg hd,sub_zero]

theorem prime_factor_allocation (P : Ideal O) (hP : Prime P)
    (s : Finset ι) (v : ι → Ideal O) :
    (if P ∣ ∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
        ∏ i ∈ J, if P ∣ v i then (1:ℂ) else 0 := by
  let f := fun J : Finset ι => (-1:ℂ)^J.card*∏ i ∈ J,if P∣v i then (1:ℂ) else 0
  have he : (∑ J ∈ nonemptySelections s,f J)+1 =
      if P ∣ ∏ i ∈ s,v i then (0:ℂ) else 1 := by
    have hr := Finset.sum_erase_add s.powerset f (Finset.mem_powerset.mpr (Finset.empty_subset s))
    have hh := Finset.prod_sub (fun _i : ι => (1:ℂ))
      (fun i => if P∣v i then (1:ℂ) else 0) s
    simp only [Finset.prod_const_one,mul_one] at hh
    rw [prime_complement P hP s v] at hh
    simpa only [nonemptySelections,f,Finset.card_empty,pow_zero,Finset.prod_empty,one_mul] using hr.trans hh.symm
  have hn : (∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
      ∏ i ∈ J,if P∣v i then (1:ℂ) else 0) = -(∑ J ∈ nonemptySelections s,f J) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [f]
    rw [pow_succ]
    ring
  rw [hn]
  by_cases h : P∣∏ i ∈ s,v i <;> simp only [h,ite_true,ite_false] at he ⊢ <;>
    linear_combination he

theorem squarefree_dvd_iff (D I : Ideal O) (hD : Squarefree D) :
    D∣I ↔ ∀ P ∈ primeSupport D,P∣I := by
  constructor
  · intro hd P hP
    exact (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)).trans hd
  · intro h
    rw [← squarefree_support_product_self hD]
    apply Finset.prod_dvd_of_coprime ?_ h
    intro P hP Q hQ hne
    let : P.IsMaximal := (Ideal.isPrime_of_prime (support_prime hP)).isMaximal (support_prime hP).ne_zero
    let : Q.IsMaximal := (Ideal.isPrime_of_prime (support_prime hQ)).isMaximal (support_prime hQ).ne_zero
    exact Ideal.isCoprime_of_isMaximal hne

theorem squarefree_mask_allocation (D : Ideal O) (hD : Squarefree D)
    (s : Finset ι) (v : ι → Ideal O) :
    (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ a : Allocation D s, allocationTerm D s v a := by
  have hprod : (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∏ P : primeSupport D, if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0 := by
    by_cases hd : D∣∏ i ∈ s,v i
    · rw [if_pos hd]
      symm
      apply Finset.prod_eq_one
      intro P hP
      rw [if_pos ((squarefree_dvd_iff _ _ hD).mp hd P P.property)]
    · rw [if_neg hd]
      obtain ⟨P,hP,hnd⟩ := not_forall.mp (fun h => hd ((squarefree_dvd_iff _ _ hD).mpr h))
        |> fun h => by simpa only [not_forall,_root_.not_imp] using h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨P,hP⟩ : primeSupport D)) (by simp only [if_neg hnd])
  rw [hprod]
  have hl (P : primeSupport D) :
      (if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J : nonemptySelections s, (-1:ℂ)^(J.val.card+1)*
        ∏ i ∈ J.val, if (P:Ideal O)∣v i then (1:ℂ) else 0 := by
    rw [prime_factor_allocation P (support_prime P.property) s v]
    exact (Finset.sum_coe_sort (nonemptySelections s) (fun J =>
      (-1:ℂ)^(J.card+1)*∏ i ∈ J,if (P:Ideal O)∣v i then (1:ℂ) else 0)).symm
  simp_rw [hl]
  exact Fintype.prod_sum _

theorem allocation_card_bound (D : Ideal O) (s : Finset ι) :
    Fintype.card (Allocation D s) ≤ (2^(primeSupport D).card)^s.card := by
  have hc : (nonemptySelections s).card ≤ 2^s.card := by
    simpa only [nonemptySelections,Finset.card_powerset] using
      (Finset.card_erase_le (s := s.powerset) (a := (∅:Finset ι)))
  change Fintype.card (primeSupport D → nonemptySelections s) ≤ _
  simp only [Fintype.card_fun,Fintype.card_coe]
  calc
    _ ≤ (2^s.card)^(primeSupport D).card := Nat.pow_le_pow_left hc _
    _ = _ := by simp only [← pow_mul,Nat.mul_comm]

end SevenEighths.CenteredMomentDivisorAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorExtraction
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorExtraction
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem selected_divides_factor (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) : (P:Ideal O)∣v i := by
  have hP := (Finset.prod_ne_zero_iff.mp hn) P (Finset.mem_univ P)
  have hprod := (mul_ne_zero_iff.mp hP).2
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) i hi
  by_contra h
  exact hfactor (by simp only [if_neg h])

theorem selectedDivisor_dvd (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) (i : ι) :
    selectedDivisor D s a i ∣ v i := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hne
    let : (P:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal
      (support_prime P.property).ne_zero
    let : (Q:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime Q.property)).isMaximal
      (support_prime Q.property).ne_zero
    exact Ideal.isCoprime_of_isMaximal (fun he => hne (Subtype.ext he))
  · intro P hP
    exact selected_divides_factor D s v a hn P i (Finset.mem_filter.mp hP).2

end SevenEighths.CenteredMomentDivisorExtraction

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorEnergy
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι α ρ : Type*} [DecidableEq ι]

theorem allocation_card_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      (Fintype.card (Allocation D s):ℝ) ≤ C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C ^N,pow_pos hC _,?_⟩
  intro D hD s hs
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C ^N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

end SevenEighths.CenteredMomentDivisorEnergy

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

end SevenEighths.CenteredMomentAbsoluteEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorTensor
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorTensor
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentMask HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem allocationSign_norm (D : Ideal O) (s : Finset ι) (a : Allocation D s) :
    ‖allocationSign D s a‖=1 := by
  simp only [allocationSign,norm_prod,norm_pow,norm_neg,norm_one,one_pow,Finset.prod_const_one]

theorem allocationTerm_eq_ite (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a =
      if ∀ i ∈ s, selectedDivisor D s a i∣v i then allocationSign D s a else 0 := by
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [if_pos hh]
    unfold allocationTerm allocationSign
    apply Finset.prod_congr rfl
    intro P hP
    have he : (∏ i ∈ (a P).val,if (P:Ideal O)∣v i then (1:ℂ) else 0)=1 := by
      apply Finset.prod_eq_one
      intro i hi
      have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a P).property)) hi
      have hPi : (P:Ideal O)∣selectedDivisor D s a i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ P,hi⟩)
      rw [if_pos (hPi.trans (hh i his))]
    rw [he,mul_one]
  · rw [if_neg hh]
    by_contra hn
    exact hh (fun i _ => selectedDivisor_dvd D s v a hn i)

theorem allocationTerm_eq_product (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a = allocationSign D s a*
      ∏ i ∈ s, if selectedDivisor D s a i∣v i then (1:ℂ) else 0 := by
  rw [allocationTerm_eq_ite]
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [if_pos hh,Finset.prod_eq_one (fun i hi => by rw [if_pos (hh i hi)]),mul_one]
  · rw [if_neg hh]
    push Not at hh
    obtain ⟨i,hi,hnd⟩ := hh
    rw [Finset.prod_eq_zero hi (by simp only [if_neg hnd]),mul_zero]

end SevenEighths.CenteredMomentDivisorTensor

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorSlots
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorSlots
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem selected_slot_exact (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if D∣I then β I else 0) t =
      if P ∈ S ∧ D∣P then β P*rowWeight η m A z t P else 0 := by
  rw [rowSlot_eq_weight]
  have hz (I : Ideal O) (hI : I ∈ S) (hne : I ≠ P) :
      (if D∣I then β I else 0)*rowWeight η m A z t I=0 := by
    have hnd : ¬D∣I := fun hd => hne ((prime_dvd_prime_iff_eq hP (hS I hI)).mp (hPD.trans hd)).symm
    simp only [if_neg hnd,zero_mul]
  by_cases hmem : P ∈ S
  · rw [Finset.sum_eq_single P (fun I hI hne => hz I hI hne) (fun h => (h hmem).elim)]
    by_cases hd : D∣P <;> simp only [hmem,hd,and_self,true_and,ite_true,ite_false,zero_mul]
  · rw [Finset.sum_eq_zero (fun I hI => hz I hI (fun he => hmem (he ▸ hI)))]
    simp only [hmem,false_and,ite_false]

theorem selected_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M) (hβ : ∀ I ∈ S, ‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if D∣I then β I else 0) t‖ ≤ M := by
  rw [selected_slot_exact η m A z t D P hP hPD S hS β]
  split_ifs with h
  · rw [norm_mul]
    exact (mul_le_mul (hβ P h.1) (row_twisted_coefficient_norm η m A z t P hP.ne_zero)
      (norm_nonneg _) hM).trans_eq (mul_one M)
  · simpa only [norm_zero] using hM

theorem selectedDivisor_empty (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (he : selectedPrimes D s a i=∅) : selectedDivisor D s a i=1 := by
  simp only [selectedDivisor,he,Finset.prod_empty]

end SevenEighths.CenteredMomentDivisorSlots

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRectangle
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorRectangle
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentHeckeExpansion CenteredMomentMask CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem allocationTerm_rectangle (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (I J : Ideal O) :
    allocationTerm D Finset.univ (factorTuple v I J) a =
      allocationSign D Finset.univ a *
        (∏ i,if selectedSlot D a i ∣ v i then (1:ℂ) else 0)*
        (if selectedPlain D a 0 ∣ I then 1 else 0)*
        (if selectedPlain D a 1 ∣ J then 1 else 0) := by
  rw [allocationTerm_eq_product,Fintype.prod_sum_type,Fin.prod_univ_two]
  simp only [factorTuple,Sum.elim_inl,Sum.elim_inr,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,
    selectedPlain,selectedSlot]
  simp only [mul_assoc]
  rfl

theorem double_selected_reindex (D₁ D₂ : Ideal O) (h₁ : D₁ ≠ 0) (h₂ : D₂ ≠ 0)
    (F : Ideal O → Ideal O → ℂ) :
    (∑' I : Ideal O,∑' J : Ideal O,
      (if D₁∣I then (1:ℂ) else 0)*(if D₂∣J then 1 else 0)*F I J) =
      ∑' I : Ideal O,∑' J : Ideal O,F (D₁*I) (D₂*J) := by
  have he (I J : Ideal O) :
      (if D₁∣I then (1:ℂ) else 0)*(if D₂∣J then 1 else 0)*F I J =
        if D₁∣I then (if D₂∣J then F I J else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  have hi (I : Ideal O) :
      (∑' J : Ideal O,if D₁∣I then (if D₂∣J then F I J else 0) else 0) =
        if D₁∣I then (∑' J : Ideal O,if D₂∣J then F I J else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hi]
  rw [tsum_ideal_divisible D₁ h₁]
  exact tsum_congr (fun I => tsum_ideal_divisible D₂ h₂ (F (D₁*I)))

theorem allocated_rectangle_reindex (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ v : (i : ι) → S i,(∏ i,β i (v i))*
      ∑' I : Ideal O,∑' J : Ideal O,
        allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ∑ v : (i : ι) → S i,
          (∏ i,if selectedSlot D a i ∣ (v i:Ideal O) then β i (v i) else 0)*
          ∑' I : Ideal O,∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
            idealRectangle W₁ W₂
              (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))
              (Y₁/Ideal.absNorm (selectedPlain D a 0)) (Y₂/Ideal.absNorm (selectedPlain D a 1)) I J := by
  let F (v : (i : ι) → S i) (I J : Ideal O) :=
    rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J
  have he (v : (i : ι) → S i) (I J : Ideal O) :
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
      (allocationSign D Finset.univ a * (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0))*
        ((if selectedPlain D a 0∣I then (1:ℂ) else 0)*
          (if selectedPlain D a 1∣J then 1 else 0)*F v I J) := by
    rw [allocationTerm_rectangle]
    dsimp only [F]
    ring
  have hint (v : (i : ι) → S i) :
      (∑' I : Ideal O,∑' J : Ideal O,
        allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (allocationSign D Finset.univ a * (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0))*
        (∑' I : Ideal O,∑' J : Ideal O,F v (selectedPlain D a 0*I) (selectedPlain D a 1*J)) := by
    simp_rw [he]
    have ht := double_selected_reindex (selectedPlain D a 0) (selectedPlain D a 1)
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)) (F v)
    rw [← ht,← tsum_mul_left]
    apply tsum_congr
    intro I
    exact tsum_mul_left
  simp_rw [hint]
  have hβ (v : (i : ι) → S i) :
      (∏ i,β i (v i))*(allocationSign D Finset.univ a*
        (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0)) =
      allocationSign D Finset.univ a *
        (∏ i,if selectedSlot D a i∣(v i:Ideal O) then β i (v i) else 0) := by
    rw [mul_left_comm,← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> simp
  simp_rw [← mul_assoc]
  simp only [← mul_assoc] at hβ
  simp_rw [hβ]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  dsimp only [F]
  rw [common_extracted_slot_rectangle η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t
    W₁ W₂ X₁ X₂ Y₁ Y₂ (selectedPlain D a 0) (selectedPlain D a 1)]
  simp only [mul_assoc]

end SevenEighths.CenteredMomentDivisorRectangle

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRows
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRows
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentDivisorRectangle CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem allocatedRectangle_eq_rows (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ((rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
          rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1)))*
          ∏ i,rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t) := by
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedRectangle
  rw [allocated_rectangle_reindex]
  rw [actual_slot_rectangle_sum η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t W₁ W₂ b₁ b₂
    _ _ _ _ hW₁ hW₂ (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1))
    (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))]

theorem allocatedRectangle_norm_le (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      ‖rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
        rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))‖ *
        ∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖ := by
  rw [allocatedRectangle_eq_rows η m A z t S β D a W₁ W₂ b₁ b₂ _ _ _ _
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂,norm_mul,norm_mul,allocationSign_norm,one_mul,norm_mul,norm_prod]
  apply mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact row_twisted_coefficient_norm η m A z t _ (mul_ne_zero
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))

end SevenEighths.CenteredMomentDivisorRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRaw
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorSlots
open CenteredMomentDivisorRectangle CenteredMomentDivisorRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem split_slot_product {M : Type*} [CommMonoid M] (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (f : ι → M) :
    (∏ i∈frozenIndices D a,f i)*(∏ i∈liveIndices D a,f i)=∏ i,f i :=
  Finset.prod_filter_mul_prod_filter_not _ _ _

theorem selected_live_slot (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ liveIndices D a) (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t =
      rowSlot η m A z S β t := by
  have he := selectedDivisor_empty D Finset.univ a (Sum.inl i)
    (Finset.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hi).2)
  simp only [selectedSlot,he,one_dvd,ite_true]

theorem selected_frozen_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ frozenIndices D a) (S : Finset (Ideal O))
    (hS : ∀ I∈S,Prime I) (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hβ : ∀ I∈S,‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t‖ ≤ M := by
  obtain ⟨P,hP⟩ := (Finset.mem_filter.mp hi).2
  exact selected_slot_bound η m A z t (selectedSlot D a i) P
    (IdealMobiusDivisorSum.support_prime P.property) (Finset.dvd_prod_of_mem _ hP)
    S hS β M hM hβ

theorem selected_slot_product_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M : ι → ℝ) (hM : ∀ i,0 ≤ M i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i) :
    (∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖) ≤
      (∏ i∈frozenIndices D a,M i)*∏ i∈liveIndices D a,‖rowSlot η m A z (S i) (β i) t‖ := by
  rw [← split_slot_product D a]
  apply mul_le_mul
  · apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro i hi
    exact selected_frozen_slot_bound η m A z t D a i hi (S i) (hS i) (β i) (M i) (hM i) (hβ i)
  · apply le_of_eq
    apply Finset.prod_congr rfl
    intro i hi
    rw [selected_live_slot η m A z t D a i hi]
  · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  · exact Finset.prod_nonneg (fun i _ => hM i)

theorem selectedNorm_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) :
    0 < selectedNorm D a := by
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a _))

theorem raw_scale_identity (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ) :
    rawRemaining D a T P*formalReductionFactor D a P=T*∏ i,P i := by
  unfold rawRemaining formalReductionFactor
  rw [← split_slot_product D a P]
  field_simp [(selectedNorm_pos D a).ne']

end SevenEighths.CenteredMomentDivisorRaw

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

theorem allocated_raw_energy (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        ‖residualCenteredRow η m A z t S β P D a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2 := by
  let R : ℂ :=
    rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
      rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
    rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
      rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))
  let L : ℂ := R*∏ i∈liveIndices D a,rowSlot η m A z (S i) (β i) t
  have hn : ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      (∏ i∈frozenIndices D a,M i)*‖L‖ := by
    apply (allocatedRectangle_norm_le η m A z t S β D a W₁ W₂ b₁ b₂
      _ _ _ _ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂).trans
    have hh := mul_le_mul_of_nonneg_left
      (selected_slot_product_bound η m A z t D a S hS β M hM hβ) (norm_nonneg R)
    dsimp only [L]
    rw [norm_mul,norm_prod]
    convert (preTransparency := .instances) hh using 1 ; ring
  have hraw : 0 < rawRemaining D a T P := mul_pos (div_pos hT (selectedNorm_pos D a))
    (Finset.prod_pos (fun i _ => hP i))
  have hformal : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hres : ‖residualCenteredRow η m A z t S β P D a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2 =
      ‖L‖^2/rawRemaining D a T P := by
    unfold residualCenteredRow centeredSlotRow
    rw [Finset.prod_coe_sort (liveIndices D a) P,
      Finset.prod_coe_sort (liveIndices D a) (fun i => rowSlot η m A z (S i) (β i) t)]
    exact normalized_norm_sq _ hraw L
  rw [normalized_norm_sq _ htotal,hres]
  calc
    _ ≤ ((∏ i∈frozenIndices D a,M i)*‖L‖)^2/(T*∏ i,P i) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) htotal.le
    _ = _ := by
      rw [← raw_scale_identity D a T P,mul_pow]
      field_simp [hraw.ne',hformal.ne']

end SevenEighths.CenteredMomentDivisorRawEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SlotRatios
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

theorem logWindow_nonneg (a b : ℝ) : 0 ≤ logWindow a b :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem slot_log_ratio_bound (W : ℝ → ℂ) (a b P Z : ℝ) (I : Ideal O)
    (ha : 0 < a) (hZ : 1 < Z)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hW : W ((Ideal.absNorm I:ℝ)/P) ≠ 0) :
    |Real.logb Z ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b/Real.log Z := by
  have hw := hs hW
  have hr : 0 < (Ideal.absNorm I:ℝ)/P := ha.trans_le hw.1
  have hlow := Real.log_le_log ha hw.1
  have hhigh := Real.log_le_log hr hw.2
  have habs : |Real.log ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b := by
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le (Real.log a)
      have hm := le_max_left |Real.log a| |Real.log b|
      dsimp only [logWindow]
      linarith
    · exact hhigh.trans ((le_abs_self _).trans (le_max_right _ _))
  rw [Real.logb,abs_div,abs_of_pos (Real.log_pos hZ)]
  exact div_le_div_of_nonneg_right habs (Real.log_pos hZ).le

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem frozen_subset_ratio_bound (entrance frozen : Finset ι) (hsub : frozen ⊆ entrance)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ frozen,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |∑ i ∈ frozen,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  calc
    _ ≤ ∑ i ∈ frozen,|Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ frozen,logWindow (a i) (b i)/Real.log Z :=
      Finset.sum_le_sum (fun i hi => slot_log_ratio_bound (W i) (a i) (b i) (P i) Z (v i)
        (ha i (hsub hi)) hZ (hs i (hsub hi)) (hW i hi))
    _ = (∑ i ∈ frozen,logWindow (a i) (b i))/Real.log Z := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => logWindow_nonneg (a i) (b i))) (Real.log_pos hZ).le

end SevenEighths.CenteredMomentSlotRatios

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorWitness
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorWitness
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentHeckeExpansion
open CenteredMomentRectangle HeckeFamily IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_tsum_term {α : Type*} (f : α → ℂ) (h : (∑' x,f x) ≠ 0) :
    ∃ x,f x ≠ 0 := by
  by_contra hn
  push Not at hn
  exact h (by simp only [hn,tsum_zero])

theorem allocated_nonzero_witness (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    ∃ (v : (i : ι) → S i) (I J : Ideal O),
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a ≠ 0 ∧
      (∀ i,β i (v i) ≠ 0) ∧ idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J ≠ 0 := by
  obtain ⟨v,_,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hβ,ht⟩ := mul_ne_zero_iff.mp hv
  obtain ⟨I,hI⟩ := exists_tsum_term _ ht
  obtain ⟨J,hJ⟩ := exists_tsum_term _ hI
  have hh := mul_ne_zero_iff.mp hJ
  exact ⟨v,I,J,(mul_ne_zero_iff.mp hh.1).1,
    fun i => Finset.prod_ne_zero_iff.mp hβ i (Finset.mem_univ i),hh.2⟩

private theorem prime_dvd_selectedPlain (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) (P : primeSupport D)
    (hP : P ∈ selectedPrimes D Finset.univ a (Sum.inr j)) :
    (P : Ideal O) ∣ selectedPlain D a j := by
  exact Finset.dvd_prod_of_mem (fun q : primeSupport D => (q : Ideal O))
    (a := P) (s := selectedPrimes D Finset.univ a (Sum.inr j)) hP

theorem divisor_dvd_actualExtracted (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (I J : Ideal O)
    (hn : allocationTerm D Finset.univ (factorTuple v I J) a ≠ 0) :
    D ∣ actualExtracted D a v := by
  apply (squarefree_dvd_iff D _ hD).mpr
  intro P hP
  let PP : primeSupport D := ⟨P,hP⟩
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp (a PP).property).1
  have hmem : PP ∈ selectedPrimes D Finset.univ a i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ PP,hi⟩
  cases i with
  | inl i =>
      have hfr : i ∈ frozenIndices D a := Finset.mem_filter.mpr ⟨Finset.mem_univ i,⟨PP,hmem⟩⟩
      have hd : P∣v i := selected_divides_factor D Finset.univ (factorTuple v I J) a hn PP (Sum.inl i) hi
      exact dvd_mul_of_dvd_right (hd.trans (Finset.dvd_prod_of_mem v (a := i) (s := frozenIndices D a) hfr)) _
  | inr j =>
      have hd : P∣selectedPlain D a j := prime_dvd_selectedPlain D a j PP hmem
      fin_cases j
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _

theorem actualExtracted_ne_zero (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) : actualExtracted D a v ≠ 0 :=
  mul_ne_zero (mul_ne_zero (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hv i))

theorem actualExtracted_norm_boundary (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) (I J : Ideal O)
    (hn : allocationTerm D Finset.univ (factorTuple v I J) a ≠ 0) :
    (Ideal.absNorm D:ℝ) ≤ selectedNorm D a*∏ i∈frozenIndices D a,(Ideal.absNorm (v i):ℝ) := by
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (actualExtracted_ne_zero D a v hv))) (map_dvd Ideal.absNorm (divisor_dvd_actualExtracted D hD a v I J hn))
  simpa only [actualExtracted,map_mul,map_prod,Nat.cast_mul,Nat.cast_prod,selectedNorm] using
    (show (Ideal.absNorm D:ℝ) ≤ Ideal.absNorm (actualExtracted D a v) by exact_mod_cast h)

end SevenEighths.CenteredMomentDivisorWitness

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorActualBoundary
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorActualBoundary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentDivisorWitness CenteredMomentSlotRatios HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem selected_log_identity (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) (P : ι → ℝ) (hP : ∀ i,0 < P i) (Z : ℝ) :
    Real.logb Z (selectedNorm D a*∏ i∈frozenIndices D a,(Ideal.absNorm (v i:Ideal O):ℝ)) =
      Real.logb Z (formalReductionFactor D a P)+
        ∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i) := by
  have hn (i : ι) : (Ideal.absNorm (v i:Ideal O):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i))
  unfold formalReductionFactor
  rw [Real.logb_mul (selectedNorm_pos D a).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)),
    Real.logb_mul (selectedNorm_pos D a).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => (hP i).ne')),
    Real.logb_prod _ _ (fun i _ => hn i),Real.logb_prod _ _ (fun i _ => (hP i).ne')]
  simp_rw [Real.logb_div (hn _) (hP _).ne']
  rw [Finset.sum_sub_distrib]
  ring

theorem nonzero_row_formal_boundary (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (hβW : ∀ i I,β i I ≠ 0 → W i ((Ideal.absNorm I:ℝ)/P i) ≠ 0)
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
  obtain ⟨v,I,J,ha,hβ,hrect⟩ := allocated_nonzero_witness η m A z t S β D a
    W₁ W₂ X₁ X₂ Y₁ Y₂ hne
  have hv (i : ι) : (v i:Ideal O) ≠ 0 := (hS i (v i) (v i).property).ne_zero
  have hb := actualExtracted_norm_boundary D hD a (fun i => v i) hv I J ha
  have hND : (0:ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hl := Real.logb_le_logb_of_le hZ hND hb
  rw [selected_log_identity D a (fun i => v i) hv P hP Z] at hl
  have hr : |∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i)| ≤
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
    apply frozen_subset_ratio_bound (ι := ι) Finset.univ (frozenIndices D a) (Finset.subset_univ _)
      W lo hi P (fun i => (v i:Ideal O)) Z hZ
    · intro i _
      exact hlo i
    · intro i _
      exact hW i
    · intro i _
      exact hβW i (v i) (hβ i)
  have hh := (le_abs_self (∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i))).trans hr
  linarith

theorem original_nonzero_row_formal_boundary (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S
      (fun i I => ν i I*W i ((Ideal.absNorm I:ℝ)/P i)) D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z :=
  nonzero_row_formal_boundary η m A z t S hS _ W lo hi P hlo hP hW
    (fun _i _I h => (mul_ne_zero_iff.mp h).2) D hD a W₁ W₂ X₁ X₂ Y₁ Y₂ Z hZ hne

end SevenEighths.CenteredMomentDivisorActualBoundary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorFullMask
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorFullMask
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O

 theorem annular_hasFiniteSupport (W : ℝ → ℂ) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (fun I : Ideal O => W ((Ideal.absNorm I:ℝ)/X)).HasFiniteSupport := by
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b*X))).subset
  intro I hI
  have hn := (div_le_iff₀ hX).mp (hs hI)
  exact_mod_cast hn.trans (Nat.le_ceil (b*X))

theorem rectangle_hasFiniteSupport (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (fun v : Ideal O × Ideal O => idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ v.1 v.2).HasFiniteSupport := by
  have h₁ := (annular_hasFiniteSupport W₁ b₁ X₁ hX₁ hW₁).union
    (annular_hasFiniteSupport W₁ b₁ Y₁ hY₁ hW₁)
  have h₂ := (annular_hasFiniteSupport W₂ b₂ X₂ hX₂ hW₂).union
    (annular_hasFiniteSupport W₂ b₂ Y₂ hY₂ hW₂)
  apply (h₁.prod h₂).subset
  intro v hv
  constructor
  · by_contra hn
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hv (by simp only [idealRectangle,hn.1,hn.2,zero_mul,sub_self])
  · by_contra hn
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hv (by simp only [idealRectangle,hn.1,hn.2,mul_zero,sub_self])

theorem rectangle_tsum_sum {α : Type*} [Fintype α]
    (f : α → Ideal O → Ideal O → ℂ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O,∑' J : Ideal O,
      ∑ a, f a I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      ∑ a,∑' I : Ideal O,∑' J : Ideal O,f a I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J := by
  have hs (a : α) : Summable (fun v : Ideal O × Ideal O =>
      f a v.1 v.2*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ v.1 v.2) :=
    summable_of_hasFiniteSupport ((rectangle_hasFiniteSupport W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
      hW₁ hW₂ hX₁ hX₂ hY₁ hY₂).mul_right _)
  have hi (I : Ideal O) := Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => (hs a).prod_factor I)
  simp_rw [hi]
  exact Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => (hs a).prod)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem factorTuple_product (v : ι → Ideal O) (I J : Ideal O) :
    (∏ i,factorTuple v I J i)=(∏ i,v i)*I*J := by
  rw [Fintype.prod_sum_type,Fin.prod_univ_two]
  simp only [factorTuple,Sum.elim_inl,Sum.elim_inr,ite_true,
    show (1:Fin 2) ≠ 0 by decide,ite_false,mul_assoc]

theorem full_mask_eq_allocated_rectangles (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O) (hD : Squarefree D)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i,(∏ i,β i (v i))*
      ∑' I : Ideal O,∑' J : Ideal O,
        (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ := by
  have he (v : (i : ι) → S i) (I J : Ideal O) :
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0) =
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a := by
    rw [← factorTuple_product]
    exact squarefree_mask_allocation D hD Finset.univ _
  simp_rw [he,Finset.sum_mul]
  simp_rw [rectangle_tsum_sum _ W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

end SevenEighths.CenteredMomentDivisorFullMask

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRowEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorRowEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRows CenteredMomentDivisorFullMask
open CenteredMomentDivisorEnergy CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_allocated_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
      (D : Ideal O),Squarefree D → ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z ∈ rows,0 ≤ ω z) →
      (∑ z ∈ rows,ω z*‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
            ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
  obtain ⟨C,hC,hcard⟩ := allocation_card_small_power (ι := ι ⊕ Fin 2) (N+2) (by omega) ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows ω hω
  have hc : (Finset.univ : Finset (ι ⊕ Fin 2)).card ≤ N+2 := by
    simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hslots 2
  have hrow (z : O) :
      ‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
        (Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
          ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
            ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
    unfold maskedRectangle
    rw [full_mask_eq_allocated_rectangles η m A z t S β D hD W₁ W₂ b₁ b₂
      _ _ _ _ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂]
    calc
      _ ≤ (∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)) => (1:ℝ))
          (fun a => ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖))
  calc
    _ ≤ ∑ z ∈ rows,ω z*((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) :=
      Finset.sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hrow z) (hω z hz))
    _ = (Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
      simp_rw [mul_left_comm (ω _) _,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD.ne_zero Finset.univ hc)
      (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun z hz => mul_nonneg (hω z hz) (sq_nonneg _))))

end SevenEighths.CenteredMomentDivisorRowEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RetainedProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedProfile
open CenteredMomentLattice CenteredMomentTwist CenteredMomentHeckeTwist
open CenteredMomentHeckeHeight CenteredMomentHeckeVolume CenteredMomentHeckeCancellation HeckeFamily
open EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

theorem clippedScale_ge_one (S : ℝ) : 1 ≤ clippedScale S := le_max_left _ _

theorem clipped_source (W : ℝ → ℂ) (S x : ℝ) (hS : 0 < S) :
    dilated W (clipDilation S) (x / clippedScale S) = W (x / S) := by
  have hclip : clippedScale S ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (clippedScale_ge_one S))
  unfold dilated clipDilation
  congr 1
  field_simp

theorem strict_subunit_ideal_zero (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1)
    (I : Ideal O) (hI : I ≠ 0) : W ((Ideal.absNorm I : ℝ) / S) = 0 := by
  by_contra h
  have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu := (div_le_iff₀ hS).mp (hs h)
  nlinarith

theorem strict_subunit_sum_zero (A : Ideal O → ℂ) (hA : A 0 = 0)
    (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) = 0 := by
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · rw [hI, hA, zero_mul]
      · rw [strict_subunit_ideal_zero W b S hS hs hstrict I hI, mul_zero]
    _ = 0 := tsum_zero

theorem clipped_ideal_sum (A : Ideal O → ℂ) (W : ℝ → ℂ) (S : ℝ) (hS : 0 < S) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) =
      ∑' I : Ideal O, A I * dilated W (clipDilation S)
        ((Ideal.absNorm I : ℝ) / clippedScale S) := by
  apply tsum_congr
  intro I
  rw [clipped_source W S _ hS]

theorem clipped_rowTwistedSum (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    rowTwistedSum η m A₀ z W t S =
      rowTwistedSum η m A₀ z (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_rowTwistedSum_zero (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : rowTwistedSum η m A₀ z W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

end SevenEighths.CenteredMomentRetainedProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RetainedEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredMomentRetainedProfile
open CenteredMomentDivisorRawEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem retained_rectangle_raw_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ T : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hT : 0 < T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏ i,rowSlot η m A z (S i) (β i) t)‖^2 =
      (clippedScale X₁*clippedScale X₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  have hp : 0 < ∏ i,P i := Finset.prod_pos (fun i _ => hP i)
  have hc₁ : 0 < clippedScale X₁ := zero_lt_one.trans_le (clippedScale_ge_one _)
  have hc₂ : 0 < clippedScale X₂ := zero_lt_one.trans_le (clippedScale_ge_one _)
  unfold retainedPositiveRow positiveSlotRow
  rw [normalized_norm_sq _ (mul_pos hT hp),normalized_norm_sq _ (mul_pos (mul_pos hc₁ hc₂) hp),
    clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  field_simp [hp.ne',hT.ne',hc₁.ne',hc₂.ne']

omit [DecidableEq ι] in
theorem retained_rectangle_uniform_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (b₁ b₂ t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 ≤
      (max 1 b₁*max 1 b₂)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  have hB : 0 ≤ max 1 b₁*max 1 b₂ := mul_nonneg
    (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left _ _))
  by_cases h₁ : X₁*b₁ < 1
  · unfold positiveSlotRow
    rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h₁,zero_mul,zero_mul,mul_zero,norm_zero,zero_pow (by decide)]
    exact mul_nonneg hB (sq_nonneg _)
  by_cases h₂ : X₂*b₂ < 1
  · unfold positiveSlotRow
    rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h₂,mul_zero,zero_mul,mul_zero,norm_zero,zero_pow (by decide)]
    exact mul_nonneg hB (sq_nonneg _)
  have hr : clippedScale X₁*clippedScale X₂/(X₁*X₂) ≤ max 1 b₁*max 1 b₂ := by
    have h := mul_le_mul (clipDilation_le b₁ X₁ hX₁ (le_of_not_gt h₁))
      (clipDilation_le b₂ X₂ hX₂ (le_of_not_gt h₂))
      (zero_le_one.trans (clipDilation_ge_one _ hX₂)) (zero_le_one.trans (le_max_left _ _))
    simpa only [clipDilation,div_mul_div_comm] using h
  unfold positiveSlotRow
  rw [retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t X₁ X₂ (X₁*X₂) hX₁ hX₂ (mul_pos hX₁ hX₂)]
  exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)

omit [DecidableEq ι] in
theorem centered_to_retained_uniform_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (b₁ b₂ t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2 ≤
      2*(max 1 b₁*max 1 b₂)*
        (‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2+
         ‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2) := by
  have he : centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T =
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂-
      positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂ := by
    unfold centeredSlotRow positiveSlotRow
    rw [hX,hY]
    ring
  rw [he]
  have hx := retained_rectangle_uniform_energy η m A z W₁ W₂ S β P hP b₁ b₂ t X₁ X₂ hX₁ hX₂ hs₁ hs₂
  have hy := retained_rectangle_uniform_energy η m A z W₁ W₂ S β P hP b₁ b₂ t Y₁ Y₂ hY₁ hY₂ hs₁ hs₂
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le
    (positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
    (positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂)) 2
  nlinarith [sq_nonneg (‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖-
    ‖positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂‖)]

end SevenEighths.CenteredMomentRetainedEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DivisorRetained
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem allocated_to_retained_energy (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
         ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hx : (X₁/Ideal.absNorm (selectedPlain D a 0))*(X₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hX]; rfl
  have hy : (Y₁/Ideal.absNorm (selectedPlain D a 0))*(Y₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hY]; rfl
  have hr := allocated_raw_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hT
  have hc := centered_to_retained_uniform_energy η m A z W₁ W₂
    (fun i : liveIndices D a => S i) (fun i : liveIndices D a => β i)
    (fun i : liveIndices D a => P i) (fun i => hP i) b₁ b₂ t _ _ _ _ _
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))
    hx hy hW₁ hW₂
  have hF : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have hh := mul_le_mul_of_nonneg_left hc (div_nonneg (sq_nonneg (∏ i∈frozenIndices D a,M i)) hF.le)
  apply hr.trans
  convert (preTransparency := .instances) hh using 1 <;> simp only [residualCenteredRow,allocatedPositiveRow] ; ring

end SevenEighths.CenteredMomentDivisorRetained

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ActiveAllocation
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentActiveAllocation
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained
open CenteredMomentSlotRatios CenteredMomentDivisorActualBoundary CenteredMomentDivisorRectangle
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem inactive_zero (η:Character) (m A:O) (t:ℝ) (S:ι→Finset (Ideal O))
    (β:ι→Ideal O→ℂ) (D:Ideal O) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (ha:a∉activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂) (z:O) :
    allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂=0 := by
  by_contra hn
  exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,z,hn⟩)

theorem active_allocated_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
      (D : Ideal O),Squarefree D → ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z ∈ rows,0 ≤ ω z) →
      (∑ z ∈ rows,ω z*‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a ∈ activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
            ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
  obtain ⟨C,hC,hbase⟩:=actual_allocated_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ rows ω hω
  apply (hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ rows ω hω).trans_eq
  congr 1
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a ha hn
  simp only [inactive_zero η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂ a hn,norm_zero,zero_pow (by norm_num:2≠0),mul_zero,Finset.sum_const_zero]

theorem active_raw_to_retained_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)),(∀ i,∀ I∈S i,Prime I) →
      ∀ (β : ι → Ideal O → ℂ) (M P : ι → ℝ),(∀ i,0 ≤ M i) → (∀ i,0 < P i) →
      (∀ i,∀ I∈S i,‖β i I‖ ≤ M i) → ∀ (D : Ideal O),Squarefree D →
      ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z∈rows,0 ≤ ω z) →
      (∑ z∈rows,ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
      C*(Ideal.absNorm D:ℝ)^ε*
        ∑ a ∈ activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
             ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  obtain ⟨C,hC,hbase⟩ := active_allocated_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S hS β M P hM hP hβ D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY rows ω hω
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hh := hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows (fun z => ω z/(T*∏ i,P i))
    (fun z hz => div_nonneg (hω z hz) htotal.le)
  have he (z : O) (x : ℂ) : (ω z/(T*∏ i,P i))*‖x‖^2 =
      ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*x‖^2 := by
    rw [normalized_norm_sq _ htotal]
    ring
  simp_rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hb := mul_le_mul_of_nonneg_left
    (allocated_to_retained_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
      b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY) (hω z hz)
  convert (preTransparency := .instances) hb using 1 ; ring

theorem active_formal_boundary (η : Character) (m A : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hactive : a∈activeAllocations η m A t S
      (fun i I => ν i I*W i ((Ideal.absNorm I:ℝ)/P i)) D W₁ W₂ X₁ X₂ Y₁ Y₂) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
  obtain ⟨z,hz⟩:=(Finset.mem_filter.mp hactive).2
  exact original_nonzero_row_formal_boundary η m A z t S hS ν W lo hi P hlo hP hW
    D hD a W₁ W₂ X₁ X₂ Y₁ Y₂ Z hZ hz

end SevenEighths.CenteredMomentActiveAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ActiveDivisorShell
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentActiveDivisorShell
open HeckeFamily CenteredMomentActiveAllocation CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem Source.active_boundary (s:Source ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.active D) (Z:ℝ) (hZ:1<Z) :
    Real.logb Z (Ideal.absNorm D:ℝ)≤Real.logb Z (formalReductionFactor D a s.P)+s.allowance Z :=
  active_formal_boundary s.η s.m s.A s.t s.slots s.prime s.ν s.W s.lo s.hi s.P s.lo_pos s.P_pos
    s.support D hD a s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ Z hZ ha

theorem reciprocal_sqrt_log (Z x y:ℝ) (hZ:1<Z) (hx:0<x) (hy:0<y) :
    1/Real.sqrt (x*y)=Z^(-(Real.logb Z x+Real.logb Z y)/2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  calc
    _=(x*y)^(-(1/2:ℝ)):=by rw [Real.sqrt_eq_rpow,one_div,Real.rpow_neg (mul_nonneg hx.le hy.le)]
    _=(Z^(Real.logb Z x+Real.logb Z y))^(-(1/2:ℝ)):=by
      rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hx,Real.rpow_logb hz hZ.ne' hy]
    _=_:=by rw [←Real.rpow_mul hz.le]; congr 1; ring

theorem Source.active_pair_weight {κ:Type*} [Fintype κ] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (ha:a∈s.active D) (hb:b∈v.active D) (Z:ℝ) (hZ:1<Z) :
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)≤
      Z^((s.allowance Z+v.allowance Z)/2)/(Ideal.absNorm D:ℝ) := by
  have hs:0<formalReductionFactor D a s.P:=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))
  have hv:0<formalReductionFactor D b v.P:=
    mul_pos (selectedNorm_pos D b) (Finset.prod_pos (fun i _=>v.P_pos i))
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  rw [reciprocal_sqrt_log Z _ _ hZ hs hv]
  have hl:=s.active_boundary D hD a ha Z hZ
  have hr:=v.active_boundary D hD b hb Z hZ
  have he:-(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P))/2≤
      (s.allowance Z+v.allowance Z)/2-Real.logb Z (Ideal.absNorm D:ℝ):=by linarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le he
  rwa [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn] at hp

end SevenEighths.CenteredMomentActiveDivisorShell

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.UniformDivisorShell
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformDivisorShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

theorem subset_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (J:Finset ι) (s:Source J) (lo hi:ι→ℝ) (hlo:∀i:J,s.lo i=lo i) (hhi:∀i:J,s.hi i=hi i)
    (Z:ℝ) (hZ:1<Z) : s.allowance Z≤(∑i,logWindow (lo i) (hi i))/Real.log Z := by
  unfold Source.allowance
  simp_rw [hlo,hhi]
  rw [Finset.sum_coe_sort J (fun i:ι=>logWindow (lo i) (hi i))]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hZ).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>logWindow_nonneg _ _)

theorem numerical_allowance (Z H:ℝ) (hZ:1<Z) : Z^(H/Real.log Z)=Real.exp H := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
  congr 1
  field_simp [(Real.log_pos hZ).ne']

end SevenEighths.CenteredMomentUniformDivisorShell

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.EligibleEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEligibleEnergy
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorRowEnergy
local notation "O" => ActualEisensteinCubic.O

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma Data.child_nonneg (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0≤ s.childEnergy D a :=
  Finset.sum_nonneg (fun z hz=>mul_nonneg (s.weight_nonneg z hz) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

omit [DecidableEq ι] in
lemma Data.profile_nonneg (s:Data ι) : 0≤ s.profileFactor :=by
  unfold Data.profileFactor
  exact mul_nonneg (by positivity) (sq_nonneg _)

lemma Data.reduction_pos (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0<formalReductionFactor D a s.P :=
  mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤E) →
      s.energy D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=active_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s D hD E hE hchild
  have hh:=hbound s.η s.m s.A s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D hD s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos rfl s.same_product s.rows s.weight s.weight_nonneg
  change s.energy D≤_ at hh
  apply hh.trans
  calc
    _≤C*(Ideal.absNorm D:ℝ)^ε*∑a∈s.toSource.active D,
        (s.profileFactor/formalReductionFactor D a s.P)*E:=by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      apply Finset.sum_le_sum
      intro a ha
      have hp:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
        Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
          (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
      apply mul_le_mul _ (hchild a ha) (s.child_nonneg D a) _
      · apply div_le_div_of_nonneg_right _ (s.reduction_pos D a).le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) hp 2
      · exact div_nonneg s.profile_nonneg (s.reduction_pos D a).le
    _=_:=by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

end SevenEighths.CenteredMomentEligibleEnergy

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

 theorem retained_positive_summable {ι:Type*} [Fintype ι]
    (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  unfold retainedPositiveRow positiveSlotRow
  simp_rw [←clipped_rowTwistedSum η m A _ W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A _ W₂ t X₂ hX₂]
  obtain ⟨B,hB⟩:=product_bounded η m A t
    (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem allocated_positive_summable {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (D:Ideal O) (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  have hN (j:Fin 2):(0:ℝ)<Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedPositiveRow
  exact retained_positive_summable η m A t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) _ _ _ keep Φ K hK

end SevenEighths.CenteredMomentPositiveSummability

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentPositiveSummability
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma child_summable (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :
    Summable (fun z:O=>r.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)) := by
  have hX:=allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.slots s.coefficient s.P D a
    r.keep r.profile r.scale r.scale_pos
  have hY:=allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.Y₁_pos s.Y₂_pos s.slots s.coefficient s.P D a
    r.keep r.profile r.scale r.scale_pos
  convert (preTransparency := .instances) hX.add hY using 1
  funext z
  unfold Radial.weight
  split_ifs <;> ring

lemma finite_child_le (s:Data ι) (r:Radial) (S:Finset O) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :
    (finiteData s r S).childEnergy D a≤ childEnergy s r D a := by
  exact sum_le_hasSum S (fun z _=>mul_nonneg (r.weight_nonneg z)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))) (child_summable s r D a).hasSum

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial),∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentEligibleEnergy.actual_source_from_children N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD E hE hchild
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))
  intro S
  exact hbound (finiteData s r S) D hD E hE
    (fun a ha=>(finite_child_le s r S D a).trans (hchild a ha))

end SevenEighths.CenteredMomentRadialEligibleEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RadialPointwiseEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseEnergy
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentSlotRatios CenteredMomentUniformDivisorShell
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma inverse_reduction (s:Data ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.toSource.active D)
    (Z:ℝ) (hZ:1<Z) :
    1/formalReductionFactor D a s.P≤Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ) := by
  have hh:=s.toSource.active_pair_weight s.toSource D hD a a ha ha Z hZ
  rw [show formalReductionFactor D a s.P*formalReductionFactor D a s.P=
    (formalReductionFactor D a s.P)^2 by ring,Real.sqrt_sq (s.reduction_pos D a).le] at hh
  convert (preTransparency := .instances) hh using 1
  congr 2
  ring

 theorem actual_pointwise_divisor (N:ℕ) (hι:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
      ∀E Z:ℝ,0≤E → 1<Z → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
        (s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  obtain ⟨C₁,hC₁,henergy⟩:=CenteredMomentRadialEligibleEnergy.actual_source_from_children N hι ε hε
  obtain ⟨C₂,hC₂,hcard⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s r D hD E Z hE hZ hc
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
  have hsz:((s.toSource.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((s.toSource.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard D hD.ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hs:(∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)≤
      (C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by
    calc
      _≤∑a∈s.toSource.active D,Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ):=
        Finset.sum_le_sum (fun a ha=>inverse_reduction s D hD a ha Z hZ)
      _=((s.toSource.active D).card:ℝ)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by simp
      _≤_:=mul_le_mul_of_nonneg_right hsz (div_nonneg (Real.rpow_nonneg (by linarith) _) hn.le)
  apply (henergy s r D hD E hE hc).trans
  calc
    _≤C₁*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ((C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ))):=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg (mul_nonneg hC₁.le hp) s.profile_nonneg) hE)
    _=_:=by
      have he:(Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε):=by
        rw [←Real.rpow_add hn];congr 1;ring
      calc
        _=(C₁*C₂)*((Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε)*
          Z^(s.toSource.allowance Z)*(s.profileFactor*E)/(Ideal.absNorm D:ℝ):=by ring
        _=_:=by rw [he]

end SevenEighths.CenteredMomentRadialPointwiseEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RadialPointwiseUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseUniform
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentRadialPointwiseEnergy CenteredMomentUniformDivisorShell
open CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

 theorem uniform_subset (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J:Finset ι,Bound J C ε := by
  have he (J:Finset ι):∃C:ℝ,0<C ∧ Bound J C ε:=
    actual_pointwise_divisor (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose C hC hb using he
  let D:ℝ:=1+∑J:Finset ι,C J
  have hs:0≤∑J:Finset ι,C J:=Finset.sum_nonneg (fun J _=>(hC J).le)
  refine ⟨D,by dsimp [D];linarith,?_⟩
  intro J s r I hI E Z hE hZ hc
  have hd:C J≤D:=by
    have hh:=Finset.single_le_sum (fun J _=>(hC J).le) (Finset.mem_univ J)
    dsimp [D];linarith
  apply (hb J s r I hI E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (Nat.cast_nonneg _) _)

 theorem actual_uniform_divisor_oai (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J:Finset ι) (s:Data J),(∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      ∀(r:Radial) (D:Ideal O),Squarefree D → ∀E Z:ℝ,0≤E → 1<Z →
      (Ideal.absNorm D:ℝ)≤Z^B → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*Z^δ*(s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  obtain ⟨C,hC,hbound⟩:=uniform_subset (ι:=ι) ε hε
  let A:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*A,by dsimp [A];positivity,?_⟩
  intro J s hlo hhi r D hD E Z hE hZ hN hc
  have hz:0<Z:=zero_lt_one.trans hZ
  have ha:Z^(s.toSource.allowance Z)≤A:=by
    dsimp [A]
    rw [←numerical_allowance Z _ hZ]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (subset_allowance J s.toSource lo hi hlo hhi Z hZ)
  have hp:(Ideal.absNorm D:ℝ)^(2*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have he:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  apply (hbound J s r D hD E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  calc
    _≤C*Z^δ*A:=mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) ha
      (Real.rpow_nonneg hz.le _) (by positivity)
    _=_:=by ring

end SevenEighths.CenteredMomentRadialPointwiseUniform

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentRadialPointwiseUniform.actual_uniform_divisor_oai.{u_1} := @OAI.SevenEighths.CenteredMomentRadialPointwiseUniform.actual_uniform_divisor_oai.{u_1}
