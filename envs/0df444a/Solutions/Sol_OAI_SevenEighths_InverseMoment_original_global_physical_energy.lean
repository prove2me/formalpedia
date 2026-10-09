-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.original_global_physical_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:56:59.688968+00:00
-- url     : https://prove2.me/submissions/22714f2f-330f-496b-b356-c89353a65776

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B009
import Theorems.Thm_OAI_SevenEighths_InverseMoment_canonical_first_physical_split

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.LocalProductAssembly
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

open ConcreteTraceCRT
open scoped ComplexConjugate

theorem canonicalSextic_inverse_eq_conj_on_units (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) (u : (O ⧸ P)ˣ) :
    (canonicalSextic P hgood (u : O ⧸ P))⁻¹ =
      star (canonicalSextic P hgood (u : O ⧸ P)) := by
  let χ := canonicalSextic P hgood
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hval : χ (u : O ⧸ P) ^ 6 = 1 := by
    rw [← χ.pow_apply_coe 6 u, hχ6, MulChar.one_apply_coe]
  exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hval (by decide))

end ActualEisensteinCubic

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

section

open scoped ComplexConjugate

theorem canonicalSextic_conj_as_row_label
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (e : O) :
    star (canonicalSextic P hgood (Ideal.Quotient.mk P e)) =
      canonicalSextic P hgood (Ideal.Quotient.mk P e) *
        (canonicalSextic P hgood (Ideal.Quotient.mk P e)) ^ 4 := by
  let χ := canonicalSextic P hgood
  let x : O ⧸ P := Ideal.Quotient.mk P e
  have hconj : star (χ x) = (χ x)⁻¹ := by
    by_cases hx : IsUnit x
    · let u : (O ⧸ P)ˣ := hx.unit
      have hu : (u : O ⧸ P) = x := hx.unit_spec
      rw [← hu]
      exact (canonicalSextic_inverse_eq_conj_on_units P hgood u).symm
    · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
      simp [hzero]
  rw [hconj]
  by_cases hx : IsUnit x
  · have h6 : (χ x) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0),
        canonicalSextic_pow_six P hgood]
      exact MulChar.one_apply hx
    apply inv_eq_of_mul_eq_one_right
    calc
      χ x * (χ x * (χ x) ^ 4) = (χ x) ^ 6 := by ring
      _ = 1 := h6
  · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
    change (χ x)⁻¹ = χ x * (χ x) ^ 4
    simp [hzero]

end

end ActualEisensteinCubic

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
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

namespace ActualEisensteinCubic

theorem canonicalSextic_sq_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 := by
  have hP2 : (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hPgood (Ideal.Quotient.mk P q)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  have hQ2 : (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar Q hQgood (Ideal.Quotient.mk Q p)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  rw [hP2, hQ2, cubic_reciprocity_primary P Q hPgood hQgood p q hP hQ hpprimary hqprimary]

end ActualEisensteinCubic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
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
namespace FirstPassCubeLabels
open ActualEisensteinCubic

section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem row_pow (a : O) (m : ℕ) :
    finiteSquarefreeRow P hg S (a ^ m) = finiteSquarefreeRow P hg S a ^ m := by
  simp only [finiteSquarefreeRow, map_pow, Finset.prod_pow]

theorem row_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    finiteSquarefreeRow P hg S (∏ j ∈ B, a j) =
      ∏ j ∈ B, finiteSquarefreeRow P hg S (a j) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [finiteSquarefreeRow]
  | @insert j B hj ih =>
    simp only [Finset.prod_insert hj, finiteSquarefreeRow_mul, ih]

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

theorem mask_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    rowCoprimeMask P S (∏ j ∈ B, a j) = ∏ j ∈ B, rowCoprimeMask P S (a j) := by
  rw [← row_sixth P hg S, row_prod, ← Finset.prod_pow]
  simp only [row_sixth]

end Rows

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
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
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss canonicalProductGauss_cross_factors)
open MixedGaussConversion (localGauss)

theorem canonicalProductGauss_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ S, e i ≠ 0) :
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) =
      gaussBlock p hp hg S e := by
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  have hin (i : S) :
      (∏ k ∈ (Finset.univ : Finset S).erase i,
        (canonicalSextic (Ideal.span {p i.val}) (hg i.val) ^ e i.val)
          (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) =
      ∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val := by
    apply Finset.prod_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h), k.property⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro k hk
      refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h),
        Finset.mem_univ _⟩
    · intro k hk
      exact MulChar.pow_apply' _ (he i.val i.property) _
  calc
    _ = ∏ i : S, (∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val) *
        localGauss (p i.val) (hp i.val) (hg i.val) (e i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hin i]
      rfl
    _ = _ := Finset.prod_coe_sort S (fun i =>
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) * localGauss (p i) (hp i) (hg i) (e i))

theorem gaussBlock_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) :
    gaussBlock p hp hg (S ∪ T) e =
      gaussBlock p hp hg S e * gaussBlock p hp hg T e * blockCross p hg S T e := by
  have hS (i : ι) (hi : i ∈ S) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ T, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ T := fun h => Finset.disjoint_left.mp hd hi h
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hT (i : ι) (hi : i ∈ T) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ T.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ S, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ S := fun h => Finset.disjoint_left.mp hd h hi
    rw [Finset.union_comm S T, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpS : (∏ i ∈ S, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg S e * (∏ i ∈ S, ∏ k ∈ T, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hS i hi]
    ring
  have hpT : (∏ i ∈ T, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg T e * (∏ i ∈ T, ∏ k ∈ S, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hT i hi]
    ring
  rw [gaussBlock, Finset.prod_union hd, hpS, hpT,
    Finset.prod_comm (s := T) (t := S)]
  simp only [blockCross, Finset.prod_mul_distrib]
  ring

theorem columnCoefficient_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg S =
      star (FiniteGaussPhase.angularFactor (∏ i ∈ S, p i)) *
        gaussBlock p hp hg S (fun _ => 2) := by
  unfold MixedCrossSeparation.columnCoefficient FiniteGaussPhase.canonicalProductCoefficient
  rw [Finset.prod_coe_sort]
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg S (fun _ => 2) (fun _ _ => by decide)]

theorem blockCross_two_eq_row_four {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    blockCross p hg S T (fun _ => 2) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  simp only [blockCross, finiteSquarefreeRow, map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  change crossSymbol p hg i k ^ 2 * crossSymbol p hg k i ^ 2 = crossSymbol p hg i k ^ 4
  rw [← hr]
  ring

theorem columnCoefficient_union_row_four {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg (S ∪ T) =
      MixedCrossSeparation.columnCoefficient p hp hcop hg S *
        MixedCrossSeparation.columnCoefficient p hp hcop hg T *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  have ha : FiniteGaussPhase.angularFactor (∏ i ∈ S ∪ T, p i) =
      FiniteGaussPhase.angularFactor (∏ i ∈ S, p i) *
        FiniteGaussPhase.angularFactor (∏ i ∈ T, p i) := by
    rw [Finset.prod_union hd]
    simp only [FiniteGaussPhase.angularFactor, map_mul, norm_mul, Complex.ofReal_mul,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [columnCoefficient_eq_gaussBlock, columnCoefficient_eq_gaussBlock,
    columnCoefficient_eq_gaussBlock, ha, star_mul, gaussBlock_union p hp hg S T hd,
    blockCross_two_eq_row_four p hg hpr S T]
  ring

end FirstPassCubeLabels

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator
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
namespace FirstPassCubeLabels
open ActualEisensteinCubic

theorem conductorExponent_val (parityBit ε₁ ε₂ : Bool) :
    (conductorExponent parityBit ε₁ ε₂).val = (bit ε₁ + 5 * bit ε₂ + 3 * bit parityBit) % 6 := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

theorem cube_pair_exponent_mod (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) :
    (bit ε₁ + 5 * bit ε₂ + 3 * m₁ + 15 * m₂) % 6 =
      (conductorExponent (parity (m₁ + m₂)) ε₁ ε₂).val := by
  have hmod := Nat.mod_lt (m₁ + m₂) (by decide : 0 < 2)
  rw [conductorExponent_val]
  cases ε₁ <;> cases ε₂ <;> by_cases h : (m₁ + m₂) % 2 = 1 <;>
    norm_num [parity, bit, h] <;> omega

theorem cubePairLocal_eq_character
    (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m₁ + m₂ + bit ε₁ + bit ε₂) (z : O) :
    cubePairLocal P hg m₁ m₂ ε₁ ε₂ z =
      (canonicalSextic P hg ^ (conductorExponent (parity (m₁ + m₂)) ε₁ ε₂).val)
        (Ideal.Quotient.mk P z) := by
  let q := canonicalSextic P hg (Ideal.Quotient.mk P z)
  have hstar : star q = q ^ 5 := by
    have hs := canonicalSextic_conj_as_row_label P hg z
    change star q = q * q ^ 4 at hs
    rw [hs]
    ring
  have hleft : cubePairLocal P hg m₁ m₂ ε₁ ε₂ z =
      q ^ (bit ε₁ + 5 * bit ε₂ + 3 * m₁ + 15 * m₂) := by
    change q ^ bit ε₁ * star (q ^ bit ε₂) * q ^ (3 * m₁) * star (q ^ (3 * m₂)) = _
    simp only [star_pow, hstar, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hleft]
  by_cases hz : z ∈ P
  · have hq : q = 0 := by
      change canonicalSextic P hg (Ideal.Quotient.mk P z) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
    rw [hq, Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
    exact zero_pow (by omega)
  · have hu : IsUnit (Ideal.Quotient.mk P z) := by
      let : Field (O ⧸ P) := Ideal.Quotient.field P
      exact isUnit_iff_ne_zero.mpr (fun h => hz (Ideal.Quotient.eq_zero_iff_mem.mp h))
    have h6 : q ^ 6 = 1 := by
      have h := canonicalSextic_sixth_power_mask P hg z
      simp only [map_pow, if_neg hz] at h
      exact h
    rw [pow_eq_pow_mod _ h6, cube_pair_exponent_mod]
    exact (MulChar.pow_apply_coe _ _ hu.unit).symm

private theorem row_filter_eq_power_product {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hg : ∀ j, lambda ∉ P j)
    (B : Finset κ) (ε : κ → Bool) (z : O) :
    finiteSquarefreeRow P hg (B.filter fun j => ε j) z =
      ∏ j ∈ B, canonicalSextic (P j) (hg j) (Ideal.Quotient.mk (P j) z) ^ bit (ε j) := by
  simp only [finiteSquarefreeRow, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  cases ε j <;> simp [bit]

theorem cubePairRow_eq_product {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hg : ∀ j, lambda ∉ P j)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) (z : O) :
    cubePairRow P hg B v₁ v₂ ε₁ ε₂ z =
      ∏ j ∈ B, cubePairLocal (P j) (hg j) (v₁ j) (v₂ j) (ε₁ j) (ε₂ j) z := by
  simp only [cubePairRow, row_filter_eq_power_product, multiplicityRow,
    ← Finset.prod_pow, star_prod, ← Finset.prod_mul_distrib, ← pow_mul]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [cubePairLocal, Nat.mul_comm]

private theorem principal_product_eq_mask {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (B : Finset κ) (z : O) :
    (∏ j ∈ B, (1 : MulChar (O ⧸ P j) ℂ) (Ideal.Quotient.mk (P j) z)) =
      rowCoprimeMask P B z := by
  by_cases h : ∃ j ∈ B, z ∈ P j
  · rw [rowCoprimeMask, if_pos h]
    obtain ⟨j, hj, hz⟩ := h
    apply Finset.prod_eq_zero hj
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
  · rw [rowCoprimeMask, if_neg h]
    apply Finset.prod_eq_one
    intro j hj
    apply MulChar.one_apply
    let : Field (O ⧸ P j) := Ideal.Quotient.field (P j)
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => h ⟨j, hj, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩

theorem cubePairRow_conductor_selection {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hg : ∀ j, lambda ∉ P j)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hcover : ∀ j ∈ B, 0 < v₁ j + v₂ j + bit (ε₁ j) + bit (ε₂ j)) (z : O) :
    cubePairRow P hg B v₁ v₂ ε₁ ε₂ z =
      rowCoprimeMask P (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
        finiteSexticRow (fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val)
          (fun j => hg j.val)
          (fun j => (conductorExponent (parity (v₁ j.val + v₂ j.val))
            (ε₁ j.val) (ε₂ j.val)).val) z := by
  let e := fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j)
  let f := fun j => (canonicalSextic (P j) (hg j) ^ (e j).val) (Ideal.Quotient.mk (P j) z)
  have hlocal : cubePairRow P hg B v₁ v₂ ε₁ ε₂ z = ∏ j ∈ B, f j := by
    rw [cubePairRow_eq_product]
    apply Finset.prod_congr rfl
    intro j hj
    exact cubePairLocal_eq_character (P j) (hg j) (v₁ j) (v₂ j)
      (ε₁ j) (ε₂ j) (hcover j hj) z
  have hzero : (∏ j ∈ B.filter (fun j => e j = 0), f j) =
      rowCoprimeMask P (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro j hj
    have he : e j = 0 := (Finset.mem_filter.mp hj).2
    simp only [f, he, ZMod.val_zero, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B (fun j => e j = 0) f, hzero]
  congr 1
  exact (Finset.prod_coe_sort (s := cubeConductorSupport B v₁ v₂ ε₁ ε₂) (f := f)).symm

open scoped SchwartzMap ContDiff
open ConcreteTraceCRT
open EisensteinSchwartzPoisson (paperRadialFourier)

end FirstPassCubeLabels

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets
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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (columnPrimeCoprime quadraticCrossPhase)
open FiniteGaussPhase (canonicalProductGauss)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem blockRow_eq_product {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) :
    blockRow p hg S e u = ∏ i ∈ S,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u) :=
  Finset.prod_coe_sort S (fun i =>
    (canonicalSextic (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u))

theorem blockRow_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) (u : O) :
    blockRow p hg (S ∪ T) e u = blockRow p hg S e u * blockRow p hg T e u := by
  simp only [blockRow_eq_product, Finset.prod_union hd]

theorem blockRow_congr {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e f : ι → ℕ)
    (hef : ∀ i ∈ S, e i = f i) (u : O) : blockRow p hg S e u = blockRow p hg S f u := by
  simp only [blockRow_eq_product]
  exact Finset.prod_congr rfl (fun i hi => by rw [hef i hi])

theorem blockRow_one {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (u : O) :
    blockRow p hg S (fun _ => 1) u = finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u := by
  simp only [blockRow_eq_product, pow_one, finiteSquarefreeRow]

theorem blockRow_five {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (u : O) :
    blockRow p hg S (fun _ => 5) u = star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u) := by
  simp only [blockRow_eq_product, finiteSquarefreeRow, star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0), canonicalSextic_conj_as_row_label]
  ring

theorem threeBlockRow_factor {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (u : O) :
    blockRow p hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) u =
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N u) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P u *
      blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
        (fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) u := by
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) := hPB.mono_right (Finset.filter_subset _ _)
  have hN : ∀ i ∈ N, threeBlockExponent N P v ε₁ ε₂ i = 5 := by
    intro i hi; simp [threeBlockExponent, hi]
  have hP : ∀ i ∈ P, threeBlockExponent N P v ε₁ ε₂ i = 1 := by
    intro i hi
    simp [threeBlockExponent, hi, show i ∉ N from fun hn => Finset.disjoint_left.mp hNP hn hi]
  have hC : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂, threeBlockExponent N P v ε₁ ε₂ i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    intro i hi
    simp [threeBlockExponent,
      show i ∉ N from fun hn => Finset.disjoint_left.mp hNC hn hi,
      show i ∉ P from fun hp => Finset.disjoint_left.mp hPC hp hi]
  rw [blockRow_union p hg (N ∪ P) _ (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩),
    blockRow_union p hg N P hNP, blockRow_congr p hg N _ _ hN,
    blockRow_congr p hg P _ _ hP, blockRow_congr p hg _ _ _ hC,
    blockRow_five, blockRow_one]

end FirstPassCubeLabels

open scoped Classical BigOperators
open AddChar MulChar

open scoped Classical BigOperators
open AddChar MulChar

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy
namespace OAI

noncomputable section

namespace FirstPassCubeLabels

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

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)

section Local
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i)

theorem row_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    finiteSquarefreeRow P hg (S ∪ T) a =
      finiteSquarefreeRow P hg S a * finiteSquarefreeRow P hg T a := by
  exact Finset.prod_union hd

include hg in
theorem mask_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    rowCoprimeMask P (S ∪ T) a = rowCoprimeMask P S a * rowCoprimeMask P T a := by
  simp only [← row_sixth P hg, row_union P hg S T hd, mul_pow]

end Local

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FourierBridge (logPhase)

end FirstPassCubeLabels

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

open scoped BigOperators
namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

lemma join_split (ST : Finset ι × Finset ι) : join (split ST) = ST := by
  apply Prod.ext
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto

lemma split_mem {F : Finset ι} {ST : Finset ι × Finset ι}
    (hST : ST ∈ F.powerset ×ˢ F.powerset) : split ST ∈ triples F := by
  rcases Finset.mem_product.mp hST with ⟨hS, hT⟩
  have hSF := Finset.mem_powerset.mp hS
  have hTF := Finset.mem_powerset.mp hT
  simp only [triples, split, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨Finset.inter_subset_left.trans hSF, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hSF hi.1, by tauto⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hTF hi.1, by tauto⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1

lemma join_mem {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    join GUV ∈ F.powerset ×ˢ F.powerset := by
  rcases (by simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
    Finset.mem_product, Finset.mem_powerset] using h) with ⟨hG, ⟨hU, hV⟩, _⟩
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_powerset.mpr
  · exact Finset.union_subset hG (hU.trans Finset.sdiff_subset)
  · exact Finset.union_subset hG (hV.trans Finset.sdiff_subset)

lemma split_join {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    split (join GUV) = GUV := by
  rcases GUV with ⟨G, U, V⟩
  have hh : G ⊆ F ∧ (U ⊆ F \ G ∧ V ⊆ F \ G) ∧ Disjoint U V := by
    simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_product, Finset.mem_powerset] using h
  rcases hh with ⟨_, ⟨hU, hV⟩, hd⟩
  have hUG : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hU hi)).2 hg)
  have hVG : Disjoint V G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hV hi)).2 hg)
  have h₀ : (G ∪ U) ∩ (G ∪ V) = G := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have h₁ : (G ∪ U) \ (G ∪ V) = U := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    have hj : i ∈ U → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hUG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have h₂ : (G ∪ V) \ (G ∪ U) = V := by
    ext i
    have hi : i ∈ V → i ∈ U → False := fun hi hj => Finset.disjoint_left.mp hd.symm hi hj
    have hj : i ∈ V → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hVG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  simp only [split, join, h₀, h₁, h₂]

theorem sum_pair_eq_overlap {β : Type*} [AddCommMonoid β]
    (F : Finset ι) (C : Finset ι → Finset ι → β) :
    (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, C S T) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then C (G ∪ U) (G ∪ V) else 0 := by
  classical
  have hs : (∑ ST ∈ F.powerset ×ˢ F.powerset, C ST.1 ST.2) =
      ∑ GUV ∈ triples F, C (join GUV).1 (join GUV).2 := by
    apply Finset.sum_bij (fun ST _ => split ST)
    · intro ST hST
      exact split_mem hST
    · intro ST hST SU hSU heq
      have hh := congrArg join heq
      simpa only [join_split] using hh
    · intro GUV hGUV
      exact ⟨join GUV, join_mem hGUV, split_join hGUV⟩
    · intro ST hST
      rw [join_split]
  simpa only [triples, Finset.sum_sigma, Finset.sum_filter, Finset.sum_product, join] using hs

end FiniteOverlapDecomposition

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ChildTransfer
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem commonProduct_mask
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (U G : Finset ι) :
    rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) =
      if Disjoint U G then 1 else 0 := by
  by_cases hd : Disjoint U G
  · rw [if_pos hd, FirstPassCubeLabels.mask_prod _ hg U G p]
    apply Finset.prod_eq_one
    intro j hj
    have hh : ¬ ∃ i ∈ U, p j ∈ Ideal.span {p i} := by
      rintro ⟨i, hi, hpi⟩
      have hij : i ≠ j := fun he => Finset.disjoint_left.mp hd hi (he ▸ hj)
      exact (prime_generator_not_mem_of_ne (Ideal.span {p i}) (Ideal.span {p j})
        (fun he => hij (hinj he)) (p j) rfl) hpi
    simp [rowCoprimeMask, hh]
  · rw [if_neg hd]
    obtain ⟨i, hiU, hiG⟩ := Finset.not_disjoint_iff.mp hd
    have hh : ∃ j ∈ U, (∏ i ∈ G, p i) ∈ Ideal.span {p j} :=
      ⟨i, hiU, Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hiG)⟩
    simp [rowCoprimeMask, hh]

end

open ActualEisensteinCubic

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeCoreCoefficient cubeOddSupport coreRayCoefficient coreRayTwist
  coreRayCharacter dilatedCoreRow dilatedRayColumn afterDilationLabel b0Label jLabel)
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RowMajorants
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
namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

lemma rowMajorant_one (s : ℝ) (hs : |s| ≤ 1) : rowMajorant s = 1 :=
  (Classical.choose_spec exists_rowMajorant).2.1 s hs

lemma rowMajorant_zero (s : ℝ) (hs : 2 < s) : rowMajorant s = 0 :=
  (Classical.choose_spec exists_rowMajorant).2.2 s hs

lemma rowMajorant_zero_outside (Y : ℝ) (hY : 0 < Y) (z : O)
    (hz : z ∉ rowMajorantBall Y) : rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) = 0 := by
  have hn : Nat.ceil (2 * Y) < Ideal.absNorm (Ideal.span {z}) := by
    apply Nat.lt_of_not_ge
    intro hn
    exact hz (ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le _ z hn)
  have hn' : (Nat.ceil (2 * Y) : ℝ) < (Ideal.absNorm (Ideal.span {z}) : ℝ) := by exact_mod_cast hn
  apply rowMajorant_zero
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  apply (lt_div_iff₀ hY).2
  linarith [Nat.le_ceil (2 * Y)]

lemma rowMajorant_summable (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz, zero_mul]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

open MeasureTheory Set Module
open scoped BigOperators Classical ENNReal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyBlocks
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportConjugateSum supportMobius)
open RayFourExpansion (RayCharacter)

theorem nonzeroRowMajorantSum_eq_sub (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum P Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) -
        (↑(‖P 0‖ ^ 2) : ℂ) := by
  have h := (rowMajorant_summable P Y hY).tsum_eq_add_tsum_ite 0
  have h0 : rowMajorant (0 : ℝ) = 1 := rowMajorant_one 0 (by norm_num)
  simp only [map_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, h0, one_mul] at h
  change _ = _ + nonzeroRowMajorantSum P Y at h
  rw [h]
  ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs
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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm )
open ConcreteTraceCRT (eisEmbedding)

theorem mem_secondFrequencyCutoff (scale H : ℝ) (k : O)
    (hk : ‖eisEmbedding k‖^2 ≤ H/scale) : k ∈ secondFrequencyCutoff scale H := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hk
  exact_mod_cast hk.trans (Nat.le_ceil (H/scale))

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog jLabel b0Label )
open JointLogSeparation (tripleCoefficient)

end SecondPassArithmetic

open scoped BigOperators Classical

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

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm squarefreeLabel jLabel j2Label b0Label
  bit parity conductorExponent cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_ne_zero (B : Finset ι) (v : ι → ℕ) : primeProduct p B v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi => pow_ne_zero _ (hp i))

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.GlobalEncoding
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

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel b0Label jLabel cubeActiveSupport primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

namespace CubeCoordinates
variable {ι : Type*} [DecidableEq ι]

theorem support_pos (x : CubeCoordinates ι) (i : ι) (hi : i ∈ x.support) :
    0 < x.leftExponent i+x.rightExponent i := by
  simp only [support,Finset.mem_union,Finsupp.mem_support_iff] at hi
  omega

end CubeCoordinates

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource
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

open scoped BigOperators
namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

theorem sum_powerset_split {β : Type*} [AddCommMonoid β]
    (F B : Finset ι) (hB : B⊆F) (f : Finset ι→β) :
    (∑S∈F.powerset,f S)=∑A∈B.powerset,∑U∈(F\B).powerset,f (A∪U) := by
  have hsplit (S : Finset ι) : S∩B∪S\B=S := by
    ext i
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have he : (∑S∈F.powerset,f S)=
      ∑AU∈B.powerset ×ˢ (F\B).powerset,f (AU.1∪AU.2) := by
    apply Finset.sum_bij (fun S _ => (S∩B,S\B))
    · intro S hS
      rw [Finset.mem_product,Finset.mem_powerset,Finset.mem_powerset]
      refine ⟨Finset.inter_subset_right,?_⟩
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) (Finset.mem_sdiff.mp hi).1,(Finset.mem_sdiff.mp hi).2⟩
    · intro S hS T hT he
      have hi := congrArg (fun AU : Finset ι×Finset ι => AU.1∪AU.2) he
      simpa only [hsplit] using hi
    · intro AU hAU
      rcases Finset.mem_product.mp hAU with ⟨hA,hU⟩
      have hAB := Finset.mem_powerset.mp hA
      have hUFB := Finset.mem_powerset.mp hU
      refine ⟨AU.1∪AU.2,Finset.mem_powerset.mpr (Finset.union_subset (hAB.trans hB) (hUFB.trans Finset.sdiff_subset)),?_⟩
      apply Prod.ext <;> ext i
      · have h1 : i∈AU.1 → i∈B := fun hi => hAB hi
        have h2 : i∈AU.2 → i∉B := fun hi => (Finset.mem_sdiff.mp (hUFB hi)).2
        simp only [Finset.mem_inter,Finset.mem_union]
        tauto
      · have h1 : i∈AU.1 → i∈B := fun hi => hAB hi
        have h2 : i∈AU.2 → i∉B := fun hi => (Finset.mem_sdiff.mp (hUFB hi)).2
        simp only [Finset.mem_sdiff,Finset.mem_union]
        tauto
    · intro S hS
      rw [hsplit]
  simpa only [Finset.sum_product] using he

theorem sum_pair_split_cube {β : Type*} [AddCommMonoid β]
    (F B : Finset ι) (hB : B⊆F) (f : Finset ι→Finset ι→β) :
    (∑S∈F.powerset,∑T∈F.powerset,f S T)=
      ∑A₂∈B.powerset,∑A₁∈B.powerset,∑C∈(F\B).powerset,
        ∑N∈((F\B)\C).powerset,∑P∈((F\B)\C).powerset,
          if Disjoint N P then f ((A₂∪C)∪N) ((A₁∪C)∪P) else 0 := by
  rw [sum_powerset_split F B hB]
  apply Finset.sum_congr rfl
  intro A₂ hA₂
  simp_rw [sum_powerset_split F B hB]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A₁ hA₁
  rw [sum_pair_eq_overlap]
  simp only [Finset.union_assoc]

end FiniteOverlapDecomposition

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

theorem canonicalSourceCoefficient_union
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (D S : Finset ι) (hd : Disjoint D S) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f H (D∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) D *
      (columnCoefficient p hp hcop hg S *
        multiplicativeCoreColumn p Ψ m (fun U => H (D∪U)) S *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏i∈D,p i)^4 *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f^4) := by
  have hA := columnCoefficient_union_row_four p hp hcop hg hpr S D hd.symm
  rw [Finset.union_comm S D] at hA
  simp only [canonicalSourceCoefficient,hA,Finset.prod_union hd,map_mul,
    row_union _ hg D S hd,mask_union _ hg D S hd,mul_pow,multiplicativeCoreColumn]
  ring

theorem canonicalCube_pair_row
    (B C N P : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hcover : ∀ i∈B,0<v₁ i+v₂ i)
    (hCB : Disjoint C B) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N B) (hPB : Disjoint P B) (hNP : Disjoint N P)
    (z : O) :
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg
      (((B.filter fun i => ε₂ i)∪C)∪N) z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg
        (((B.filter fun i => ε₁ i)∪C)∪P) z *
      star (multiplicityRow (fun i => Ideal.span {p i}) hg B v₂ z^3) *
      multiplicityRow (fun i => Ideal.span {p i}) hg B v₁ z^3 =
    rowCoprimeMask (fun i => Ideal.span {p i})
      (C∪cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
    blockRow p hg ((N∪P)∪cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
      (threeBlockExponent N P (fun i => v₁ i+v₂ i) ε₁ ε₂) z := by
  have hA₁C : Disjoint (B.filter fun i => ε₁ i) C := hCB.symm.mono_left (Finset.filter_subset _ _)
  have hA₂C : Disjoint (B.filter fun i => ε₂ i) C := hCB.symm.mono_left (Finset.filter_subset _ _)
  have hA₁P : Disjoint (B.filter fun i => ε₁ i) P := hPB.symm.mono_left (Finset.filter_subset _ _)
  have hA₂N : Disjoint (B.filter fun i => ε₂ i) N := hNB.symm.mono_left (Finset.filter_subset _ _)
  have hCp : Disjoint C (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) :=
    hCB.mono_right (Finset.filter_subset _ _)
  have hsel : cubePairRow (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂ z =
      rowCoprimeMask (fun i => Ideal.span {p i}) (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
      blockRow p hg (cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
        (fun i => (conductorExponent (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i)).val) z := by
    exact cubePairRow_conductor_selection (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂
      (fun i hi => by have := hcover i hi;omega) z
  rw [row_union _ hg _ N (Finset.disjoint_union_left.mpr ⟨hA₂N,hNC.symm⟩),
    row_union _ hg _ P (Finset.disjoint_union_left.mpr ⟨hA₁P,hPC.symm⟩),
    row_union _ hg _ C hA₂C,row_union _ hg _ C hA₁C]
  simp only [star_mul]
  calc
    _ = (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg C z)*
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg C z)*
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N z)*
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P z)*
      cubePairRow (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂ z := by
        simp only [cubePairRow];ring
    _ = _ := by
      rw [ActualEisensteinCubic.finiteSquarefreeRow_self_pair (fun i => Ideal.span {p i}) hg C z,
        hsel,
        threeBlockRow_factor p hg N P B hNP hNB hPB,
        mask_union _ hg C _ hCp]
      ring

theorem canonicalSourceCoefficient_cube_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (B C S : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (hCB : Disjoint C B) (hSC : Disjoint S C) (hSB : Disjoint S B) :
    let A := B.filter (fun i => if negative then ε₂ i else ε₁ i)
    canonicalSourceCoefficient p hp hcop hg Ψ m f H ((A∪C)∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) (A∪C) *
      (columnCoefficient p hp hcop hg S *
        originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => H ((A∪C)∪U)))
          (∏i∈C,p i) f S) := by
  dsimp only
  have hAC : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) C :=
    hCB.symm.mono_left (Finset.filter_subset _ _)
  have hAS : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) S :=
    hSB.symm.mono_left (Finset.filter_subset _ _)
  rw [canonicalSourceCoefficient_union p hp hcop hg hpr Ψ m f H _ S
    (Finset.disjoint_union_left.mpr ⟨hAS,hSC.symm⟩)]
  have hA : (∏i∈B.filter (fun i => if negative then ε₂ i else ε₁ i),p i) =
      aLabel p B (if negative then ε₂ else ε₁) := by
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,aLabel,primeProduct,
      Finset.prod_filter,bit]
    all_goals
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> simp_all
  rw [Finset.prod_union hAC,hA]
  simp only [originalLabelColumn,cubeRadical,commonProduct_mask p hg hinj S B,if_pos hSB,mul_one]
  ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open MixedCrossSeparation (columnCoefficient)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma cube_filter_left (b : CubeCoordinates ι) (hb : b.Admissible) :
    b.support.filter (fun i=>b.leftBit i)=b.leftDivisor := by
  ext i
  simp only [CubeCoordinates.leftBit,Finset.mem_filter,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi=>hb.1 hi)

lemma cube_filter_right (b : CubeCoordinates ι) (hb : b.Admissible) :
    b.support.filter (fun i=>b.rightBit i)=b.rightDivisor := by
  ext i
  simp only [CubeCoordinates.rightBit,Finset.mem_filter,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi=>hb.2 hi)

theorem canonicalCubeSourcePair_factor
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1)
    (b : CubeCoordinates ι) (hb : b.Admissible) (C N P : Finset ι)
    (hCB : Disjoint C b.support) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N b.support) (hPB : Disjoint P b.support) (hNP : Disjoint N P)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeSourcePair p hp hcop hg b.support ((b.rightDivisor∪C)∪N) ((b.leftDivisor∪C)∪P)
      b.leftExponent b.rightExponent Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
    canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
      (star (columnCoefficient p hp hcop hg N*canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁ N)*
        (columnCoefficient p hp hcop hg P*canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂ P))*
      ∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i})
        (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit) z*
        blockRow p hg ((N∪P)∪cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
          (threeBlockExponent N P (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) z*
        W (‖eisEmbedding z‖^2/K) := by
  have hN := canonicalSourceCoefficient_cube_split p hp hcop hg hinj hpr Ψ₁ m₁ f H₁
    b.support C N b.leftBit b.rightBit true hCB hNC hNB
  have hP := canonicalSourceCoefficient_cube_split p hp hcop hg hinj hpr Ψ₂ m₂ f H₂
    b.support C P b.leftBit b.rightBit false hCB hPC hPB
  simp only [Bool.false_eq_true,ite_true,ite_false,cube_filter_left b hb,cube_filter_right b hb] at hN hP
  have hz (z : O) := canonicalCube_pair_row p hg b.support C N P b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos hCB hNC hPC hNB hPB hNP z
  simp only [cube_filter_left b hb,cube_filter_right b hb] at hz
  simp only [canonicalCubeSourcePair,hN,hP,star_mul,canonicalCubeOuter,canonicalCubeResidual]
  simp only [Bool.false_eq_true,ite_true,ite_false]
  simp_rw [hz]
  ring

theorem canonicalCubeCorrelation_eq_blocks
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1) (pool : Finset ι) (v₁ v₂ : ι→₀ℕ)
    (hB : v₁.support∪v₂.support⊆pool)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      ∑A₂∈(v₁.support∪v₂.support).powerset,∑A₁∈(v₁.support∪v₂.support).powerset,
        ∑C∈(pool\(v₁.support∪v₂.support)).powerset,
          canonicalCubeBeforePoisson p hp hcop hg pool ⟨v₁,v₂,A₁,A₂⟩ C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K := by
  unfold canonicalCubeCorrelation
  rw [FiniteOverlapDecomposition.sum_pair_split_cube pool _ hB]
  apply Finset.sum_congr rfl
  intro A₂ hA₂
  apply Finset.sum_congr rfl
  intro A₁ hA₁
  apply Finset.sum_congr rfl
  intro C hC
  let b : CubeCoordinates ι:=⟨v₁,v₂,A₁,A₂⟩
  have hb : b.Admissible:=⟨Finset.mem_powerset.mp hA₁,Finset.mem_powerset.mp hA₂⟩
  have hCB : Disjoint C b.support := Finset.disjoint_left.mpr (fun i hiC hiB =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hiC)).2 hiB)
  have hpool : (pool\(v₁.support∪v₂.support))\C=pool\(b.support∪C) := by
    ext i
    simp only [CubeCoordinates.support,b,Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hpool]
  change _=canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K
  simp only [canonicalCubeBeforePoisson,disjointCanonicalSource,Finset.mul_sum,one_mul]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    have hNC : Disjoint N C:=Finset.disjoint_left.mpr (fun i hiN hiC =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 (Finset.mem_union_right _ hiC))
    have hPC : Disjoint P C:=Finset.disjoint_left.mpr (fun i hiP hiC =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hP) hiP)).2 (Finset.mem_union_right _ hiC))
    have hNB : Disjoint N b.support:=Finset.disjoint_left.mpr (fun i hiN hiB =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 (Finset.mem_union_left _ hiB))
    have hPB : Disjoint P b.support:=Finset.disjoint_left.mpr (fun i hiP hiB =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hP) hiP)).2 (Finset.mem_union_left _ hiB))
    simpa only [mul_assoc,b,CubeCoordinates.support] using canonicalCubeSourcePair_factor p hp hcop hg hinj hpr b hb C N P
      hCB hNC hPC hNB hPB hNP Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K
  · simp only [hNP,ite_false,mul_zero]

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.DyadicKernel
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
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma multiplicityRow_norm_le_one (B : Finset ι) (v : ι→ℕ) (z:O) :
    ‖multiplicityRow (fun i=>Ideal.span {p i}) hg B v z‖≤1 := by
  simp only [multiplicityRow,norm_prod,norm_pow]
  calc
    _ ≤ ∏i∈B,(1:ℝ) := by
      apply Finset.prod_le_prod (fun i hi=>by positivity)
      intro i hi
      apply pow_le_one₀ (norm_nonneg _)
      let : Fintype (O⧸Ideal.span {p i}) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by simp

omit [DecidableEq ι] in
lemma multiplicityRow_support (B : Finset ι) (v : ι→₀ℕ) (hv : v.support⊆B) (z:O) :
    multiplicityRow (fun i=>Ideal.span {p i}) hg B v z =
      multiplicityRow (fun i=>Ideal.span {p i}) hg v.support v z := by
  unfold multiplicityRow
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

end SecondPassArithmetic

open scoped BigOperators Classical

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ReopenedFibers
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

open scoped BigOperators Classical
namespace SecondPassArithmetic

section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

lemma mem_reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFiber v₁ v₂ ↔
      b.leftExponent=v₁ ∧ b.rightExponent=v₂ ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨h₂,h₁⟩ := Finset.mem_product.mp hA
    exact ⟨rfl,rfl,Finset.mem_powerset.mp h₁,Finset.mem_powerset.mp h₂⟩
  · rintro ⟨hl,hr,hb⟩
    apply Finset.mem_image.mpr
    refine ⟨(b.rightDivisor,b.leftDivisor),?_,?_⟩
    · apply Finset.mem_product.mpr
      have hs : b.support=v₁.support∪v₂.support := by rw [CubeCoordinates.support,hl,hr]
      exact ⟨Finset.mem_powerset.mpr (hs ▸ hb.2),Finset.mem_powerset.mpr (hs ▸ hb.1)⟩
    · exact CubeCoordinates.ext hl.symm hr.symm rfl rfl

lemma mem_reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFamily Q ↔ b.leftExponent ∈ Q ∧ b.rightExponent ∈ Q ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨v,hv,hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    exact ⟨hl ▸ (Finset.mem_product.mp hv).2,hr ▸ (Finset.mem_product.mp hv).1,ha⟩
  · rintro ⟨hl,hr,ha⟩
    exact Finset.mem_biUnion.mpr ⟨(b.rightExponent,b.leftExponent),Finset.mem_product.mpr ⟨hr,hl⟩,
      (mem_reopenedCubeFiber _ _ b).mpr ⟨rfl,rfl,ha⟩⟩

lemma reopenedCubeFamily_admissible (Q : Finset (ι →₀ ℕ)) :
    ∀ b ∈ reopenedCubeFamily Q,b.Admissible :=
  fun b hb => ((mem_reopenedCubeFamily Q b).mp hb).2.2

theorem sum_reopenedCubeFamily {M : Type*} [AddCommMonoid M]
    (Q : Finset (ι →₀ ℕ)) (f : CubeCoordinates ι → M) :
    (∑ b ∈ reopenedCubeFamily Q,f b) =
      ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ A₂ ∈ (v₁.support∪v₂.support).powerset,
        ∑ A₁ ∈ (v₁.support∪v₂.support).powerset,f ⟨v₁,v₂,A₁,A₂⟩ := by
  unfold reopenedCubeFamily
  rw [Finset.sum_biUnion]
  · change (∑ x ∈ Q ×ˢ Q,∑ i ∈ reopenedCubeFiber x.2 x.1,f i)=_
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro v₂ hv₂
    apply Finset.sum_congr rfl
    intro v₁ hv₁
    unfold reopenedCubeFiber
    rw [Finset.sum_image]
    · change (∑ x ∈ (v₁.support∪v₂.support).powerset ×ˢ (v₁.support∪v₂.support).powerset,
        f ⟨v₁,v₂,x.2,x.1⟩)=_
      rw [Finset.sum_product]
    · intro A hA B hB he
      exact Prod.ext (congrArg CubeCoordinates.rightDivisor he) (congrArg CubeCoordinates.leftDivisor he)
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro b hb hc
    obtain ⟨hbl,hbr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    obtain ⟨hcl,hcr,hc⟩ := (mem_reopenedCubeFiber w.2 w.1 b).mp hc
    exact hne (Prod.ext (hbr.symm.trans hcr) (hbl.symm.trans hcl))

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ChildCutoff
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ childFrequencyBall a R ↔ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))
  simp only [childFrequencyBall, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_,h⟩⟩
  apply mem_secondFrequencyCutoff
  apply (le_div_iff₀ hn).mpr
  simpa only [map_mul, norm_mul, mul_pow, mul_comm] using h

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstCommonMeasure
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation MeasureTheory
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem firstPhysicalCommonRows_indexed (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis) :
    firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
    ∑ j ∈ firstCommonIndices F, firstCommonWeight p hg C₁ C₂ h j *
      firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K (firstCommonNorms p A₁ A₂ C R d h j) := by
  simp only [firstPhysicalCommonRows,firstCommonIndices,Finset.sum_product,Finset.sum_sigma,
    firstCommonWeight,firstCommonNorms,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstPhysicalCutoff
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma firstPhysicalMultiplier_ne_zero {ι : Type*} (p : ι→O) (hp : ∀ i,p i≠0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (S : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) (hf : f≠0) :
    firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f≠0 :=
  mul_ne_zero (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero f hf))
    (primeProduct_ne_zero p hp _ _)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstPhysicalFamily
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

lemma first_unblocked_physical (F : Finset ι) (C₁ C₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstBlockedPhysicalRows p hg F (fun _=>1) C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed]
  simp only [firstBlockedPhysicalRows,one_mul]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstRetainedFamily
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem sum_firstRetainedSource {A : Type*} [AddCommMonoid A]
    (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ) (H : Ideal O×O→A) :
    ∑ x∈firstRetainedSource p labels b Y,H x =
    ∑ f∈labels,∑ h∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y,H (f,h) := by
  unfold firstRetainedSource
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro f hf
    exact Finset.sum_image (fun h hh k hk he=>congrArg Prod.snd he)
  · intro f hf g hg hfg
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hy
    exact hfg (congrArg Prod.fst he).symm

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ReopenedSource
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem bounded_row_square_expansion {β : Type*}
    (C : Finset β) (a : β→ℂ) (r : β→O→ℂ) (hr : ∀b∈C,∀z,‖r b z‖≤1)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:O,W (‖eisEmbedding z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ))=
      ∑b∈C,∑c∈C,(star (a b)*a c)*∑'z:O,(star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K) := by
  have hs (b c : β) (hb:b∈C) (hc:c∈C) : Summable (fun z:O =>
      (star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K)) := by
    have hW : Summable (fun z:O=>‖W (‖eisEmbedding z‖^2/K)‖) := by
      simpa only [EisensteinSchwartzPoisson.scaledRadialTest_apply] using
        EisensteinSchwartzPoisson.actual_eisenstein_summable_norm
          (EisensteinSchwartzPoisson.scaledRadialTest W K hK)
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z=>norm_nonneg _) _ hW
    intro z
    simp only [norm_mul,norm_star]
    calc
      _ ≤ 1*1*‖W (‖eisEmbedding z‖^2/K)‖ := by
        gcongr
        · exact hr b hb z
        · exact hr c hc z
      _ = _ := by ring
  have he (z:O) : W (‖eisEmbedding z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ)=
      ∑b∈C,∑c∈C,(star (a b)*a c)*((star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K)) := by
    rw [Complex.sq_norm (∑b∈C,a b*r b z),Complex.normSq_eq_conj_mul_self]
    simp only [map_sum,map_mul,starRingEnd_apply]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun b hb=>summable_sum (fun c hc=>(hs b c hb hc).mul_left _))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Summable.tsum_finsetSum (fun c hc=>(hs b c hb hc).mul_left _)]
  apply Finset.sum_congr rfl
  intro c hc
  exact tsum_mul_left

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_reopened_smoothed_expand
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (β : (ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m f : O) (H : (ι→₀ℕ)→Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:O,W (‖eisEmbedding z‖^2/K)*(‖varyingReopenedRow p hp hcop hg pool Q β Ψ m f H z‖^2:ℝ))=
      ∑v₂∈Q,∑v₁∈Q,(star (β v₂)*β v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ Ψ m m f (H v₂) (H v₁) W K := by
  let a : (ι→₀ℕ)×Finset ι→ℂ := fun b=>β b.1*canonicalSourceCoefficient p hp hcop hg Ψ m f (H b.1) b.2
  let r : (ι→₀ℕ)×Finset ι→O→ℂ := fun b z=>
    multiplicityRow (fun i=>Ideal.span {p i}) hg pool b.1 z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg b.2 z
  have hr (b : (ι→₀ℕ)×Finset ι) (hb:b∈Q×ˢpool.powerset) (z:O) : ‖r b z‖≤1 := by
    dsimp [r]
    rw [norm_mul,norm_pow]
    calc
      _ ≤ 1 * ‖finiteSquarefreeRow (fun i => Ideal.span {p i}) hg b.2 z‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) (multiplicityRow_norm_le_one p hg pool b.1 z))
          (norm_nonneg _)
      _ ≤ 1 := by simpa using finiteSquarefreeRow_norm_le_one _ hg b.2 z
  have he:=bounded_row_square_expansion (Q×ˢpool.powerset) a r hr W K hK
  simp only [Finset.sum_product] at he
  change (∑'z:O,W (‖eisEmbedding z‖^2/K)*
    (‖varyingReopenedRow p hp hcop hg pool Q β Ψ m f H z‖^2:ℝ))=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro v₂ hv₂
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v₁ hv₁
  simp only [canonicalCubeCorrelation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  have hB₁ : v₁.support⊆v₁.support∪v₂.support:=Finset.subset_union_left
  have hB₂ : v₂.support⊆v₁.support∪v₂.support:=Finset.subset_union_right
  have hr₁ (z:O) : multiplicityRow (fun i=>Ideal.span {p i}) hg pool v₁ z=
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₁ z := by
    rw [multiplicityRow_support p hg pool v₁ (hQ v₁ hv₁),multiplicityRow_support p hg _ v₁ hB₁]
  have hr₂ (z:O) : multiplicityRow (fun i=>Ideal.span {p i}) hg pool v₂ z=
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₂ z := by
    rw [multiplicityRow_support p hg pool v₂ (hQ v₂ hv₂),multiplicityRow_support p hg _ v₂ hB₂]
  simp only [a,r,canonicalCubeSourcePair,star_mul,hr₁,hr₂]
  have ht : (∑'z:O,(star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)*
      star (multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₂ z^3)*
      (multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₁ z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg T z))*W (‖eisEmbedding z‖^2/K))=
      ∑'z:O,(star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg T z*
      star (multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₂ z^3)*
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₁ z^3)*W (‖eisEmbedding z‖^2/K) := by
    apply tsum_congr
    intro z
    ring
  rw [ht]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ReopenedBlocks
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem varying_reopened_smoothed_source {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (H : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑ I ∈ labels,∑' z : ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/K)*
      (‖varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (H I) z‖^2 : ℝ)) =
    varyingCanonicalSourceTotal p hp hcop hg pool Q labels β Ψ m H W K := by
  rw [varyingCanonicalSourceTotal,sum_reopenedCubeFamily]
  simp only [reopenedPairCoefficient,CubeCoordinates.support]
  calc
    _ = ∑ I ∈ labels,∑ v₂ ∈ Q,∑ v₁ ∈ Q,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (H I v₂)
          (H I v₁) W K := by
      apply Finset.sum_congr rfl
      intro I hI
      exact varying_reopened_smoothed_expand p hp hcop hg pool Q hQ (β I) Ψ m
        (idealGenerator I) (H I) W K hK
    _ = ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ I ∈ labels,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (H I v₂)
          (H I v₁) W K := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      apply Finset.sum_congr rfl
      intro v₁ hv₁
      have hs : v₁.support∪v₂.support ⊆ pool := Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂)
      simp_rw [canonicalCubeCorrelation_eq_blocks p hp hcop hg hinj hpr pool v₁ v₂ hs,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₂ hA₂
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₁ hA₁
      rw [Finset.sum_comm]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ReopenedPhysicalSplit
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_reopened_physical_split
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀ v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀ I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D) :
    (∑ I∈labels,∑' z:O,Φ (‖eisEmbedding z‖^2/K)*
      (‖varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark I v U*W (primeProductNorm p U)) z‖^2:ℝ)) =
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) Φ K) +
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I (mark I) W Φ K (R b C I)) +
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) Φ K
        (reopenedPhysicalCutoff p b I (R b C I))) := by
  rw [varying_reopened_smoothed_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m]
  · unfold varyingCanonicalSourceTotal reopenedPhysicalSourceSum
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro C hC
    apply Finset.sum_congr rfl
    intro I hI
    have hCb : Disjoint C b.support := by
      exact Finset.disjoint_left.mpr (fun i hi hib=>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hi)).2 hib)
    have he := canonical_first_physical_split p hp hcop hg hinj hc hpr pool b
      (reopenedCubeFamily_admissible Q b hb) C hCb Ψ Ψ m m I (hlabels I hI)
      (mark I b.rightExponent) (mark I b.leftExponent) W W Φ K hK (R b C I) (hR b hb C hC I hI)
    dsimp only at he
    rw [he]
    simp only [reopenedPhysicalRetained]
    rw [show reopenedPhysicalCutoff p b I (R b C I) =
      (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent
        b.leftBit b.rightBit I) (R b C I D)) from rfl]
    ring
  · exact hK

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceIndex
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

lemma mem_firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : FirstOriginalOuter ι) :
    k∈firstOriginalOuter pool Q ↔ k.1∈reopenedCubeFamily Q ∧ k.2.1∈(pool\k.1.support).powerset ∧
      k.2.2∈(k.2.1∪cubePrincipalSupport k.1.support k.1.leftExponent k.1.rightExponent k.1.leftBit k.1.rightBit).powerset := by
  simp [firstOriginalOuter]

lemma retained_cutoff_enlargement (E : O) (hE : E≠0) (R Y : ℝ) (hRY : R≤Y) (f : O→ℂ) :
    (∑h∈(childFrequencyBall E R).erase 0,f h)=
      ∑h∈nonzeroChildFrequencyBall E Y,(if h∈childFrequencyBall E R then (1:ℂ) else 0)*f h := by
  have hsub : (childFrequencyBall E R).erase 0⊆nonzeroChildFrequencyBall E Y := by
    intro h hh
    rcases Finset.mem_erase.mp hh with ⟨hn,hm⟩
    exact Finset.mem_erase.mpr ⟨hn,(mem_childFrequencyBall E hE Y h).mpr
      (((mem_childFrequencyBall E hE R h).mp hm).trans hRY)⟩
  calc
    _=∑h∈(childFrequencyBall E R).erase 0,(if h∈childFrequencyBall E R then (1:ℂ) else 0)*f h := by
      apply Finset.sum_congr rfl
      intro h hh
      simp [(Finset.mem_erase.mp hh).2]
    _=_ := Finset.sum_subset hsub (by
      intro h hh hn
      have hne := (Finset.mem_erase.mp hh).1
      have hout : h∉childFrequencyBall E R := fun hm=>hn (Finset.mem_erase.mpr ⟨hne,hm⟩)
      simp [hout])

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_retained_global_index
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y) :
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I mark W Φ K (R b C I)) =
    ∑x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      firstOriginalWeight p β R x.1 x.2 *
      canonicalCubeOuter p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator x.2.1)*
      firstCubePhysicalMode p hp hcop hg pool x.1.1 x.1.2.1 Ψ Ψ m m
        (ConcretePrimeRowBridge.idealGenerator x.2.1) (mark x.1.1.rightExponent) (mark x.1.1.leftExponent)
        W W Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) x.2.2 := by
  simp only [firstGlobalRetainedSource,firstOriginalOuter,Finset.sum_sigma,sum_firstRetainedSource]
  unfold reopenedPhysicalSourceSum reopenedPhysicalRetained
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro C hC
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro f hf
  have hE := firstPhysicalMultiplier_ne_zero p hp b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit f (hlabels f hf)
  have hRY' := hRY ⟨b,⟨C,D⟩⟩ ((mem_firstOriginalOuter pool Q _).mpr ⟨hb,hC,hD⟩) f hf
  rw [show reopenedPhysicalCutoff p b f (R b C f) D=
    childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R b C f D) from rfl]
  rw [retained_cutoff_enlargement _ hE _ Y hRY']
  apply Finset.sum_congr rfl
  intro h hh
  simp only [firstOriginalWeight,reopenedPhysicalCutoff]
  ac_rfl

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceSupport
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma first_squarefree_row_zero_mem (U : Finset ι) (i : ι) (hi : i∈U) (n : O)
    (hn : n∈Ideal.span {p i}) : finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg U n=0 := by
  unfold finiteSquarefreeRow
  apply Finset.prod_eq_zero hi
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn,MulChar.map_zero]

lemma canonicalCubeResidual_zero_overlap (b : CubeCoordinates ι) (C U : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ)
    (hn : ¬Disjoint U (b.support∪C)) : canonicalCubeResidual p hg b C negative Ψ m f H U=0 := by
  obtain ⟨i,hi,hib⟩ := Finset.not_disjoint_iff.mp hn
  rcases Finset.mem_union.mp hib with hib|hiC
  · have hm : cubeRadical p b.support∈Ideal.span {p i} :=
      Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hib)
    have hz : rowCoprimeMask (fun i=>Ideal.span {p i}) U (cubeRadical p b.support)=0 := by
      simp only [rowCoprimeMask,ite_eq_left_iff]
      intro hh
      exact False.elim (hh ⟨i,hi,hm⟩)
    simp only [canonicalCubeResidual,originalLabelColumn,hz,mul_zero,zero_mul]
  · have hm : aLabel p b.support (if negative then b.rightBit else b.leftBit)*(∏j∈C,p j)∈Ideal.span {p i} :=
      Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiC) _)
    have hz := first_squarefree_row_zero_mem p hg U i hi _ hm
    simp only [canonicalCubeResidual,originalLabelColumn,hz,zero_pow (by norm_num : 4≠0),mul_zero,zero_mul]

lemma firstCanonicalCoefficient_zero_overlap (b : CubeCoordinates ι) (C U : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O)
    (hn : ¬Disjoint U (b.support∪C)) : firstCanonicalCoefficient p hp hcop hg b C negative Ψ m d H x U=0 := by
  have hz := canonicalCubeResidual_zero_overlap p hg b C U negative Ψ m
    (ConcretePrimeRowBridge.idealGenerator x.1) H hn
  cases negative <;>
    simp only [firstCanonicalCoefficient,firstBareCubeCoefficient,Bool.false_eq_true,ite_false,ite_true,
      cubeMinusCoefficient,cubePlusCoefficient,firstPassColumnMinus,firstPassColumnPlus,hz,mul_zero]

lemma firstCommonIndices_membership (F : Finset ι) (j : FirstCommonIndex ι) :
    j∈firstCommonIndices F ↔ j.2.1⊆F ∧ j.2.2.1⊆F\j.2.1 ∧ j.2.2.2⊆F\j.2.1 := by
  simp [firstCommonIndices]

lemma firstCommonIndices_mono {F G : Finset ι} (h : F⊆G) : firstCommonIndices F⊆firstCommonIndices G := by
  intro j hj
  rcases (firstCommonIndices_membership F j).mp hj with ⟨hd,hu,hv⟩
  exact (firstCommonIndices_membership G j).mpr ⟨hd.trans h,
    hu.trans (Finset.sdiff_subset_sdiff h le_rfl),hv.trans (Finset.sdiff_subset_sdiff h le_rfl)⟩

lemma firstCommonWeight_zero_outside (F G : Finset ι) (C₁ C₂ : Finset ι→ℂ) (h : O)
    (hC₁ : ∀U,U⊆G → ¬U⊆F → C₁ U=0) (hC₂ : ∀U,U⊆G → ¬U⊆F → C₂ U=0)
    (j : FirstCommonIndex ι) (hj : j∈firstCommonIndices G) (hjF : j∉firstCommonIndices F) :
    firstCommonWeight p hg C₁ C₂ h j=0 := by
  rcases (firstCommonIndices_membership G j).mp hj with ⟨hd,hu,hv⟩
  by_cases hleft : j.2.1∪j.2.2.1⊆F
  · have hright : ¬j.2.1∪j.2.2.2⊆F := by
      intro hr
      apply hjF
      apply (firstCommonIndices_membership F j).mpr
      refine ⟨Finset.Subset.trans Finset.subset_union_left hleft,?_,?_⟩
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨hleft (Finset.mem_union_right _ hi),(Finset.mem_sdiff.mp (hu hi)).2⟩
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨hr (Finset.mem_union_right _ hi),(Finset.mem_sdiff.mp (hv hi)).2⟩
    have hz := hC₂ _ (Finset.union_subset hd (hv.trans Finset.sdiff_subset)) hright
    simp only [firstCommonWeight,firstCommonCoefficient,hz,mul_zero,zero_mul]
  · have hz := hC₁ _ (Finset.union_subset hd (hu.trans Finset.sdiff_subset)) hleft
    simp only [firstCommonWeight,firstCommonCoefficient,hz,mul_zero,zero_mul,star_zero]

theorem firstPhysicalCommonRows_fixed_pool (F G : Finset ι) (hFG : F⊆G)
    (C₁ C₂ : Finset ι→ℂ) (hC₁ : ∀U,U⊆G → ¬U⊆F → C₁ U=0)
    (hC₂ : ∀U,U⊆G → ¬U⊆F → C₂ U=0)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h=
      firstPhysicalCommonRows p hg G C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed,firstPhysicalCommonRows_indexed]
  exact Finset.sum_subset (firstCommonIndices_mono hFG) (fun j hj hn=>by
    rw [firstCommonWeight_zero_outside p hg F G C₁ C₂ h hC₁ hC₂ j hj hn,zero_mul])

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourcePhysical
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem firstCubePhysicalMode_fixed_pool (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ d : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (x : Ideal O×O) :
    firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator x.1) H₁ H₂ W₁ W₂ Φ K d x.2=
    (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d x.2 *
      firstPhysicalCommonRows p hg pool
        (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁ x)
        (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂ x)
        (fun y=>star (W₁ y)) W₂ Φ
        (‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
        (‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
        (primeProductNorm p C)
        (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d x.2 := by
  change _*firstPhysicalCommonRows p hg (pool\(b.support∪C))
      (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁ x)
      (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂ x) _ _ _ _ _ _ _ _ _ _ = _
  apply congrArg (fun z : ℂ =>
    (K : ℂ) * cubeBaseFactor p hp hg b.support
      (fun i => b.leftExponent i + b.rightExponent i) b.leftBit b.rightBit d x.2 * z)
  apply firstPhysicalCommonRows_fixed_pool p hg _ pool Finset.sdiff_subset
  · intro U hU hn
    apply firstCanonicalCoefficient_zero_overlap p hp hcop hg
    intro hd
    apply hn
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi,fun he=>Finset.disjoint_left.mp hd hi he⟩
  · intro U hU hn
    apply firstCanonicalCoefficient_zero_overlap p hp hcop hg
    intro hd
    apply hn
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi,fun he=>Finset.disjoint_left.mp hd hi he⟩

theorem original_retained_global_family
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I mark W Φ K (R b C I)) =
    (K:ℂ)*firstFamilyPhysicalRows p hg
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y) pool
      (fun _ _=>1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 true Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.rightExponent) x.2)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 false Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.leftExponent) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (firstOriginalWeight p β R x.1) x.2)
      (fun y=>star (W ((s 0*s 2*s 5*s 7)*y))) (fun y=>W ((s 1*s 2*s 5*s 8)*y)) Φ
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.rightBit)‖^2)
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.leftBit)‖^2)
      (fun x=>primeProductNorm p x.1.2.1)
      (fun x=>primeProductNorm p (cubeActiveSupport x.1.1.support
        (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)) K
      (fun x=>primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (fun x=>x.2.2) s := by
  rw [original_retained_global_index p hp hcop hg pool Q labels hlabels β Ψ m mark W Φ K Y R hRY]
  have hleft : s 0*s 2*s 5*s 7≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (hs 0)) (ne_of_gt (hs 2))) (ne_of_gt (hs 5))) (ne_of_gt (hs 7))
  have hright : s 1*s 2*s 5*s 8≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (hs 1)) (ne_of_gt (hs 2))) (ne_of_gt (hs 5))) (ne_of_gt (hs 8))
  have hw₁ : (fun y=>star (W ((s 0*s 2*s 5*s 7)*(y/(s 0*s 2*s 5*s 7)))))=fun y=>star (W y) := by
    funext y
    rw [mul_div_cancel₀ _ hleft]
  have hw₂ : (fun y=>W ((s 1*s 2*s 5*s 8)*(y/(s 1*s 2*s 5*s 8))))=W := by
    funext y
    rw [mul_div_cancel₀ _ hright]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum,hw₁,hw₂]
  apply Finset.sum_congr rfl
  intro x hx
  rw [first_unblocked_physical,firstCubePhysicalMode_fixed_pool p hp hcop hg]
  unfold retainedCubeWeight
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ReopenedPhysicalEnergy
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem rowFamilyEnergy_le_of_full_split (labels : Finset (Ideal O))
    (P : Ideal O→O→ℂ) (K : ℝ) (hK : 0<K) (A B C : ℂ)
    (he : (∑ I∈labels,∑' z:O,rowMajorant (‖eisEmbedding z‖^2/K)*(‖P I z‖^2:ℝ))=A+B+C) :
    CanonicalRowCompletion.rowFamilyEnergy labels P K ≤ ‖A‖+‖B‖+‖C‖ := by
  unfold CanonicalRowCompletion.rowFamilyEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re]
  rw [he]
  have hn : 0≤(∑ I∈labels,((‖P I 0‖^2:ℝ):ℂ)).re := by
    simp only [Complex.re_sum,Complex.ofReal_re]
    exact Finset.sum_nonneg (fun I hI=>sq_nonneg _)
  simp only [Complex.add_re]
  linarith [Complex.re_le_norm A,Complex.re_le_norm B,Complex.re_le_norm C]

theorem original_reopened_physical_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀ v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀ I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ)
    (K : ℝ) (hK : 0<K) (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D) :
    CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark I v U*W (primeProductNorm p U)) z) K ≤
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) rowMajorant K)‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I (mark I) W rowMajorant K (R b C I))‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) rowMajorant K
        (reopenedPhysicalCutoff p b I (R b C I)))‖ := by
  apply rowFamilyEnergy_le_of_full_split labels _ K hK
  exact original_reopened_physical_split p hp hcop hg hinj hc hpr pool Q hQ labels hlabels
    β Ψ m mark W rowMajorant K hK R hR

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceEnergy
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_global_physical_energy_oai
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (K Y : ℝ) (hK : 0<K)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark v U*W (primeProductNorm p U)) z) K ≤
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark b.leftExponent U*W (primeProductNorm p U)) rowMajorant K)‖ +
    K*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W rowMajorant K Y R s‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark b.leftExponent U*W (primeProductNorm p U)) rowMajorant K
        (reopenedPhysicalCutoff p b I (R b C I)))‖ := by
  have he := original_reopened_physical_energy p hp hcop hg hinj hc hpr pool Q hQ labels hlabels
    β Ψ m (fun _=>mark) W K hK R hR
  rw [original_retained_global_family p hp hcop hg pool Q labels hlabels β Ψ m mark W rowMajorant K Y R hRY s hs] at he
  simpa only [originalRetainedFamily,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK] using he

end
end SevenEighths.InverseMoment

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.InverseMoment.original_global_physical_energy_oai.{u_1} := @OAI.SevenEighths.InverseMoment.original_global_physical_energy_oai.{u_1}
