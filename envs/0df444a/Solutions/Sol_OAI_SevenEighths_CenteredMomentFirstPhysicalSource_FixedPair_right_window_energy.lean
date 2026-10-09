-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFirstPhysicalSource.FixedPair.right_window_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:38:50.679628+00:00
-- url     : https://prove2.me/submissions/2a9eff81-3960-437b-9fc6-8a3670360150

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.DirichletForm
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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

namespace CompletedGauss

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory

theorem finite_integral_energy_bound {κ : Type*} [Fintype κ]
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (E : ℝ) (hE : 0≤E)
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀k,Integrable (fun t => b t*φ k t))
    (hbound : ∀t,(∑k,‖φ k t‖^2)≤E) :
    (∑k,‖∫t : ℝ,b t*φ k t‖^2)≤E*(∫t : ℝ,‖b t‖)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ→EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖≤‖b t‖*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE]
    change (∑k,‖b t*φ k t‖^2)≤‖b t‖^2*E
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫t : ℝ,F t)=e.symm (fun k => ∫t : ℝ,b t*φ k t) := by
    rw [show F=(fun t => e.symm (fun k => b t*φ k t)) from rfl,e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫t : ℝ,b t*φ k t)‖≤(∫t : ℝ,‖b t‖)*Real.sqrt E := by
    rw [←he,←integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hs
  simpa [e,mul_comm] using hs

open CanonicalQuadraticSieve ActualEisensteinCubic

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CanonicalQuadraticSieve

end CompletedGauss

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Smooth
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentSmooth
open FourierBridge EisensteinSchwartzPoisson

theorem logPhase_norm_ratio (q X θ : ℝ) (hq : 0 < q) (hX : 0 < X) :
    logPhase θ (-Real.log (q / X)) =
      logPhase θ (Real.log X) * (q : ℂ) ^ (Complex.I * (-(2 * Real.pi * θ))) := by
  have hlog : -Real.log (q / X) = Real.log X + -Real.log q := by
    rw [Real.log_div hq.ne' hX.ne']
    ring
  rw [hlog, logPhase_add]
  congr 1
  have hθ : (-(2 * Real.pi * θ)) / (2 * Real.pi) = -θ := by
    have hp := Real.pi_ne_zero
    field_simp
  have hn := CenteredMomentLattice.logPhase_eq_normPower (-(2 * Real.pi * θ)) q hq
  rw [hθ] at hn
  push_cast at hn
  rw [← hn]
  unfold logPhase
  congr 1
  push_cast
  ring

open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentSmooth
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeColumnWindow
open FourierBridge HeckeFamily CenteredMomentSmooth CenteredMomentGaussEnergy
open CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem heightCoeff_add (τ : Character) (I : Ideal O) (hI : I≠0) (t v : ℝ) :
    heightCoeff τ (t+v) I=heightCoeff τ t I*(Ideal.absNorm I:ℂ)^(Complex.I*v) := by
  have hn : (Ideal.absNorm I:ℂ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [heightCoeff,Complex.ofReal_add,mul_add,Complex.cpow_add _ _ hn]
  ring

theorem heightCoeff_phase (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    heightCoeff τ t I*logPhase θ (-Real.log ((Ideal.absNorm I:ℝ)/X))=
      logPhase θ (Real.log X)*heightCoeff τ (t-2*Real.pi*θ) I := by
  have hn : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [logPhase_norm_ratio _ X θ hn hX,sub_eq_add_neg,heightCoeff_add τ I hI]
  push_cast
  ring

theorem rootProfile_apply (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (u : ℝ) :
    rootProfile V hVc hVs u=rootWindow V u := by
  change V u*(Real.exp (-u/2):ℂ)=_
  rw [rootWindow,← Real.exp_half,show -u/2=-(u/2) by ring,Real.exp_neg,
    Complex.ofReal_inv,div_eq_mul_inv]
  ring

theorem columnDensity_moments (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (J : ℕ) :
    Integrable (fun w : ℝ => (1+‖w‖)^J*‖columnDensity V hVc hVs w‖) :=
  JointLogSeparation.weighted_schwartz_integrable _ J

theorem rootWindow_integral (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (u : ℝ) :
    rootWindow V u=∫ w : ℝ,logPhase w u*columnDensity V hVc hVs w := by
  rw [← rootProfile_apply V hVc hVs u,schwartz_log_inversion]
  apply integral_congr_ae
  filter_upwards [] with w
  congr 2
  simp only [Real.inner_apply]
  push_cast
  ring

theorem phase_combine (w θ u : ℝ) :
    logPhase w u*logPhase θ (-u)=logPhase (θ-w) (-u) := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem height_column_integral (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    heightCoeff τ t I*columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) I := by
  rw [columnPhase,rootWindow_integral V hVc hVs,← mul_assoc,← integral_const_mul,← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with w
  calc
    _ = columnDensity V hVc hVs w*(heightCoeff τ t I*
      (logPhase w (Real.log ((Ideal.absNorm I:ℝ)/X))*
        logPhase θ (-Real.log ((Ideal.absNorm I:ℝ)/X)))) := by ring
    _ = _ := by
      rw [phase_combine,heightCoeff_phase τ I hI t (θ-w) X hX,
        show t-2*Real.pi*(θ-w)=t+2*Real.pi*(w-θ) by ring]
      ring

theorem height_column_integrable (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      heightCoeff τ (t+2*Real.pi*(w-θ)) I) := by
  have he (w : ℝ) : logPhase (θ-w) (Real.log X)*heightCoeff τ (t+2*Real.pi*(w-θ)) I=
      heightCoeff τ t I*logPhase (θ-w) (-Real.log ((Ideal.absNorm I:ℝ)/X)) := by
    rw [heightCoeff_phase τ I hI t (θ-w) X hX]
    congr 2
    ring
  have hfun : (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      heightCoeff τ (t+2*Real.pi*(w-θ)) I) =
      (fun w : ℝ => columnDensity V hVc hVs w*(heightCoeff τ t I*
        logPhase (θ-w) (-Real.log ((Ideal.absNorm I:ℝ)/X)))) := by
    funext w
    rw [mul_assoc,he w]
  rw [hfun]
  apply ((columnDensity V hVc hVs).integrable.norm.const_mul ‖heightCoeff τ t I‖).mono'
  · have hp := (logPhase_continuous_left (-Real.log ((Ideal.absNorm I:ℝ)/X))).comp
      (show Continuous (fun w : ℝ => θ-w) from continuous_const.sub continuous_id)
    exact ((columnDensity V hVc hVs).continuous.mul (hp.const_mul _)).aestronglyMeasurable
  · filter_upwards [] with w
    simp only [norm_mul,logPhase_norm,mul_one]
    exact le_of_eq (mul_comm _ _)

theorem gauss_column_integral {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    gaussPolynomial S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z := by
  have hi (i : α) : Integrable (fun w : ℝ => β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*gaussRow (a i) (ha i) z) :=
    ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul _).mul_const _
  unfold gaussPolynomial
  calc
    _ = ∑ i∈S,∫ w : ℝ,β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*gaussRow (a i) (ha i) z := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_const,integral_const_mul,← height_column_integral V hVc hVs τ _ (ha i).1 t θ X hX]
      ring
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => hi i)]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end SevenEighths.CenteredMomentHeckeColumnWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ConjugateWindow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentConjugateWindow
open FourierBridge CenteredMomentSmooth

theorem star_logPhase (t u : ℝ) : star (logPhase t u)=logPhase (-t) u := by
  simp only [logPhase,Complex.star_def,← Complex.exp_conj,map_mul,
    Complex.conj_ofReal,Complex.conj_I]
  congr 1
  push_cast
  ring

theorem star_columnPhase (V : ℝ → ℂ) (u t : ℝ) :
    star (columnPhase V u t)=columnPhase (fun x => star (V x)) u (-t) := by
  rw [columnPhase,star_mul,star_logPhase,columnPhase,mul_comm]
  congr 1
  simp only [rootWindow,Complex.star_def,map_div₀,Complex.conj_ofReal]

end SevenEighths.CenteredMomentConjugateWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LiveDomain
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentLiveDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem supported_residualPool (C : Ideal O) (hC : Supported C) (S : Finset (Ideal O)) :
    supportedColumns (residualPool C hC.1 S)=residualPool C hC.1 (supportedColumns S) := by
  ext I
  simp only [supportedColumns,Finset.mem_filter,mem_residualPool]
  rw [supported_mul_iff]
  tauto

theorem source_gaussPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*primaryGaussRow I z := by
  unfold gaussPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*primaryGaussRow I z)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [primaryGaussRow,dif_pos (Finset.mem_filter.mp I.property).2]
  rfl

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentLiveDomain

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem finite_weighted_integral_energy {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (w : ℝ → ℝ) (hw : ∀ t,0<w t)
    (E : ℝ) (hE : 0≤E) (hb : Integrable (fun t => w t*‖b t‖))
    (hφ : ∀ k,Integrable (fun t => b t*φ k t))
    (hbound : ∀ t,(∑ k,‖φ k t‖^2)≤E*(w t)^2) :
    (∑ k,‖∫ t : ℝ,b t*φ k t‖^2)≤E*(∫ t : ℝ,w t*‖b t‖)^2 := by
  have hn (t : ℝ) : (w t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw t).ne'
  have hnorm (t : ℝ) : ‖(w t:ℂ)‖=w t := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hw t)]
  have he (k : κ) (t : ℝ) : ((w t:ℂ)*b t)*(φ k t/(w t:ℂ))=b t*φ k t := by
    field_simp [hn t]
  have hh := CompletedGauss.finite_integral_energy_bound
    (fun t => (w t:ℂ)*b t) (fun k t => φ k t/(w t:ℂ)) E hE
    (by simpa only [norm_mul,hnorm] using hb)
    (fun k => by simpa only [he] using hφ k) (fun t => by
      simp only [norm_div,hnorm,div_pow,← Finset.sum_div]
      exact (div_le_iff₀ (sq_pos_of_pos (hw t))).mpr (hbound t))
  simpa only [he,norm_mul,hnorm] using hh

theorem gauss_column_integrable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (gaussRow (a i) (ha i) z)
  convert (preTransparency := .instances) integrable_finsetSum S (fun i _ => hi i) using 1
  funext w
  simp only [gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem heightCost_pos (t θ : ℝ) : 0<heightCost t θ := by
  unfold heightCost
  positivity

theorem norm_height_shift (t θ w : ℝ) :
    1+‖t+2*Real.pi*(w-θ)‖≤heightCost t θ*(1+‖w‖) := by
  have hπ : 0≤2*Real.pi := by positivity
  have hn := norm_add_le t (2*Real.pi*(w-θ))
  rw [norm_mul,Real.norm_of_nonneg hπ] at hn
  have hs := norm_sub_le w θ
  have hr : 1+‖t+2*Real.pi*(w-θ)‖≤1+‖t‖+2*Real.pi*‖θ‖+2*Real.pi*‖w‖ := by
    nlinarith
  have hb : 1≤1+‖t‖+2*Real.pi*‖θ‖ := by
    nlinarith [norm_nonneg t,mul_nonneg hπ (norm_nonneg θ)]
  have hw : 0≤2*Real.pi*‖w‖ := by positivity
  calc
    _ ≤ (1+‖t‖+2*Real.pi*‖θ‖)*(1+2*Real.pi*‖w‖) := by nlinarith
    _ ≤ _ := by
      unfold heightCost
      rw [mul_assoc (1+‖t‖+2*Real.pi*‖θ‖) (1+2*Real.pi) (1+‖w‖)]
      apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hb)
      nlinarith [norm_nonneg w,Real.pi_pos]

end SevenEighths.CenteredMomentHeckeWindowEnergy

end

end OAI
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

theorem finite_weighted_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖gaussPolynomial S a ha c z‖^2*(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)≤
      (gaussEnergy S a ha c U K).re :=
  sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hU z)) (gaussEnergy_hasSum_re S a ha c U K hK)

theorem smoothed_window_energy_from_shifted {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(gaussEnergy S a ha
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K).re≤E*(1+‖w‖)^(2*J)) :
    (gaussEnergy S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun z : O => (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re
  let c := fun i => β i*heightCoeff τ t (Ideal.span {a i})*
    CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ
  have hnorm (z : O) (x : ℂ) : ‖(Real.sqrt (u z):ℂ)*x‖^2=u z*‖x‖^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (hU z)]
  have hfin (rows : Finset O) : (∑ z∈rows,‖gaussPolynomial S a ha c z‖^2*u z)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun z : rows => fun w : ℝ => (Real.sqrt (u z):ℂ)*
      (logPhase (θ-w) (Real.log X)*gaussPolynomial S a ha
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z)
    have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
      have h := (gauss_column_integrable S a ha β τ t θ X hX V hVc hVs z).const_mul (Real.sqrt (u z):ℂ)
      convert (preTransparency := .instances) h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
      simp only [φ]
      simp_rw [hnorm]
      simp only [norm_mul,logPhase_norm,one_mul,← pow_mul]
      rw [Finset.sum_coe_sort rows (fun z : O => u z*‖gaussPolynomial S a ha
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
      simpa only [mul_comm,Nat.mul_comm] using
        (finite_weighted_le_gaussEnergy S a ha _ U K hK hU rows).trans (henergy w)
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (z : rows) : (∫ w : ℝ,columnDensity V hVc hVs w*φ z w)=
        (Real.sqrt (u z):ℂ)*gaussPolynomial S a ha c z := by
      rw [show gaussPolynomial S a ha c z=_ from gauss_column_integral S a ha β τ t θ X hX V hVc hVs z,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    simp only [he,hnorm] at hh
    rw [Finset.sum_coe_sort rows (fun z : O => u z*‖gaussPolynomial S a ha c z‖^2)] at hh
    simpa only [mul_comm] using hh
  have hs := gaussEnergy_hasSum_re S a ha c U K hK
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hU z)) hfin

theorem smoothed_window_energy_from_height {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(gaussEnergy S a ha
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) U K).re≤E*(1+‖v‖)^(2*J)) :
    (gaussEnergy S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply smoothed_window_energy_from_shifted V hVc hVs J S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end SevenEighths.CenteredMomentSmoothedWindowEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem coprime_of_same_support (C D a : Ideal O) (hC : C≠0) (hD : D≠0) (ha : a≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    IsCoprime C a ↔ IsCoprime D a := by
  change IdealMobiusDivisorSum.primeSupport C=IdealMobiusDivisorSum.primeSupport D at hCD
  rw [←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha,
    ←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hD ha,hCD]

end SevenEighths.CenteredMomentSecondSectorColumns

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFixedRowMask
open CenteredMomentFirstFamily CenteredMomentFirstIdealFamily CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentCanonicalFirst CenteredMomentCommonSupport
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationFamily
open CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentLiveDomain CenteredMomentPrimaryCharacter
open ActualEisensteinCubic ConcreteTraceCRT CenteredMomentChildAssembly CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "fixedBadMask" => (goodLambda*(2:O))

lemma divisor_column_masked (η τ : Character) (F : O → ℂ) (ξ : RayCharacter)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*
        (F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (u : O) (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryGenerator J)
      (fun J => β J*rowWeight η (fixedBadMask*u) 1 1 t J*F (primaryGenerator J)) ξ I =
      (if L∣I then maskedSource u β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,primary_span_supported I hI,rowWeight_mask_factor η u I hI t,hτ I hI t]
  split_ifs
  · simp only [maskedSource]; ring
  · ring

lemma maskedSource_eq_of_live (u : O) (β : Ideal O → ℂ)
    (h : ∀ I, β I≠0 → IsCoprime I (Ideal.span {u})) : maskedSource u β=β := by
  funext I
  by_cases hi : β I=0
  · simp [maskedSource,hi]
  · simp [maskedSource,idealMask,h I hi]

end SevenEighths.CenteredMomentFirstMaskedFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalColumn
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentSecondSectorColumns CenteredMomentFirstSectorTransform IdealMobiusDivisorSum
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentLiveDomain
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentChildAssembly
local notation "O"=>ActualEisensteinCubic.O

theorem columns_gauss_polynomial_filter (Q C:Ideal O)(hC:Supported C)(S:Finset (Ideal O))
    (f:Ideal O→ℂ)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 S) (element_supported Q C hC.1 S)
      (fun a=>f a) z=
    gaussPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
      (sourceGenerator_supported _) (fun I=>if IsCoprime Q (I:Ideal O) then f I else 0) z:=by
  rw [source_gaussPolynomial (residualPool C hC.1 S)
    (fun I=>if IsCoprime Q I then f I else 0) z,supported_residualPool C hC S]
  have he (a:columns Q C hC.1 S):
      gaussRow (element Q C hC.1 S a) (element_supported Q C hC.1 S a) z=
        primaryGaussRow a z:=by
    rw [primaryGaussRow,dif_pos (column_supported Q C hC.1 S a)]
    rfl
  simp only [gaussPolynomial,he]
  rw [Finset.sum_coe_sort (columns Q C hC.1 S) (fun I=>f I*primaryGaussRow I z)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

variable {ι:Type*}[Fintype ι]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowColumns
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum
open FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

lemma element_norm (Q C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(I:columns Q C hC S):
    ‖eisEmbedding (element Q C hC S I)‖^2=(Ideal.absNorm (I:Ideal O):ℝ):=by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

lemma column_unwindowed_common (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I) z=
      commonGauss s C hC τ t L z:=by
  rw [columns_gauss_polynomial_filter Q C hC s.columns
    (fun I=>(if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I) z]
  unfold commonGauss
  congr 1
  funext I
  rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]

theorem column_unwindowed_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I) U K=
      commonEnergy s C hC τ t L U K:=by
  unfold gaussEnergy commonEnergy
  apply tsum_congr
  intro z
  rw [column_unwindowed_common s Q C hQ hC hQC τ t L z]
  rfl

theorem column_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2:=by
  have hh:=smoothed_window_energy_from_height V hVc hVs J Finset.univ
    (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
    (fun I:columns Q C hC.1 s.columns=>if L∣(I:Ideal O) then s.beta (C*I) else 0)
    τ t θ X hX U K hK hU E hE (fun v=>by
      simp only [element_span]
      rw [column_unwindowed_energy s Q C hQ hC hQC]
      exact henergy v)
  simpa only [ha,element_span,element_norm] using hh

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondWindowSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentConjugateWindow
local notation "O" => ActualEisensteinCubic.O

theorem star_logAnnulus (x : ℝ) : star (logAnnulus x)=logAnnulus x := by
  simp only [logAnnulus,Complex.star_def,Complex.conj_ofReal]

theorem star_logAnnulus_column (u t : ℝ) :
    star (columnPhase logAnnulus u t)=columnPhase logAnnulus u (-t) := by
  rw [star_columnPhase]
  simp only [star_logAnnulus]

end SevenEighths.CenteredMomentSecondWindowSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowBudget
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentSecondWindowSource

theorem heightCost_le_envelope (t θ : ℝ) : heightCost t θ≤heightEnvelope t*(1+‖θ‖) := by
  have hh : 1+‖t‖+2*Real.pi*‖θ‖≤(1+‖t‖+2*Real.pi)*(1+‖θ‖) := by
    nlinarith [norm_nonneg t,norm_nonneg θ,Real.pi_pos]
  have he := mul_le_mul_of_nonneg_right hh (show 0≤1+2*Real.pi by positivity)
  convert (preTransparency := .instances) he using 1 <;> simp only [heightCost,heightEnvelope] ; ring

theorem shifted_window_budget (J : ℕ) (t θ E : ℝ) (hE : 0≤E) :
    (E*heightCost t θ^(2*J))*profileMoment J^2≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  calc
    _ ≤ E*(heightEnvelope t*(1+‖θ‖))^(2*J)*profileMoment J^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (heightCost_pos _ _).le (heightCost_le_envelope t θ) _) hE)
        (sq_nonneg _)
    _ = _ := by
      rw [show 2*J=J*2 by omega,pow_mul]
      simp only [windowBudget,mul_pow,Real.sq_sqrt hE]
      ring

end SevenEighths.CenteredMomentSecondWindowBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceDyadicWindowEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentLogDyadic CenteredMomentSecondWindowSource CenteredMomentSecondWindowBudget
open IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

theorem column_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase logAnnulus
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  exact (column_window_energy s Q C hQ hC hQC τ t θ X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth L a ha U K hK hU J E hE henergy).trans
      (shifted_window_budget J t θ E hE)

theorem column_star_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*star (columnPhase logAnnulus
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ)) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  simpa only [star_logAnnulus_column,norm_neg] using
    column_dyadic_window_energy s Q C hQ hC hQC τ t (-θ) X hX L a ha U K hK hU J E hE henergy

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedZeroEnergy
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentZeroMode
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentZeroMeanBridge EisensteinSchwartzPoisson HeckeFamily
local notation "O" => ActualEisensteinCubic.O

theorem finiteColumnCoefficient_witness {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O)
    (hI : finiteColumnCoefficient S β I≠0) :
    ∃ v∈S, β v≠0 ∧ finiteTupleProduct v=I := by
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  exact ⟨v,(Finset.mem_filter.mp hv).1,hne,(Finset.mem_filter.mp hv).2⟩

end SevenEighths.CenteredMomentSupportedZeroEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy CenteredMomentCommonSupport
open CenteredMomentChildAssembly CenteredMomentAddedZeroUniform RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

variable {ι:Type*}[Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentFirstPhysicalSource.firstFixedFamilyDecidableEq
theorem beta_coprime (s:OriginalData ι)(I:Ideal O)(h:s.beta I≠0):IsCoprime I s.R:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.S) s.profile I h
  rw [←he]
  by_contra hn
  apply hv0
  simp only [OriginalData.profile,profileCoefficient,hn,ite_false,mul_zero,zero_mul]

lemma extracted_mask_redundant (s:OriginalData ι)(C:Ideal O):
    maskedSource (idealGenerator s.R) (fun I=>s.beta (C*I))=(fun I=>s.beta (C*I)):=by
  apply maskedSource_eq_of_live
  intro I hI
  rw [span_idealGenerator]
  exact (beta_coprime s (C*I) hI).of_mul_left_right

theorem fixed_divisor_column (s:OriginalData ι)(η τ:Character)(C:Ideal O)
    (F:O→ℂ)(ξ:RayCharacter)
    (hτ:∀I:Ideal O,Supported I→∀t:ℝ,heightCoeff τ t I=
      rowWeight η fixedBadMask 1 1 t I*(F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (L I:Ideal O)(hI:Supported I)(t:ℝ):
    divisorCoefficient L (fun J:Ideal O=>primaryGenerator J)
      (fun J=>s.beta (C*J)*rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t J*
        F (primaryGenerator J)) ξ I=
      (if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I:=by
  have hh:=divisor_column_masked η τ F ξ hτ (idealGenerator s.R) L I hI (fun J=>s.beta (C*J)) t
  rw [extracted_mask_redundant] at hh
  exact hh

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonSupport CenteredMomentConjugateWindow
open CenteredMomentChildAssembly RayFourExpansion CompletedGauss CenteredMomentGaussEnergy FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.right_column (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (s:OriginalData ι)(t:ℝ)(L:Ideal O)(I:columns C D hD.1 s.columns):
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta D a*
        rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C D hD.1 s.columns a)) ξ₂ I=
      (if L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff F.right t I:=
  fixed_divisor_column s η F.right D _ ξ₂ F.right_height L I
    (column_supported C D hD.1 s.columns I) t

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.right_window_energy_oai (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(B:ℝ)(hB:0≤B)
    (hsource:∀v:ℝ,(commonEnergy s D hD F.right v L U K).re≤B*(1+‖v‖)^(2*J)):
    (∑'z:O,((‖rightWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L θ X logAnnulus z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K)).re≤(windowBudget J t B*(1+‖θ‖)^J)^2:=by
  exact column_star_dyadic_window_energy s C D hC.1 hD hCD F.right t θ X hX L _
    (F.right_column hD s t L) U K hK hU J B hB hsource

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentFirstPhysicalSource.FixedPair.right_window_energy_oai.{u_1} := @OAI.SevenEighths.CenteredMomentFirstPhysicalSource.FixedPair.right_window_energy_oai.{u_1}
