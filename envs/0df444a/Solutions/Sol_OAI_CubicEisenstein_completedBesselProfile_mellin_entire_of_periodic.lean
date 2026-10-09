-- Prove2me | solution 1 for OAI.CubicEisenstein.completedBesselProfile_mellin_entire_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:10:09.143983+00:00
-- url     : https://prove2.me/submissions/98a09bb4-4045-4d91-a106-c9a01e68dce9

import Mathlib
import Definitions.Def_OAIHecke78B021

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
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

namespace CompletedGauss

section

open ActualEisensteinCubic

theorem primaryGenerator_norm_sq (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator I)‖ ^ 2 = (Ideal.absNorm I : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, (primaryGenerator_spec I h).1]

open ActualEisensteinCubic

end
section

open ActualEisensteinCubic ConcreteTraceCRT

theorem squarefreeGaussCoefficient_eq (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    squarefreeGaussCoefficient I =
      star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I hI := by
  rw [squarefreeGaussCoefficient, dif_pos ⟨hs, hI⟩]

theorem primaryGenerator_norm (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    ‖eisEmbedding (primaryGenerator I)‖ = Real.sqrt (Ideal.absNorm I : ℝ) := by
  rw [← primaryGenerator_norm_sq I hI, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem columnWeight_eq (Ψ : O →* ℂ) (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    columnWeight Ψ I = star (FiniteGaussPhase.angularFactor (primaryGenerator I)) *
      gaussTwo I hI * Ψ (primaryGenerator I) := by
  rw [columnWeight, squarefreeGaussCoefficient_eq I hs hI]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
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

namespace CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

theorem symbol_traceLambda_congr_mod_nine (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol traceLambda x = symbol traceLambda y := by
  rw [symbol_traceLambda_eq_linearRay x hx, symbol_traceLambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 0 (-1) x y hx hy hxy

end CubicRamified

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RowCaps
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

open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff

namespace CubicEisenstein

lemma mobiusSpatial_positive (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    0< mobiusSpatial g p 2 := div_pos hp (mobiusSpatialDenominator_pos g p hp)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage
namespace OAI

noncomputable section

namespace CubicEisenstein

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem rational_cusp_average_right_T (r:SL(2,ℤ)) (n:ℕ) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)∂hyperbolicVolume)=
    ∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex r • w)∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (rationalComplex r • w)
  have hf : Continuous f := (hyperbolicEisenstein_continuous s hs).comp (continuous_hyperbolic_action _)
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).comp (continuous_hyperbolic_action _)
  change (∫w in cuspPeriodStrip 5 6,f w∂hyperbolicVolume)=∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates f hf.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable f hf),
    cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  dsimp only
  apply congrArg (fun q:ℂ=>q/(v:ℂ)^3)
  simp_rw [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper]
  have hh:=period_integral_translation
    (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0))
    (fun a z=>hyperbolicEisenstein_rational_periodic r a s hs z v hv0) (n:ℂ)
  simpa only [add_comm] using hh

theorem translatedCuspFourier_residue_eq_of_initial (M N:levelTwo)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix M • w)∂hyperbolicVolume)=
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix N • w)∂hyperbolicVolume) :
    translatedCuspFourier 0 M cubicEisensteinResidue=
      translatedCuspFourier 0 N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedCuspFamily 0 M 2 3 (by norm_num) (by norm_num)
  let g : ℂ→ℂ := translatedCuspFamily 0 N 2 3 (by norm_num) (by norm_num)
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal 0 M 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal 0 N 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedCuspFamily_initial 0 M 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      translatedCuspFamily_initial 0 N 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2]
    simp only [cuspFourierPhase_zero,mul_one]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedCuspFamily_residue_limit 0 M 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  have hr := (translatedCuspFamily_residue_limit 0 N 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  exact congrArg (fun z:ℂ=>((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*z) hv

end

open CubicKubota

lemma translatedCuspFourier_one_residue :
    translatedCuspFourier 0 1 cubicEisensteinResidue=cuspConstantAverageResidue := by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one,
    kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average]

lemma translatedCuspFourier_bruhat_residue (i:RationalBruhatIndex) :
    translatedCuspFourier 0 (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue=
      cuspConstantAverageResidue := by
  rcases i with ⟨e,a|⟨a,b⟩⟩
  · calc
      _=translatedCuspFourier 0 1 cubicEisensteinResidue := by
        apply translatedCuspFourier_residue_eq_of_initial
        intro s hs hi
        simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
        simp only [map_one,one_smul]
      _=cuspConstantAverageResidue := translatedCuspFourier_one_residue
  · calc
      _=translatedCuspFourier 0 oppositeSource cubicEisensteinResidue := by
        apply translatedCuspFourier_residue_eq_of_initial
        intro s hs hi
        simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
        change (∫w in cuspPeriodStrip 5 6,
          hyperbolicEisenstein s (rationalComplex ModularGroup.S •
            (rationalComplex (ModularGroup.T^b.val) • w))∂hyperbolicVolume)=
          ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)∂hyperbolicVolume
        simpa only [map_mul,mul_smul] using
          rational_cusp_average_right_T ModularGroup.S b.val s (by linarith)
      _=cuspConstantAverageResidue := translatedCuspFourier_opposite_zero_residue

theorem kernelSourceProjection_residue_cusp_average :
    kernelCuspStripAverage (kernelSourceProjection cubicEisensteinResidue)=
      cuspConstantAverageResidue := by
  rw [←kernelCuspFourier_zero,kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  have he (i:RationalBruhatIndex) :
      kernelCuspFourier 0 (kernelSourcePullback (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=
        cuspConstantAverageResidue := translatedCuspFourier_bruhat_residue i
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_sum,
    Fintype.card_fin,smul_eq_mul,nsmul_eq_mul]
  norm_num
  ring

theorem cubicSourceResidualFunction_cusp_average :
    (∫w in cuspPeriodStrip 5 6,cubicSourceResidualFunction w∂hyperbolicVolume)=
      cuspConstantAverageResidue := by
  rw [←kernelSourceProjection_residue_cusp_average,kernelCuspStripAverage_hyperbolic]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae cubicSourceResidualFunction_represents_projection] with w hw
  exact hw.symm

theorem cubicSourceResidualFunction_ne_zero : cubicSourceResidualFunction≠0 := by
  intro hz
  have he:=cubicSourceResidualFunction_cusp_average
  rw [hz] at he
  simp only [Pi.zero_apply,integral_zero] at he
  exact cuspConstantAverageResidue_ne_zero he.symm

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform
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

open scoped BigOperators Classical
namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem primeCubicGauss_trivial_nonzero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (he:3∣e) (h:Eis) (hph:¬p∣h):
    primeCubicGauss p hp hprimary e h=-1:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h≠0:=by
    intro hh
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  rw [primeCubicGauss_eq_gaussSum,(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he]
  exact gaussSum_one_left (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero hh)

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.TranslatedFourierResidues
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma brevePhase_hasDerivAt (freq z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ShortDraftTrace.breveE (freq*(z+(x:ℂ)*direction)))
      (horizontalPhaseMultiplier freq direction*
        ShortDraftTrace.breveE (freq*(z+(t:ℂ)*direction))) t := by
  have hz : HasDerivAt (fun x : ℝ => freq*(z+(x:ℂ)*direction)) (freq*direction) t := by
    convert (preTransparency := .instances) (((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const direction).const_add z).const_mul freq using 1 <;>
      simp
  have he := ((hz.add hz.star).const_mul (2*Real.pi*Complex.I)).cexp
  change HasDerivAt (fun x : ℝ => Complex.exp ((2*Real.pi*Complex.I)*
    (freq*(z+(x:ℂ)*direction)+star (freq*(z+(x:ℂ)*direction)))))
    ((2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))*
      Complex.exp ((2*Real.pi*Complex.I)*
        (freq*(z+(t:ℂ)*direction)+star (freq*(z+(t:ℂ)*direction))))) t
  simpa only [Pi.add_apply,mul_comm] using he

lemma horizontalPhaseMultiplier_norm (freq direction : ℂ) :
    ‖horizontalPhaseMultiplier freq direction‖≤4*Real.pi*‖freq‖*‖direction‖ := by
  have hc : ‖(2*Real.pi*Complex.I:ℂ)‖=2*Real.pi := by
    norm_num [norm_mul,abs_of_pos Real.pi_pos]
  unfold horizontalPhaseMultiplier
  rw [norm_mul,hc]
  calc
    _ ≤ (2*Real.pi)*(‖freq*direction‖+‖star (freq*direction)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = _ := by rw [norm_star,norm_mul];ring

lemma summable_norm_mul_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => ‖cuspFrequency h‖*Real.exp (-a*‖cuspFrequency h‖)) := by
  apply Summable.of_nonneg_of_le (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (fun h => norm_mul_exp_neg_bound a _ ha)
  exact (summable_exp_neg_cuspFrequency_norm (a/2) (half_pos ha)).mul_left (2/a)

local notation "O" => ActualEisensteinCubic.O

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.PrimePowerGaussSums
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
namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma series_bessel (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.series (v,z)=∑'h : ActualEisensteinCubic.O,coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  exact tsum_congr (fun h => coeff.term_eq_amplitude v hv h z)

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O
end CubicEisenstein

open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.BesselDerivatives
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma cubicBesselDensity_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y : ℝ => cubicBesselDensity y t) (cubicBesselDensityDeriv x t) x := by
  have he := ((((hasDerivAt_id x).pow 2).div_const (4*t)).const_sub (-t)).exp.const_mul (t^(-(2:ℝ)/3))
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one] at he
  convert (preTransparency := .instances) he using 1
  · funext y
    rfl
  · unfold cubicBesselDensityDeriv cubicBesselDensity
    ring

lemma cubic_exp_damping (y : ℝ) : y*Real.exp (-y)≤1 := by
  have hy : y≤Real.exp y := by linarith [Real.add_one_le_exp y]
  calc
    _ ≤ Real.exp y*Real.exp (-y) := mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
    _ = 1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]

lemma cubicBesselDensityDeriv_bound (delta x t : ℝ)
    (hdelta : 0<delta) (hx : delta≤x) (ht : 0<t) :
    ‖cubicBesselDensityDeriv x t‖≤
      (4/delta)*Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
  have hxp : 0<x := hdelta.trans_le hx
  have hdamp : (x/(2*t))*Real.exp (-(x^2/(8*t)))≤4/x := by
    have hrewrite : x/(2*t)=(4/x)*(x^2/(8*t)) := by field_simp;ring
    rw [hrewrite,mul_assoc]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (cubic_exp_damping (x^2/(8*t))) (by positivity : 0≤4/x)
  have hyoung : x/2-t/2≤x^2/(8*t) :=
    (le_div_iff₀ (show 0<8*t by positivity)).mpr (by nlinarith [sq_nonneg (x-2*t)])
  have he : Real.exp (-t-x^2/(4*t))≤
      Real.exp (-x/2)*Real.exp (-t/2)*Real.exp (-(x^2/(8*t))) := by
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsplit : x^2/(4*t)=2*(x^2/(8*t)) := by ring
    rw [hsplit]
    linarith
  have hnorm : ‖cubicBesselDensityDeriv x t‖=
      (x/(2*t))*t^(-(2:ℝ)/3)*Real.exp (-t-x^2/(4*t)) := by
    unfold cubicBesselDensityDeriv cubicBesselDensity
    rw [norm_mul,norm_neg,Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)]
    ring
  rw [hnorm]
  calc
    _ ≤ (x/(2*t))*t^(-(2:ℝ)/3)*
        (Real.exp (-x/2)*Real.exp (-t/2)*Real.exp (-(x^2/(8*t)))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((x/(2*t))*Real.exp (-(x^2/(8*t))))*
        Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by ring
    _ ≤ (4/x)*Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
      gcongr
    _ ≤ _ := by
      gcongr

lemma cubicBesselDerivativeMajorant_integrable :
    IntegrableOn (fun t : ℝ => t^(-(2:ℝ)/3)*Real.exp (-t/2)) (Set.Ioi 0) volume := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (s:=-(2:ℝ)/3) (p:=1) (b:=1/2)
    (by norm_num) (by norm_num) (by norm_num)
  apply hh.congr
  filter_upwards with t
  rw [Real.rpow_one]
  congr 1
  congr 1
  ring

lemma cubicBesselDensityDeriv_integrable (x : ℝ) (hx : 0<x) :
    IntegrableOn (cubicBesselDensityDeriv x) (Set.Ioi 0) volume := by
  apply (cubicBesselDerivativeMajorant_integrable.const_mul ((4/x)*Real.exp (-x/2))).mono'
  · unfold cubicBesselDensityDeriv cubicBesselDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselDensityDeriv_bound x x t hx le_rfl ht

lemma cubicBesselIntegral_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun y : ℝ => ∫t in Set.Ioi (0:ℝ),cubicBesselDensity y t)
      (∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  have hU : Set.Ioi delta∈𝓝 x := isOpen_Ioi.mem_nhds (by
    change delta<x
    dsimp [delta]
    linarith)
  have hbound : ∀ᵐt ∂volume.restrict (Set.Ioi (0:ℝ)),∀y∈Set.Ioi delta,
      ‖cubicBesselDensityDeriv y t‖≤(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : 0<t := ht
    intro y hy
    have hyp : 0<y := hdelta.trans hy
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (F := cubicBesselDensity) (F' := cubicBesselDensityDeriv)
    (bound := fun t => (4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2))) hU
    (Eventually.of_forall (fun y => by unfold cubicBesselDensity;fun_prop))
    (cubicBesselDensity_integrable x)
    (by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
    hbound (cubicBesselDerivativeMajorant_integrable.const_mul (4/delta))
    (Eventually.of_forall (fun t y _ => cubicBesselDensity_hasDerivAt y t))
  exact h.2

lemma schlafliBesselK_cubic_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun y : ℝ => schlafliBesselK (1/3) y)
      (schlafliBesselK_cubic_derivative x) x := by
  have hp : HasDerivAt (fun y : ℝ => (1/2:ℝ)*(y/2)^(-(1:ℝ)/3))
      ((-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)) x := by
    have hh := (((hasDerivAt_id x).div_const 2).rpow_const
      (p:=-(1:ℝ)/3) (Or.inl (by positivity : x/2≠0))).const_mul (1/2:ℝ)
    convert (preTransparency := .instances) hh using 1 <;> norm_num ; ring
  have hr := hp.mul (cubicBesselIntegral_hasDerivAt x hx)
  have hreal : HasDerivAt (fun y : ℝ => (1/2:ℝ)*(y/2)^(-(1:ℝ)/3)*
      (∫t in Set.Ioi (0:ℝ),cubicBesselDensity y t)) (cubicBesselRealDeriv x) x := by
    exact hr
  apply hreal.ofReal_comp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact schlafliBesselK_cubic_real y hy

lemma cubicBesselDerivativeMajorant_integral :
    (∫t in Set.Ioi (0:ℝ),t^(-(2:ℝ)/3)*Real.exp (-t/2))=
      (2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3) := by
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1/3:ℝ)) (r := (1/2:ℝ)) (by norm_num) (by norm_num)
  convert (preTransparency := .instances) hh using 1 <;> norm_num ; congr 2 ; funext t ; ring_nf

lemma cubicBesselIntegral_norm_bound (x : ℝ) :
    ‖∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t‖≤
      Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hpos : 0≤∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselDensity_nonneg x t ht.le
  rw [Real.norm_of_nonneg hpos]
  exact cubicBesselIntegral_upper x

lemma cubicBesselIntegralDeriv_norm_bound (delta x : ℝ) (hdelta : 0<delta) (hx : delta≤x) :
    ‖∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t‖≤
      (4/delta)*Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hi := cubicBesselDensityDeriv_integrable x (hdelta.trans_le hx)
  have hb := integral_mono_ae hi.norm
    (cubicBesselDerivativeMajorant_integrable.const_mul ((4/delta)*Real.exp (-x/2)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselDensityDeriv_bound delta x t hdelta hx ht)
  rw [integral_const_mul,cubicBesselDerivativeMajorant_integral] at hb
  exact (norm_integral_le_integral_norm _).trans hb

lemma cubicBesselDerivativeUpper_nonneg (delta : ℝ) (hdelta : 0<delta) :
    0≤ cubicBesselDerivativeUpper delta := by
  unfold cubicBesselDerivativeUpper
  positivity

lemma schlafliBesselK_cubic_derivative_bound (delta x : ℝ) (hdelta : 0<delta) (hx : delta≤x) :
    ‖schlafliBesselK_cubic_derivative x‖≤ cubicBesselDerivativeUpper delta*Real.exp (-x/2) := by
  have hxp : 0<x := hdelta.trans_le hx
  have hp1 : (x/2)^(-(1:ℝ)/3)≤(delta/2)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hp4 : (x/2)^(-(4:ℝ)/3)≤(delta/2)^(-(4:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  rw [schlafliBesselK_cubic_derivative,Complex.norm_real,cubicBesselRealDeriv]
  calc
    _ ≤ ‖(-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)‖+
        ‖(1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t)‖ := norm_add_le _ _
    _ = (1/12:ℝ)*(x/2)^(-(4:ℝ)/3)*‖∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t‖+
        (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*‖∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t‖ := by
      have hn4 : ‖(x/2)^(-(4:ℝ)/3)‖=(x/2)^(-(4:ℝ)/3) :=
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      have hn1 : ‖(x/2)^(-(1:ℝ)/3)‖=(x/2)^(-(1:ℝ)/3) :=
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      simp only [norm_mul,hn4,hn1]
      norm_num
    _ ≤ (1/12:ℝ)*(delta/2)^(-(4:ℝ)/3)*
          (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)))+
        (1/2:ℝ)*(delta/2)^(-(1:ℝ)/3)*
          ((4/delta)*Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      gcongr
      · exact cubicBesselIntegral_norm_bound x
      · exact cubicBesselIntegralDeriv_norm_bound delta x hdelta hx
    _ = _ := by unfold cubicBesselDerivativeUpper;ring

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicGauss_add_three (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis):primeCubicGauss p hp hprimary (e+3) h=primeCubicGauss p hp hprimary e h:=by
  unfold primeCubicGauss
  rw [pow_add,primeCubicMulChar_cube,mul_one]

lemma cubicUnitGaussSum_prime_cube_shift_pos (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum (h*p^3) (p^(n+4))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*cubicUnitGaussSum h (p^(n+1)):=by
  by_cases hd:p^n∣h
  · obtain ⟨r,rfl⟩:=hd
    have harg:p^n*r*p^3=p^(n+3)*r:=by rw [pow_add];ring
    rw [harg,show n+4=(n+3)+1 by omega,
      cubicUnitGaussSum_prime_power_lift p hp hprimary (n+3) r,
      cubicUnitGaussSum_prime_power_lift p hp hprimary n r]
    rw [show n+3+1=(n+1)+3 by omega,primeCubicGauss_add_three,pow_add]
    ring
  · have hlow:cubicUnitGaussSum h (p^(n+1))=0:=by
      by_contra hh
      exact hd (cubicUnitGaussSum_prime_power_support p hp hprimary n h hh)
    have hhigh:cubicUnitGaussSum (h*p^3) (p^(n+4))=0:=by
      by_contra hh
      have hh':cubicUnitGaussSum (h*p^3) (p^((n+3)+1))≠0:=by convert (preTransparency := .instances) hh using 1
      have hd':p^(n+3)∣h*p^3:=cubicUnitGaussSum_prime_power_support p hp hprimary (n+3) (h*p^3) hh'
      have hd'':p^3*p^n∣p^3*h:=by simpa only [pow_add,mul_comm,mul_left_comm,mul_assoc] using hd'
      exact hd ((mul_dvd_mul_iff_left (pow_ne_zero 3 hp.ne_zero)).mp hd'')
    rw [hhigh,hlow,mul_zero]

lemma cubicUnitGaussSum_prime_cube_shift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (k:ℕ) (h:Eis):
    cubicUnitGaussSum (h*p^3) (p^(k+3))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*cubicUnitGaussSum h (p^k)-
        if k=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2 else 0:=by
  cases k with
  | zero=>
    rw [Nat.zero_add,cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      (dvd_mul_left (p^3) h)]
    have he:=cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    norm_num at he ⊢
    rw [he]
    ring
  | succ n=>
    simpa only [show n+1+3=n+4 by omega,Nat.succ_ne_zero,ite_false,sub_zero] using
      cubicUnitGaussSum_prime_cube_shift_pos p hp hprimary n h

private lemma primeExpansionTerm_cube_shift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (h:Eis) (k:ℕ):
    primeExpansionTerm p s (h*p^3) (k+3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        primeExpansionTerm p s h k-
      if k=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*unramifiedPrimeDeletedSeries p s h else 0:=by
  have hv:unramifiedPrimeDeletedSeries p s (h*p^3*p^(k+3))=
      unramifiedPrimeDeletedSeries p s (h*p^k):=by
    have he:h*p^3*p^(k+3)=(h*p^k*p^3)*p^3:=by rw [pow_add];ring
    rw [he,unramifiedPrimeDeletedSeries_cube_shift p hp,
      unramifiedPrimeDeletedSeries_cube_shift p hp]
  unfold primeExpansionTerm
  rw [cubicUnitGaussSum_prime_cube_shift p hp hprimary k h,hv,pow_add]
  split_ifs with hk
  · subst k
    simp only [pow_zero,mul_one,cubicUnitGaussSum_one]
    ring
  · ring

theorem unramifiedCubicGaussSeries_cube_step (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^(a+3))=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^a)+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph (a+3)
  have hold:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph a
  change unramifiedCubicGaussSeries s (h*p^a)=
    ∑k∈Finset.range (a+2),primeExpansionTerm p s (h*p^a) k at hold
  have harg:h*p^(a+3)=(h*p^a)*p^3:=by rw [pow_add,mul_assoc]
  change unramifiedCubicGaussSeries s (h*p^(a+3))=
    ∑k∈Finset.range (a+3+2),primeExpansionTerm p s (h*p^(a+3)) k at he
  rw [show a+3+2=3+(a+2) by omega,Finset.sum_range_add,harg] at he
  have hsmall:∑k∈Finset.range 3,primeExpansionTerm p s (h*p^a*p^3) k=
      unramifiedPrimeDeletedSeries p s (h*p^a):=by
    have hg1:cubicUnitGaussSum (h*p^a*p^3) p=0:=by
      rw [cubicUnitGaussSum_frequency_dvd _ _ hp.ne_zero
        ((dvd_pow_self p (by decide:3≠0)).trans (dvd_mul_left (p^3) (h*p^a)))]
      simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
    have hg2:cubicUnitGaussSum (h*p^a*p^3) (p^2)=0:=by
      rw [cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
        ((pow_dvd_pow p (by omega:2≤3)).trans (dvd_mul_left (p^3) (h*p^a)))]
      simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,primeExpansionTerm,
      pow_zero,pow_one,cubicUnitGaussSum_one,mul_one,one_mul,zero_add,hg1,hg2,
      mul_zero,zero_mul,add_zero]
    rw [unramifiedPrimeDeletedSeries_cube_shift p hp]
  rw [hsmall] at he
  have htail:∑k∈Finset.range (a+2),primeExpansionTerm p s (h*p^a*p^3) (3+k)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedPrimeDeletedSeries p s (h*p^a):=by
    simp_rw [show ∀k:ℕ,3+k=k+3 by omega,primeExpansionTerm_cube_shift p hp hprimary]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←hold]
    simp
  rw [htail,←harg] at he
  exact he.trans (by ring)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

lemma inverseCuspPath_zero (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) :
    inverseCuspPath c d v direction 0=(-d/c,1/(‖c‖^2*v)) := by
  unfold inverseCuspPath
  simp only [Complex.ofReal_zero,zero_pow (by decide : 2≠0),zero_mul,add_zero,zero_div,sub_zero]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hc,hv.ne']

theorem inverseCuspPath_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) :
    HasDerivAt (inverseCuspPath c d v direction)
      (-(star direction)/(c^2*(v:ℂ)^2),0) 0 := by
  have hn : ‖c‖≠0 := norm_ne_zero_iff.mpr hc
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hden : HasDerivAt (fun t : ℝ=>v^2+t^2*‖direction‖^2) 0 0 := by
    convert (preTransparency := .instances) (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (‖direction‖^2)).const_add (v^2) using 1 <;> norm_num
  have hnum : HasDerivAt (fun t : ℝ=>(t:ℂ)*star direction) (star direction) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const (star direction))
  have hdenC := hden.ofReal_comp.const_mul (c^2)
  have hdenR := hden.const_mul (‖c‖^2)
  have hcz : c^2*((v^2+(0:ℝ)^2*‖direction‖^2:ℝ):ℂ)≠0 := by
    simpa using mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 hvc)
  have hrz : ‖c‖^2*(v^2+(0:ℝ)^2*‖direction‖^2)≠0 := by positivity
  have hz : HasDerivAt
      (fun t : ℝ=>-d/c-(t:ℂ)*star direction/(c^2*((v^2+t^2*‖direction‖^2:ℝ):ℂ)))
      (-(star direction)/(c^2*(v:ℂ)^2)) 0 := by
    convert (preTransparency := .instances) (hnum.div hdenC hcz).const_sub (-d/c) using 1 ;
      simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero,Complex.ofReal_pow,
        Complex.ofReal_zero,mul_zero,sub_zero]
    field_simp

  have hvd : HasDerivAt (fun t : ℝ=>v/(‖c‖^2*(v^2+t^2*‖direction‖^2))) 0 0 := by
    convert (preTransparency := .instances) (hasDerivAt_const (0:ℝ) v).div hdenR hrz using 1 ; simp
  exact hz.prodMk hvd

theorem inverseCuspPath_comp_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    HasDerivAt (fun t=>F (inverseCuspPath c d v direction t))
      (A (-(star direction)/(c^2*(v:ℂ)^2),0)) 0 := by
  have hf : HasFDerivAt F A (inverseCuspPath c d v direction 0) := by
    rwa [inverseCuspPath_zero c d v direction hc hv]
  exact hf.comp_hasDerivAt 0 (inverseCuspPath_hasDerivAt c d v direction hc hv)

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.InverseCuspCoordinates
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate MatrixGroups Matrix

lemma inverseCuspCoordinates_line (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) :
    inverseCuspCoordinates c d v ((t:ℂ)*direction)=inverseCuspPath c d v direction t := by
  simp only [inverseCuspCoordinates,inverseCuspPath,star_mul,Complex.star_def,
    Complex.conj_ofReal,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,mul_comm]

theorem inverse_cusp_action (g : SL(2,ℂ)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    g⁻¹ • upperPoint (z+g 0 0/g 1 0) v hv =
      upperPoint (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1
        (inverseCuspCoordinates (g 1 0) (g 1 1) v z).2
        (inverseCuspCoordinates_height_pos _ _ _ _ hc hv) := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have h00 : (g⁻¹) 0 0=g 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h01 : (g⁻¹) 0 1= -g 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h10 : (g⁻¹) 1 0= -g 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h11 : (g⁻¹) 1 1=g 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have hl : (-g 1 0)*(z+g 0 0/g 1 0)+g 0 0= -(g 1 0*z) := by
    field_simp
    ; ring
  have ht : g 1 1*(z+g 0 0/g 1 0)+(-g 0 1)=g 1 1*z+1/g 1 0 := by
    field_simp
    linear_combination hdet
  have hden : ‖-(g 1 0*z)‖^2+‖-g 1 0‖^2*v^2=
      ‖g 1 0‖^2*(v^2+‖z‖^2) := by rw [norm_neg,norm_neg,norm_mul,mul_pow];ring
  have hnormc : ((‖g 1 0‖^2:ℝ):ℂ)=g 1 0*star (g 1 0) := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj (g 1 0)).symm
  have hnormz : ((‖z‖^2:ℝ):ℂ)=z*star z := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj z).symm
  have hT : v^2+‖z‖^2≠0 := by positivity
  have hTc : ((v^2+‖z‖^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hT
  have hcc : star (g 1 0)≠0 := star_ne_zero.mpr hc
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · rw [h00,h01,h10,h11,hl,ht,hden]
    dsimp [inverseCuspCoordinates]
    rw [Complex.ofReal_mul,hnormc]
    simp only [Complex.star_def,map_neg,map_mul]
    simp only [Complex.star_def] at hcc
    field_simp [hc,hcc,hTc]
    rw [Complex.ofReal_add,Complex.ofReal_pow,hnormz]
    simp only [Complex.star_def,]
    ; ring
  · rw [h10,h11,hl,hden]
    rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

lemma real_linear_horizontal_decompose (A : (ℂ×ℝ)→L[ℝ]ℂ) (z : ℂ) :
    A (z,0)=(z.re:ℂ)*A (1,0)+(z.im:ℂ)*A (Complex.I,0) := by
  have hz : ((z,0):ℂ×ℝ)=z.re • (1,0)+z.im • (Complex.I,0) := by
    apply Prod.ext
    · simpa only [Prod.fst_add,Prod.smul_fst,Complex.real_smul,mul_one] using z.re_add_im.symm
    · simp
  rw [hz,map_add,map_smul,map_smul]
  simp only [Complex.real_smul]

lemma real_linear_wirtinger_swap (A : (ℂ×ℝ)→L[ℝ]ℂ) (k : ℂ) :
    (1/2:ℂ)*(A (k,0)+Complex.I*A (-Complex.I*k,0))=
      k*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  rw [real_linear_horizontal_decompose A k,real_linear_horizontal_decompose A (-Complex.I*k)]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,zero_mul,neg_mul,one_mul,
    zero_add,zero_sub,Complex.ofReal_neg]
  conv_rhs => lhs; rw [←k.re_add_im]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem inverse_cusp_wirtingerBar (c d : ℂ) (v : ℝ) (hc : c≠0) (hv : 0<v)
    (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    horizontalWirtingerBar (fun z=>F (inverseCuspCoordinates c d v z)) 0=
      (-1/(c^2*(v:ℂ)^2))*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  have h1 := (inverseCuspPath_comp_hasDerivAt c d v 1 hc hv F A hF).deriv
  have hI := (inverseCuspPath_comp_hasDerivAt c d v Complex.I hc hv F A hF).deriv
  have he1 : (fun t : ℝ=>F (inverseCuspCoordinates c d v (t:ℂ)))=
      (fun t : ℝ=>F (inverseCuspPath c d v 1 t)) := by
    funext t
    rw [←inverseCuspCoordinates_line]
    simp only [mul_one]
  have heI : (fun t : ℝ=>F (inverseCuspCoordinates c d v ((t:ℂ)*Complex.I)))=
      (fun t : ℝ=>F (inverseCuspPath c d v Complex.I t)) := by
    funext t
    rw [inverseCuspCoordinates_line]
  rw [horizontalWirtingerBar]
  simp only [zero_add]
  rw [he1,heI,h1,hI]
  simp only [star_one,Complex.star_def,Complex.conj_I,neg_neg]
  convert (preTransparency := .instances) real_linear_wirtinger_swap A (-1/(c^2*(v:ℂ)^2)) using 1 ;
    congr 2 ; ring_nf

lemma horizontalWirtingerZ_eq_fderiv (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (z : ℂ) (v : ℝ) (hF : HasFDerivAt F A (z,v)) :
    horizontalWirtingerZ (fun w=>F (w,v)) z=
      (1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0)) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ=>F (z+(t:ℂ)*direction,v)) (A (direction,0)) 0 := by
    have hz : HasDerivAt (fun t : ℝ=>z+(t:ℂ)*direction) direction 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const direction).const_add z)
    have hp := hz.prodMk (hasDerivAt_const (0:ℝ) v)
    have hf : HasFDerivAt F A (z+(0:ℂ)*direction,v) := by simpa using hF
    exact hf.comp_hasDerivAt 0 hp
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerZ,h1,hI]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

theorem cusp_mellin_reflection (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q) :
    mellin (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) (2*s)=
      A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  have he : (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹)))=
      (fun v : ℝ=>A • ((v:ℂ)^(-2:ℂ) • g ((Q*v)⁻¹))) := by
    funext v; simp only [smul_eq_mul]
  rw [he,mellin_const_smul,mellin_cpow_smul]
  have hm := mellin_comp_mul_left (fun v : ℝ=>g v⁻¹) (2*s+(-2:ℂ)) hQ
  rw [mellin_comp_inv] at hm
  rw [hm]
  simp only [smul_eq_mul]
  rw [show -(2*s+(-2:ℂ))=2-2*s by ring]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma horizontalPhaseCLM_apply (freq direction : ℂ) :
    horizontalPhaseCLM freq direction = horizontalPhaseMultiplier freq direction := by
  simp [horizontalPhaseCLM,horizontalPhaseMultiplier]
  ring

lemma brevePhase_hasFDerivAt (freq z : ℂ) :
    HasFDerivAt (fun w : ℂ => ShortDraftTrace.breveE (freq*w))
      (ShortDraftTrace.breveE (freq*z) • horizontalPhaseCLM freq) z := by
  have hh := (horizontalPhaseCLM freq).hasFDerivAt.cexp (x:=z)
  convert! (preTransparency := .instances) hh using 1

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma amplitude_hasDerivAt (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    HasDerivAt (fun y : ℝ => coeff.amplitude y h) (coeff.amplitudeDeriv v h) v := by
  by_cases hh : h=0
  · simp only [amplitude,amplitudeDeriv,if_pos hh]
    exact hasDerivAt_const v 0
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hslope : HasDerivAt (fun y : ℝ => 4*Real.pi*‖cuspFrequency h‖*y)
      (4*Real.pi*‖cuspFrequency h‖) v := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id v).const_mul (4*Real.pi*‖cuspFrequency h‖)
  have hk := (schlafliBesselK_cubic_hasDerivAt (4*Real.pi*‖cuspFrequency h‖*v)
    (by positivity)).scomp v hslope
  have hvd := (Complex.ofRealCLM.hasDerivAt (x:=v)).mul hk
  have hfull := hvd.const_mul (coeff.value h)
  simp only [amplitude,amplitudeDeriv,if_neg hh]
  convert! (preTransparency := .instances) hfull using 1 <;> simp [Function.comp_def,Pi.mul_apply,Complex.ofRealCLM_apply,Complex.real_smul,mul_assoc]

lemma term_hasFDerivAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt (coeff.term h) (coeff.termFDeriv h p) p := by
  by_cases hh : h=0
  · have hzero : coeff.term h=(fun _ : ℝ × ℂ => (0:ℂ)) := by
      funext q
      simp only [term,if_pos hh]
    rw [hzero,termFDeriv,if_pos hh]
    exact hasFDerivAt_const (𝕜:=ℝ) (0:ℂ) p
  have hvd := (coeff.amplitude_hasDerivAt p.1 hp h).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜:=ℝ) (p:=p))
  have hzd := (brevePhase_hasFDerivAt (cuspFrequency h) p.2).comp p
    (hasFDerivAt_snd (𝕜:=ℝ) (p:=p))
  have hprod : HasFDerivAt (fun q : ℝ × ℂ => coeff.amplitude q.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*q.2)) (coeff.termFDeriv h p) p := by
    convert! (preTransparency := .instances) hvd.mul hzd using 1
    apply ContinuousLinearMap.ext
    intro direction
    simp only [termFDeriv,if_neg hh]
    change (direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))+
      coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2 =
      coeff.amplitude p.1 h*(ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        horizontalPhaseCLM (cuspFrequency h) direction.2)+
      ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        ((direction.1:ℂ)*coeff.amplitudeDeriv p.1 h)
    rw [coeff.term_eq_amplitude p.1 hp h p.2]
    ring
  apply hprod.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.term_eq_amplitude q.1 hq h q.2

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma weighted_bessel_bounds (a : ℝ) (ha : 0<a) :
    ∃A B : ℝ,0≤A ∧ 0≤B ∧ ∀(h : ActualEisensteinCubic.O),h≠0 → ∀v : ℝ,a≤v →
      ‖coeff.value h‖*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖≤
        A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) ∧
      ‖coeff.value h‖*‖schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖≤
        B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hKu := (cubicBesselUpperAway_pos delta hdelta).le
  have hKd := cubicBesselDerivativeUpper_nonneg delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*cubicBesselUpperAway delta,C*cubicBesselDerivativeUpper delta,
    mul_nonneg hC hKu,mul_nonneg hC hKd,?_⟩
  intro h hh v hv
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hv ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  have hcombine (y D : ℝ) (hy : 0≤y) (hD : 0≤D)
      (hbound : y≤D*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :
      ‖coeff.value h‖*y≤(C*D)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
    calc
      _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*
          (D*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
        mul_le_mul (hcoeff h hh) hbound hy (by positivity)
      _ = (C*D)*Real.exp ((Real.pi*a)*‖cuspFrequency h‖-
          (4*Real.pi*‖cuspFrequency h‖*v)/2) := by
        rw [show (Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2=
          (Real.pi*a)*‖cuspFrequency h‖+(-(4*Real.pi*‖cuspFrequency h‖*v)/2) by ring,
          Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hD)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hv (mul_pos Real.pi_pos hr).le]
  exact ⟨hcombine _ _ (norm_nonneg _) hKu
    (schlafliBesselK_cubic_upper_away delta _ hdelta hx),
    hcombine _ _ (norm_nonneg _) hKd
    (schlafliBesselK_cubic_derivative_bound delta _ hdelta hx)⟩

lemma amplitudeDeriv_norm_le (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ‖coeff.amplitudeDeriv v h‖≤
      ‖coeff.value h‖*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖+
      (v*(4*Real.pi*‖cuspFrequency h‖))*
        (‖coeff.value h‖*‖schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖) := by
  rw [amplitudeDeriv,if_neg hh,norm_mul]
  calc
    _ ≤ ‖coeff.value h‖*(‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖+
      ‖(v:ℂ)*(4*Real.pi*‖cuspFrequency h‖:ℝ)*
        schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = _ := by
      rw [norm_mul,norm_mul,Complex.norm_of_nonneg hv.le,
        Complex.norm_of_nonneg (by positivity : 0≤4*Real.pi*‖cuspFrequency h‖)]
      ring

lemma termFDeriv_norm_le (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) :
    ‖coeff.termFDeriv h p‖≤‖coeff.amplitudeDeriv p.1 h‖+
      ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := by
  by_cases hh : h=0
  · simp only [termFDeriv,if_pos hh,norm_zero]
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  simp only [termFDeriv,if_neg hh]
  change ‖(direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*p.2))+
    coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2‖≤_
  calc
    _ ≤ ‖(direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))‖+
      ‖coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2‖ := norm_add_le _ _
    _ = ‖direction.1‖*‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*‖horizontalPhaseMultiplier (cuspFrequency h) direction.2‖ := by
      rw [norm_mul,norm_mul,Complex.norm_real,breveE_norm,mul_one,norm_mul,
        horizontalPhaseCLM_apply]
    _ ≤ ‖direction‖*‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*((4*Real.pi*‖cuspFrequency h‖)*‖direction‖) := by
      gcongr
      · exact norm_fst_le direction
      · exact (horizontalPhaseMultiplier_norm _ _).trans (by
          gcongr
          exact norm_snd_le direction)
    _ = _ := by ring

lemma termFDeriv_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.termFDeriv h p‖≤C*((1+‖cuspFrequency h‖)*
        Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨A,B,hA,hB,hweighted⟩ := coeff.weighted_bessel_bounds a ha
  obtain ⟨T,hT,hterm⟩ := coeff.slab_bound a b ha hab
  let D := B*b*(4*Real.pi)+T*(4*Real.pi)
  have hb : 0<b := ha.trans_le hab
  have hD : 0≤D := by dsimp [D];positivity
  refine ⟨A+D,add_nonneg hA hD,?_⟩
  intro h p hp
  by_cases hh : h=0
  · simp only [termFDeriv,if_pos hh,norm_zero]
    positivity
  have hv : 0<p.1 := ha.trans_le hp.1
  obtain ⟨hKu,hKd⟩ := hweighted h hh p.1 hp.1
  have hamp : ‖coeff.amplitudeDeriv p.1 h‖≤
      A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
      (b*(4*Real.pi*‖cuspFrequency h‖))*
        (B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
    apply (coeff.amplitudeDeriv_norm_le p.1 hv h hh).trans
    gcongr
    exact hp.2
  calc
    _ ≤ ‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := coeff.termFDeriv_norm_le h p
    _ ≤ (A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
        (b*(4*Real.pi*‖cuspFrequency h‖))*(B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))+
        (T*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))*(4*Real.pi*‖cuspFrequency h‖) := by
      gcongr
      exact hterm h p hp
    _ = (A+D*‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
      dsimp [D]
      ring
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith [mul_nonneg hA (norm_nonneg (cuspFrequency h))]

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O

lemma summable_one_add_norm_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => (1+‖cuspFrequency h‖)*Real.exp (-a*‖cuspFrequency h‖)) := by
  simpa only [add_mul,one_mul] using
    (summable_exp_neg_cuspFrequency_norm a ha).add (summable_norm_mul_exp_neg_cuspFrequency a ha)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma series_hasFDerivAt (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt coeff.series (∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p) p := by
  let a := p.1/2
  let b := 2*p.1
  have ha : 0<a := by dsimp [a];linarith
  have hab : a≤b := by dsimp [a,b];linarith
  have hap : a<p.1 := by dsimp [a];linarith
  have hpb : p.1<b := by dsimp [b];linarith
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  have hsum := (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a)
    (mul_pos Real.pi_pos ha)).mul_left C
  let slab : Set (ℝ × ℂ) := Set.Ioo a b ×ˢ Set.univ
  have hslab : IsOpen slab := isOpen_Ioo.prod isOpen_univ
  have hconn : IsPreconnected slab := isPreconnected_Ioo.prod isPreconnected_univ
  have hpSlab : p∈slab := ⟨⟨hap,hpb⟩,Set.mem_univ _⟩
  exact hasFDerivAt_tsum_of_isPreconnected hsum hslab hconn
    (fun h q hq => coeff.term_hasFDerivAt h q (ha.trans hq.1.1))
    (fun h q hq => hbound h q ⟨hq.1.1.le,hq.1.2.le⟩)
    hpSlab (coeff.summable p hp) hpSlab

lemma series_differentiableAt (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ coeff.series p := (coeff.series_hasFDerivAt p hp).differentiableAt

lemma fullFunction_cusp_eq (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    coeff.fullFunction constant (cuspCoordinateLift p)=
      constant*(p.1:ℂ)^(2/3:ℂ)+coeff.series p := by
  rw [show p=(p.1,p.2) from rfl,cuspCoordinateLift_positive p.1 p.2 hp]
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]

lemma fullFunction_cusp_differentiableAt (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hc := ((hasDerivAt_ofReal_cpow_const hp.ne' (r:=(2/3:ℂ))
    (by norm_num)).const_mul constant).differentiableAt.comp p
      (differentiableAt_fst (𝕜:=ℝ) (p:=p))
  have ht : DifferentiableAt ℝ (fun q : ℝ × ℂ =>
      constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p := by
    convert! (preTransparency := .instances) hc.add (coeff.series_differentiableAt p hp) using 1
  apply ht.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

lemma truncatedCuspProfile_eventually_top (c : ℝ) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[atTop] f := by
  filter_upwards [eventually_gt_atTop c] with x hx
  simp only [truncatedCuspProfile,if_pos hx]

lemma truncatedCuspProfile_eventually_zero (c : ℝ) (hc : 0<c) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[𝓝[>] 0] 0 := by
  have he : ∀ᶠx : ℝ in 𝓝[>] 0,x<c := (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with x hx
  simp only [truncatedCuspProfile,if_neg (not_lt_of_ge hx.le),Pi.zero_apply]

lemma truncatedCuspProfile_locallyIntegrable (c : ℝ) (hc : 0<c) (f : ℝ→ℂ)
    (hf : ContinuousOn f (Set.Ioi 0)) :
    LocallyIntegrable (truncatedCuspProfile c f) volume := by
  have hcont : Continuous (fun x : ℝ=>f (max (c/2) x)) :=
    hf.comp_continuous (continuous_const.max continuous_id)
      (fun x=>lt_of_lt_of_le (by linarith : 0<c/2) (le_max_left _ _))
  have he : truncatedCuspProfile c f=
      (Set.Ioi c).indicator (fun x : ℝ=>f (max (c/2) x)) := by
    funext x
    by_cases hx : c<x
    · have hm : max (c/2) x=x := max_eq_right (by linarith)
      simp [truncatedCuspProfile,Set.indicator,hx,hm]
    · simp [truncatedCuspProfile,Set.indicator,hx]
  rw [he]
  exact hcont.locallyIntegrable.indicator measurableSet_Ioi

theorem truncatedCuspProfile_mellin_entire (c decay : ℝ) (hc : 0<c) (hdecay : 0<decay)
    (f : ℝ→ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (hbound : f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x))) :
    (∀s : ℂ,MellinConvergent (truncatedCuspProfile c f) s) ∧
      Differentiable ℂ (mellin (truncatedCuspProfile c f)) := by
  have hlocal := (truncatedCuspProfile_locallyIntegrable c hc f hf).locallyIntegrableOn (Set.Ioi 0)
  have htop : truncatedCuspProfile c f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x)) :=
    hbound.congr' (truncatedCuspProfile_eventually_top c f).symm Filter.EventuallyEq.rfl
  have hzero (b : ℝ) : truncatedCuspProfile c f =O[𝓝[>] 0] (fun x : ℝ=>x^(-b)) :=
    (Asymptotics.isBigO_zero (fun x : ℝ=>x^(-b)) (𝓝[>] 0)).congr'
      (truncatedCuspProfile_eventually_zero c hc f).symm Filter.EventuallyEq.rfl
  constructor
  · intro s
    exact mellinConvergent_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)
  · intro s
    exact mellin_differentiableAt_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceBesselExpansion
namespace OAI

noncomputable section

namespace CubicEisenstein

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

theorem cubicSourceResidualFunction_bessel (v:ℝ) (hv:0<v) (z:ℂ) :
    cubicSourceResidualFunction (upperPoint z v hv)=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)+
      ∑'h:ActualEisensteinCubic.O,(if h=0 then 0 else sourceResidualFourierCoefficient h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [cubicSourceResidualFunction_eq_bessel,sourceBesselFunction,SubexponentialBesselCoefficients.fullFunction,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    sourceBesselCoefficients.series_bessel v hv z]
  rfl

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ReflectedCuspMellin
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

lemma reflectedCuspProfile_mellin (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q) :
    mellin (reflectedCuspProfile A Q g) s=
      A*(Q:ℂ)^(2-s)*mellin g (2-s) := by
  unfold reflectedCuspProfile
  have hh := cusp_mellin_reflection g A (s/2) Q hQ
  simpa only [show (2*(s/2):ℂ)=s by ring,reflectedCuspProfile] using hh

lemma reflectedCuspProfile_mellinConvergent (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ)
    (hQ : 0<Q) (hg : MellinConvergent g (2-s)) :
    MellinConvergent (reflectedCuspProfile A Q g) s := by
  unfold reflectedCuspProfile
  have hinv : MellinConvergent (fun t : ℝ=>g t⁻¹) (s-2) := by
    have hh := (MellinConvergent.comp_rpow (f := g) (s := s-2)
      (a := -1) (by norm_num : (-1:ℝ)≠0)).mpr
        (show MellinConvergent g ((s-2)/(-1:ℝ)) by
          simpa only [show ((s-2)/(-1:ℝ):ℂ)=2-s by push_cast;ring] using hg)
    simpa only [Real.rpow_neg_one] using hh
  have hscale := (MellinConvergent.comp_mul_left (f := fun t : ℝ=>g t⁻¹)
    (s := s-2) hQ).mpr hinv
  have hpow := (MellinConvergent.cpow_smul (f := fun t : ℝ=>g (Q*t)⁻¹)
    (s := s) (a := -2)).mpr (by simpa only [sub_eq_add_neg] using hscale)
  simpa only [reflectedCuspProfile,smul_eq_mul] using hpow.const_smul A

lemma cusp_truncation_reflection_ae (f g : ℝ→ℂ) (A : ℂ) (Q : ℝ) (hQ : 0<Q)
    (hfg : ∀v : ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    f =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun v=>truncatedCuspProfile 1 f v+
        reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) := by
  have hne : ∀ᵐv : ℝ ∂volume.restrict (Set.Ioi 0),v≠1 :=
    ae_restrict_of_ae (Measure.ae_ne volume 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with v hv hv1
  have hrel : 1/Q<(Q*v)⁻¹ ↔ v<1 := by
    rw [inv_eq_one_div,div_lt_div_iff₀ hQ (mul_pos hQ hv)]
    constructor <;> intro hh <;> nlinarith
  by_cases hhi : 1<v
  · have hlo : ¬1/Q<(Q*v)⁻¹ := fun hh=>not_lt_of_ge hhi.le (hrel.mp hh)
    simp only [truncatedCuspProfile,if_pos hhi,reflectedCuspProfile,if_neg hlo,
      mul_zero,add_zero]
  · have hlo : 1/Q<(Q*v)⁻¹ := hrel.mpr (lt_of_le_of_ne (le_of_not_gt hhi) hv1)
    simp only [truncatedCuspProfile,if_neg hhi,reflectedCuspProfile,if_pos hlo,zero_add]
    exact hfg v hv

theorem cusp_mellin_entire (f g : ℝ→ℂ) (A : ℂ) (Q decayF decayG : ℝ)
    (hQ : 0<Q) (hdecayF : 0<decayF) (hdecayG : 0<decayG)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfbound : f =O[atTop] (fun v : ℝ=>Real.exp (-decayF*v)))
    (hgbound : g =O[atTop] (fun v : ℝ=>Real.exp (-decayG*v)))
    (hfg : ∀v : ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    (∀s : ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f) := by
  obtain ⟨hfc,hfd⟩ := truncatedCuspProfile_mellin_entire 1 decayF (by norm_num) hdecayF f hf hfbound
  obtain ⟨hgc,hgd⟩ := truncatedCuspProfile_mellin_entire (1/Q) decayG
    (by positivity) hdecayG g hg hgbound
  have hae := cusp_truncation_reflection_ae f g A Q hQ hfg
  have hresult (s : ℂ) : HasMellin f s
      (mellin (truncatedCuspProfile 1 f) s+
        A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) := by
    have hr := reflectedCuspProfile_mellinConvergent
      (truncatedCuspProfile (1/Q) g) A s Q hQ (hgc (2-s))
    have hsum := hasMellin_add (hfc s) hr
    constructor
    · apply hsum.1.congr
      filter_upwards [hae] with v hv
      exact congrArg (fun z : ℂ=>(v:ℂ)^(s-1) • z) hv.symm
    · have he : mellin f s=mellin (fun v=>truncatedCuspProfile 1 f v+
          reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) s := by
        unfold mellin
        apply integral_congr_ae
        filter_upwards [hae] with v hv
        rw [hv]
      rw [he,hsum.2,reflectedCuspProfile_mellin _ _ _ _ hQ]
  refine ⟨fun s=>(hresult s).1,?_⟩
  have he : mellin f=(fun s : ℂ=>mellin (truncatedCuspProfile 1 f) s+
      A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) :=
    funext (fun s=>(hresult s).2)
  rw [he]
  let : NeZero (Q:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hQ.ne'⟩
  have hp := (differentiable_const_cpow_of_neZero (Q:ℂ)).comp
    ((differentiable_const (2:ℂ)).sub differentiable_id)
  exact hfd.add (((differentiable_const A).mul hp).mul
    (hgd.comp ((differentiable_const (2:ℂ)).sub differentiable_id)))

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma term_horizontal_hasDerivAt (h : ActualEisensteinCubic.O) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.term h (v,z+(x:ℂ)*direction))
      (coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (brevePhase_hasDerivAt (cuspFrequency h) z direction t).const_mul
    (coeff.amplitude v h)
  have hf : (fun x : ℝ => coeff.term h (v,z+(x:ℂ)*direction))=
      (fun x : ℝ => coeff.amplitude v h*
        ShortDraftTrace.breveE (cuspFrequency h*(z+(x:ℂ)*direction))) := by
    funext x
    exact coeff.term_eq_amplitude v hv h _
  rw [hf]
  convert (preTransparency := .instances) hh using 1
  rw [directionalTerm,coeff.term_eq_amplitude v hv h]
  ring

lemma directionalTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),v∈Set.Icc a b →
      ‖coeff.directionalTerm h v z direction‖≤
        C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hv
  rw [directionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h (v,z) hv)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma directionalTerm_summable (v : ℝ) (hv : 0<v) (z direction : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => coeff.directionalTerm h v z direction) := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound v v hv le_rfl direction
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h v z ⟨le_rfl,le_rfl⟩)
  exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C

lemma series_horizontal_hasDerivAt (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.series (v,z+(x:ℂ)*direction))
      (∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound v v hv le_rfl direction
  have hs := (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C
  have hz : Summable (fun h : ActualEisensteinCubic.O => coeff.term h (v,z+(0:ℂ)*direction)) := by
    simpa only [zero_mul,add_zero] using coeff.summable (v,z) hv
  exact hasDerivAt_tsum hs (fun h x => coeff.term_horizontal_hasDerivAt h v hv z direction x)
    (fun h x => hbound h v (z+(x:ℂ)*direction) ⟨le_rfl,le_rfl⟩) hz t

lemma fullFunction_horizontal_hasDerivAt (constant : ℂ) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.fullFunction constant (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (coeff.series_horizontal_hasDerivAt v hv z direction t).const_add
    (constant*(v:ℂ)^(2/3:ℂ))
  simpa only [fullFunction,function,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint] using hh

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma directionalTerm_cusp_majorant (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃D : ℝ,0≤D ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖coeff.directionalTerm h v z direction‖≤
        (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*
          (‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := coeff.term_cusp_bound a ha
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · subst h
    simp only [directionalTerm,term,ite_true,mul_zero,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have he : Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)≤
      Real.exp (-(2*residualCuspDecayRate)*v)*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (cuspFrequency_norm_lower h hh)
      (show 0≤Real.pi*v/2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hav (show 0≤Real.pi*‖cuspFrequency h‖/2 by positivity)
    unfold residualCuspDecayRate
    nlinarith
  rw [directionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h v z hav)
        (norm_nonneg _) (by positivity)
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*(Real.exp (-(2*residualCuspDecayRate)*v)*
          Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖))) := by
      gcongr
    _ = _ := by ring

lemma directionalSeries_cusp_decay (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(z : ℂ),a≤v →
      ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z direction‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨D,hD,hbound⟩ := coeff.directionalTerm_cusp_majorant a ha direction
  have hc := residualCuspDecayRate_pos
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hs := summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a/2) (by positivity)
  refine ⟨D*S*(2/(2*residualCuspDecayRate)),by positivity,?_⟩
  intro v z hav
  have hsum := tsum_of_norm_bounded
    (hs.hasSum.mul_left (D*v*Real.exp (-(2*residualCuspDecayRate)*v)))
    (fun h => hbound h v z hav)
  calc
    _ ≤ (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D*S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D*S)*((2/(2*residualCuspDecayRate))*
        Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      rw [show -((2*residualCuspDecayRate)/2)*v=-residualCuspDecayRate*v by ring]
      ring

theorem fullFunction_wirtingerBar_cusp_decay (constant : ℂ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => coeff.fullFunction constant (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C1,hC1,hbound1⟩ := coeff.directionalSeries_cusp_decay a ha 1
  obtain ⟨CI,hCI,hboundI⟩ := coeff.directionalSeries_cusp_decay a ha Complex.I
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖Complex.I*(∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-residualCuspDecayRate*v)+CI*Real.exp (-residualCuspDecayRate*v)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hbound1 v z hav) (hboundI v z hav)
    _ = _ := by ring

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma spatialComplexSplit_differentiable : Differentiable ℝ spatialComplexSplit := by
  change Differentiable ℝ (fun p : EuclideanSpatial => (p 2,(p 0:ℂ)+(p 1:ℂ)*Complex.I))
  fun_prop

lemma spatialComplexSplit_symm_differentiable : Differentiable ℝ spatialComplexSplit.symm := by
  change Differentiable ℝ (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  have hlin := (WithLp.linearEquiv 2 ℝ (Fin 3→ℝ)).symm.toContinuousLinearMap.differentiable
  have hcoords : Differentiable ℝ (fun q : ℝ × ℂ => ![q.2.re,q.2.im,q.1]) := by
    apply differentiable_pi.mpr
    intro j
    fin_cases j
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.re)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.im)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.1)
      fun_prop
  exact hlin.comp hcoords

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_euclidean_differentiableAt (constant : ℂ) (p : EuclideanSpatial) (hp : 0<p 2) :
    DifferentiableAt ℝ (fun q : EuclideanSpatial => coeff.fullFunction constant (euclideanToHyperbolic q)) p := by
  have hh := (coeff.fullFunction_cusp_differentiableAt constant (spatialComplexSplit p) hp).comp p
    spatialComplexSplit_differentiable.differentiableAt
  simpa only [Function.comp_def,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply] using hh

lemma fullFunction_translate_cusp_differentiableAt (constant : ℂ) (g : SL(2,ℂ))
    (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => coeff.fullFunction constant (g • cuspCoordinateLift q)) p := by
  have hx : 0<(spatialComplexSplit.symm p) 2 := by
    rw [spatialComplexSplit_symm_eq]
    exact hp
  obtain ⟨A,hA,hAn⟩ := hyperbolicDifferentialIsometry g (spatialComplexSplit.symm p) hx
  have hh := ((coeff.fullFunction_euclidean_differentiableAt constant
    (euclideanAction g (spatialComplexSplit.symm p)) (euclideanAction_positive _ _)).comp _
      hA.differentiableAt).comp p spatialComplexSplit_symm_differentiable.differentiableAt
  simpa only [Function.comp_def,euclideanAction,euclideanToHyperbolic_coordinates,cuspCoordinateLift] using hh

lemma fullFunction_translate_split_differentiableAt (constant : ℂ) (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => coeff.fullFunction constant (g • cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : DifferentiableAt ℝ (fun q : ℂ × ℝ => (q.2,q.1)) p :=
    differentiableAt_snd.prodMk differentiableAt_fst
  exact (coeff.fullFunction_translate_cusp_differentiableAt constant g (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceResidualFunction (g • cuspCoordinateLift (q.2,q.1))) p := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_translate_split_differentiableAt
    ((3*(Real.pi:ℂ))*constantArithmeticResidue) g p hp

lemma cubicSourceResidualFunction_wirtingerBar_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerBar_cusp_decay _ a ha

end

local notation "O" => ActualEisensteinCubic.O

lemma horizontalPhaseMultiplier_wirtingerZ (freq : ℂ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq 1-
      Complex.I*horizontalPhaseMultiplier freq Complex.I)=2*Real.pi*Complex.I*freq := by
  simp only [horizontalPhaseMultiplier,mul_one,star_mul,Complex.star_def,
    Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ring

lemma horizontalWirtingerBar_star (f : ℂ→ℂ) (z : ℂ) :
    horizontalWirtingerBar (fun w => star (f w)) z=star (horizontalWirtingerZ f z) := by
  unfold horizontalWirtingerBar horizontalWirtingerZ
  rw [deriv.star,deriv.star]
  simp []

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_wirtingerZ (constant : ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerZ (fun w => coeff.fullFunction constant (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*cuspFrequency h)*coeff.term h (v,z) := by
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerZ,h1,hI]
  have hs1 := coeff.directionalTerm_summable v hv z 1
  have hsI := (coeff.directionalTerm_summable v hv z Complex.I).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_sub hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold directionalTerm
  linear_combination coeff.term h (v,z)*horizontalPhaseMultiplier_wirtingerZ (cuspFrequency h)

lemma fullFunction_wirtingerZ_cusp_decay (constant : ℂ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => coeff.fullFunction constant (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C1,hC1,hbound1⟩ := coeff.directionalSeries_cusp_decay a ha 1
  obtain ⟨CI,hCI,hboundI⟩ := coeff.directionalSeries_cusp_decay a ha Complex.I
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerZ,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖Complex.I*(∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-residualCuspDecayRate*v)+CI*Real.exp (-residualCuspDecayRate*v)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hbound1 v z hav) (hboundI v z hav)
    _ = _ := by ring

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_wirtingerZ_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerZ_cusp_decay _ a ha

lemma cubicSourceConjugateFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceConjugateFunction (g • cuspCoordinateLift (q.2,q.1))) p :=
  (cubicSourceResidualFunction_translate_split_differentiableAt g p hp).star

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

lemma horizontalWirtingerBar_translate (f : ℂ→ℂ) (a : ℂ) :
    horizontalWirtingerBar (fun z=>f (z+a)) 0=horizontalWirtingerBar f a := by
  unfold horizontalWirtingerBar
  simp only [zero_add]
  have h1 : (fun t : ℝ=>f ((t:ℂ)+a))=(fun t : ℝ=>f (a+(t:ℂ))) := by
    funext t
    rw [add_comm]
  have hI : (fun t : ℝ=>f ((t:ℂ)*Complex.I+a))=(fun t : ℝ=>f (a+(t:ℂ)*Complex.I)) := by
    funext t
    rw [add_comm]
  rw [h1,hI]

lemma cuspDerivative_of_transform (f : HyperbolicSpace→ℂ) (g H : SL(2,ℂ))
    (κ : ℂ) (htransform : ∀w,f (g•w)=κ*f (H•w)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v)
    (hD : DifferentiableAt ℝ
      (fun q : ℂ × ℝ=>f (H•cuspCoordinateLift (q.2,q.1)))
      (-g 1 1/g 1 0,1/(‖g 1 0‖^2*v))) :
    horizontalWirtingerBar (fun z=>f (upperPoint z v hv)) (g 0 0/g 1 0)=
      (κ*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>f (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  let FH : ℂ × ℝ→ℂ := fun q=>f (H•cuspCoordinateLift (q.2,q.1))
  let base : ℂ × ℝ := (-g 1 1/g 1 0,1/(‖g 1 0‖^2*v))
  let D := fderiv ℝ FH base
  have hF : HasFDerivAt FH D base := hD.hasFDerivAt
  have hscaled : HasFDerivAt (fun q=>κ*FH q) (κ • D) base := hF.const_mul κ
  have he := inverse_cusp_wirtingerBar (g 1 0) (g 1 1) v hc hv
    (fun q=>κ*FH q) (κ • D) hscaled
  have hline : (fun z=>κ*FH (inverseCuspCoordinates (g 1 0) (g 1 1) v z))=
      (fun z=>f (upperPoint (z+g 0 0/g 1 0) v hv)) := by
    funext z
    have ht := htransform (g⁻¹•upperPoint (z+g 0 0/g 1 0) v hv)
    rw [smul_inv_smul,inverse_cusp_action g hc v hv z] at ht
    change κ*f (H•cuspCoordinateLift
      ((inverseCuspCoordinates (g 1 0) (g 1 1) v z).2,
       (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1))=_
    rw [cuspCoordinateLift_positive _ _ (inverseCuspCoordinates_height_pos _ _ _ _ hc hv)]
    exact ht.symm
  rw [hline] at he
  have hshift := horizontalWirtingerBar_translate (fun z=>f (upperPoint z v hv)) (g 0 0/g 1 0)
  rw [hshift] at he
  have hz := horizontalWirtingerZ_eq_fderiv FH D (-g 1 1/g 1 0) (1/(‖g 1 0‖^2*v)) hF
  have hFH : (fun z=>FH (z,1/(‖g 1 0‖^2*v)))=
      (fun z=>f (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity))) := by
    funext z
    exact congrArg (fun w=>f (H•w)) (cuspCoordinateLift_positive _ _ (by positivity))
  rw [hFH] at hz
  rw [hz]
  rw [he]
  simp only [_root_.smul_apply,smul_eq_mul]
  ring

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reciprocity.CubeCorrespondence
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

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma cuspBarProfile_positive (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspBarProfile f z v=horizontalWirtingerBar (fun w=>f (upperPoint w v hv)) z := by
  simp only [cuspBarProfile,cuspCoordinateLift_positive v _ hv]

lemma cuspZProfile_positive (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspZProfile f z v=horizontalWirtingerZ (fun w=>f (upperPoint w v hv)) z := by
  simp only [cuspZProfile,cuspCoordinateLift_positive v _ hv]

lemma horizontalWirtingerZ_star (f : ℂ→ℂ) (z : ℂ) :
    horizontalWirtingerZ (fun w=>star (f w)) z=star (horizontalWirtingerBar f z) := by
  unfold horizontalWirtingerBar horizontalWirtingerZ
  rw [deriv.star,deriv.star]
  simp [sub_eq_add_neg]

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma directionalSeries_continuousOn_slab (direction : ℂ) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn (coeff.directionalSeries direction) {p : ℝ × ℂ|p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound a b ha hab direction
  apply continuousOn_tsum (u:=fun h : ActualEisensteinCubic.O=>C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))
  · intro h
    have ht : ContinuousOn (coeff.term h) {p : ℝ × ℂ|p.1∈Set.Icc a b} :=
      (coeff.term_continuousOn h).mono (fun p hp=>ha.trans_le hp.1)
    exact ht.const_mul (horizontalPhaseMultiplier (cuspFrequency h) direction)
  · exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · intro h p hp
    exact hbound h p.1 p.2 hp

lemma directionalSeries_continuousOn (direction : ℂ) :
    ContinuousOn (coeff.directionalSeries direction) {p : ℝ × ℂ|0<p.1} := by
  intro p hp
  have hclosed := coeff.directionalSeries_continuousOn_slab direction (p.1/2) (2*p.1)
    (by change 0<p.1 at hp;linarith) (by change 0<p.1 at hp;linarith)
  have hnb : {q : ℝ × ℂ|q.1∈Set.Icc (p.1/2) (2*p.1)}∈𝓝 p :=
    continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by change 0<p.1 at hp;linarith)
      (by change 0<p.1 at hp;linarith))
  exact (hclosed.continuousAt hnb).continuousWithinAt

lemma cuspZProfile_full_eq (constant z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspZProfile (coeff.fullFunction constant) z v=
      (1/2:ℂ)*(coeff.directionalSeries 1 (v,z)-Complex.I*coeff.directionalSeries Complex.I (v,z)) := by
  rw [cuspZProfile_positive _ _ _ hv,horizontalWirtingerZ]
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [h1,hI]
  rfl

lemma cuspZProfile_continuousOn (constant z : ℂ) :
    ContinuousOn (cuspZProfile (coeff.fullFunction constant) z) (Set.Ioi 0) := by
  have hd (direction : ℂ) : ContinuousOn (fun v : ℝ=>coeff.directionalSeries direction (v,z)) (Set.Ioi 0) :=
    (coeff.directionalSeries_continuousOn direction).comp
      (continuousOn_id.prodMk continuousOn_const) (fun v hv=>hv)
  apply (continuousOn_const.mul ((hd 1).sub (continuousOn_const.mul (hd Complex.I)))).congr
  intro v hv
  exact coeff.cuspZProfile_full_eq constant z v hv

end SubexponentialBesselCoefficients

lemma cuspZProfile_source_continuousOn (z : ℂ) :
    ContinuousOn (cuspZProfile cubicSourceResidualFunction z) (Set.Ioi 0) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.cuspZProfile_continuousOn _ z

lemma cuspBarProfile_conjugate_eq (z : ℂ) :
    cuspBarProfile cubicSourceConjugateFunction z=fun v=>star (cuspZProfile cubicSourceResidualFunction z v) := by
  funext v
  exact horizontalWirtingerBar_star _ z

lemma cuspZProfile_conjugate_eq (z : ℂ) :
    cuspZProfile cubicSourceConjugateFunction z=fun v=>star (cuspBarProfile cubicSourceResidualFunction z v) := by
  funext v
  exact horizontalWirtingerZ_star _ z

lemma cuspBarProfile_conjugate_continuousOn (z : ℂ) :
    ContinuousOn (cuspBarProfile cubicSourceConjugateFunction z) (Set.Ioi 0) := by
  rw [cuspBarProfile_conjugate_eq]
  exact (cuspZProfile_source_continuousOn z).star

lemma cuspBarProfile_source_isBigO (z : ℂ) :
    cuspBarProfile cubicSourceResidualFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC,hbound⟩ := cubicSourceResidualFunction_wirtingerBar_cusp_decay 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp : 0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspBarProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hbound v hvp z hv

lemma cuspZProfile_source_isBigO (z : ℂ) :
    cuspZProfile cubicSourceResidualFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC,hbound⟩ := cubicSourceResidualFunction_wirtingerZ_cusp_decay 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp : 0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspZProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hbound v hvp z hv

lemma cuspBarProfile_conjugate_isBigO (z : ℂ) :
    cuspBarProfile cubicSourceConjugateFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp (cuspZProfile_source_isBigO z)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with v hv
  simpa only [cuspBarProfile_conjugate_eq,norm_star] using hv

lemma cuspZProfile_conjugate_isBigO (z : ℂ) :
    cuspZProfile cubicSourceConjugateFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp (cuspBarProfile_source_isBigO z)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with v hv
  simpa only [cuspZProfile_conjugate_eq,norm_star] using hv

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConjugateCuspProfiles
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cubicBesselIntegralDeriv_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt (fun y : ℝ=>∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv y t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  apply continuousAt_of_dominated («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (bound:=fun t : ℝ=>(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)))
  · exact Eventually.of_forall (fun y=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
  · filter_upwards [Ioi_mem_nhds (show delta<x by dsimp [delta];linarith)] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hyp : 0<y := hdelta.trans hy
    have htp : 0<t := ht
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  · exact cubicBesselDerivativeMajorant_integrable.const_mul (4/delta)
  · exact Eventually.of_forall (fun t=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)

lemma schlafliBesselK_cubic_derivative_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt schlafliBesselK_cubic_derivative x := by
  have hp4 : ContinuousAt (fun y : ℝ=>(y/2)^(-(4:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hp1 : ContinuousAt (fun y : ℝ=>(y/2)^(-(1:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hI := (cubicBesselIntegral_hasDerivAt x hx).continuousAt
  have hD := cubicBesselIntegralDeriv_continuousAt x hx
  apply Complex.continuous_ofReal.continuousAt.comp
  exact ((continuousAt_const.mul hp4).mul hI).add ((continuousAt_const.mul hp1).mul hD)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma amplitudeDeriv_continuousAt (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    ContinuousAt (fun y : ℝ=>coeff.amplitudeDeriv y h) v := by
  by_cases hh : h=0
  · simpa only [amplitudeDeriv,if_pos hh] using (continuousAt_const (y:=(0:ℂ)) (x:=v))
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hK : ContinuousAt (fun y : ℝ=>schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*y)) v :=
    (schlafliBesselK_cubic_hasDerivAt _ (by positivity)).continuousAt.comp (by fun_prop)
  have hD : ContinuousAt (fun y : ℝ=>schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*y)) v :=
    (schlafliBesselK_cubic_derivative_continuousAt _ (by positivity)).comp (by fun_prop)
  simp only [amplitudeDeriv,if_neg hh]
  exact continuousAt_const.mul (hK.add ((Complex.continuous_ofReal.continuousAt.mul continuousAt_const).mul hD))

lemma termFDeriv_continuousAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContinuousAt (coeff.termFDeriv h) p := by
  by_cases hh : h=0
  · have he : coeff.termFDeriv h=fun _=>(0:(ℝ × ℂ)→L[ℝ]ℂ) := by
      funext q
      simp only [termFDeriv,if_pos hh]
    rw [he]
    exact continuousAt_const
  have hA := (coeff.amplitudeDeriv_continuousAt p.1 hp h).comp continuousAt_fst
  have hphase : ContinuousAt (fun q : ℝ × ℂ=>ShortDraftTrace.breveE (cuspFrequency h*q.2)) p := by
    change ContinuousAt (fun q : ℝ × ℂ=>Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2)))) p
    fun_prop
  have hfirst := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℂ) ℂ
    (ContinuousLinearMap.fst ℝ ℝ ℂ)).continuous.continuousAt.comp (hA.mul hphase)
  have hterm := (coeff.term_continuousOn h).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
  have hsecond := hterm.smul (continuousAt_const
    (y:=(horizontalPhaseCLM (cuspFrequency h)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)))
  have he : coeff.termFDeriv h=(fun q : ℝ × ℂ=>
      (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
        (coeff.amplitudeDeriv q.1 h*ShortDraftTrace.breveE (cuspFrequency h*q.2))+
      coeff.term h q • (horizontalPhaseCLM (cuspFrequency h)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)) := by
    funext q
    simp only [termFDeriv,if_neg hh]
  rw [he]
  exact hfirst.add hsecond

lemma seriesFDeriv_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn (fun p : ℝ × ℂ=>∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p)
      {p : ℝ × ℂ|p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  apply continuousOn_tsum (u:=fun h : ActualEisensteinCubic.O=>C*((1+‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))
  · intro h p hp
    exact (coeff.termFDeriv_continuousAt h p (ha.trans_le hp.1)).continuousWithinAt
  · exact (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound

lemma series_contDiffAt_one (p : ℝ × ℂ) (hp : 0<p.1) : ContDiffAt ℝ 1 coeff.series p := by
  apply contDiffAt_one_iff.mpr
  refine ⟨(fun q=>∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h q),
    {q : ℝ × ℂ|q.1∈Set.Icc (p.1/2) (2*p.1)},?_,?_,?_⟩
  · exact continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  · exact coeff.seriesFDeriv_continuousOn_slab _ _ (by linarith) (by linarith)
  · intro q hq
    exact coeff.series_hasFDerivAt q (by change p.1/2≤q.1 ∧ q.1≤2*p.1 at hq;linarith [hq.1])

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

lemma cuspSpatialInput_contDiff : ContDiff ℝ 1 cuspSpatialInput := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.re)
    exact Complex.reCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.im)
    exact Complex.imCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.1)
    fun_prop

lemma cuspSpatialOutput_contDiff : ContDiff ℝ 1 cuspSpatialOutput :=
  (contDiff_apply ℝ ℝ 2).prodMk (spatialHorizontal_contDiff.of_le (by simp))

lemma cuspSpatialAction_lift (g : SL(2,ℂ)) (q : ℝ × ℂ) (hq : 0<q.1) :
    cuspCoordinateLift (cuspSpatialOutput (mobiusSpatial g (cuspSpatialInput q)))=
      g•cuspCoordinateLift q := by
  have hin : hyperbolicSpatialCoordinates (cuspCoordinateLift q)=cuspSpatialInput q := by
    rw [show q=(q.1,q.2) from rfl,cuspCoordinateLift_positive q.1 q.2 hq]
    simp only [hyperbolicSpatialCoordinates,hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint,cuspSpatialInput]
  have he := mobiusSpatial_coordinates_global g (cuspCoordinateLift q)
  rw [hin] at he
  have hr := hyperbolicSpatialCoordinates_reconstruct (g•cuspCoordinateLift q)
  have hp : 0< mobiusSpatial g (cuspSpatialInput q) 2 := mobiusSpatial_positive g _ hq
  rw [cuspSpatialOutput,cuspCoordinateLift_positive _ _ hp]
  refine Eq.trans ?_ hr
  apply upperPoint_congr
  · rw [he]
    rfl
  · rw [he]

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_cusp_contDiffAt_one (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hreal : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>q.1^(2/3:ℝ)) p :=
    contDiff_fst.contDiffAt.rpow_const_of_ne hp.ne'
  have hcast := Complex.ofRealCLM.contDiff.contDiffAt.comp p hreal
  have hpow : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>(q.1:ℂ)^(2/3:ℂ)) p := by
    apply hcast.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
    have he := Complex.ofReal_cpow (le_of_lt hq) (2/3:ℝ)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
    exact he.symm
  have hfull : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p :=
    (contDiffAt_const.mul hpow).add (coeff.series_contDiffAt_one p hp)
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq

lemma fullFunction_translate_cusp_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (g•cuspCoordinateLift q)) p := by
  have hmid : ContDiffAt ℝ 1 (fun q=>mobiusSpatial g (cuspSpatialInput q)) p :=
    ((mobiusSpatial_contDiffAt g (cuspSpatialInput p) hp).of_le (by simp)).comp p
      cuspSpatialInput_contDiff.contDiffAt
  have hact := cuspSpatialOutput_contDiff.contDiffAt.comp p hmid
  have hpos : 0<(cuspSpatialOutput (mobiusSpatial g (cuspSpatialInput p))).1 :=
    mobiusSpatial_positive g _ hp
  have hfull := (coeff.fullFunction_cusp_contDiffAt_one constant _ hpos).comp p hact
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact congrArg (coeff.fullFunction constant) (cuspSpatialAction_lift g q hq).symm

lemma fullFunction_translate_split_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>coeff.fullFunction constant (g•cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>(q.2,q.1)) p := by fun_prop
  exact (coeff.fullFunction_translate_cusp_contDiffAt_one constant g (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_translate_split_contDiffAt_one (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>cubicSourceResidualFunction (g•cuspCoordinateLift (q.2,q.1))) p := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_translate_split_contDiffAt_one _ g p hp

lemma cubicSourceConjugateFunction_translate_split_contDiffAt_one (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>cubicSourceConjugateFunction (g•cuspCoordinateLift (q.2,q.1))) p := by
  exact Complex.conjCLE.contDiff.contDiffAt.comp p
    (cubicSourceResidualFunction_translate_split_contDiffAt_one g p hp)

lemma cuspZProfile_continuousOn_of_contDiff (f : HyperbolicSpace→ℂ)
    (hreg : ∀p : ℂ × ℝ,0<p.2 → ContDiffAt ℝ 1
      (fun q : ℂ × ℝ=>f (cuspCoordinateLift (q.2,q.1))) p) (z : ℂ) :
    ContinuousOn (cuspZProfile f z) (Set.Ioi 0) := by
  let F : ℂ × ℝ→ℂ := fun q=>f (cuspCoordinateLift (q.2,q.1))
  intro v hv
  have hd : ContinuousAt (fderiv ℝ F) (z,v) :=
    (hreg (z,v) hv).continuousAt_fderiv (by norm_num)
  have hc : ContinuousAt (fun y : ℝ=>(z,y)) v := continuousAt_const.prodMk continuousAt_id
  have h1 := (hd.comp hc).clm_apply (continuousAt_const (y:=((1,0):ℂ × ℝ)))
  have hI := (hd.comp hc).clm_apply (continuousAt_const (y:=((Complex.I,0):ℂ × ℝ)))
  have hformula : ContinuousAt (fun y : ℝ=>(1/2:ℂ)*
      ((fderiv ℝ F (z,y)) (1,0)-Complex.I*(fderiv ℝ F (z,y)) (Complex.I,0))) v :=
    continuousAt_const.mul (h1.sub (continuousAt_const.mul hI))
  apply ContinuousAt.continuousWithinAt
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show 0<v from hv)] with y hy
  exact horizontalWirtingerZ_eq_fderiv F (fderiv ℝ F (z,y)) z y
    ((hreg (z,y) hy).differentiableAt (by norm_num)).hasFDerivAt

lemma cuspZProfile_conjugate_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) z) (Set.Ioi 0) :=
  cuspZProfile_continuousOn_of_contDiff _
    (cubicSourceConjugateFunction_translate_split_contDiffAt_one H) z

end

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceAdjoint
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedSource_eq_series (side:Bool) (v:ℝ) (hv:0<v) (z:ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)=
      (ramifiedBesselCoefficients side).series (v/3,z/3) := by
  have he:=ramifiedScaledRow_eq_bessel side (v/3) (by positivity) (z/3)
  have hv3:3*(v/3)=v:=by ring
  have hz3:(3:ℂ)*(z/3)=z:=by ring
  simpa only [ramifiedScaledRow,hv3,hz3,cuspCoordinateLift_positive v z hv,
    SubexponentialBesselCoefficients.fullFunction,zero_mul,zero_add,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,
    hyperbolicHorizontal_upperPoint] using he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.PrimeGaussFactors
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

local instance instFintypeUnitsO_3_r226269_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
lemma unramifiedCubicGaussSeries_prime_two_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^2)=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 2
  have hg1:cubicUnitGaussSum (h*p^2) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero
      ((dvd_pow_self p (by decide : (2:ℕ)≠0)).trans (dvd_mul_left (p^2) h))]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^2) (p^2)=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ (p^2) (pow_ne_zero _ hp.ne_zero) (dvd_mul_left (p^2) h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^2) (p^3)= -(Ideal.absNorm (Ideal.span {p}):ℂ)^2:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 2 h
    rw [primeCubicGauss_trivial_nonzero p hp hprimary 3 (dvd_refl 3) h hph] at hh
    simpa only [mul_comm (p^2) h,mul_neg_one] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,mul_zero,zero_mul,add_zero] at he
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h hph 2
  rw [←unramifiedCubicGaussSeries_prime_two_power p hp hprimary s hs h hph] at he
  simpa only [show 2+3=5 from rfl,add_mul,one_mul] using he

theorem unramifiedGaussResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue (h*p^2) := by
  let A:ℂ→ℂ:=fun s=>1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  have hA (s:ℂ):AnalyticAt ℂ A s:=analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^5) (h*p^2) 0 A (fun _=>0)
    (fun s _=>hA s) (fun _ _=>analyticAt_const) (hA _).continuousAt continuousAt_const
    (fun s hs _=>by simpa only [A,zero_mul,add_zero] using
      unramifiedCubicGaussSeries_square_cube p hp hprimary s (by linarith) h hph)
  dsimp only [A] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [zero_mul,add_zero] using he

lemma principalResidueTerm_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (h*p^5) u n=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalResidueTerm (h*p^2) u n := by
  let c:=u.val*lambda^(n+2)
  have hA:=arithmeticResidueSum_frequency_cube (h*p^2) c p
    (ramifiedElement_ne_zero u (n+2)) (ramifiedElement_level u (n+2) (by omega)) hprimary
    (ramified_primary_coprime u (n+2) p hprimary).of_mul_left_right
  have hfreq:¬p∣h*(9*c):=ramified_prime_frequency_not_dvd h p hp hprimary hph u (n+2)
  rw [show (h*p^2)*p^3=h*p^5 by ring] at hA
  change _*arithmeticResidueSum (h*p^5) c*unramifiedGaussResidue ((h*p^5)*(9*c))=_
  rw [hA,show (h*p^5)*(9*c)=(h*(9*c))*p^5 by ring,
    unramifiedGaussResidue_square_cube p hp hprimary (h*(9*c)) hfreq]
  change _=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum (h*p^2) c*
      unramifiedGaussResidue ((h*p^2)*(9*c)))
  rw [show (h*p^2)*(9*c)=(h*(9*c))*p^2 by ring]
  ring

lemma principalArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    principalArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalArithmeticResidue (h*p^2) := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  let N:=max (ramifiedFrequencyBound (h*p^5)+1) (ramifiedFrequencyBound (h*p^2)+1)
  rw [principalArithmeticResidue_eq_sum (h*p^5) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum (h*p^2) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_right _ _)]
  simp_rw [principalResidueTerm_square_cube p hp hprimary h hph,←Finset.mul_sum]
  ring

theorem sourceArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*sourceArithmeticResidue (h*p^2) := by
  have hm:ShortDraftTrace.breveE (cuspFrequency (h*p^5))=
      ShortDraftTrace.breveE (cuspFrequency (h*p^2)):=by
    rw [show h*p^5=(((h*p^2)*p)*p)*p by ring]
    rw [sourceRayPhase_mul_primary _ p hprimary,sourceRayPhase_mul_primary _ p hprimary,
      sourceRayPhase_mul_primary _ p hprimary]
  have hp9:¬p∣9*h:=by
    have hh:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using hh
  simp only [sourceArithmeticResidue,hm]
  split_ifs
  · rw [principalArithmeticResidue_square_cube p hp hprimary h hph,
      show 9*(h*p^5)=(9*h)*p^5 by ring,
      unramifiedGaussResidue_square_cube p hp hprimary (9*h) hp9,
      show 9*(h*p^2)=(9*h)*p^2 by ring]
    ring
  · ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceArithmeticResidue_prime_pow_mod (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hh:h≠0) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=sourceArithmeticResidue (h*p^(n%3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n<3
    · rw [Nat.mod_eq_of_lt hn]
    · have hn3:3≤n:=by omega
      have he:h*p^n=(h*p^(n-3))*p^3:=by rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn3]
      rw [he,sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)),
        ih (n-3) (by omega)]
      have hm:(n-3)%3=n%3:=by omega
      rw [hm]

theorem sourceArithmeticResidue_prime_square (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^2)=0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have he:=sourceArithmeticResidue_square_cube p hp hprimary h hph
  rw [show h*p^5=(h*p^2)*p^3 by ring,
    sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero))] at he
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hz:(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceArithmeticResidue (h*p^2)=0:=by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)

theorem sourceArithmeticResidue_prime_power_table (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=
      if n%3=0 then sourceArithmeticResidue h
      else if n%3=1 then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
          primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h
      else 0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  rw [sourceArithmeticResidue_prime_pow_mod p hp hprimary h hh n]
  split_ifs with h0 h1
  · simp only [h0,pow_zero,mul_one]
  · simp only [h1,pow_one]
    exact sourceArithmeticResidue_prime_factor p hp hprimary h hph
  · have hn:n%3=2:=by omega
    rw [hn,sourceArithmeticResidue_prime_square p hp hprimary h hph]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicGauss_two_twist (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h) :
    primeCubicGauss p hp hprimary 2 h=eisEmbedding (symbol h p)*primeCubicGauss p hp hprimary 2 1 := by
  have hcop:IsCoprime p h:=hp.coprime_iff_not_dvd.mpr hph
  have he:=cubicUnitGaussSum_frequency_twist (1:Eis) p h hp.ne_zero hprimary hcop
  simp only [one_mul,←primeCubicGauss_one_eq p hp hprimary] at he
  have hs:(eisEmbedding (symbol h p))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime h p hprimary hcop.symm,map_one]
  have hstar:star (eisEmbedding (symbol h p))*eisEmbedding (symbol h p)=1:=by
    have hn:‖eisEmbedding (symbol h p)‖=1:=by
      have hn:=congrArg norm hs
      simp only [norm_pow,norm_one] at hn
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp (by simpa using hn)
    rw [mul_comm]
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using Complex.mul_conj (eisEmbedding (symbol h p))
  have hconj:=congrArg star he
  simp only [star_mul,←primeCubicGauss_two_eq_star] at hconj
  calc
    _=(star (eisEmbedding (symbol h p))*eisEmbedding (symbol h p))*primeCubicGauss p hp hprimary 2 h:=by rw [hstar,one_mul]
    _=eisEmbedding (symbol h p)*(star (eisEmbedding (symbol h p))*primeCubicGauss p hp hprimary 2 h):=by ring
    _=_:=by rw [mul_comm (star (eisEmbedding (symbol h p))),hconj]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSymbol_star_mul (a b:Eis) (hb:lambda^2∣b-1) (hab:IsCoprime a b) :
    star (eisEmbedding (symbol a b))*eisEmbedding (symbol a b)=1 := by
  have hc:(eisEmbedding (symbol a b))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime a b hb hab,map_one]
  have hn:‖eisEmbedding (symbol a b)‖=1:=by
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
    simpa only [norm_pow,norm_one,one_pow] using congrArg norm hc
  rw [mul_comm]
  simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using
    Complex.mul_conj (eisEmbedding (symbol a b))

lemma normalizedCubicUnitGauss_coprime_product (a b:Eis) (ha:a≠0) (hb:b≠0)
    (hap:lambda^2∣a-1) (hbp:lambda^2∣b-1) (hab:IsCoprime a b) :
    star (normalizedCubicUnitGauss (a*b))=
      eisEmbedding (symbol a b)*star (normalizedCubicUnitGauss a)*star (normalizedCubicUnitGauss b) := by
  have hG:=cubicUnitGaussSum_coprime_product 1 a b ha hb hap hbp hab
  simp only [one_mul] at hG
  have ht:=cubicUnitGaussSum_frequency_twist 1 b a hb hbp hab.symm
  simp only [one_mul] at ht
  have hN:eisEmbedding (symbol a b)*normalizedCubicUnitGauss (a*b)=
      normalizedCubicUnitGauss a*normalizedCubicUnitGauss b:=by
    unfold normalizedCubicUnitGauss
    rw [hG,map_mul,norm_mul,Complex.ofReal_mul]
    calc
      _=cubicUnitGaussSum 1 a*(eisEmbedding (symbol a b)*cubicUnitGaussSum a b)/
        ((‖eisEmbedding a‖:ℂ)*(‖eisEmbedding b‖:ℂ)):=by ring
      _=_:=by rw [ht];ring
  have hs:=congrArg star hN
  simp only [star_mul] at hs
  have hc:=cubicSymbol_star_mul a b hbp hab
  calc
    _=(star (eisEmbedding (symbol a b))*eisEmbedding (symbol a b))*
        star (normalizedCubicUnitGauss (a*b)):=by rw [hc,one_mul]
    _=eisEmbedding (symbol a b)*(star (normalizedCubicUnitGauss (a*b))*
        star (eisEmbedding (symbol a b))):=by ring
    _=_:=by rw [hs];ring

lemma sourceResidualFourierCoefficient_prime_normalized (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      eisEmbedding (symbol (9*h) p)*star (normalizedCubicUnitGauss p)*sourceResidualFourierCoefficient h := by
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  rw [sourceResidualFourierCoefficient_prime_factor p hp hprimary h hph,
    primeCubicGauss_two_twist p hp hprimary (9*h) hp9,primeCubicGauss_two_eq_star,
    normalizedCubicUnitGauss,←primeCubicGauss_one_eq p hp hprimary,
    star_div₀,Complex.star_def,Complex.conj_ofReal]
  ring

theorem sourceResidualFourierCoefficient_prime_product {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j))
    (h:Eis) (hph:∀i∈s,¬p i∣h) :
    sourceResidualFourierCoefficient (h*(∏i∈s,p i))=
      eisEmbedding (symbol (9*h) (∏i∈s,p i))*
        star (normalizedCubicUnitGauss (∏i∈s,p i))*sourceResidualFourierCoefficient h := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    have hpi:=hp i (Finset.mem_insert_self _ _)
    have hpri:=hprimary i (Finset.mem_insert_self _ _)
    have hps:∀j∈s,Prime (p j):=fun j hj=>hp j (Finset.mem_insert_of_mem hj)
    have hprs:∀j∈s,lambda^2∣p j-1:=fun j hj=>hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi:IsCoprime (p i) (∏j∈s,p j):=IsCoprime.prod_right (fun j hj=>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he;subst j;exact hi hj))
    have hbs:(∏j∈s,p j)≠0:=Finset.prod_ne_zero_iff.mpr (fun j hj=>(hps j hj).ne_zero)
    have hpb:¬p i∣h*(∏j∈s,p j):=by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd|hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.not_isUnit (hcpi.isUnit_of_dvd hd)
    have hih:=ih hps hprs (fun j hj k hk hjk=>hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj=>hph j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi,show h*(p i*(∏j∈s,p j))=(h*(∏j∈s,p j))*p i by ring,
      sourceResidualFourierCoefficient_prime_normalized (p i) hpi hpri _ hpb,hih]
    rw [mul_comm (p i) (∏j∈s,p j),
      normalizedCubicUnitGauss_coprime_product _ _ hbs hpi.ne_zero
        (primary_finset_product s p hprs) hpri hcpi.symm,
      symbol_mul_denominator,map_mul]
    rw [show (9:Eis)*(h*(∏j∈s,p j))=(9*h)*(∏j∈s,p j) by ring,
      symbol_mul_numerator _ _ (p i) hpri,map_mul]
    ring

lemma symbol_nine_eq_paperLambda (n:Eis) (hn:lambda^2∣n-1) :
    symbol 9 n=symbol ramifiedTraceLambda n := by
  have he:(9:Eis)=ramifiedTraceLambda^4:=by
    rw [show (4:ℕ)=2*2 from rfl,pow_mul,ramifiedTraceLambda_square]
    norm_num
  have hcop:IsCoprime ramifiedTraceLambda n:=
    ramified_character_coprime 0 1 _ n (Or.inl (by simp)) hn
  rw [he,symbol_pow_numerator _ _ hn,show (4:ℕ)=3+1 from rfl,pow_add,
    symbol_cube_of_isCoprime _ _ hn hcop,pow_one,one_mul]

theorem sourceResidualFourierCoefficient_primary_product {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j)) :
    star (sourceResidualFourierCoefficient (∏i∈s,p i))=
      star (sourceResidualFourierCoefficient 1)*
        star (eisEmbedding (symbol ramifiedTraceLambda (∏i∈s,p i)))*
        normalizedCubicUnitGauss (∏i∈s,p i) := by
  have he:=sourceResidualFourierCoefficient_prime_product s p hp hprimary hpair 1
    (fun i hi=>fun hd=>(hp i hi).not_isUnit (isUnit_of_dvd_one hd))
  simp only [one_mul,mul_one] at he
  rw [symbol_nine_eq_paperLambda _ (primary_finset_product s p hprimary)] at he
  rw [he,star_mul,star_mul,star_star]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSymbol_prime_zero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (x:Eis) (hpx:p∣x) : symbol x p=0 := by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  rw [symbol_prime p hp hprimary,primeValue_eq _ hg,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpx),MulChar.map_zero]

lemma cubicSymbol_zero_of_not_coprime (n:Eis) (hn:n≠0) (hprimary:lambda^2∣n-1)
    (x:Eis) (hnot:¬IsCoprime n x) : symbol x n=0 := by
  obtain ⟨s,hs,hp⟩:=exists_primary_prime_factorization n hn hprimary
  rw [←hs] at hnot ⊢
  clear hs hn hprimary n
  induction s using Multiset.induction_on with
  | empty=>exact False.elim (hnot (by simpa using (isCoprime_one_left : IsCoprime (1:Eis) x)))
  | @cons p s ih=>
    have hprime:=hp p (Multiset.mem_cons_self _ _)
    have hrest:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hp q (Multiset.mem_cons_of_mem hq)
    rw [Multiset.prod_cons,symbol_mul_denominator]
    by_cases hc:IsCoprime p x
    · have hnc:¬IsCoprime s.prod x:=fun h=>hnot (by simpa using hc.mul_left h)
      rw [ih hnc hrest,mul_zero]
    · rw [cubicSymbol_prime_zero p hprime.1 hprime.2 x
        (hprime.1.irreducible.dvd_iff_not_isCoprime.mpr hc),zero_mul]

lemma cubicUnitGaussSum_full (n:Eis) (hn:n≠0) (hprimary:lambda^2∣n-1) (h:Eis) :
    cubicUnitGaussSum h n=
      ∑'x:Eis⧸Ideal.span {n},eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
        quotientTrace n hn (Ideal.Quotient.mk _ h*x) := by
  let f:(Eis⧸Ideal.span {n})→ℂ:=fun x=>
    eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
      quotientTrace n hn (Ideal.Quotient.mk _ h*x)
  have hsup:Function.support f⊆{x|IsUnit x}:=by
    intro x hx
    by_contra hnot
    change ¬IsUnit x at hnot
    have hcop:¬IsCoprime n (GaussianShiftedPartition.representative n x):=by
      intro hc
      apply hnot
      have hh:=(isUnit_quotient_span_iff n (GaussianShiftedPartition.representative n x)).mpr hc
      simpa only [GaussianShiftedPartition.representative_spec] using hh
    exact hx (by simp only [f,cubicSymbol_zero_of_not_coprime n hn hprimary _ hcop,map_zero,zero_mul])
  change cubicUnitGaussSum h n=∑'x,f x
  rw [←tsum_subtype_eq_of_support_subset hsup]
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro x
  dsimp only [f]
  rw [←GaussianShiftedPartition.representative_spec n x.val,quotientTrace_mk_product]
  simp only [GaussianShiftedPartition.representative_spec]

theorem normalizedCubicUnitGauss_eq_gaussTwo (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hsq:Squarefree I) :
    normalizedCubicUnitGauss (primaryGenerator I)=gaussTwo I hI := by
  let n:=primaryGenerator I
  let:Finite (Eis⧸Ideal.span {n}):=finite_quotient_span hI
  let:Fintype (Eis⧸Ideal.span {n}):=Fintype.ofFinite _
  let e:=Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  rw [normalizedCubicUnitGauss,cubicUnitGaussSum_full _ hI (primaryGenerator_spec I hI).2 1,
    tsum_fintype]
  change (∑x:Eis⧸Ideal.span {n},eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
    quotientTrace n hI (Ideal.Quotient.mk _ 1*x))/(‖eisEmbedding n‖:ℂ)=
    (∑x:Eis⧸Ideal.span {n},cubicRow I hI (e x)*quotientTrace n hI x)/(‖eisEmbedding n‖:ℂ)
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  rw [Ideal.quotEquivOfEq_mk,cubicRow_eq_idealSymbol I hI hsq]
  have hc:n∣GaussianShiftedPartition.representative n (Ideal.Quotient.mk (Ideal.span {n}) a)-a:=
    gaussRep_mk_congr n a
  have hs:symbol a n=idealSymbol I a:=by
    unfold symbol
    rw [(primaryGenerator_spec I hI).1]
  rw [symbol_congr hc,hs,map_one,one_mul]

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SquarefreeCoefficients
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem infinityCoefficient_squarefree (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) :
    star (sourceResidualFourierCoefficient (primaryGenerator I))=
      infinityCoefficientScalar*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  have hpr:∀P∈primeSupport I,lambda^2∣primaryPrime P-1:=by
    intro P hP
    exact (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  have he:=sourceResidualFourierCoefficient_primary_product (primeSupport I) primaryPrime
    (fun P hP=>primaryPrime_isPrime_of_mem I P hI hP) hpr
    (primaryPrime_support_coprime I hI)
  rw [←primaryGenerator_squarefree_support I hI hsq,normalizedCubicUnitGauss_eq_gaussTwo I hI hsq] at he
  exact he

theorem infinityCoefficient_squarefree_cube (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I) :
    star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))=
      infinityCoefficientScalar*(‖eisEmbedding (primaryGenerator J)‖:ℂ)*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  rw [sourceResidualFourierCoefficient_primary_cube _ hJ (primaryGenerator_spec J hJ).2 _ hI,
    star_mul,infinityCoefficient_squarefree I hI hsq]
  simp only [Complex.star_def,Complex.conj_ofReal]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceArithmeticResidue_valuation_ne_two (I P:Ideal Eis)
    (hI:primaryGenerator I≠0) (hP:P∈normalizedFactors I)
    (hS:sourceArithmeticResidue (primaryGenerator I)≠0) :
    (normalizedFactors I).count P%3≠2 := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hprime:=prime_of_normalized_factor P hP
  let p:=primaryPrime P
  have hp0:p≠0:=primaryPrime_factor_ne_zero I P hI hP
  have hps:=primaryPrime_spec P hp0
  have hp:Prime p:=primaryPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
  obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hgen:primaryGenerator I=p^(multiplicity P I)*primaryGenerator J:=by
    calc
      _=primaryGenerator (P^(multiplicity P I)*J):=congrArg primaryGenerator hJ
      _=p^(multiplicity P I)*primaryGenerator J:=by
        rw [primaryGenerator_mul,primaryGenerator_pow]
        have he:primaryGenerator P=p:=by
          rw [←hps.2.2.1,primaryGenerator_span p hp0 hps.2.2.2]
        rw [he]
  have hgJ:primaryGenerator J≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,mul_zero])
  have hpd:¬p∣primaryGenerator J:=by
    intro hd
    apply hnot
    rw [Ideal.dvd_iff_le,←hps.2.2.1,←(primaryGenerator_spec J hgJ).1,
      Ideal.span_singleton_le_span_singleton]
    exact hd
  have hcount:=multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm:(multiplicity P I)%3=2:=by rwa [hcount]
  apply hS
  rw [hgen,mul_comm,sourceArithmeticResidue_prime_power_table p hp hps.2.2.2 _ hpd,
    hm]
  norm_num

lemma thetaSquarefreePart_squarefree (I:Ideal Eis) : Squarefree (thetaSquarefreePart I) := by
  apply IdealMobiusDivisorSum.squarefree_support_product
  exact Finset.filter_subset _ _

lemma thetaParts_mul_cube (I:Ideal Eis) (hI:I≠0)
    (he:∀P∈normalizedFactors I,(normalizedFactors I).count P%3≠2) :
    thetaSquarefreePart I*thetaCubePart I ^3=I := by
  rw [thetaSquarefreePart,Finset.prod_filter,thetaCubePart,←Finset.prod_pow,←Finset.prod_mul_distrib]
  calc
    _=∏P∈primeSupport I,P^((normalizedFactors I).count P):=by
      apply Finset.prod_congr rfl
      intro P hP
      have hp:=he P (Multiset.mem_toFinset.mp hP)
      have hm:(normalizedFactors I).count P%3=0 ∨ (normalizedFactors I).count P%3=1:=by omega
      rcases hm with hm|hm
      · rw [if_neg (by omega),one_mul,←pow_mul]
        congr 1
        omega
      · rw [if_pos hm,←pow_mul,←pow_succ']
        congr 1
        omega
    _=(normalizedFactors I).prod:=(Finset.prod_multiset_count (normalizedFactors I)).symm
    _=I:=Ideal.prod_normalizedFactors_eq_self hI

theorem sourceArithmeticResidue_squarefree_cube_support (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hS:sourceArithmeticResidue (primaryGenerator I)≠0) :
    Squarefree (thetaSquarefreePart I) ∧
    primaryGenerator (thetaSquarefreePart I)≠0 ∧
    primaryGenerator (thetaCubePart I)≠0 ∧
    thetaSquarefreePart I*thetaCubePart I ^3=I := by
  have he:=thetaParts_mul_cube I (primaryGenerator_ne_zero_ideal I hI)
    (fun P hP=>sourceArithmeticResidue_valuation_ne_two I P hI hP hS)
  have hgen:primaryGenerator I=
      primaryGenerator (thetaSquarefreePart I)*(primaryGenerator (thetaCubePart I))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart I*thetaCubePart I ^3):=congrArg primaryGenerator he.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart I)≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,zero_mul])
  have hB:primaryGenerator (thetaCubePart I)≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  exact ⟨thetaSquarefreePart_squarefree I,hA,hB,he⟩

theorem sourceFourier_squarefree_cube_support (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hS:sourceResidualFourierCoefficient (primaryGenerator I)≠0) :
    ∃A B:Ideal Eis,Squarefree A ∧ primaryGenerator A≠0 ∧ primaryGenerator B≠0 ∧ A*B^3=I := by
  have hs:sourceArithmeticResidue (primaryGenerator I)≠0:=by
    intro hz
    exact hS (by rw [sourceResidualFourierCoefficient,hz,mul_zero])
  exact ⟨thetaSquarefreePart I,thetaCubePart I,
    sourceArithmeticResidue_squarefree_cube_support I hI hs⟩

theorem sourceFourier_primary_zero_of_base_zero (hC:infinityCoefficientScalar=0)
    (n:Eis) (hprimary:lambda^2∣n-1) : sourceResidualFourierCoefficient n=0 := by
  have hn:n≠0:=primary_ne_zero n hprimary
  let I:Ideal Eis:=Ideal.span {n}
  have hgen:primaryGenerator I=n:=primaryGenerator_span n hn hprimary
  have hI:primaryGenerator I≠0:=by rwa [hgen]
  by_contra hT
  have hTI:sourceResidualFourierCoefficient (primaryGenerator I)≠0:=by rwa [hgen]
  obtain ⟨A,B,hA,hAg,hBg,hAB⟩:=sourceFourier_squarefree_cube_support I hI hTI
  have harg:primaryGenerator A*(primaryGenerator B)^3=n:=by
    have he:=congrArg primaryGenerator hAB
    simpa only [primaryGenerator_mul,primaryGenerator_pow,hgen] using he
  have he:=infinityCoefficient_squarefree_cube A B hAg hBg hA
  rw [harg,hC,zero_mul,zero_mul,zero_mul] at he
  exact hT (star_eq_zero.mp he)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma extraPeriodWitness_factor :
    integralComplexMatrix (extraPeriodWitness:SL(2,Eis))=
      complexTranslation (-eisEmbedding omega)*
        integralComplexMatrix (rationalEmbedding rationalLowerMinusThree)*
        complexTranslation (eisEmbedding omega) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix_apply,
    rationalEmbedding, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [extraPeriodWitness, rationalLowerMinusThree, complexTranslation, map_ofNat] <;> ring

lemma extraPeriodWitness_character : complexCharacter extraPeriodWitness=eisEmbedding omega := by
  change eisEmbedding (symbol (-3) (1+3*omega))=eisEmbedding omega
  apply congrArg eisEmbedding
  have hp:lambda^2∣(1+3*omega)-1:=lambda_sq_dvd_three.trans ⟨omega,by ring⟩
  rw [symbol_neg_numerator _ _ hp]
  have he:=ramified_symbol_at_omega (-(ramifiedOmegaUnit^2)) 2 2
    (Or.inr (by simp only [Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]))
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination ramified_omega_relation
  have hnum:((-(ramifiedOmegaUnit^2):Eisˣ):Eis)*lambda^2=3:=by
    simp only [Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
    rw [hl]
    calc
      _=3*omega^3:=by ring
      _=3:=by rw [omega_primitive.pow_eq_one];ring
  rw [hnum] at he
  have hw:omega^(2*2)=omega:=by
    norm_num only [Nat.reduceMul]
    calc
      omega^4=omega^3*omega:=by ring
      _=omega:=by rw [omega_primitive.pow_eq_one,one_mul]
  exact he.trans hw

lemma extraPeriodWitness_character_ne_one : complexCharacter extraPeriodWitness≠1 := by
  rw [extraPeriodWitness_character]
  intro he
  exact omega_primitive.ne_one (by decide) (eisEmbedding_injective (by simpa only [map_one] using he))

theorem cubicSource_not_eisenstein_periodic :
    ¬(∀a:Eis,∀w:HyperbolicSpace,
      cubicSourceResidualFunction (complexTranslation (eisEmbedding a) • w)=
        cubicSourceResidualFunction w) := by
  intro hperiod
  apply cubicSourceResidualFunction_ne_zero
  funext w
  have hneg (u:HyperbolicSpace):
      cubicSourceResidualFunction (complexTranslation (-eisEmbedding omega) • u)=
        cubicSourceResidualFunction u:=by
    simpa only [map_neg] using hperiod (-omega) u
  have hinv:cubicSourceResidualFunction
      (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=cubicSourceResidualFunction w:=by
    rw [extraPeriodWitness_factor,mul_smul,mul_smul,hneg,
      cubicSourceResidualFunction_rational_invariant,hperiod]
  have hchar:=cubicSourceResidualFunction_automorphy (sourceLevelInclusion extraPeriodWitness) w
  change cubicSourceResidualFunction (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=
    levelTwoComplexCharacter ⟨(extraPeriodWitness:SL(2,Eis)),levelThree_le_levelTwo extraPeriodWitness.property⟩*
      cubicSourceResidualFunction w at hchar
  rw [levelTwoComplexCharacter_restrict] at hchar
  change cubicSourceResidualFunction (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=
    complexCharacter extraPeriodWitness*cubicSourceResidualFunction w at hchar
  rw [hinv] at hchar
  have hz:(complexCharacter extraPeriodWitness-1)*cubicSourceResidualFunction w=0:=by
    linear_combination -hchar
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr extraPeriodWitness_character_ne_one)

end CubicEisenstein

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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma source_period_of_three_supported
    (hs:∀h:Eis,¬(3:Eis)∣h→sourceResidualFourierCoefficient h=0)
    (a:Eis) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubicSourceResidualFunction (upperPoint (z+eisEmbedding a) v hv)=
      cubicSourceResidualFunction (upperPoint z v hv) := by
  rw [cubicSourceResidualFunction_bessel,cubicSourceResidualFunction_bessel]
  apply congrArg (fun t:ℂ=>(3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)+t)
  apply tsum_congr
  intro h
  by_cases hd:(3:Eis)∣h
  · obtain ⟨b,rfl⟩:=hd
    have hp:ShortDraftTrace.breveE (cuspFrequency (3*b)*eisEmbedding a)=1:=by
      have he:cuspFrequency (3*b)*eisEmbedding a=cuspFrequency b*(3*eisEmbedding a):=by
        unfold cuspFrequency
        rw [map_mul,map_ofNat]
        ring
      rw [he,cuspFrequency_period]
    rw [mul_add,AddChar.map_add_eq_mul,hp,mul_one]
  · rw [hs h hd]
    by_cases hh:h=0 <;> simp [hh]

theorem exists_source_coefficient_not_three :
    ∃h:Eis,¬(3:Eis)∣h ∧ sourceResidualFourierCoefficient h≠0 := by
  by_contra hn
  have hs:∀h:Eis,¬(3:Eis)∣h→sourceResidualFourierCoefficient h=0:=by
    intro h hh
    by_contra hne
    exact hn ⟨h,hh,hne⟩
  apply cubicSource_not_eisenstein_periodic
  intro a w
  obtain ⟨z,v,hv,rfl⟩:=upperPoint_surjective w
  rw [complexTranslation_action]
  exact source_period_of_three_supported hs a z v hv

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical BigOperators Topology

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.BesselReflection
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

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups

section
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedSource_horizontal_hasDerivAt (side:Bool) (v:ℝ) (hv:0<v)
    (z direction:ℂ) (t:ℝ) :
    HasDerivAt (fun x:ℝ => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3)
        (z/3+(t:ℂ)*(direction/3)) (direction/3)) t := by
  have he : (fun x:ℝ => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (z+(x:ℂ)*direction) v hv)) =
      (fun x:ℝ => (ramifiedBesselCoefficients side).series
        (v/3,z/3+(x:ℂ)*(direction/3))) := by
    funext x
    rw [ramifiedSource_eq_series]
    congr 2
    ring
  rw [he]
  exact (ramifiedBesselCoefficients side).series_horizontal_hasDerivAt
    (v/3) (by positivity) (z/3) (direction/3) t

lemma ramifiedSource_wirtingerBar_cusp_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C ∧ ∀(v:ℝ)(hv:0<v)(z:ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
        (upperPoint w v hv)) z‖ ≤ C*Real.exp (-(residualCuspDecayRate/3)*v) := by
  obtain ⟨C1,hC1,h1b⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (1/3)
  obtain ⟨CI,hCI,hIb⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (Complex.I/3)
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (ramifiedSource_horizontal_hasDerivAt side v hv z 1 0).deriv
  have hI := (ramifiedSource_horizontal_hasDerivAt side v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  have he : -residualCuspDecayRate*(v/3)=-(residualCuspDecayRate/3)*v := by ring
  have hb1 := h1b (v/3) (z/3) (by linarith)
  have hbI := hIb (v/3) (z/3) (by linarith)
  rw [he] at hb1 hbI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖Complex.I*(∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3))‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3)‖) := by
        rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-(residualCuspDecayRate/3)*v)+
      CI*Real.exp (-(residualCuspDecayRate/3)*v)) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hbI) (by norm_num)
    _ = _ := by ring

lemma ramifiedConjugate_zProfile_isBigO (side:Bool) (z:ℂ) :
    cuspZProfile (fun w => cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w)) z
      =O[atTop] (fun v:ℝ => Real.exp (-(residualCuspDecayRate/3)*v)) := by
  obtain ⟨C,hC,hb⟩ := ramifiedSource_wirtingerBar_cusp_decay side 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp:0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspZProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖horizontalWirtingerZ (fun w => star (ramifiedSourceFunction
    (ramifiedCuspRoot side:Eis) (upperPoint w v hvp))) z‖ ≤ _
  rw [horizontalWirtingerZ_star,norm_star]
  exact hb v hvp z hv

end

local notation "Eis" => ActualEisensteinCubic.O

lemma reflectedCuspProfile_eq_inv_square (A:ℂ) (Q:ℝ) (g:ℝ→ℂ) (v:ℝ) :
    reflectedCuspProfile A Q g v=A/(v:ℂ)^2*g ((Q*v)⁻¹) := by
  unfold reflectedCuspProfile
  rw [Complex.cpow_neg,Complex.cpow_ofNat]
  ring

lemma reflectedCuspProfile_reverse (A:ℂ) (hA:A≠0) (Q:ℝ) (hQ:0<Q)
    (f g:ℝ→ℂ) (hfg:∀v:ℝ,0<v→f v=reflectedCuspProfile A Q g v)
    (v:ℝ) (hv:0<v) :
    g v=reflectedCuspProfile (A⁻¹/(Q:ℂ)^2) Q f v := by
  have he:=hfg (Q*v)⁻¹ (by positivity)
  have harg:(Q*(Q*v)⁻¹)⁻¹=v := by field_simp
  rw [reflectedCuspProfile_eq_inv_square,harg] at he
  rw [reflectedCuspProfile_eq_inv_square,he,Complex.ofReal_inv,Complex.ofReal_mul]
  have hcQ:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  have hcv:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

theorem cusp_mellin_entire_both (f g:ℝ→ℂ) (A:ℂ) (hA:A≠0)
    (Q decayF decayG:ℝ) (hQ:0<Q) (hdecayF:0<decayF) (hdecayG:0<decayG)
    (hf:ContinuousOn f (Set.Ioi 0)) (hg:ContinuousOn g (Set.Ioi 0))
    (hfbound:f =O[atTop] (fun v:ℝ=>Real.exp (-decayF*v)))
    (hgbound:g =O[atTop] (fun v:ℝ=>Real.exp (-decayG*v)))
    (hfg:∀v:ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    ((∀s:ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f)) ∧
    ((∀s:ℂ,MellinConvergent g s) ∧ Differentiable ℂ (mellin g)) := by
  constructor
  · exact cusp_mellin_entire f g A Q decayF decayG hQ hdecayF hdecayG
      hf hg hfbound hgbound hfg
  · exact cusp_mellin_entire g f (A⁻¹/(Q:ℂ)^2) Q decayG decayF hQ hdecayG hdecayF
      hg hf hgbound hfbound (reflectedCuspProfile_reverse A hA Q hQ f g hfg)

end CubicEisenstein

open scoped BigOperators Classical

namespace CompletedGauss

section
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem squarefree_cube_decomposition_unique {I J I' J':Ideal Eis}
    (hJ:J≠0) (hJ':J'≠0) (hI:Squarefree I) (hI':Squarefree I')
    (h:I*J^3=I'*J'^3) : I=I' ∧ J=J' := by
  have hf:=congrArg normalizedFactors h
  rw [normalizedFactors_mul hI.ne_zero (pow_ne_zero _ hJ),
    normalizedFactors_mul hI'.ne_zero (pow_ne_zero _ hJ'),
    normalizedFactors_pow,normalizedFactors_pow] at hf
  have hi:=(squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI
  have hi':=(squarefree_iff_nodup_normalizedFactors hI'.ne_zero).mp hI'
  have hc (P:Ideal Eis) :
      (normalizedFactors I).count P=(normalizedFactors I').count P ∧
      (normalizedFactors J).count P=(normalizedFactors J').count P := by
    have he:=congrArg (Multiset.count P) hf
    simp only [Multiset.count_add,Multiset.count_nsmul] at he
    have h1:=Multiset.nodup_iff_count_le_one.mp hi P
    have h2:=Multiset.nodup_iff_count_le_one.mp hi' P
    omega
  constructor
  · calc
      I=(normalizedFactors I).prod:=(Ideal.prod_normalizedFactors_eq_self hI.ne_zero).symm
      _=(normalizedFactors I').prod:=congrArg Multiset.prod (Multiset.ext.mpr (fun P=>(hc P).1))
      _=I':=Ideal.prod_normalizedFactors_eq_self hI'.ne_zero
  · calc
      J=(normalizedFactors J).prod:=(Ideal.prod_normalizedFactors_eq_self hJ).symm
      _=(normalizedFactors J').prod:=congrArg Multiset.prod (Multiset.ext.mpr (fun P=>(hc P).2))
      _=J':=Ideal.prod_normalizedFactors_eq_self hJ'

theorem primary_squarefree_cube_eq_iff {I J I' J':Ideal Eis}
    (hI:Squarefree I) (hI':Squarefree I')
    (hgI:primaryGenerator I≠0) (hgJ:primaryGenerator J≠0)
    (hgI':primaryGenerator I'≠0) (hgJ':primaryGenerator J'≠0) :
    primaryGenerator I*(primaryGenerator J)^3=
      primaryGenerator I'*(primaryGenerator J')^3 ↔ I=I' ∧ J=J' := by
  constructor
  · intro h
    have hleft:primaryGenerator (I*J^3)≠0:=by
      rw [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow]
      exact mul_ne_zero hgI (pow_ne_zero _ hgJ)
    have hright:primaryGenerator (I'*J'^3)≠0:=by
      rw [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow]
      exact mul_ne_zero hgI' (pow_ne_zero _ hgJ')
    have he:I*J^3=I'*J'^3:=by
      calc
        I*J^3=Ideal.span {primaryGenerator (I*J^3)}:=(primaryGenerator_spec _ hleft).1.symm
        _=Ideal.span {primaryGenerator (I'*J'^3)}:=by
          apply congrArg (fun z:Eis => (Ideal.span {z}:Ideal Eis))
          simpa only [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow] using h
        _=I'*J'^3:=(primaryGenerator_spec _ hright).1
    exact squarefree_cube_decomposition_unique
      (primaryGenerator_ne_zero_ideal J hgJ) (primaryGenerator_ne_zero_ideal J' hgJ') hI hI' he
  · rintro ⟨rfl,rfl⟩
    rfl

theorem primary_squarefree_cube_injective :
    Function.Injective (fun x:
      {I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0} =>
        primaryGenerator x.1.val*(primaryGenerator x.2.val)^3) := by
  intro x y he
  have h:= (primary_squarefree_cube_eq_iff x.1.property.1 y.1.property.1
    x.1.property.2 x.2.property y.1.property.2 y.2.property).mp he
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.DualKernelSummability
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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

attribute [local instance] OAI.CubicEisenstein.ramifiedFrequencyUnitsFintype
lemma ramifiedFrequencyChar_neg_unit (k:Eis) (u:Eisˣ) (n:ℕ) :
    ramifiedFrequencyChar k (-u) n=ramifiedFrequencyChar k u n := by
  ext x
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  have hp:lambda^2∣(1+3*d)-1:=by
    rw [add_sub_cancel_left]
    exact dvd_mul_of_dvd_left lambda_sq_dvd_three d
  rw [ramifiedFrequencyChar_mk,ramifiedFrequencyChar_mk,Units.val_neg,neg_mul,
    symbol_neg_numerator _ _ hp]

lemma arithmeticResidueSum_neg_unit (h:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum (-h) (u.val*lambda^n)=
      arithmeticResidueSum h ((-u).val*lambda^n) := by
  by_cases hd:u.val*lambda^n∣3*(-h)
  · obtain ⟨k,hk⟩:=hd
    have hk':3*h=((-u).val*lambda^n)*k:=by
      simp only [Units.val_neg]
      linear_combination -hk
    rw [ramified_arithmetic_character_test (-h) k u n hn hk,
      ramified_arithmetic_character_test h k (-u) n hn hk',ramifiedFrequencyChar_neg_unit]
  · have hl:arithmeticResidueSum (-h) (u.val*lambda^n)=0:=by
      by_contra he
      exact hd (ramified_arithmetic_support (-h) u n hn he)
    have hr:arithmeticResidueSum h ((-u).val*lambda^n)=0:=by
      by_contra he
      obtain ⟨k,hk⟩:=ramified_arithmetic_support h (-u) n hn he
      apply hd
      refine ⟨k,?_⟩
      simp only [Units.val_neg] at hk
      linear_combination -hk
    rw [hl,hr]

lemma principalResidueTerm_neg (h:Eis) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (-h) u n=principalResidueTerm h (-u) n := by
  unfold principalResidueTerm
  rw [arithmeticResidueSum_neg_unit h u (n+2) (by omega)]
  congr 2
  simp only [Units.val_neg]
  ring

lemma principalArithmeticResidue_neg (h:Eis) :
    principalArithmeticResidue (-h)=principalArithmeticResidue h := by
  by_cases hh:h=0
  · rw [hh,neg_zero]
  let N:=max (ramifiedFrequencyBound (-h)+1) (ramifiedFrequencyBound h+1)
  rw [principalArithmeticResidue_eq_sum (-h) (neg_ne_zero.mpr hh) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum h hh N (le_max_right _ _)]
  apply congrArg (fun z:ℂ=>z/((9*Real.sqrt 3/2:ℝ):ℂ))
  simp_rw [principalResidueTerm_neg]
  exact Fintype.sum_equiv (Equiv.neg Eisˣ)
    (fun u=>∑n∈Finset.range N,principalResidueTerm h (-u) n)
    (fun u=>∑n∈Finset.range N,principalResidueTerm h u n) (fun _=>rfl)

theorem sourceArithmeticResidue_neg (h:Eis) :
    sourceArithmeticResidue (-h)=sourceArithmeticResidue h := by
  have hU:unramifiedGaussResidue (-(9*h))=unramifiedGaussResidue (9*h):=by
    have he:=unramifiedGaussResidue_of_initial_relation (-(9*h)) (9*h) 0
      (fun _=>1) (fun _=>0) (fun _ _=>analyticAt_const) (fun _ _=>analyticAt_const)
      continuousAt_const continuousAt_const
      (fun s hs hi=>by simpa only [one_mul,zero_mul,add_zero] using unramifiedCubicGaussSeries_neg s (9*h))
    simpa only [one_mul,zero_mul,add_zero] using he
  simp only [sourceArithmeticResidue,cuspFrequency_neg,
    AddChar.map_neg_eq_inv,inv_eq_one,principalArithmeticResidue_neg,
    mul_neg,hU]

lemma cubicBesselNormalizer_neg (h:Eis) : cubicBesselNormalizer (-h)=cubicBesselNormalizer h := by
  simp only [cubicBesselNormalizer,cuspFrequency_neg,norm_neg]

theorem sourceResidualFourierCoefficient_neg (h:Eis) :
    sourceResidualFourierCoefficient (-h)=sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,sourceResidualFourierCoefficient,
    cubicBesselNormalizer_neg,sourceArithmeticResidue_neg]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_eq_one_iff_coordinate (h:Eis) :
    ShortDraftTrace.breveE (cuspFrequency h)=1 ↔
      (3:ℤ)∣(ActualEisensteinCoordinates.coords h).2 := by
  have he:ShortDraftTrace.breveE (cuspFrequency h)=
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        3 (by norm_num) (Ideal.Quotient.mk _ h):=by
    rw [eisTraceModChar,IdealGaussCRT.traceModChar_mk]
    unfold cuspFrequency
    simp only [map_ofNat]
  rw [he,trace_third_coordinate]
  simpa only [pow_zero,one_mul,Nat.cast_zero,zero_add] using
    omega3_pow_exp_eq_one_iff 0 (ActualEisensteinCoordinates.coords h).2

lemma primary_or_negative_primary_of_source_mask (h:Eis) (h3:¬(3:Eis)∣h)
    (hphase:ShortDraftTrace.breveE (cuspFrequency h)=1) :
    lambda^2∣h-1 ∨ lambda^2∣(-h)-1 := by
  let a:ℤ:=(ActualEisensteinCoordinates.coords h).1
  let b:ℤ:=(ActualEisensteinCoordinates.coords h).2
  have heval:h=(a:Eis)+(b:Eis)*omega:=
    (ActualEisensteinCoordinates.eval_coords h).symm
  obtain ⟨B,hB⟩:=(sourceRayPhase_eq_one_iff_coordinate h).mp hphase
  have hBc:(b:Eis)=3*(B:Eis):=by exact_mod_cast hB
  have ha:¬(3:ℤ)∣a:=by
    rintro ⟨A,hA⟩
    apply h3
    refine ⟨(A:Eis)+(B:Eis)*omega,?_⟩
    have hAc:(a:Eis)=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hAc,hBc]
    ring
  have hcases:(3:ℤ)∣a-1 ∨ (3:ℤ)∣a+1:=by omega
  rcases hcases with ⟨A,hA⟩|⟨A,hA⟩
  · left
    apply lambda_sq_dvd_three.trans
    refine ⟨(A:Eis)+(B:Eis)*omega,?_⟩
    have hAc:(a:Eis)-1=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hBc]
    linear_combination hAc
  · right
    apply lambda_sq_dvd_three.trans
    refine ⟨-((A:Eis)+(B:Eis)*omega),?_⟩
    have hAc:(a:Eis)+1=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hBc]
    linear_combination -hAc

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceFourier_supported_three_of_base_zero (hC:infinityCoefficientScalar=0)
    (h:Eis) (h3:¬(3:Eis)∣h) : sourceResidualFourierCoefficient h=0 := by
  by_cases hm:ShortDraftTrace.breveE (cuspFrequency h)=1
  · rcases primary_or_negative_primary_of_source_mask h h3 hm with hh|hh
    · exact sourceFourier_primary_zero_of_base_zero hC h hh
    · rw [←sourceResidualFourierCoefficient_neg h]
      exact sourceFourier_primary_zero_of_base_zero hC (-h) hh
  · simp only [sourceResidualFourierCoefficient,sourceArithmeticResidue,if_neg hm,mul_zero]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem infinityCoefficientScalar_ne_zero : infinityCoefficientScalar≠0 := by
  intro hC
  obtain ⟨h,h3,hn⟩:=exists_source_coefficient_not_three
  exact hn (sourceFourier_supported_three_of_base_zero hC h h3)

theorem normalized_infinityCoefficient_squarefree_cube (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I) :
    infinityCoefficientScalar⁻¹*
      star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))=
      (‖eisEmbedding (primaryGenerator J)‖:ℂ)*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  rw [infinityCoefficient_squarefree_cube I J hI hJ hsq]
  simp only [←mul_assoc,inv_mul_cancel₀ infinityCoefficientScalar_ne_zero,one_mul]

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.FiniteTranslations
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

namespace CubicEisenstein

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

namespace SubexponentialBesselCoefficients

lemma term_horizontal_translate (coeff : SubexponentialBesselCoefficients)
    (h : Eis) (v : ℝ) (z a : ℂ) :
    coeff.term h (v,z+a)=ShortDraftTrace.breveE (cuspFrequency h*a)*coeff.term h (v,z) := by
  by_cases hh:h=0
  · simp only [term,if_pos hh,mul_zero]
  · simp only [term,if_neg hh,mul_add,AddChar.map_add_eq_mul]
    ring

lemma finiteTranslate_term {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (h : Eis) (v : ℝ) (z : ℂ) :
    (coeff.finiteTranslate shift weight).term h (v,z)=
      ∑i,weight i*coeff.term h (v,z+shift i) := by
  simp_rw [term_horizontal_translate]
  rw [show (∑i,weight i*(ShortDraftTrace.breveE (cuspFrequency h*shift i)*coeff.term h (v,z)))=
      finiteTranslationMultiplier shift weight h*coeff.term h (v,z) by
    simp only [finiteTranslationMultiplier,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  by_cases hh:h=0
  · simp only [term,if_pos hh,mul_zero]
  · simp only [term,if_neg hh,finiteTranslate]
    ring

theorem finiteTranslate_series {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    (coeff.finiteTranslate shift weight).series (v,z)=
      ∑i,weight i*coeff.series (v,z+shift i) := by
  simp only [series,finiteTranslate_term]
  rw [Summable.tsum_finsetSum (fun i hi=>(coeff.summable (v,z+shift i) hv).mul_left (weight i))]
  apply Finset.sum_congr rfl
  intro i hi
  exact tsum_mul_left

theorem finiteTranslate_fullFunction {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ) (constant : ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    (coeff.finiteTranslate shift weight).fullFunction ((∑i,weight i)*constant) (upperPoint z v hv)=
      ∑i,weight i*coeff.fullFunction constant (upperPoint (z+shift i) v hv) := by
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    finiteTranslate_series coeff shift weight v hv,Finset.sum_mul,mul_add,
    Finset.sum_add_distrib]
  have hconst : (∑i,weight i*constant*(v:ℂ)^(2/3:ℂ))=
      ∑i,constant*(v:ℂ)^(2/3:ℂ)*weight i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hconst]
  ring_nf

end SubexponentialBesselCoefficients

end

section
local notation "Eis" => ActualEisensteinCubic.O

lemma finiteAdditiveFourier_inversion {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (φ : R→ℂ) (x : R) :
    (∑h,finiteAdditiveFourierCoeff ψ φ h*ψ (h*x))=φ x := by
  have hN : (Fintype.card R:ℂ)≠0:=by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (∑h,∑y,φ y*ψ (-h*y)*ψ (h*x))/(Fintype.card R:ℂ) := by
      simp only [finiteAdditiveFourierCoeff,div_mul_eq_mul_div,Finset.sum_mul,Finset.sum_div]
    _ = (∑y,φ y*∑h,ψ (h*(x-y)))/(Fintype.card R:ℂ) := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [mul_assoc,←AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (∑y,φ y*(if x-y=0 then (Fintype.card R:ℂ) else 0))/(Fintype.card R:ℂ) := by
      simp only [AddChar.sum_mulShift _ hψ,apply_ite,Nat.cast_zero]
    _ = φ x := by
      have he : (∑y,φ y*(if x-y=0 then (Fintype.card R:ℂ) else 0))=
          φ x*(Fintype.card R:ℂ) := by
        simp [sub_eq_zero]
      rw [he,mul_div_cancel_right₀ _ hN]

lemma thetaFourierTranslation_phase (c : Eis) (hc : c≠0)
    (h : Eis⧸Ideal.span {c}) (x : Eis) :
    ShortDraftTrace.breveE (-cuspFrequency x*thetaFourierTranslation c h)=
      quotientTrace c hc (h*Ideal.Quotient.mk _ x) := by
  have hm : h*Ideal.Quotient.mk _ x=Ideal.Quotient.mk _ (Quotient.out h*x) := by
    rw [map_mul,Ideal.Quotient.mk_out]
  rw [hm]
  simp only [quotientTrace,ConcreteTraceCRT.eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency thetaFourierTranslation
  rw [map_mul]
  have hc0:=ConcreteTraceCRT.eisEmbedding_ne_zero hc
  have hl:=ConcreteTraceCRT.eisLam_ne_zero
  field_simp
  linear_combination -(ConcreteTraceCRT.eisEmbedding x*
    ConcreteTraceCRT.eisEmbedding (Quotient.out h))*TraceLambdaPhase.eisLam_sq

lemma thetaFourierTranslation_inversion (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ) (x : Eis) :
    (∑h,finiteAdditiveFourierCoeff (quotientTrace c hc) φ h*
      ShortDraftTrace.breveE (-cuspFrequency x*thetaFourierTranslation c h))=
      φ (Ideal.Quotient.mk _ x) := by
  simp only [thetaFourierTranslation_phase c hc]
  exact finiteAdditiveFourier_inversion (quotientTrace c hc)
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) φ _

end

section
local notation "Eis" => ActualEisensteinCubic.O

lemma breveE_star (z : ℂ) : star (ShortDraftTrace.breveE z)=ShortDraftTrace.breveE (-z) := by
  change (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*(z+starRingEnd ℂ z)))=
    Complex.exp (2*Real.pi*Complex.I*((-z)+starRingEnd ℂ (-z)))
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul,map_add,map_neg,map_ofNat,Complex.conj_ofReal,Complex.conj_I,
    starRingEnd_self_apply]
  ring

lemma finiteTranslationMultiplier_star {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) :
    star (finiteTranslationMultiplier shift (fun i=>star (weight i)) h)=
      ∑i,weight i*ShortDraftTrace.breveE (-cuspFrequency h*shift i) := by
  simp only [finiteTranslationMultiplier,star_sum,star_mul,star_star,breveE_star,neg_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma finiteTranslate_term_multiplier {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (h : Eis) (v : ℝ) (z : ℂ) :
    (coeff.finiteTranslate shift weight).term h (v,z)=
      finiteTranslationMultiplier shift weight h*coeff.term h (v,z) := by
  by_cases hh:h=0
  · simp only [SubexponentialBesselCoefficients.term,if_pos hh,mul_zero]
  · simp only [SubexponentialBesselCoefficients.term,if_neg hh,
      SubexponentialBesselCoefficients.finiteTranslate]
    ring

lemma finiteConjugateSource_eq_bessel {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    finiteConjugateSource shift weight v hv z=
      star ((sourceBesselCoefficients.finiteTranslate shift (fun i=>star (weight i))).fullFunction
        ((∑i,star (weight i))*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv)) := by
  rw [sourceBesselCoefficients.finiteTranslate_fullFunction]
  simp only [star_sum,star_mul,star_star,finiteConjugateSource,cubicSourceConjugateFunction,
    cubicSourceResidualFunction_eq_bessel,sourceBesselFunction]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteConjugateSource_wirtingerBar {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (finiteConjugateSource shift weight v hv) z=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        (∑i,weight i*ShortDraftTrace.breveE (-cuspFrequency h*shift i))*
          star (sourceBesselCoefficients.term h (v,z)) := by
  have hf : finiteConjugateSource shift weight v hv = fun z=>
      star ((sourceBesselCoefficients.finiteTranslate shift (fun i=>star (weight i))).fullFunction
        ((∑i,star (weight i))*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv)) :=
    funext (finiteConjugateSource_eq_bessel shift weight v hv)
  rw [hf,horizontalWirtingerBar_star,
    SubexponentialBesselCoefficients.fullFunction_wirtingerZ,tsum_star]
  apply tsum_congr
  intro h
  rw [finiteTranslate_term_multiplier,star_mul,star_mul,finiteTranslationMultiplier_star]
  have hphase : star (2*Real.pi*Complex.I*cuspFrequency h)=
      -2*Real.pi*Complex.I*star (cuspFrequency h) := by
    simp only [star_mul,Complex.star_def,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
    ring
  rw [hphase]
  ring

theorem traceTwistedConjugateSource_wirtingerBar (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) z=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        φ (Ideal.Quotient.mk _ h)*star (sourceBesselCoefficients.term h (v,z)) := by
  change horizontalWirtingerBar (finiteConjugateSource (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) φ) v hv) z = _
  rw [finiteConjugateSource_wirtingerBar]
  simp only [thetaFourierTranslation_inversion c hc]

theorem traceTwistedConjugateSource_wirtingerBar_zero (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) 0=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        φ (Ideal.Quotient.mk _ h)*star (sourceResidualFourierCoefficient h)*
          (v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  rw [traceTwistedConjugateSource_wirtingerBar]
  apply tsum_congr
  intro h
  by_cases hh:h=0
  · subst h
    simp [cuspFrequency]
  · rw [sourceBesselCoefficients.term_bessel h hh v hv]
    have hx : 0<4*Real.pi*‖cuspFrequency h‖*v :=
      mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))) hv
    rw [schlafliBesselK_cubic_real _ hx]
    have he0 : ShortDraftTrace.breveE (0:ℂ)=1 := by
      simp [ShortDraftTrace.breveE]
    simp only [mul_zero,he0,mul_one,star_mul,
      Complex.star_def,Complex.conj_ofReal,sourceBesselCoefficients]
    ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedThetaTwist_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : lambda^2∣x-1) :
    fixedThetaTwist Ψ x=eisEmbedding (symbol ramifiedTraceLambda x)*Ψ x := by
  simp only [fixedThetaTwist,if_pos hx]

lemma fixedThetaTwist_not_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : ¬lambda^2∣x-1) :
    fixedThetaTwist Ψ x=0 := by
  simp only [fixedThetaTwist,if_neg hx]

lemma paperLambda_symbol_cube (x : Eis) (hx : lambda^2∣x-1) :
    (eisEmbedding (symbol ramifiedTraceLambda x))^3=1 := by
  rw [←map_pow,symbol_cube_of_isCoprime _ _ hx
    (ramified_character_coprime 0 1 _ x (Or.inl (by simp)) hx),map_one]

lemma paperLambda_symbol_norm (x : Eis) (hx : lambda^2∣x-1) :
    ‖eisEmbedding (symbol ramifiedTraceLambda x)‖=1 := by
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one,one_pow] using congrArg norm (paperLambda_symbol_cube x hx)

theorem fixedThetaTwist_periodic (Ψ : Eis→*ℂ) (Q : Ideal Eis)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (x y : Eis)
    (hxy : x-y∈Ideal.span {(9:Eis)}*Q) : fixedThetaTwist Ψ x=fixedThetaTwist Ψ y := by
  have h9 : (9:Eis)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_left hxy)
  have hd : lambda^2∣x-y := lambda_sq_dvd_three.trans ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9)
  have hp : lambda^2∣x-1 ↔ lambda^2∣y-1 := by
    constructor
    · intro hx
      convert (preTransparency := .instances) dvd_sub hx hd using 1 ; ring
    · intro hy
      convert (preTransparency := .instances) dvd_add hd hy using 1 ; ring
  by_cases hx : lambda^2∣x-1
  · have hy := hp.mp hx
    rw [fixedThetaTwist_primary Ψ x hx,fixedThetaTwist_primary Ψ y hy,
      hΨ x y (Ideal.mul_le_right hxy)]
    congr 2
    exact CubicRamified.symbol_traceLambda_congr_mod_nine x y hx hy h9
  · rw [fixedThetaTwist_not_primary Ψ x hx,
      fixedThetaTwist_not_primary Ψ y (fun hy=>hx (hp.mpr hy))]

lemma fixedThetaQuotient_mk (Ψ : Eis→*ℂ) (Q : Ideal Eis)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (c : Eis)
    (hc : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (x : Eis) :
    fixedThetaQuotient Ψ c (Ideal.Quotient.mk _ x)=fixedThetaTwist Ψ x := by
  apply fixedThetaTwist_periodic Ψ Q hΨ
  exact hc (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) x)))

lemma paperLambda_symbol_squarefree_cube (n b : Eis) (hb : lambda^2∣b-1) :
    eisEmbedding (symbol ramifiedTraceLambda (n*b^3))=
      eisEmbedding (symbol ramifiedTraceLambda n) := by
  rw [symbol_mul_denominator,cubicSymbol_pow_denominator,map_mul,map_pow,
    paperLambda_symbol_cube b hb,mul_one]

theorem fixedThetaTwist_infinity_coefficient (Ψ : Eis→*ℂ) (I J : Ideal Eis)
    (hI : primaryGenerator I≠0) (hJ : primaryGenerator J≠0) (hsq : Squarefree I) :
    infinityCoefficientScalar⁻¹ *
      star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))*
        fixedThetaTwist Ψ (primaryGenerator I*(primaryGenerator J)^3)=
      (‖eisEmbedding (primaryGenerator J)‖:ℂ)*gaussTwo I hI*
        Ψ (primaryGenerator I)*(Ψ (primaryGenerator J))^3 := by
  have hn := (primaryGenerator_spec I hI).2
  have hb := (primaryGenerator_spec J hJ).2
  have hnb : lambda^2∣primaryGenerator I*(primaryGenerator J)^3-1 :=
    CubicJacobiGlobal.primary_mul _ _ hn (primary_pow_congruence _ hb 3)
  rw [normalized_infinityCoefficient_squarefree_cube I J hI hJ hsq,
    fixedThetaTwist_primary Ψ _ hnb,paperLambda_symbol_squarefree_cube _ _ hb,map_mul,map_pow]
  have hunit : star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
      eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I))=1 := by
    simpa only [Complex.star_def,paperLambda_symbol_norm _ hn,one_pow,
      Complex.ofReal_one] using Complex.conj_mul' (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))
  calc
    _ = (star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
        eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
        ((‖eisEmbedding (primaryGenerator J)‖:ℂ)*gaussTwo I hI*
          Ψ (primaryGenerator I)*(Ψ (primaryGenerator J))^3) := by ring
    _ = _ := by rw [hunit,one_mul]

end

open ActualEisensteinCubic CompletedGauss CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFourier_primary_squarefree_cube_preimage (x:Eis)
    (hx:lambda^2∣x-1) (hT:sourceResidualFourierCoefficient x≠0) :
    ∃p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0}),
      primaryGenerator p.1.val*(primaryGenerator p.2.val)^3=x := by
  have hx0:x≠0:=primary_ne_zero x hx
  have hgen:primaryGenerator (Ideal.span {x})=x:=primaryGenerator_span x hx0 hx
  have hg:primaryGenerator (Ideal.span {x})≠0:=by rwa [hgen]
  have ht:sourceResidualFourierCoefficient (primaryGenerator (Ideal.span {x}))≠0:=by
    rwa [hgen]
  obtain ⟨I,J,hI,hgI,hgJ,hIJ⟩:=sourceFourier_squarefree_cube_support (Ideal.span {x}) hg ht
  refine ⟨(⟨I,hI,hgI⟩,⟨J,hgJ⟩),?_⟩
  have he:=congrArg primaryGenerator hIJ
  simpa only [primaryGenerator_mul,primaryGenerator_pow,hgen] using he

theorem sourceFourier_tsum_primary_pairs (w:Eis→ℂ)
    (hw:∀x:Eis,w x≠0→lambda^2∣x-1) :
    (∑'x:Eis,w x*star (sourceResidualFourierCoefficient x))=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        w (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)*
          star (sourceResidualFourierCoefficient
            (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)) := by
  let P:=({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
    {J:Ideal Eis // primaryGenerator J≠0})
  let phi:P→Eis:=fun p=>primaryGenerator p.1.val*(primaryGenerator p.2.val)^3
  let f:Eis→ℂ:=fun x=>w x*star (sourceResidualFourierCoefficient x)
  change (∑'x:Eis,f x)=∑'p:P,f (phi p)
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p:Function.support (fun p:P=>f (phi p))=>phi p.val)
  · exact primary_squarefree_cube_injective.comp Subtype.val_injective
  · intro x hx
    have hwx:w x≠0:=by
      intro hz
      exact hx (by simp only [f,hz,zero_mul])
    have hTx:sourceResidualFourierCoefficient x≠0:=by
      intro hz
      exact hx (by simp only [f,hz,star_zero,mul_zero])
    obtain ⟨p,hp⟩:=sourceFourier_primary_squarefree_cube_preimage x (hw x hwx) hTx
    have hphi:phi p=x:=hp
    have hfp:f (phi p)≠0:=by rwa [hphi]
    exact ⟨⟨p,hfp⟩,hphi⟩
  · intro p
    rfl

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.MellinSupport
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

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeWeight_zero_of_primaryGenerator_zero (Ψ:Eis→*ℂ) (I:Ideal Eis)
    (h:primaryGenerator I=0) : cubeWeight Ψ I=0 := by
  simp [cubeWeight,h,FiniteGaussPhase.angularFactor]

lemma completedMellinCoefficient_support (Ψ:Eis→*ℂ) (p:CompletedMellinIndex)
    (hp:completedMellinCoefficient Ψ p≠0) :
    Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 ∧ primaryGenerator p.2.val≠0 := by
  have hleft:Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 := by
    by_contra hh
    apply hp
    simp only [completedMellinCoefficient,columnWeight,squarefreeGaussCoefficient,
      dif_neg hh,zero_mul,zero_div]
  refine ⟨hleft.1,hleft.2,?_⟩
  intro hright
  apply hp
  rw [completedMellinCoefficient,cubeWeight_zero_of_primaryGenerator_zero Ψ _ hright,mul_zero]

lemma primaryCubePairToMellinIndex_injective : Function.Injective primaryCubePairToMellinIndex := by
  intro p q hpq
  exact Prod.ext
    (Subtype.ext (congrArg (fun x:CompletedMellinIndex=>x.1.val) hpq))
    (Subtype.ext (congrArg (fun x:CompletedMellinIndex=>x.2.val) hpq))

theorem completedMellinCoefficient_tsum_primary_pairs (Ψ:Eis→*ℂ)
    (w:CompletedMellinIndex→ℂ) :
    (∑'p:CompletedMellinIndex,completedMellinCoefficient Ψ p*w p)=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        completedMellinCoefficient Ψ (primaryCubePairToMellinIndex p)*
          w (primaryCubePairToMellinIndex p) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p=>primaryCubePairToMellinIndex p.val)
  · exact primaryCubePairToMellinIndex_injective.comp Subtype.val_injective
  · intro p hp
    change completedMellinCoefficient Ψ p*w p≠0 at hp
    have hc:completedMellinCoefficient Ψ p≠0 := by
      intro hz
      exact hp (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=completedMellinCoefficient_support Ψ p hc
    let q:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0}):=(⟨p.1.val,hs,hI⟩,⟨p.2.val,hJ⟩)
    have hq:primaryCubePairToMellinIndex q=p := by
      exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    refine ⟨⟨q,?_⟩,hq⟩
    change completedMellinCoefficient Ψ (primaryCubePairToMellinIndex q)*
      w (primaryCubePairToMellinIndex q)≠0
    simpa only [hq] using hp
  · intro p
    rfl

theorem completedBesselProfile_primary_pairs (Ψ:Eis→*ℂ) (q v:ℝ) :
    completedBesselProfile Ψ q v=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        (completedMellinCoefficient Ψ (primaryCubePairToMellinIndex p)*
          (completedMellinLength (primaryCubePairToMellinIndex p):ℂ))*(v:ℂ)*
            CubicEisenstein.schlafliBesselK (1/3)
              (4*Real.pi*q*Real.sqrt (completedMellinLength (primaryCubePairToMellinIndex p))*v) := by
  unfold completedBesselProfile CubicEisenstein.radialBesselProfile
  simpa only [mul_assoc] using completedMellinCoefficient_tsum_primary_pairs Ψ
    (fun p=>(completedMellinLength p:ℂ)*(v:ℂ)*CubicEisenstein.schlafliBesselK (1/3)
      (4*Real.pi*q*Real.sqrt (completedMellinLength p)*v))

end CompletedGauss

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSourceConjugateFunction_levelTwo (G:levelTwo) (w:HyperbolicSpace) :
    cubicSourceConjugateFunction (integralComplexMatrix (G:SL(2,Eis)) • w)=
      star (levelTwoComplexCharacter G)*cubicSourceConjugateFunction w := by
  simp only [cubicSourceConjugateFunction,cubicSourceResidualFunction_automorphy,star_mul]
  ring

theorem cubicSourceConjugateFunction_cuspDerivative_levelTwo (G:levelTwo)
    (g H:SL(2,ℂ)) (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*H)
    (hc:g 1 0≠0) (v:ℝ) (hv:0<v) :
    horizontalWirtingerBar (fun z=>cubicSourceConjugateFunction (upperPoint z v hv)) (g 0 0/g 1 0)=
      (star (levelTwoComplexCharacter G)*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>cubicSourceConjugateFunction (H • upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  refine cuspDerivative_of_transform cubicSourceConjugateFunction g H
    (star (levelTwoComplexCharacter G)) ?_ hc v hv ?_
  · intro w
    rw [hfactor,mul_smul,cubicSourceConjugateFunction_levelTwo]
  · exact cubicSourceConjugateFunction_translate_split_differentiableAt H _ (by positivity)

lemma cuspBarProfile_conjugate_reflection_levelTwo (G:levelTwo)
    (g H:SL(2,ℂ)) (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*H)
    (hc:g 1 0≠0) (v:ℝ) (hv:0<v) :
    cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0) v=
      reflectedCuspProfile (-star (levelTwoComplexCharacter G)/(g 1 0)^2)
        (‖g 1 0‖^2)
        (cuspZProfile (fun w=>cubicSourceConjugateFunction (H • w)) (-g 1 1/g 1 0)) v := by
  have hdual:0<(‖g 1 0‖^2*v)⁻¹ := by positivity
  rw [cuspBarProfile_positive _ _ _ hv,reflectedCuspProfile,cuspZProfile_positive _ _ _ hdual]
  have he:=cubicSourceConjugateFunction_cuspDerivative_levelTwo G g H hfactor hc v hv
  have hp:(v:ℂ)^(-2:ℂ)=((v:ℂ)^2)⁻¹ := by
    rw [Complex.cpow_neg,Complex.cpow_ofNat]
  rw [hp]
  simp only [one_div] at he
  rw [he]
  ring

lemma conjugateSource_cuspRepresentative_zProfile_decay (j:Fin 3) (z:ℂ) :
    ∃deltaLoss:ℝ,0<deltaLoss ∧ cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (cuspRepresentative j) • w)) z
        =O[atTop] (fun v:ℝ=>Real.exp (-deltaLoss*v)) := by
  fin_cases j
  · refine ⟨residualCuspDecayRate,residualCuspDecayRate_pos,?_⟩
    simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero]
      using cuspZProfile_conjugate_isBigO z
  · refine ⟨residualCuspDecayRate/3,div_pos residualCuspDecayRate_pos (by norm_num),?_⟩
    simpa [cuspRepresentative,cuspParameter,ramifiedCuspRoot,ramifiedOmegaUnit_val]
      using ramifiedConjugate_zProfile_isBigO false z
  · refine ⟨residualCuspDecayRate/3,div_pos residualCuspDecayRate_pos (by norm_num),?_⟩
    simpa [cuspRepresentative,cuspParameter,ramifiedCuspRoot,ramifiedOmegaUnit_val]
      using ramifiedConjugate_zProfile_isBigO true z

theorem conjugateSource_levelTwo_three_cusp_mellin_entire (G:levelTwo)
    (j:Fin 3) (g:SL(2,ℂ))
    (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j))
    (hc:g 1 0≠0) :
    ((∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)))) ∧
    ((∀s:ℂ,MellinConvergent
      (cuspZProfile (fun w=>cubicSourceConjugateFunction
        (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0)) s) ∧
      Differentiable ℂ (mellin
        (cuspZProfile (fun w=>cubicSourceConjugateFunction
          (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0)))) := by
  have hchar:levelTwoComplexCharacter G≠0 := by
    intro hz
    have hn:=norm_levelTwoComplexCharacter G
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  have hscalar:-star (levelTwoComplexCharacter G)/(g 1 0)^2≠0 :=
    div_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr hchar)) (pow_ne_zero 2 hc)
  obtain ⟨deltaLoss,hδ,hb⟩:=conjugateSource_cuspRepresentative_zProfile_decay j (-g 1 1/g 1 0)
  exact cusp_mellin_entire_both
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0))
    (-star (levelTwoComplexCharacter G)/(g 1 0)^2) hscalar (‖g 1 0‖^2)
    residualCuspDecayRate deltaLoss (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualCuspDecayRate_pos hδ
    (cuspBarProfile_conjugate_continuousOn _) (cuspZProfile_conjugate_translate_continuousOn _ _)
    (cuspBarProfile_conjugate_isBigO _) hb
    (fun v hv=>cuspBarProfile_conjugate_reflection_levelTwo G g _ hfactor hc v hv)

end

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem conjugateSource_integral_cusp_mellin_entire (M:SL(2,Eis)) (hc:M 1 0≠0) :
    (∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction
        (eisEmbedding (M 0 0)/eisEmbedding (M 1 0))) s) ∧
    Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction
      (eisEmbedding (M 0 0)/eisEmbedding (M 1 0)))) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
  let g:SL(2,ℂ):=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j)
  have he:integralComplexMatrix M=g*integralComplexMatrix T:=by
    rw [hM,map_mul,map_mul]
  have ht:integralComplexMatrix T 1 0=0:=by
    rw [integralComplexMatrix_apply,hT,map_zero]
  have hmc:(g*integralComplexMatrix T) 1 0≠0:=by
    rw [←he,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hc
  obtain ⟨hg,hratio⟩:=upper_triangular_right_cusp_ratio g (integralComplexMatrix T) ht hmc
  have hresult:=(conjugateSource_levelTwo_three_cusp_mellin_entire G j g rfl hg).1
  rw [←hratio,←he] at hresult
  simpa only [integralComplexMatrix_apply] using hresult

theorem conjugateSource_rational_cusp_mellin_entire (a c:Eis) (hc:c≠0) :
    (∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (eisEmbedding a/eisEmbedding c)) s) ∧
    Differentiable ℂ (mellin
      (cuspBarProfile cubicSourceConjugateFunction (eisEmbedding a/eisEmbedding c))) := by
  obtain ⟨M,hM,hratio⟩:=exists_integral_matrix_cusp_ratio a c hc
  simpa only [hratio] using conjugateSource_integral_cusp_mellin_entire M hM

theorem conjugateSource_finite_twist_cusp_mellin_entire (h c:Eis) (hc:c≠0) :
    (∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (-3*eisEmbedding h/eisEmbedding c)) s) ∧
    Differentiable ℂ (mellin
      (cuspBarProfile cubicSourceConjugateFunction (-3*eisEmbedding h/eisEmbedding c))) := by
  simpa only [map_mul,map_neg,map_ofNat] using
    conjugateSource_rational_cusp_mellin_entire (-3*h) c hc

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedTransform
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaFrequencyScale_ne_zero : thetaFrequencyScale≠0 := by
  exact one_div_ne_zero (mul_ne_zero (by norm_num) eisLam_ne_zero)

lemma thetaDerivativeScalar_ne_zero : thetaDerivativeScalar≠0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    (star_ne_zero.mpr thetaFrequencyScale_ne_zero)) infinityCoefficientScalar_ne_zero

lemma cuspFrequency_eq_thetaFrequencyScale (h : Eis) :
    cuspFrequency h=thetaFrequencyScale*eisEmbedding h := by
  unfold cuspFrequency thetaFrequencyScale
  ring

lemma completedCoefficient_mul_length (Ψ : Eis→*ℂ) (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0)
    (hsq : Squarefree I.val) :
    completedMellinCoefficient Ψ (I,J)*(completedMellinLength (I,J):ℂ)=
      star (eisEmbedding (primaryGenerator I.val*(primaryGenerator J.val)^3))*
        (‖eisEmbedding (primaryGenerator J.val)‖:ℂ)*gaussTwo I.val hI*
        Ψ (primaryGenerator I.val)*(Ψ (primaryGenerator J.val))^3 := by
  have hni : (Ideal.absNorm I.val:ℂ)=(‖eisEmbedding (primaryGenerator I.val)‖:ℂ)^2 := by
    exact_mod_cast (primaryGenerator_norm_sq I.val hI).symm
  have hnj : (Ideal.absNorm J.val:ℂ)=(‖eisEmbedding (primaryGenerator J.val)‖:ℂ)^2 := by
    exact_mod_cast (primaryGenerator_norm_sq J.val hJ).symm
  have hi0 : (‖eisEmbedding (primaryGenerator I.val)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hI))
  have hj0 : (‖eisEmbedding (primaryGenerator J.val)‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hJ))
  rw [completedMellinCoefficient,columnWeight_eq Ψ I.val hsq hI]
  rw [show cubeWeight Ψ J.val=star (FiniteGaussPhase.angularFactor (primaryGenerator J.val))^3*
    Ψ (primaryGenerator J.val)^3/(Ideal.absNorm J.val:ℂ) from rfl]
  simp only [FiniteGaussPhase.angularFactor,completedMellinLength,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
    ←primaryGenerator_norm I.val hI,hni,hnj,map_mul,map_pow,star_mul,star_pow,
    Complex.star_def,map_div₀,Complex.conj_ofReal]
  field_simp [hi0,hj0]

lemma thetaPair_frequency_norm (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0) :
    ‖cuspFrequency (primaryGenerator I.val*(primaryGenerator J.val)^3)‖=
      thetaBesselScale*Real.sqrt (completedMellinLength (I,J)) := by
  rw [cuspFrequency_eq_thetaFrequencyScale,norm_mul,map_mul,map_pow,norm_mul,norm_pow]
  have he : completedMellinLength (I,J)=
      (‖eisEmbedding (primaryGenerator I.val)‖*‖eisEmbedding (primaryGenerator J.val)‖^3)^2 := by
    rw [completedMellinLength,←primaryGenerator_norm_sq I.val hI,←primaryGenerator_norm_sq J.val hJ]
    ring
  rw [he,Real.sqrt_sq (by positivity)]
  rfl

lemma thetaPair_derivative_coefficient (Ψ : Eis→*ℂ) (I J : NonzeroIdeal)
    (hI : primaryGenerator I.val≠0) (hJ : primaryGenerator J.val≠0)
    (hsq : Squarefree I.val) :
    (-2*Real.pi*Complex.I*star (cuspFrequency (primaryGenerator I.val*(primaryGenerator J.val)^3)))*
      fixedThetaTwist Ψ (primaryGenerator I.val*(primaryGenerator J.val)^3)*
        star (sourceResidualFourierCoefficient (primaryGenerator I.val*(primaryGenerator J.val)^3))=
      thetaDerivativeScalar*(completedMellinCoefficient Ψ (I,J)*(completedMellinLength (I,J):ℂ)) := by
  have he := fixedThetaTwist_infinity_coefficient Ψ I.val J.val hI hJ hsq
  have he' := congrArg (fun z:ℂ=>infinityCoefficientScalar*z) he
  simp only [←mul_assoc,mul_inv_cancel₀ infinityCoefficientScalar_ne_zero,one_mul] at he'
  rw [completedCoefficient_mul_length Ψ I J hI hJ hsq,cuspFrequency_eq_thetaFrequencyScale,star_mul]
  unfold thetaDerivativeScalar
  calc
    _ = (-2*Real.pi*Complex.I*star thetaFrequencyScale)*
        star (eisEmbedding (primaryGenerator I.val*(primaryGenerator J.val)^3))*
          (star (sourceResidualFourierCoefficient (primaryGenerator I.val*(primaryGenerator J.val)^3))*
            fixedThetaTwist Ψ (primaryGenerator I.val*(primaryGenerator J.val)^3)) := by ring
    _ = _ := by rw [he'];ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem thetaTwistedSource_wirtingerBar_eq_completedBesselProfile
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (thetaTwistedSource Ψ c hc v hv) 0=
      thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v := by
  change horizontalWirtingerBar (traceTwistedConjugateSource c hc (fixedThetaQuotient Ψ c) v hv) 0 = _
  rw [traceTwistedConjugateSource_wirtingerBar_zero]
  simp only [fixedThetaQuotient_mk Ψ Q hΨ c hcQ]
  let w : Eis→ℂ := fun h=>(-2*Real.pi*Complex.I*star (cuspFrequency h))*
    fixedThetaTwist Ψ h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)
  have hw : ∀h:Eis,w h≠0→lambda^2∣h-1 := by
    intro h hwh
    by_contra hh
    exact hwh (by simp only [w,fixedThetaTwist_not_primary Ψ h hh,mul_zero,zero_mul])
  calc
    _ = ∑'h:Eis,w h*star (sourceResidualFourierCoefficient h) := by
      apply tsum_congr
      intro h
      dsimp only [w]
      ring
    _ = ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        w (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)*
          star (sourceResidualFourierCoefficient
            (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)) :=
      sourceFourier_tsum_primary_pairs w hw
    _ = thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v := by
      rw [completedBesselProfile_primary_pairs,←tsum_mul_left]
      apply tsum_congr
      intro p
      let ip := primaryCubePairToMellinIndex p
      have he := thetaPair_derivative_coefficient Ψ ip.1 ip.2 p.1.property.2 p.2.property p.1.property.1
      have hn := thetaPair_frequency_norm ip.1 ip.2 p.1.property.2 p.2.property
      change (-2*Real.pi*Complex.I*star (cuspFrequency (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)))*
          fixedThetaTwist Ψ (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)‖*v)*
          star (sourceResidualFourierCoefficient (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)) =
        thetaDerivativeScalar*((completedMellinCoefficient Ψ ip*(completedMellinLength ip:ℂ))*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*thetaBesselScale*Real.sqrt (completedMellinLength ip)*v))
      rw [hn,show 4*Real.pi*(thetaBesselScale*Real.sqrt (completedMellinLength ip))*v=
        4*Real.pi*thetaBesselScale*Real.sqrt (completedMellinLength ip)*v by ring]
      calc
        _ = ((-2*Real.pi*Complex.I*star (cuspFrequency (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)))*
            fixedThetaTwist Ψ (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)*
            star (sourceResidualFourierCoefficient (primaryGenerator ip.1.val*(primaryGenerator ip.2.val)^3)))*
            (v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*thetaBesselScale*Real.sqrt (completedMellinLength ip)*v) := by ring
        _ = _ := by rw [he];ring

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma horizontalWirtingerBar_finite_sum {ι : Type*} [Fintype ι]
    (f : ι→ℂ→ℂ) (weight : ι→ℂ) (z : ℂ)
    (h1 : ∀i,DifferentiableAt ℝ (fun t:ℝ=>f i (z+(t:ℂ))) 0)
    (hI : ∀i,DifferentiableAt ℝ (fun t:ℝ=>f i (z+(t:ℂ)*Complex.I)) 0) :
    horizontalWirtingerBar (fun w=>∑i,weight i*f i w) z=
      ∑i,weight i*horizontalWirtingerBar (f i) z := by
  unfold horizontalWirtingerBar
  rw [deriv_fun_sum (fun i hi=>(h1 i).const_mul (weight i)),
    deriv_fun_sum (fun i hi=>(hI i).const_mul (weight i))]
  simp only [deriv_const_mul_field,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma finiteConjugateSource_wirtingerBar_sum {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (finiteConjugateSource shift weight v hv) 0=
      ∑i,weight i*cuspBarProfile cubicSourceConjugateFunction (shift i) v := by
  have hd (i : ι) (direction : ℂ) : DifferentiableAt ℝ
      (fun t:ℝ=>cubicSourceConjugateFunction (upperPoint (((t:ℂ)*direction)+shift i) v hv)) 0 := by
    have he : (fun t:ℝ=>cubicSourceConjugateFunction (upperPoint (((t:ℂ)*direction)+shift i) v hv))=
        fun t:ℝ=>star (sourceBesselCoefficients.fullFunction ((3*(Real.pi:ℂ))*constantArithmeticResidue)
          (upperPoint (shift i+(t:ℂ)*direction) v hv)) := by
      funext t
      simp only [cubicSourceConjugateFunction,cubicSourceResidualFunction_eq_bessel,sourceBesselFunction,add_comm]
    rw [he]
    exact (sourceBesselCoefficients.fullFunction_horizontal_hasDerivAt _ v hv (shift i) direction 0).differentiableAt.star
  rw [show finiteConjugateSource shift weight v hv=
    fun w=>∑i,weight i*cubicSourceConjugateFunction (upperPoint (w+shift i) v hv) from rfl]
  rw [horizontalWirtingerBar_finite_sum _ weight 0
    (fun i=>by simpa only [zero_add,mul_one] using hd i 1)
    (fun i=>by simpa only [zero_add] using hd i Complex.I)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cuspBarProfile_positive _ _ _ hv]
  apply congrArg (fun z : ℂ => weight i * z)
  exact horizontalWirtingerBar_translate (fun z=>cubicSourceConjugateFunction (upperPoint z v hv)) (shift i)

theorem thetaTwistedCuspProfile_eq_completedBesselProfile
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v := by
  rw [←thetaTwistedSource_wirtingerBar_eq_completedBesselProfile Ψ Q hΨ c hc hcQ v hv]
  exact (finiteConjugateSource_wirtingerBar_sum (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c)) v hv).symm

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.EntireMellinProfile
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

namespace CubicEisenstein
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma finite_mellin_entire {ι : Type*} [Fintype ι] (f : ι→ℝ→ℂ) (weight : ι→ℂ)
    (hf : ∀i,(∀s:ℂ,MellinConvergent (f i) s) ∧ Differentiable ℂ (mellin (f i))) :
    (∀s:ℂ,MellinConvergent (fun v=>∑i,weight i*f i v) s) ∧
      Differentiable ℂ (mellin (fun v=>∑i,weight i*f i v)) := by
  have hs (s : ℂ) (i : ι) : MellinConvergent (fun v=>weight i*f i v) s := by
    simpa only [smul_eq_mul] using (hf i).1 s |>.const_smul (weight i)
  have hsi (s : ℂ) (i : ι) : IntegrableOn (fun v:ℝ=>(v:ℂ)^(s-1)*(weight i*f i v)) (Set.Ioi 0) := by
    simpa only [MellinConvergent,smul_eq_mul] using hs s i
  have he (s : ℂ) : mellin (fun v=>∑i,weight i*f i v) s=∑i,weight i*mellin (f i) s := by
    unfold mellin
    simp only [smul_eq_mul,Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i hi=>hsi s i)]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [mellin,smul_eq_mul] using mellin_const_smul (f i) s (weight i)
  constructor
  · intro s
    change IntegrableOn (fun v:ℝ=>(v:ℂ)^(s-1)*(∑i,weight i*f i v)) (Set.Ioi 0)
    simpa only [IntegrableOn,Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i hi=>hsi s i)
  · rw [show mellin (fun v=>∑i,weight i*f i v)=(fun s=>∑i,weight i*mellin (f i) s) from funext he]
    exact Differentiable.fun_sum (fun i hi=>(hf i).2.const_mul (weight i))

lemma thetaTwistedCuspProfile_mellin_entire (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] :
    (∀s:ℂ,MellinConvergent (thetaTwistedCuspProfile Ψ c hc) s) ∧
      Differentiable ℂ (mellin (thetaTwistedCuspProfile Ψ c hc)) := by
  apply finite_mellin_entire
  intro h
  have he : thetaFourierTranslation c h=(-3:ℂ)*eisEmbedding (Quotient.out h)/eisEmbedding c := by
    rw [thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
  rw [he]
  exact conjugateSource_finite_twist_cusp_mellin_entire (Quotient.out h) c hc

theorem completedBesselProfile_mellin_entire_of_periodic_oai
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) :
    (∀s:ℂ,MellinConvergent (completedBesselProfile Ψ thetaBesselScale) s) ∧
      Differentiable ℂ (mellin (completedBesselProfile Ψ thetaBesselScale)) := by
  have hf := thetaTwistedCuspProfile_mellin_entire Ψ c hc
  have he (v : ℝ) (hv : 0<v) :
      thetaDerivativeScalar⁻¹*thetaTwistedCuspProfile Ψ c hc v=
        completedBesselProfile Ψ thetaBesselScale v := by
    rw [thetaTwistedCuspProfile_eq_completedBesselProfile Ψ Q hΨ c hc hcQ v hv,
      ←mul_assoc,inv_mul_cancel₀ thetaDerivativeScalar_ne_zero,one_mul]
  have hm (s : ℂ) : mellin (completedBesselProfile Ψ thetaBesselScale) s=
      thetaDerivativeScalar⁻¹*mellin (thetaTwistedCuspProfile Ψ c hc) s := by
    have hmul := mellin_const_smul (thetaTwistedCuspProfile Ψ c hc) s thetaDerivativeScalar⁻¹
    simp only [smul_eq_mul] at hmul
    rw [←hmul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    simp only [smul_eq_mul,he v hv]
  constructor
  · intro s
    have hi := (hf.1 s).const_smul thetaDerivativeScalar⁻¹
    apply hi.congr_fun _ measurableSet_Ioi
    intro v hv
    simp only [smul_eq_mul,he v hv]
  · rw [show mellin (completedBesselProfile Ψ thetaBesselScale)=
      (fun s=>thetaDerivativeScalar⁻¹*mellin (thetaTwistedCuspProfile Ψ c hc) s) from funext hm]
    exact hf.2.const_mul _

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

end

end OAI
end

theorem solution : type_of% @OAI.CubicEisenstein.completedBesselProfile_mellin_entire_of_periodic_oai := @OAI.CubicEisenstein.completedBesselProfile_mellin_entire_of_periodic_oai
