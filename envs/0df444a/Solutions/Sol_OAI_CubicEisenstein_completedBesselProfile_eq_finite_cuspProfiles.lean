-- Prove2me | solution 1 for OAI.CubicEisenstein.completedBesselProfile_eq_finite_cuspProfiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:00:36.188896+00:00
-- url     : https://prove2.me/submissions/9dadacb3-3620-4ba3-9450-5bb74c37ce40

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
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

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

end SubexponentialBesselCoefficients

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

local instance instFintypeUnitsO_3_rb5e7f5_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FullFrequencyExpansion
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
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem completedBesselProfile_eq_finite_cuspProfiles_oai
    (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (d:(Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd:∀h,(d h).point=thetaFourierTranslation c h) (v:ℝ) (hv:0<v) :
    completedBesselProfile Ψ thetaBesselScale v=
      ∑h:Eis⧸Ideal.span {c},
        (thetaDerivativeScalar⁻¹*
          finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h)*
        cuspBarProfile cubicSourceConjugateFunction (d h).point v := by
  calc
    _=thetaDerivativeScalar⁻¹*thetaTwistedCuspProfile Ψ c hc v:=by
      rw [thetaTwistedCuspProfile_eq_completedBesselProfile Ψ Q hperiod c hc hcQ v hv,
        ←mul_assoc,inv_mul_cancel₀ thetaDerivativeScalar_ne_zero,one_mul]
    _=_:=by
      simp only [thetaTwistedCuspProfile,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [hd h]
      ring

end

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end

open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

theorem solution : type_of% @OAI.CubicEisenstein.completedBesselProfile_eq_finite_cuspProfiles_oai := @OAI.CubicEisenstein.completedBesselProfile_eq_finite_cuspProfiles_oai
