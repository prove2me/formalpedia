-- Prove2me | solution 1 for OAI.SevenEighths.InverseReflectedPhase.original_low_member_geometry_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:13:40.405595+00:00
-- url     : https://prove2.me/submissions/60294874-c7c3-4e7d-bba2-b6dd38d70369

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_original_low_sector_full_budget

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

theorem primaryGenerator_norm (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    ‖eisEmbedding (primaryGenerator I)‖ = Real.sqrt (Ideal.absNorm I : ℝ) := by
  rw [← primaryGenerator_norm_sq I hI, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
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

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter

open scoped BigOperators Classical

namespace DescentWeightedCauchy

theorem weighted_cauchy_sq {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ^ 2 ≤
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have hnorm : ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      ∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖ := by
    simpa only [norm_mul, norm_star] using
      norm_sum_le s (fun i => w i * U i * star (V i))
  calc
    _ ≤ (∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => by positivity)) |>.mpr hnorm
    _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i _ => by positivity) (fun i _ => by positivity)
      (fun i _ => by ring_nf; exact le_rfl)

end DescentWeightedCauchy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ResidualCuspDecay
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

namespace ShortDraftCusp

open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_ramified_fixed_factor_congr (M c0 u a a0 b b0 : Eis)
    (h9M : (9:Eis)∣M) (hcM : c0∣M) (huM : u∣M)
    (ha : lambda^2∣a-1) (ha0 : lambda^2∣a0-1)
    (hA : lambda^2∣a-u*b-1) (hA0 : lambda^2∣a0-u*b0-1)
    (hma : M∣a-a0) (hmb : M∣b-b0) :
    symbol (-u) (a-u*b)*symbol c0 a=
      symbol (-u) (a0-u*b0)*symbol c0 a0 := by
  have hdiff : M∣(a-u*b)-(a0-u*b0) := by
    convert (preTransparency := .instances) dvd_sub hma (dvd_mul_of_dvd_right hmb u) using 1 ; ring
  have hfirst : symbol (-u) (a-u*b)=symbol (-u) (a0-u*b0) := by
    apply symbol_denominator_congr _ _ _ hA hA0 (h9M.trans hdiff)
    exact neg_dvd.mpr (huM.trans hdiff)
  have hsecond := symbol_denominator_congr c0 a a0 ha ha0 (h9M.trans hma) (hcM.trans hma)
  rw [hfirst,hsecond]

theorem A3_unramified_fixed_factor_congr (M c0 a a0 : Eis)
    (hcM : c0∣M) (hma : M∣a-a0) : symbol a c0=symbol a0 c0 :=
  symbol_congr (hcM.trans hma)

theorem norm_embedded_cubic_symbol (x a : Eis)
    (ha : lambda^2∣a-1) (hcop : IsCoprime x a) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol x a)‖=1 := by
  have hcube : ConcreteTraceCRT.eisEmbedding (symbol x a)^3=1 := by
    rw [←map_pow,symbol_cube_of_isCoprime x a ha hcop,map_one]
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm hcube

theorem norm_A3_ramified_fixed_factor (a b c0 r d u : Eis)
    (hdet : a*d-b*(u*(c0*r))=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣a-u*b-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b)*symbol c0 a)‖=1 := by
  have hfirst : ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b))‖=1 := by
    apply norm_embedded_cubic_symbol _ _ hA
    refine ⟨b*(c0*r-d),d,?_⟩
    linear_combination hdet
  have hsecond : ‖ConcreteTraceCRT.eisEmbedding (symbol c0 a)‖=1 := by
    apply norm_embedded_cubic_symbol _ _ ha
    refine ⟨-b*u*r,d,?_⟩
    linear_combination hdet
  rw [map_mul,norm_mul,hfirst,hsecond,one_mul]

theorem norm_A3_unramified_fixed_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (hc : lambda^2∣c0-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol a c0)‖=1 := by
  apply norm_embedded_cubic_symbol _ _ hc
  refine ⟨d,-b*r,?_⟩
  linear_combination hdet

end ShortDraftCusp

open scoped BigOperators Classical

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

open scoped BigOperators Classical

namespace ShortDraftCRT
variable {R : Type*} [CommRing R]

theorem inverse_residue_congr (D r r0 u u0 : R) (hcop : IsCoprime D r)
    (hr : D∣r-r0) (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) : D∣u-u0 := by
  apply hcop.dvd_of_dvd_mul_right
  have hh := dvd_sub (dvd_sub hu hu0) (dvd_mul_of_dvd_right hr u0)
  convert (preTransparency := .instances) hh using 1 ; ring

theorem inverse_weight_residue_congr (D r r0 u u0 d d0 : R)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    D∣(-d*u)-(-d0*u0) := by
  have hi := inverse_residue_congr D r r0 u u0 hcop hr hu hu0
  have hh := dvd_add (dvd_mul_of_dvd_left hd u) (dvd_mul_of_dvd_right hi d0)
  convert (preTransparency := .instances) dvd_neg.mpr hh using 1 ; ring

end ShortDraftCRT

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedCuspArrays
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

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedCuspCoefficientBound_pos : 0<fixedCuspCoefficientBound :=
  (Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).1

lemma fixedCuspArrayWeight_pos (m:ℕ) (J:Ideal Eis) (hJ:primaryGenerator J≠0) :
    0<fixedCuspArrayWeight m J := by
  rw [fixedCuspArrayWeight,←primaryGenerator_norm J hJ]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))

lemma sourceCuspCoefficients_squarefree_cube_bound (j:Fin 3) (u:Eisˣ) (m:ℕ)
    (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J) :
    ‖(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)‖≤
      fixedCuspCoefficientBound*fixedCuspArrayWeight m J := by
  rcases helig with ⟨hsq,hI,hJ⟩
  have hb:=(Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).2
    I J hI hJ hsq u m
  rw [primaryGenerator_norm J hJ] at hb
  fin_cases j
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.1
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 false
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 true

lemma fixedCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedCuspArray j u m I J‖≤1 := by
  by_cases h:fixedCuspArrayEligible I J
  · have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
    rw [fixedCuspArray,if_pos h,norm_div,Complex.norm_real,Real.norm_of_nonneg hpos.le]
    exact (div_le_one hpos).mpr (sourceCuspCoefficients_squarefree_cube_bound j u m I J h)
  · simp only [fixedCuspArray,if_neg h,norm_zero,zero_le_one]

lemma fixedConjugateCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedConjugateCuspArray j u m I J‖≤1 := by
  simpa only [fixedConjugateCuspArray,norm_star] using fixedCuspArray_norm_le_one j u m I J

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.WeylRepresentatives
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
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFrequencyAngle_norm (h:Eis) (hh:h≠0) : ‖sourceFrequencyAngle h‖=1 := by
  rw [sourceFrequencyAngle,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))

end

open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped Classical BigOperators

open scoped BigOperators Classical Matrix MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.ResiduePhases
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

open scoped Classical BigOperators

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4BadPhase_as_fixed_residue (c0:Eis) (hc0:c0≠0) (d U:Eis) :
    A4BadPhase c0 hc0 d U=
      A4PhaseFromResidue c0 hc0 (Ideal.Quotient.mk _ (-d*U)) := by
  funext x
  simp only [A4BadPhase,A4PhaseFromResidue,map_mul]

end ShortDraftCusp

open scoped Classical BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.FixedCuspBranches
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

open scoped BigOperators Classical ContDiff

namespace CompletedGauss

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedCuspArrayWithPhase_norm_le_one (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖fixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 := by
  rw [fixedCuspArrayWithPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m n b)).trans (fixedConjugateCuspArray_norm_le_one cusp u m n b)

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases
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

section
open scoped BigOperators Classical MatrixGroups

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4PhaseFromResidue_norm (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) :
    ‖A4PhaseFromResidue c0 hc0 v x‖=1 := by
  let:Finite (Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}):=
    finite_quotient_span (A4_bad_modulus_ne_zero c0 hc0)
  unfold A4PhaseFromResidue
  exact AddChar.norm_apply _ _
end ShortDraftCusp

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss ShortDraftCusp ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFrequencyAngle_norm_le_one (h:Eis) : ‖sourceFrequencyAngle h‖≤1 := by
  by_cases hh:h=0
  · simp only [hh,sourceFrequencyAngle,map_zero,norm_zero,Complex.ofReal_zero,div_zero]
    norm_num
  · exact (sourceFrequencyAngle_norm h hh).le

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma reflectionStaticPhase_norm_le_one (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) : ‖s.reflectionStaticPhase c0 hc0 v dualNumerator u m I J‖≤1 := by
  simp only [reflectionStaticPhase,norm_mul,breveE_norm,A4PhaseFromResidue_norm,mul_one]
  exact sourceFrequencyAngle_norm_le_one _

lemma fixedCuspArrayWithPhase_reflectionStaticPhase (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) :
    fixedCuspArrayWithPhase s.index u (s.reflectionStaticPhase c0 hc0 v dualNumerator u) m I J=
      s.amplitude u m I J*A4PhaseFromResidue c0 hc0 v (dualNumerator m I J) := by
  unfold fixedCuspArrayWithPhase reflectionStaticPhase amplitude
  ring

end FixedCuspShape
end CubicEisenstein
end

open scoped Classical BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A3_ramified_relative_primary (M:SL(2,Eis)) (u:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    lambda^2∣(M 0 0-u*M 0 1)-1 := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  exact hA

end ShortDraftCusp

namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma determinant (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v 0 0*D.matrix v 1 1-D.matrix v 0 1*(c0*∏i,p i)=1 := by
  simpa only [Matrix.det_fin_two,D.denominator] using (D.matrix v).property

end ControlledStratumArithmetic
end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedFrequencyExpansion
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
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

theorem fixedFactor_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1) : ‖D.fixedFactor‖=1 := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact norm_A3_unramified_fixed_factor _ _ _ _ _ (D.determinant (fun _=>1)) hbase
  · apply norm_A3_ramified_fixed_factor _ _ 1 (∏i,p i) _ c0
    · simpa only [one_mul] using D.determinant (fun _=>1)
    · exact D.numerator_primary h3N hr hbase (fun _=>1)
    · exact A3_ramified_relative_primary (D.matrix (fun _=>1)) c0
        (D.ramified_relative h3N hr hbase c0 (by simp) (fun _=>1))

end ControlledStratumArithmetic
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SlotProducts
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem slotProductCoefficient_at_product
    (tuples : Finset (ι → Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)))
    (a : (ι → Ideal Eis) → ℂ) (p : ι → Ideal Eis) (hp : p ∈ tuples) :
    slotProductCoefficient tuples a (slotTupleProduct p) = a p := by
  unfold slotProductCoefficient
  rw [Finset.sum_eq_single p]
  · simp
  · intro q hq hqp
    exact if_neg (fun he => hqp (hinj hq hp he))
  · exact fun hn => (hn hp).elim

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Sector
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem separate_product_congruence {A : Type*} [CommRing A]
    (M f r r₀ P P₀ : A) (hr : M^2 ∣ r-r₀) (hP : M^2 ∣ P-P₀) :
    M^2 ∣ f*r*P-f*r₀*P₀ := by
  have h := dvd_add (dvd_mul_of_dvd_left hr P) (dvd_mul_of_dvd_right hP r₀)
  convert (preTransparency := .instances) dvd_mul_of_dvd_right h f using 1 ; ring

theorem separateSector_product (M f r r₀ P P₀ : Eis)
    (h : separateSector M r P = separateSector M r₀ P₀) :
    M^2 ∣ f*r*P-f*r₀*P₀ := by
  apply separate_product_congruence
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Prod.fst h))
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Prod.snd h))

theorem controlled_bad_phase_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} {p₀ : κ → Eis} {N a c : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode) (hc : c ≠ 0)
    (hbad : ramifiedTraceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, p₀ i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1 - D₀.matrix (fun _ => 1) 1 1) :
    ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U =
      ShortDraftCusp.A4BadPhase c hc (D₀.matrix (fun _ => 1) 1 1) D₀.U := by
  have hu : ramifiedTraceLambda^3*c ∣ D.U*(∏ i, p i)-1 := by
    refine ⟨-D.w, ?_⟩
    linear_combination D.bezout
  have hu₀ : ramifiedTraceLambda^3*c ∣ D₀.U*(∏ i, p₀ i)-1 := by
    refine ⟨-D₀.w, ?_⟩
    linear_combination D₀.bezout
  have hcop : IsCoprime (ramifiedTraceLambda^3*c) (∏ i, p i) := by
    refine ⟨D.w,D.U,?_⟩
    linear_combination D.bezout
  have he := ShortDraftCRT.inverse_weight_residue_congr
    (ramifiedTraceLambda^3*c) (∏ i, p i) (∏ i, p₀ i) D.U D₀.U
    (D.matrix (fun _ => 1) 1 1) (D₀.matrix (fun _ => 1) 1 1)
    hcop (hbad.trans hr) hu hu₀ (hbad.trans hd)
  rw [ShortDraftCusp.A4BadPhase_as_fixed_residue, ShortDraftCusp.A4BadPhase_as_fixed_residue]
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr he)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Static
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss ShortDraftCusp
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {p : ι → Eis} {p₀ : κ → Eis} {N a c : Eis} {mode : Bool}

theorem controlled_fixedFactor_eq
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode)
    (hN : (9:Eis)*c ∣ N)
    (hr : λ₀^2 ∣ (∏ i, p i)-1) (hr₀ : λ₀^2 ∣ (∏ i, p₀ i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (ha : N ∣ D.matrix (fun _ => 1) 0 0 - D₀.matrix (fun _ => 1) 0 0)
    (hb : N ∣ D.matrix (fun _ => 1) 0 1 - D₀.matrix (fun _ => 1) 0 1) :
    D.fixedFactor = D₀.fixedFactor := by
  have h9N : (9:Eis) ∣ N := (dvd_mul_right 9 c).trans hN
  have hcN : c ∣ N := (dvd_mul_left c 9).trans hN
  have h3N : (3:Eis) ∣ N := (show (3:Eis) ∣ 9 from ⟨3,by norm_num⟩).trans h9N
  cases mode
  · exact congrArg eisEmbedding (A3_unramified_fixed_factor_congr N c _ _ hcN ha)
  · apply congrArg eisEmbedding
    exact A3_ramified_fixed_factor_congr N 1 c _ _ _ _ h9N (one_dvd _) hcN
      (D.numerator_primary h3N hr hbase _) (D₀.numerator_primary h3N hr₀ hbase _)
      (A3_ramified_relative_primary _ c (D.ramified_relative h3N hr hbase c (by simp) _))
      (A3_ramified_relative_primary _ c (D₀.ramified_relative h3N hr₀ hbase c (by simp) _)) ha hb

theorem controlled_static_array_eq
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode) (hc : c ≠ 0)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hbad : ramifiedTraceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, p₀ i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1 - D₀.matrix (fun _ => 1) 1 1)
    (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
        (s.modelDualNumerator u) u) m I J =
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D₀.matrix (fun _ => 1) 1 1)*D₀.U))
        (s.modelDualNumerator u) u) m I J := by
  rw [s.fixedCuspArrayWithPhase_reflectionStaticPhase, s.fixedCuspArrayWithPhase_reflectionStaticPhase]
  have he := congrFun (controlled_bad_phase_eq D D₀ hc hbad hr hd) (s.modelDualNumerator u m I J)
  rw [A4BadPhase_as_fixed_residue,A4BadPhase_as_fixed_residue] at he
  rw [he]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Family
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators MatrixGroups
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase ShortDraftCRT CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem simultaneous_controlled_matrices_dependent {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:Eis) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ mat : ∀ x, (∀ i, (Eis ⧸ Ideal.span {p x i})ˣ) → SL(2,Eis),
      (∀ x v, mat x v 0 0 = (D x).matrix v 0 0) ∧
      (∀ x v, mat x v 1 0 = c*∏ i, p x i) ∧
      (∀ x v, if mode then (9:Eis) ∣ mat x v 0 1 ∧ (3:Eis) ∣ mat x v 1 1-1
        else (3:Eis) ∣ mat x v 0 1+1 ∧ (9:Eis) ∣ mat x v 1 1) ∧
      ∀ x y v w, sector x = sector y → ∀ i j, N ∣ mat x v i j-mat y w i j := by
  let X := Σ x : α, (∀ i, (Eis ⧸ Ideal.span {p x i})ˣ)
  let aa : X → Eis := fun x => (D x.1).matrix x.2 0 0
  let rr : X → Eis := fun x => ∏ i, p x.1 i
  let ss : X → Q := fun x => sector x.1
  have h3N : (3:Eis) ∣ N := (show (3:Eis) ∣ 9 from ⟨3,by norm_num⟩).trans h9N
  have hacop (x : X) : IsCoprime (aa x) (c*rr x) := by
    refine ⟨(D x.1).matrix x.2 1 1, -(D x.1).matrix x.2 0 1, ?_⟩
    have hd := ((D x.1).matrix x.2).property
    rw [Matrix.det_fin_two] at hd
    change (D x.1).matrix x.2 0 0 * (D x.1).matrix x.2 1 1 -
      (D x.1).matrix x.2 0 1 * (D x.1).matrix x.2 1 0 = 1 at hd
    rw [(D x.1).denominator] at hd
    dsimp [aa,rr]
    linear_combination hd
  have haa (x y : X) (h : ss x = ss y) : N*c ∣ aa x-aa y := by
    dsimp [aa]
    rw [(D x.1).numerator,(D y.1).numerator]
    exact finiteCrossNumerator_fixed_sector N a c ramifiedTraceLambda
      (p x.1) ((D x.1).lift x.2) (p y.1) ((D y.1).lift y.2)
      hcN ((D x.1).lift_period x.2) ((D y.1).lift_period y.2) (hsector x.1 y.1 h)
  have hrr (x y : X) (h : ss x = ss y) : N ∣ rr x-rr y :=
    (dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x.1 y.1 h)
  have hex : ∃ (b d : X → Eis) (C : Q → Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {N})),
      (∀ x, aa x*d x-b x*(c*rr x)=1) ∧
      (∀ x, if mode then (9:Eis) ∣ b x ∧ (3:Eis) ∣ d x-1
        else (3:Eis) ∣ b x+1 ∧ (9:Eis) ∣ d x) ∧
      ∀ x, (!![aa x,b x;c*rr x,d x] : Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {N})) = C (ss x) := by
    cases mode
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩ := exists_primary_denominator_sector_completions
        N c h9N hbase ss aa rr (fun x => hprimary x.1) hacop
        (fun x => hcop x.1) haa hrr
      exact ⟨b,d,C,hd,fun x => ⟨hb x,hz x⟩,hm⟩
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩ := exists_primary_numerator_sector_completions
        N c hc h9N ss aa rr
        (fun x => (D x.1).numerator_primary h3N (hprimary x.1) hbase x.2)
        (fun x => hprimary x.1) hacop (fun x => hcop x.1) haa hrr
      exact ⟨b,d,C,hd,fun x => ⟨hb x,hz x⟩,hm⟩
  obtain ⟨b,d,C,hdet,hcond,hmat⟩ := hex
  let mat := fun (x : α) (v : ∀ i, (Eis ⧸ Ideal.span {p x i})ˣ) =>
    controlledCompletionMatrix (aa ⟨x,v⟩) (b ⟨x,v⟩) (c*rr ⟨x,v⟩) (d ⟨x,v⟩) (hdet ⟨x,v⟩)
  refine ⟨mat,fun _ _ => rfl,fun _ _ => rfl,fun x v => hcond ⟨x,v⟩,?_⟩
  intro x y v w hs i j
  have hs' : ss ⟨x,v⟩ = ss ⟨y,w⟩ := hs
  have he := (hmat ⟨x,v⟩).trans ((congrArg C hs').trans (hmat ⟨y,w⟩).symm)
  have he' := congrArg (fun T : Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {N}) => T i j) he
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he')

theorem exists_sector_controlled_arithmetic_dependent {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:Eis) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∀ x y v w, sector x = sector y → ∀ i j,
        N ∣ (E x).matrix v i j-(E y).matrix w i j := by
  obtain ⟨mat,ha,hr,hcond,hfixed⟩ := simultaneous_controlled_matrices_dependent
    p N a c mode D hc h9N hcN hprimary hbase hcop sector hsector
  let E : ∀ x, ControlledStratumArithmetic (p x) N a c mode := fun x =>
    { D x with
      matrix := mat x
      numerator := fun v => (ha x v).trans ((D x).numerator v)
      denominator := hr x
      matrix_fixed := fun v i j => hfixed x x v (fun _ => 1) rfl i j
      conditions := hcond x }
  exact ⟨E,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,hfixed⟩

theorem exists_sector_templates {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i))
    (hmatrix : ∀ x y, sector x = sector y → ∀ i j,
      N ∣ (D x).matrix (fun _ => 1) i j-(D y).matrix (fun _ => 1) i j) :
    ∃ (κ : Q → ℂ) (β : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
      (∀ x, (D x).fixedFactor = κ (sector x)) ∧
      ∀ x u m n b,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c hc
            (Ideal.Quotient.mk _ (-((D x).matrix (fun _ => 1) 1 1)*(D x).U))
            (s.modelDualNumerator u) u) m n b = β (sector x) u m n b := by
  have hbad : ramifiedTraceLambda^3*c ∣ N := by
    apply (show ramifiedTraceLambda^3*c ∣ (9:Eis)*c from ?_).trans hN
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [← A4_traceLambda_pow_four]
    ring
  let A := fun x (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) =>
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc
        (Ideal.Quotient.mk _ (-((D x).matrix (fun _ => 1) 1 1)*(D x).U))
        (s.modelDualNumerator u) u) m n b
  have hf : (fun x => (D x).fixedFactor).FactorsThrough sector := by
    intro x y hxy
    exact controlled_fixedFactor_eq (D x) (D y) hN (hprimary x) (hprimary y) hbase
      (hmatrix x y hxy 0 0) (hmatrix x y hxy 0 1)
  have ha : A.FactorsThrough sector := by
    intro x y hxy
    funext u m n b
    exact controlled_static_array_eq (D x) (D y) hc s hbad
      ((dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x y hxy))
      (hmatrix x y hxy 1 1) u m n b
  obtain ⟨κ,hκ⟩ := (Function.factorsThrough_iff _).mp hf
  obtain ⟨β,hβ⟩ := (Function.factorsThrough_iff A).mp ha
  refine ⟨κ,β,fun x => congrFun hκ x,?_⟩
  intro x u m n b
  exact congrFun (congrFun (congrFun (congrFun (congrFun hβ x) u) m) n) b

theorem exists_separate_ray_templates {α : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (f : Eis) (r P : α → Eis) (hprod : ∀ x, (∏ i, p x i) = f*r x*P x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x, (E x).fixedFactor = κ (separateSector N (r x) (P x))) ∧
        ∀ x u m n b,
          fixedCuspArrayWithPhase s.index u
            (s.reflectionStaticPhase c hc
              (Ideal.Quotient.mk _ (-((E x).matrix (fun _ => 1) 1 1)*(E x).U))
              (s.modelDualNumerator u) u) m n b = β (separateSector N (r x) (P x)) u m n b := by
  let sector := fun x => separateSector N (r x) (P x)
  have hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i) := by
    intro x y hxy
    rw [hprod x,hprod y]
    exact separateSector_product N f (r x) (r y) (P x) (P y) hxy
  obtain ⟨E,hlift,hU,hσ,hε,hmat⟩ := exists_sector_controlled_arithmetic_dependent p N a c mode D
    hc ((dvd_mul_right 9 c).trans hN) ((dvd_mul_left c 9).trans hN)
    hprimary hbase hcop sector hsector
  refine ⟨E,hlift,hU,hσ,hε,?_⟩
  exact exists_sector_templates p N a c mode E s hc hN hprimary hbase sector hsector
    (fun x y hxy => hmat x y (fun _ => 1) (fun _ => 1) hxy)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Canonical
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι : Type*} (G : PrimeFamily ι)

lemma generator_product [Fintype ι] :
    (∏ i, G.generator i) = primaryGenerator (∏ i, G.ideal i) := by
  change _ = primaryGeneratorHom (∏ i, G.ideal i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact primaryPrime_eq_primaryGenerator (G.ideal i)

lemma generator_product_coprime_period [Fintype ι] (N c : Eis) (hc : c ∣ N)
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    IsCoprime (∏ i, G.generator i) (N*c) := by
  have hh : IsCoprime N (∏ i, G.generator i) :=
    IsCoprime.prod_right (fun i _ => G.generator_coprime_period N hN i)
  exact hh.symm.mul_right (hh.symm.of_isCoprime_of_dvd_right hc)

end PrimeFamily

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Rows
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι κ : Type*}

lemma sum_product [Fintype ι] [Fintype κ] (G : PrimeFamily ι) (H : PrimeFamily κ) :
    (∏ i, (G.sum H).ideal i) = (∏ i, G.ideal i)*(∏ i, H.ideal i) := by
  simp only [sum,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]

lemma sum_pairwise (G : PrimeFamily ι) (H : PrimeFamily κ)
    (hG : Pairwise (Function.onFun IsCoprime G.ideal))
    (hH : Pairwise (Function.onFun IsCoprime H.ideal))
    (hcross : ∀ i k, IsCoprime (G.ideal i) (H.ideal k)) :
    Pairwise (Function.onFun IsCoprime (G.sum H).ideal) := by
  intro i k hik
  cases i with
  | inl i => cases k with
    | inl k => exact hG (fun h => hik (congrArg Sum.inl h))
    | inr k => exact hcross i k
  | inr i => cases k with
    | inl k => exact (hcross k i).symm
    | inr k => exact hH (fun h => hik (congrArg Sum.inr h))

lemma residual_pairwise (K : Ideal Eis) (hK : Admissible K) :
    Pairwise (Function.onFun IsCoprime (residual K hK).ideal) := by
  intro P Q hPQ
  apply Ideal.isCoprime_of_isMaximal
  intro h
  exact hPQ (Subtype.ext h)

lemma reflected_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i, (F.reflected K hK S).ideal i) = (∏ i, F.ideal i)*K*(∏ i, S.ideal i) := by
  rw [reflected,sum_product,sum_product,residual_product]
  ring

lemma reflected_pairwise {φ σ : Type*} [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hKS : IsCoprime K (∏ i, S.ideal i))
    (hFK : ∀ f, IsCoprime (F.ideal f) K)
    (hFS : ∀ f i, IsCoprime (F.ideal f) (S.ideal i)) :
    Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal) := by
  apply sum_pairwise F _ hF
  · apply sum_pairwise _ S (residual_pairwise K hK) hS
    intro P i
    exact (hKS.of_isCoprime_of_dvd_left (residual_dvd K hK P)).of_isCoprime_of_dvd_right
      (Finset.dvd_prod_of_mem S.ideal (Finset.mem_univ i))
  · intro f i
    cases i with
    | inl P => exact (hFK f).of_isCoprime_of_dvd_right (residual_dvd K hK P)
    | inr i => exact hFS f i

lemma reflected_period {φ σ : Type*}
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (N : Eis)
    (hF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hK' : IsCoprime (Ideal.span {N}) K)
    (hS : ∀ i, IsCoprime (Ideal.span {N}) (S.ideal i)) :
    ∀ i, IsCoprime (Ideal.span {N}) ((F.reflected K hK S).ideal i) := by
  intro i
  cases i with
  | inl f => exact hF f
  | inr i => cases i with
    | inl P => exact hK'.of_isCoprime_of_dvd_right (residual_dvd K hK P)
    | inr i => exact hS i

end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Columns
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι φ σ : Type*} [Fintype ι] [Fintype φ] [Fintype σ]
variable {p : ι → Eis} {N a c : Eis} {mode : Bool}

lemma actualCuspColumn_norm_le_one (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ‖actualCuspColumn D s hc u m n b‖ ≤ 1 :=
  fixedCuspArrayWithPhase_norm_le_one s.index u _
    (s.reflectionStaticPhase_norm_le_one c hc _ _ u) m n b

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.BoundedTemplates
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma boundedExtension_norm (z : ℂ) : ‖boundedExtension z‖ ≤ 1 := by
  unfold boundedExtension
  split_ifs with h
  · exact h
  · simp
lemma boundedExtension_eq (z : ℂ) (hz : ‖z‖ ≤ 1) : boundedExtension z = z := if_pos hz

theorem canonical_bounded_cusp_templates {α : Type*} {ι : α → Type*}
    [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : ∀ x, Pairwise (Function.onFun IsCoprime (G x).ideal))
    (hNp : ∀ x i, IsCoprime (Ideal.span {N}) ((G x).ideal i))
    (fixedIdeal : Ideal Eis) (row slot : α → Ideal Eis)
    (hprod : ∀ x, (∏ i, (G x).ideal i) = fixedIdeal*row x*slot x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode,
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (A : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ q, ‖κ q‖ ≤ 1) ∧ (∀ q u m n b, ‖A q u m n b‖ ≤ 1) ∧
        (∀ x, (E x).fixedFactor = κ (separateSector N (primaryGenerator (row x))
          (primaryGenerator (slot x)))) ∧
        ∀ x u m n b, actualCuspColumn (E x) s hc u m n b =
          A (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m n b := by
  let D : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode := fun x =>
    Classical.choice ((G x).exists_controlled N a c mode hc hN hbase hac (hcop x) (hNp x))
  have hproduct (x : α) : (∏ i, (G x).generator i) =
      primaryGenerator fixedIdeal*primaryGenerator (row x)*primaryGenerator (slot x) := by
    rw [(G x).generator_product,hprod x,primaryGenerator_mul,primaryGenerator_mul]
  obtain ⟨E,_,_,_,_,κ,A,hκ,hA⟩ := exists_separate_ray_templates
    (fun x => (G x).generator) N a c mode D s hc hN
    (fun x => (G x).generator_product_primary) hbase
    (fun x => (G x).generator_product_coprime_period N c ((dvd_mul_left c 9).trans hN) (hNp x))
    (primaryGenerator fixedIdeal) (fun x => primaryGenerator (row x))
    (fun x => primaryGenerator (slot x)) hproduct
  refine ⟨E,fun q => boundedExtension (κ q),fun q u m n b => boundedExtension (A q u m n b),
    fun q => boundedExtension_norm _,fun q u m n b => boundedExtension_norm _,?_,?_⟩
  · intro x
    change (E x).fixedFactor = boundedExtension _
    rw [← hκ x,boundedExtension_eq _ ((E x).fixedFactor_norm hN
      (G x).generator_product_primary hbase).le]
  · intro x u m n b
    change actualCuspColumn (E x) s hc u m n b = boundedExtension _
    rw [← hA x u m n b]
    exact (boundedExtension_eq _ (actualCuspColumn_norm_le_one (E x) s hc u m n b)).symm

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.SourceFamily
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

variable {φ σ : Type*} [Fintype φ] [Fintype σ]

theorem exists_source_pair_templates (F : PrimeFamily φ)
    (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis → PrimeFamily σ)
    (hrows : ∀ K ∈ rows, Admissible K)
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hScop : ∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((S P).ideal i)) :
    ∃ E : ∀ x : SourcePair rows Pset,
      ControlledStratumArithmetic
        (F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)).generator N a c mode,
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (A : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ q, ‖κ q‖ ≤ 1) ∧ (∀ q u m n b, ‖A q u m n b‖ ≤ 1) ∧
        (∀ x, (E x).fixedFactor = κ (separateSector N (primaryGenerator x.val.1.val)
          (primaryGenerator x.val.2.val))) ∧
        ∀ x u m n b, actualCuspColumn (E x) s hc u m n b =
          A (separateSector N (primaryGenerator x.val.1.val) (primaryGenerator x.val.2.val)) u m n b := by
  let G := fun x : SourcePair rows Pset =>
    F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)
  have hpair (x : SourcePair rows Pset) : Pairwise (Function.onFun IsCoprime (G x).ideal) := by
    apply F.reflected_pairwise x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val) hF
    · intro i k hik
      change IsCoprime ((F.sum (S x.val.2.val)).ideal (Sum.inr i))
        ((F.sum (S x.val.2.val)).ideal (Sum.inr k))
      exact hScop x.val.2.val x.val.2.property (Sum.inr_injective.ne hik)
    · rw [hprod _ x.val.2.property]
      exact x.property
    · exact (hrowcop _ x.val.1.property).1
    · intro f i
      change IsCoprime ((F.sum (S x.val.2.val)).ideal (Sum.inl f))
        ((F.sum (S x.val.2.val)).ideal (Sum.inr i))
      exact hScop x.val.2.val x.val.2.property (Sum.inl_ne_inr : (Sum.inl f : φ ⊕ σ) ≠ Sum.inr i)
  have hNp (x : SourcePair rows Pset) : ∀ i, IsCoprime (Ideal.span {N}) ((G x).ideal i) :=
    F.reflected_period _ _ _ N hNF (hrowcop _ x.val.1.property).2 (hSN _ x.val.2.property)
  apply canonical_bounded_cusp_templates G N a c mode s hc hN hbase hac hpair hNp
    (∏ i, F.ideal i) (fun x => x.val.1.val) (fun x => x.val.2.val)
  intro x
  rw [PrimeFamily.reflected_product,hprod _ x.val.2.property]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.OriginalTransport
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma mixedReflectedValue_cast {ι : Type*} [Fintype ι] {p q : ι→Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ i, q i≠0) (hc : c≠0)
    (hgp : ∀ i, λ₀∉Ideal.span {p i}) (hgq : ∀ i, λ₀∉Ideal.span {q i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (castControlled h D) s hq hc hgq j S W X=
      mixedReflectedValue D s hp hc hgp j S W X := by
  subst q
  rfl

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "PS" => PrimeFamily.restrict (PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S) (markedActiveSet E B T)
local notation "PF" => PrimeFamily.reflected (PrimeFamily.restrict (poolPrimeFamily R (Ideal.span (Set.singleton m)*F) Q₀) B) K hK (S.restrict T)
local notation "EA" => markedActiveEquiv E B T

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma weighted_finite_row_energy {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤
      (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*(∑ k∈rows, ‖f i k‖^2) := by
  calc
    _ ≤ ∑ k∈rows, (∑ i∈L, ‖w i‖*‖f i k‖^2)*(∑ i∈L, ‖w i‖) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [star_one,mul_one,norm_one,one_pow] using
        DescentWeightedCauchy.weighted_cauchy_sq L w (fun i => f i k) (fun _ => 1)
    _ = _ := by
      rw [← Finset.sum_mul,Finset.sum_comm]
      simp only [← Finset.mul_sum]
      ring

lemma weighted_finite_row_energy_uniform {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) (B : ℝ)
    (hf : ∀ i∈L, (∑ k∈rows, ‖f i k‖^2)≤B) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤(∑ i∈L, ‖w i‖)^2*B := by
  apply (weighted_finite_row_energy L rows w f).trans
  calc
    _ ≤ (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*B := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i hi => norm_nonneg _))
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hf i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.SectorAggregation
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma sum_fullRaySectors {M : Type*} [AddCommMonoid M] (N : Eis)
    [Fintype (Eis⧸Ideal.span {N^2})] (rows : Finset (Ideal Eis)) (f : Ideal Eis→M) :
    (∑ r : Eis⧸Ideal.span {N^2}, ∑ K∈fullRaySector N rows r,f K)=∑ K∈rows,f K :=
  Finset.sum_fiberwise rows (fun K => Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)) f

theorem full_ray_sector_energy (N : Eis) [Fintype (Eis⧸Ideal.span {N^2})]
    (rows Pset : Finset (Ideal Eis)) (f : Ideal Eis→Ideal Eis→ℂ) (E : ℝ)
    (hE : ∀ r p : Eis⧸Ideal.span {N^2},
      (∑ K∈fullRaySector N rows r, ‖∑ P∈fullRaySector N Pset p,f K P‖^2)≤E) :
    (∑ K∈rows,‖∑ P∈Pset,f K P‖^2)≤(Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^3*E := by
  rw [←sum_fullRaySectors N rows (fun K => ‖∑ P∈Pset,f K P‖^2)]
  calc
    _ ≤ ∑ r : Eis⧸Ideal.span {N^2}, (Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^2*E := by
      apply Finset.sum_le_sum
      intro r hr
      have hh := weighted_finite_row_energy_uniform (Finset.univ : Finset (Eis⧸Ideal.span {N^2}))
        (fullRaySector N rows r) (fun _ => (1:ℂ))
        (fun p K => ∑ P∈fullRaySector N Pset p,f K P) E (fun p _ => hE r p)
      simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
      have he : (∑ K∈fullRaySector N rows r, ‖∑ P∈Pset,f K P‖^2)=
          ∑ K∈fullRaySector N rows r, ‖∑ p : Eis⧸Ideal.span {N^2},∑ P∈fullRaySector N Pset p,f K P‖^2 := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [sum_fullRaySectors]
      rw [he]
      exact hh
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.SectorCover
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma sector_arithmetic_prescribed (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (hcommon : ∀ (x y : SourcePair rows Pset),
      (D x.val.1 x.val.2 x.property).fixedFactor=(D y.val.1 y.val.2 y.property).fixedFactor ∧
      ∀ u m n b,actualCuspColumn (D x.val.1 x.val.2 x.property) s hc u m n b=
        actualCuspColumn (D y.val.1 y.val.2 y.property) s hc u m n b)
    (D0 : ControlledStratumArithmetic F.generator N a c mode) :
    ∃ E : SectorArithmetic (N:=N) F rows Pset S hrows s hc,E.completion=D := by
  by_cases hn : Nonempty (SourcePair rows Pset)
  · let x0 : SourcePair rows Pset := Classical.choice hn
    exact ⟨{
      referenceIndex := φ⊕(PrimeIndex x0.val.1.val⊕σ)
      referencePrimes := F.reflected x0.val.1.val (hrows x0.val.1.val x0.val.1.property) (S x0.val.2.val)
      referenceArithmetic := D x0.val.1 x0.val.2 x0.property
      completion := D
      fixedFactor_eq := fun K P hp => (hcommon ⟨(K,P),hp⟩ x0).1
      cuspColumn_eq := fun K P hp => (hcommon ⟨(K,P),hp⟩ x0).2
    },rfl⟩
  · let F0 : PrimeFamily (ULift.{v} φ) := ⟨fun x => F.ideal x.down,fun x => F.maximal x.down,fun x => F.good x.down⟩
    let e : ULift.{v} φ ≃ φ := Equiv.ulift
    let D0' := reindexControlled D0 e
    exact ⟨{
      referenceIndex := ULift.{v} φ
      referencePrimes := F0
      referenceArithmetic := D0'
      completion := D
      fixedFactor_eq := fun K P hp => (hn ⟨⟨(K,P),hp⟩⟩).elim
      cuspColumn_eq := fun K P hp => (hn ⟨⟨(K,P),hp⟩⟩).elim
    },rfl⟩

theorem exists_global_sector_completion (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f,IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K∈rows,(∀ f,IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hprod : ∀ P∈Pset,(∏ i,(S P).ideal i)=P)
    (hScop : ∀ P∈Pset,Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P∈Pset,∀ i,IsCoprime (Ideal.span {N}) ((S P).ideal i)) :
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode,
    ∀ r p : Eis⧸Ideal.span {N^2},
    ∃ E : SectorArithmetic (N:=N) F (fullRaySector N rows r) (fullRaySector N Pset p) S
      (fun K hK => hrows K (Finset.mem_filter.mp hK).1) s hc,
    ∀ (K : fullRaySector N rows r) (P : fullRaySector N Pset p) hp,
      E.completion K P hp=D ⟨K.val,(Finset.mem_filter.mp K.property).1⟩
        ⟨P.val,(Finset.mem_filter.mp P.property).1⟩ hp := by
  obtain ⟨Dpair,κ,A,_,_,hκ,hA⟩ := exists_source_pair_templates F rows Pset S hrows hprod N a c mode s hc
    hN hbase hac hF hNF hrowcop hScop hSN
  let D := fun (K : rows) (P : Pset) (hp : IsCoprime K.val P.val) => Dpair ⟨(K,P),hp⟩
  refine ⟨D,?_⟩
  intro r p
  let Ds := fun (K : fullRaySector N rows r) (P : fullRaySector N Pset p) (hp : IsCoprime K.val P.val) =>
    D ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨P.val,(Finset.mem_filter.mp P.property).1⟩ hp
  have hh (x y : SourcePair (fullRaySector N rows r) (fullRaySector N Pset p)) :
      (Ds x.val.1 x.val.2 x.property).fixedFactor=(Ds y.val.1 y.val.2 y.property).fixedFactor ∧
      ∀ u m n b,actualCuspColumn (Ds x.val.1 x.val.2 x.property) s hc u m n b=
        actualCuspColumn (Ds y.val.1 y.val.2 y.property) s hc u m n b := by
    have hsector (x : SourcePair (fullRaySector N rows r) (fullRaySector N Pset p)) :
        separateSector N (primaryGenerator x.val.1.val) (primaryGenerator x.val.2.val)=(r,p) :=
      Prod.ext (Finset.mem_filter.mp x.val.1.property).2 (Finset.mem_filter.mp x.val.2.property).2
    let lift (z : SourcePair (fullRaySector N rows r) (fullRaySector N Pset p)) :
        SourcePair rows Pset :=
      ⟨(⟨z.val.1.val, (Finset.mem_filter.mp z.val.1.property).1⟩,
        ⟨z.val.2.val, (Finset.mem_filter.mp z.val.2.property).1⟩), z.property⟩
    constructor
    · dsimp only [Ds,D]
      exact (hκ (lift x)).trans ((congrArg κ ((hsector x).trans (hsector y).symm)).trans (hκ (lift y)).symm)
    · intro u m n b
      dsimp only [Ds,D]
      exact (hA (lift x) u m n b).trans
        ((congrArg (fun q => A q u m n b) ((hsector x).trans (hsector y).symm)).trans
          (hA (lift y) u m n b).symm)
  obtain ⟨D0⟩ := F.exists_controlled N a c mode hc hN hbase hac hF hNF
  obtain ⟨E,hE⟩ := sector_arithmetic_prescribed F (fullRaySector N rows r) (fullRaySector N Pset p) S
    (fun K hK => hrows K (Finset.mem_filter.mp hK).1) s hc Ds hh D0
  refine ⟨E,?_⟩
  intro K P hp
  rw [hE]
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.WholePair
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma sum_subtype_dite {α : Type*} [Fintype α] (p : α→Prop) (f : ∀ x,p x→ℂ) :
    (∑ x : {x // p x},f x.val x.property)=∑ x,if h:p x then f x h else 0 := by
  have hh := Fintype.sum_subtype_add_sum_subtype p (fun x => if h:p x then f x h else 0)
  have hz : (∑ x : {x // ¬p x},if h:p x.val then f x.val h else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dif_neg x.property
  rw [hz,add_zero] at hh
  simpa only [Subtype.property,dif_pos] using hh

lemma literalWholeRow_eq_pairs (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K : rows) :
    literalWholeRow F K.val (hrows K.val K.property) S jF Pset (D K) s hc W θ X r aw=
      ∑ P∈Pset,literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K.val P := by
  let f := fun (P : Pset) (hp : IsCoprime K.val P.val) => r K.val*aw P.val*
    mixedReflectedValue (D K P hp) s (F.reflected K.val (hrows K.val K.property) (S P.val)).generator_ne_zero hc
      (F.reflected K.val (hrows K.val K.property) (S P.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X
  change (∑ P : {P : Pset // IsCoprime K.val P.val},f P.val P.property)=_
  rw [sum_subtype_dite (fun P : Pset => IsCoprime K.val P.val) f,
    ←Finset.sum_coe_sort Pset (literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K.val)]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [literalPairEntry,dif_pos K.property,dif_pos P.property,f]

lemma literalPairEntry_restrict (F : PrimeFamily φ) (rows Pset rows' Pset' : Finset (Ideal Eis))
    (hrow : rows'⊆rows) (hP : Pset'⊆Pset) (S : Ideal Eis→PrimeFamily σ)
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (E : SectorArithmetic (N:=N) F rows' Pset' S (fun K hK => hrows K (hrow hK)) s hc)
    (hE : ∀ (K : rows') (P : Pset') hp,E.completion K P hp=D ⟨K.val,hrow K.property⟩ ⟨P.val,hP P.property⟩ hp)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K P : Ideal Eis) (hK : K∈rows') (hp : P∈Pset') :
    literalPairEntry F rows' Pset' S (fun K hK => hrows K (hrow hK)) jF E.completion s hc W θ X r aw K P=
      literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K P := by
  simp only [literalPairEntry,dif_pos hK,dif_pos hp,dif_pos (hrow hK),dif_pos (hP hp)]
  by_cases hcop : IsCoprime K P
  · simp only [dif_pos hcop,hE]
  · simp only [dif_neg hcop]
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.ActiveProducts
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma slotProductCoefficient_norm (tuples : Finset (σ→Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (aw : (σ→Ideal Eis)→ℂ) (haw : ∀ p∈tuples,‖aw p‖≤1)
    (P : Ideal Eis) (hP : P∈tuples.image slotTupleProduct) :
    ‖slotProductCoefficient tuples aw P‖≤1 := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
  rw [slotProductCoefficient_at_product tuples hinj aw p hp]
  exact haw p hp

theorem literalWholeRow_eq_active_tuples
    (F : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : tuples.image slotTupleProduct,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) (K : rows) :
    literalWholeRow F K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood)
      jF (tuples.image slotTupleProduct) (D K) s hc W θ X r (slotProductCoefficient tuples aw)=
    ∑ p : tuples,if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue
        (D K ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) X else 0 := by
  rw [literalWholeRow_eq_pairs F rows _ _ hrows jF D s hc W θ X r _ K,Finset.sum_image hinj]
  rw [←Finset.sum_coe_sort tuples]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [literalPairEntry,dif_pos K.property,
    dif_pos (Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩),
    slotProductCoefficient_at_product tuples hinj aw p.val p.property]
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.GlobalEnergy
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem literal_global_sector_energy [Fintype (Eis⧸Ideal.span {N^2})]
    (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (B : ℝ)
    (hsector : ∀ r₀ p₀ : Eis⧸Ideal.span {N^2},
      ∃ E : SectorArithmetic (N:=N) F (fullRaySector N rows r₀) (fullRaySector N Pset p₀) S
        (fun K hK => hrows K (fullRaySector_subset N rows r₀ hK)) s hc,
        (∀ (K : fullRaySector N rows r₀) (P : fullRaySector N Pset p₀) hp,
          E.completion K P hp=D ⟨K.val,(fullRaySector_subset N rows r₀ K.property)⟩
            ⟨P.val,(fullRaySector_subset N Pset p₀ P.property)⟩ hp) ∧
        (∑ K : fullRaySector N rows r₀,‖literalWholeRow F K.val
          (hrows K.val (fullRaySector_subset N rows r₀ K.property)) S jF (fullRaySector N Pset p₀)
          (E.completion K) s hc W θ X r aw‖^2)≤B) :
    (∑ K : rows,‖literalWholeRow F K.val (hrows K.val K.property) S jF Pset
      (D K) s hc W θ X r aw‖^2)≤(Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^3*B := by
  let f := literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw
  have hs (r₀ p₀ : Eis⧸Ideal.span {N^2}) :
      (∑ K∈fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,f K P‖^2)≤B := by
    obtain ⟨E,hE,hbound⟩ := hsector r₀ p₀
    have he : (∑ K : fullRaySector N rows r₀,‖literalWholeRow F K.val
          (hrows K.val (fullRaySector_subset N rows r₀ K.property)) S jF (fullRaySector N Pset p₀)
          (E.completion K) s hc W θ X r aw‖^2)=
        ∑ K∈fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,f K P‖^2 := by
      let fl := literalPairEntry F (fullRaySector N rows r₀) (fullRaySector N Pset p₀) S
        (fun K hK => hrows K (fullRaySector_subset N rows r₀ hK)) jF E.completion s hc W θ X r aw
      calc
        _ = ∑ K : fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,fl K.val P‖^2 := by
          apply Finset.sum_congr rfl
          intro K hK
          apply congrArg (fun z : ℂ => ‖z‖^2)
          exact literalWholeRow_eq_pairs F (fullRaySector N rows r₀) (fullRaySector N Pset p₀) S
            (fun K hK => hrows K (fullRaySector_subset N rows r₀ hK)) jF E.completion s hc W θ X r aw K
        _ = ∑ K∈fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,fl K P‖^2 :=
          Finset.sum_coe_sort _ (fun K => ‖∑ P∈fullRaySector N Pset p₀,fl K P‖^2)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro K hK
          apply congrArg (fun z : ℂ => ‖z‖^2)
          apply Finset.sum_congr rfl
          intro P hP
          exact literalPairEntry_restrict F rows Pset (fullRaySector N rows r₀) (fullRaySector N Pset p₀)
            (fullRaySector_subset N rows r₀) (fullRaySector_subset N Pset p₀) S hrows jF D s hc E hE W θ X r aw K P hK hP
    rw [←he]
    exact hbound
  have hh := full_ray_sector_energy N rows Pset f B hs
  have he : (∑ K : rows,‖literalWholeRow F K.val (hrows K.val K.property) S jF Pset
      (D K) s hc W θ X r aw‖^2)=∑ K∈rows,‖∑ P∈Pset,f K P‖^2 := by
    calc
      _ = ∑ K : rows,‖∑ P∈Pset,f K.val P‖^2 := by
        apply Finset.sum_congr rfl
        intro K hK
        exact congrArg (fun z : ℂ => ‖z‖^2) (literalWholeRow_eq_pairs F rows Pset S hrows jF D s hc W θ X r aw K)
      _ = _ := Finset.sum_coe_sort rows (fun K => ‖∑ P∈Pset,f K P‖^2)
  rw [he]
  exact hh
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.PoolArithmetic
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma poolPrimeFamily_pairwise (R Q Q₀ : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (poolPrimeFamily R Q Q₀).ideal) := by
  intro P T hPT
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPT)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.LowGlobalBudget
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_global_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤(5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (D K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_sector_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  let q := (Fintype.card (Eis⧸Ideal.span {Nlevel^2}):ℝ)
  have hq : 0≤q := Nat.cast_nonneg _
  refine ⟨degree,q^3*C+1,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows Pset S hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  obtain ⟨D,hD⟩ := exists_global_sector_completion G rows Pset S hrows s hc₀ hNlevel hbase hac hpair hGN
    hrowcop hprod hScop (fun P hP b => hSN P hP (Sum.inr b))
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hs := literal_global_sector_energy G rows Pset S hrows j D s hc₀ W θ X r aw
    (C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2)) (by
      intro r₀ p₀
      obtain ⟨E,hE⟩ := hD r₀ p₀
      refine ⟨E,hE,?_⟩
      exact henergy J I F Q Q₀ hJ hI hQ hpower hmask A
        Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
        hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
        hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
        hFcap hscap hpool (fullRaySector Nlevel rows r₀) (fullRaySector Nlevel Pset p₀) S
        (fun K hK => hrows K (Finset.mem_filter.mp hK).1) E hGN hGchar
        (fun K hK => hrowcop K (Finset.mem_filter.mp hK).1)
        (fun P hP => hprod P (Finset.mem_filter.mp hP).1)
        (fun P hP => hScop P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSN P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSchar P (Finset.mem_filter.mp hP).1)
        θ r aw hqk hqp
        (fun K hK => hKr K (Finset.mem_filter.mp hK).1)
        (fun P hP => hPr P (Finset.mem_filter.mp hP).1)
        (fun K hK => hr K (Finset.mem_filter.mp hK).1)
        (fun P hP => haw P (Finset.mem_filter.mp hP).1))
  apply hs.trans
  change q^3*(C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2))≤_
  have hp : 0≤(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by positivity
  nlinarith
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.TupleMembers
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable (tuples : Finset (σ→Ideal Eis))
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)

variable {N a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (D : ∀ P : tuples.image slotTupleProduct,IsCoprime K P.val→
      ControlledStratumArithmetic (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)

lemma memberTupleControlled_value (p : tuples) (hp : IsCoprime K (slotTupleProduct p.val))
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
      (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
      (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
      (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) W X=
    mixedReflectedValue (D ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
      (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
      (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
      (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) W X :=
  mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X

theorem literalWholeRow_eq_member_tuples
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) :
    literalWholeRow F K hK (tuplePrimeFamily tuples hne hmax hgood) j
      (tuples.image slotTupleProduct) D s hc W θ X r (slotProductCoefficient tuples aw)=
    ∑ p : tuples,if hp:IsCoprime K (slotTupleProduct p.val) then
      r K*aw p.val*mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
        (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X else 0 := by
  let hr : ∀ k∈({K}:Finset (Ideal Eis)),Admissible k := fun k hk => (Finset.mem_singleton.mp hk).symm ▸ hK
  let Ds : ∀ k : ({K}:Finset (Ideal Eis)),∀ P : tuples.image slotTupleProduct,IsCoprime k.val P.val→
      ControlledStratumArithmetic (F.reflected k.val (hr k.val k.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode := by
    intro k
    rcases k with ⟨k,hk⟩
    have hh := Finset.mem_singleton.mp hk
    subst k
    exact D
  have he := literalWholeRow_eq_active_tuples F {K} tuples hne hmax hgood hinj
    hr j Ds s hc W θ X r aw ⟨K,Finset.mem_singleton_self K⟩
  convert (preTransparency := .instances) he using 1
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hk : IsCoprime K (slotTupleProduct p.val)
  · simp only [dif_pos hk]
    rw [memberTupleControlled_value]
  · simp only [dif_neg hk]
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.LowMemberBudget
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_member_tuple_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤(5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_global_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows tuples hne hmax hgood hinj
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  obtain ⟨D,hD⟩ := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows (tuples.image slotTupleProduct) (tuplePrimeFamily tuples hne hmax hgood)
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have he := hD θ r (slotProductCoefficient tuples aw) hqk hqp hKr hPr hr
    (fun P hP => slotProductCoefficient_norm tuples hinj aw haw P hP)
  convert (preTransparency := .instances) he using 1
  apply Finset.sum_congr rfl
  intro K hK
  congr 2
  exact (literalWholeRow_eq_member_tuples tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw).symm
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.LowMemberGeometry
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem original_low_member_geometry_uniform_oai
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i)) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤(5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  have hb (i : γ) := original_low_member_tuple_full_budget (Nlevel:=Nlevel)
    ε hε lo hi hlo W hWs hW (s i) (hc₀ i) (hNlevel i) (hbase i) (hac i)
    ρ hρ η hηpos κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  choose degree C Z₀ hC hZ₀ henergy using hb
  let degreeAll := ∑ i,degree i
  let CAll := (∑ i,C i)+1
  let ZAll := (∑ i,|Z₀ i|)+2
  have hn (i : γ) : degree i≤degreeAll := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hc (i : γ) : C i≤CAll := by
    have hh : C i≤∑ j,C j := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    dsimp only [CAll]
    linarith
  have hz (i : γ) : Z₀ i≤ZAll := by
    have hh : |Z₀ i|≤∑ j,|Z₀ j| := Finset.single_le_sum (fun j _ => abs_nonneg (Z₀ j)) (Finset.mem_univ i)
    have hh' := le_abs_self (Z₀ i)
    dsimp only [ZAll]
    linarith
  have hCA : 0<CAll := by
    have hh : 0≤∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    dsimp only [CAll]
    linarith
  have hZA : 1<ZAll := by
    have hh : 0≤∑ i,|Z₀ i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    dsimp only [ZAll]
    linarith
  refine ⟨degreeAll,CAll,ZAll,hCA,hZA,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := henergy i J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    ((hz i).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  apply (hD θ r aw hqk hqp hKr hPr hr haw).trans
  have hZpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZA hZ)
  have hheight : 1≤1+‖θ‖ := by linarith [norm_nonneg θ]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
  exact mul_le_mul (hc i) (pow_le_pow_right₀ hheight (hn i)) (by positivity) hCA.le
end
end SevenEighths.InverseReflectedPhase

end OAI
end

theorem solution.{v, u_1} : type_of% @OAI.SevenEighths.InverseReflectedPhase.original_low_member_geometry_uniform_oai.{v, u_1} := @OAI.SevenEighths.InverseReflectedPhase.original_low_member_geometry_uniform_oai.{v, u_1}
