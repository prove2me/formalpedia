-- Prove2me | solution 1 for OAI.CubicEisenstein.schlafliBesselK_cubic_mellin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:38:05.585437+00:00
-- url     : https://prove2.me/submissions/87b2d4fd-e9d7-48ee-a53e-6c3fa772bd22

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RationalTranslations
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspAverage
import Theorems.Thm_OAI_CubicEisenstein_cubicMellinMixture_integrable
import Theorems.Thm_OAI_CubicEisenstein_schlafliBesselK_cubic_mellin_mixture
import Theorems.Thm_OAI_CubicEisenstein_cubicMellinMixture_double_integral

set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding
namespace OAI.CubicEisenstein
theorem _root_.solution (s : ℂ) (hs : 1/3<s.re) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*schlafliBesselK (1/3) x) =
      (2:ℂ)^(s-2)*Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by
  have hmix : Integrable (Function.uncurry (cubicMellinMixture s))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    convert cubicMellinMixture_integrable s hs using 1
    funext p
    rcases p with ⟨t,x⟩
    rfl
  have hswap := (integral_integral_swap hmix).symm
  have h4 : (4:ℂ)^((s-1/3)/2)=(2:ℂ)^(2*((s-1/3)/2)) := by
    have hh := (Complex.natCast_cpow_natCast_mul 2 2 ((s-1/3)/2)).symm
    norm_num at hh
    exact hh
  have hprod : (2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)=(2:ℂ)^s := by
    rw [h4,←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  have hscale : (1/4:ℂ)*(2:ℂ)^s=(2:ℂ)^(s-2) := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2:ℂ)≠0)]
    norm_num
    ring
  calc
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (∫x : ℝ in Set.Ioi 0,∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact schlafliBesselK_cubic_mellin_mixture s x hx
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          Complex.Gamma ((s+1/3)/2)) := by
      rw [hswap,cubicMellinMixture_double_integral s hs]
    _ = ((1/4:ℂ)*((2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)))*
        Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by ring
    _ = _ := by rw [hprod,hscale]
end OAI.CubicEisenstein
