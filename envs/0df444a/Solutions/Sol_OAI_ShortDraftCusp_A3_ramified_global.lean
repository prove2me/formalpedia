-- Prove2me | solution 1 for OAI.ShortDraftCusp.A3_ramified_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:43:11.543202+00:00
-- url     : https://prove2.me/submissions/8c2ab52d-c581-41c0-9585-4cc28d53584a

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_TranslatedFourierResidues
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualCuspDecay
import Theorems.Thm_OAI_CubicJacobiGlobal_primary_ne_zero
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_congr
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_mul_numerator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_one_numerator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_reciprocity


set_option autoImplicit false
open OAI
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
open scoped BigOperators Classical
open OAI.ShortDraftCusp
open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.ShortDraftCusp
theorem _root_.solution (a b cprime d u : Eis)
    (hdet : a*d-b*(u*cprime)=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣(a-u*b)-1) :
    symbol (u*cprime-u*d) (a-u*b)=symbol (-u) (a-u*b)*symbol cprime a := by
  have h1 : symbol a (a-u*b)*symbol (u*cprime-u*d) (a-u*b)=symbol (-u) (a-u*b) := by
    rw [←symbol_mul_numerator _ _ _ hA]
    apply symbol_congr
    refine ⟨u*cprime,?_⟩
    linear_combination -u*hdet
  have h2 : symbol (a-u*b) a*symbol cprime a=1 := by
    rw [←symbol_mul_numerator _ _ _ ha,←symbol_one_numerator a ha]
    apply symbol_congr
    refine ⟨cprime-d,?_⟩
    linear_combination hdet
  rw [symbol_reciprocity a (a-u*b) (primary_ne_zero a ha)
    (primary_ne_zero _ hA) ha hA] at h1
  calc
    _ = (symbol (a-u*b) a*symbol cprime a)*symbol (u*cprime-u*d) (a-u*b) := by rw [h2,one_mul]
    _ = (symbol (a-u*b) a*symbol (u*cprime-u*d) (a-u*b))*symbol cprime a := by ring
    _ = _ := by rw [h1]
end OAI.ShortDraftCusp
