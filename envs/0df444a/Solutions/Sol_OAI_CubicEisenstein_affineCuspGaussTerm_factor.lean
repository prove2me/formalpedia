-- Prove2me | solution 1 for OAI.CubicEisenstein.affineCuspGaussTerm_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:25:27.407946+00:00
-- url     : https://prove2.me/submissions/b6800e93-a674-4b90-b178-24f36c2d83fe

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedCuspPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
import Theorems.Thm_OAI_CubicEisenstein_affineCusp_phase_identity
import Theorems.Thm_OAI_CubicEisenstein_ramified_symbol_primary_shift_signed
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_congr
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_mul_numerator


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
open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (h h1 q r a k x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a) :
    (eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))=
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
      (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)))*
        (eisEmbedding (symbol x a)*residueAdditive (3*k) a x) := by
  have hs:symbol (a+3*x) a=symbol (3*x) a:=symbol_congr ⟨1,by ring⟩
  rw [ramified_symbol_primary_shift_signed j n r a x hr hprimary,hs,
    symbol_mul_numerator _ _ _ hprimary,map_mul eisEmbedding (symbol 3 a) (symbol x a)]
  have hp:=affineCusp_phase_identity h h1 q a k (ramifiedAffineParameter j n) x ha hq hh hk
  calc
    _ = (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol x a))*
      (ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))) := by ring
    _ = _ := by rw [hp];ring
end OAI.CubicEisenstein
