-- Prove2me | solution 2 for OAI.ShortDraftCRT.fixed_additive_sector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:39:49.871587+00:00
-- url     : https://prove2.me/submissions/4af755fb-2d96-414d-8d56-bf03b0761242

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualCuspDecay
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimePowerGaussSums
import Theorems.Thm_OAI_ShortDraftCRT_inverse_weight_residue_congr
import Theorems.Thm_OAI_ShortDraftCRT_addChar_congr_of_dvd


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
open scoped BigOperators Classical
open OAI.ShortDraftCRT
variable {R : Type*} [CommRing R]
namespace OAI.ShortDraftCRT
theorem _root_.solution {K : Type*} [Field K]
    (ι : R→+*K) (ψ : AddChar K ℂ) (lam D r r0 u u0 d d0 x : R)
    (hlam : ι lam≠0) (hD : ι D≠0)
    (hperiod : ∀y : R,ψ (ι y/ι lam)=1)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    ψ (ι (-d*u)*ι x/(ι lam*ι D))=
      ψ (ι (-d0*u0)*ι x/(ι lam*ι D)) :=
  addChar_congr_of_dvd ι ψ lam D (-d*u) (-d0*u0) x hlam hD hperiod
    (inverse_weight_residue_congr D r r0 u u0 d d0 hcop hr hu hu0 hd)
end OAI.ShortDraftCRT
