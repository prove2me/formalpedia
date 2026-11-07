-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_disjoint_pair_radial_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:32:03.098354+00:00
-- url     : https://prove2.me/submissions/2d15dc03-7d94-42e4-bc23-ec5ceaca17b5

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_radial_poisson_normalized
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSexticRow_disjoint_pair
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk

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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.ActualEisensteinCubic
theorem _root_.solution {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    let row := fun a => finiteSquarefreeRow P hgood S a *
      star (finiteSquarefreeRow P hgood (Finset.univ \ S) a)
    (∑' z : O, row z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hgood
        (fun i => if i ∈ S then 1 else 5) / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, star (row h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  have hp := canonical_radial_poisson_normalized P hcop hgood hchar
    (fun i => if i ∈ S then 1 else 5)
    (fun i => by split_ifs <;> decide) (fun i => by split_ifs <;> decide)
    W scale hscale
  simpa only [finiteSexticRow_disjoint_pair P hcop hgood S] using hp
end OAI.ActualEisensteinCubic
