-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelQuotientDefect_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:00:40.067729+00:00
-- url     : https://prove2.me/submissions/4499a5e8-d9a9-40e9-a6b7-8b39c765a594

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Theorems.Thm_OAI_CubicEisenstein_smoothCuspSeedDefect_high_zero
import Theorems.Thm_OAI_CubicEisenstein_globalKubotaKernel_compact_core_cusp_cover


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
open scoped BigOperators Classical
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    HasCompactSupport (kernelQuotientDefect a b s) := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS (max b a⁻¹)
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S (max b a⁻¹) ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r (max b a⁻¹) := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    exact hq (smoothCuspSeedDefect_high_zero a b ha hab s r⁻¹ p.1.1 p.1.2 p.2 hp.2.2)
end OAI.CubicEisenstein
