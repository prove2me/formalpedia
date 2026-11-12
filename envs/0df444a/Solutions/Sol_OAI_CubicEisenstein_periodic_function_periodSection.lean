-- Prove2me | solution 1 for OAI.CubicEisenstein.periodic_function_periodSection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:13:35.020839+00:00
-- url     : https://prove2.me/submissions/2918e9b5-e159-4549-8870-e67090d3aafe

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeResidueStrata
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedCuspPhases
import Theorems.Thm_OAI_CubicEisenstein_periodTorus_eq_implies_lattice_difference
import Theorems.Thm_OAI_CubicEisenstein_periodTorus_section


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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open ConcreteTraceCRT EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
attribute [local instance] OAI.CubicEisenstein._p2m_local_instance_8a0d29538b_510
attribute [local instance] OAI.CubicEisenstein._p2m_local_instance_8a0d29538b_511
attribute [local instance] OAI.CubicEisenstein._p2m_local_instance_8a0d29538b_513
namespace OAI.CubicEisenstein
theorem _root_.solution (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (z : ℂ) :
    f (periodSection (periodTorus z))=f z := by
  obtain ⟨n,hn⟩ := periodTorus_eq_implies_lattice_difference (periodSection (periodTorus z)) z
    (periodTorus_section (periodTorus z))
  rw [hn,hp]
end OAI.CubicEisenstein
