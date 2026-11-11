-- Prove2me | solution 1 for OAI.CanonicalUnitEuler.rowTwist_unit_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:46:15.442149+00:00
-- url     : https://prove2.me/submissions/85f03b5a-b8ee-4559-aa4e-1ffc4362ccf5

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FredholmAlternative
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_UnitNormalization
import Theorems.Thm_OAI_CanonicalUnitEuler_idealRowHom_unit_norm
import Theorems.Thm_OAI_CanonicalRowCompletion_idealRowHom_argument_mul


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
open OAI.CanonicalUnitEuler
open ActualEisensteinCubic
open CanonicalRowCompletion
open ConcreteTraceCRT (eisEmbedding)
open UniqueFactorizationMonoid
namespace OAI.CanonicalUnitEuler
theorem _root_.solution (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z n : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ)
    (hn : n≠0)
    (hgood : ∀P∈normalizedFactors (Ideal.span {n}),
      P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    rowTwist Ψ m f (u.val*z) n = rowTwist Ψ m f z n *
      eisEmbedding (u.val^((Ideal.absNorm (Ideal.span {n})-1)/6)) := by
  change Ψ n*idealRowHom (m^6*f^4*(u.val*z)) (Ideal.span {n}) =
    (Ψ n*idealRowHom (m^6*f^4*z) (Ideal.span {n}))*_
  rw [show m^6*f^4*(u.val*z)=u.val*(m^6*f^4*z) by ring,
    idealRowHom_argument_mul,
    idealRowHom_unit_norm u _ (Ideal.span_singleton_eq_bot.not.mpr hn) hgood]
  ring
end OAI.CanonicalUnitEuler
