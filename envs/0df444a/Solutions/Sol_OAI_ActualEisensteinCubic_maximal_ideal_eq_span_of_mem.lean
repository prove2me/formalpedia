-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.maximal_ideal_eq_span_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:40.143092+00:00
-- url     : https://prove2.me/submissions/3b0e87ea-8943-4015-8e0d-c5c347338aa9

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments

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
open OAI.ActualEisensteinCubic
open ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (Q : Ideal O) (hQ : Q.IsMaximal) (a : O)
    (ha : (Ideal.span {a} : Ideal O).IsMaximal) (hamem : a ∈ Q) :
    Q = Ideal.span {a} := by
  have hle : (Ideal.span {a} : Ideal O) ≤ Q :=
    (Ideal.span_singleton_le_iff_mem _).mpr hamem
  exact (ha.eq_of_le hQ.ne_top hle).symm
end OAI.ActualEisensteinCubic
