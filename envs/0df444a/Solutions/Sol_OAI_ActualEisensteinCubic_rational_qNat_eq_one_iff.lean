-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_qNat_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:39.720768+00:00
-- url     : https://prove2.me/submissions/5159b19f-317b-4334-b5e3-0198a1de4af3

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Theorems.Thm_OAI_ActualEisensteinCubic_qNat_eq_absNorm_span


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
theorem _root_.solution (x : O) : qNat x = 1 ↔ IsUnit x := by
  rw [qNat_eq_absNorm_span, Ideal.absNorm_eq_one_iff,
    Ideal.span_singleton_eq_top]
end OAI.ActualEisensteinCubic
