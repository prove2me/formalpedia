-- Prove2me | solution 1 for OAI.ShortDraftLatticeCount.coordinate_squares
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:08.299205+00:00
-- url     : https://prove2.me/submissions/cda9a7f3-83f1-4787-b8d1-04bdb3a4211e

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount

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
open OAI.ShortDraftLatticeCount
namespace OAI.ShortDraftLatticeCount
theorem _root_.solution (a b D : ℤ) (hD : 0 ≤ D)
    (h : a ^ 2 - a * b + b ^ 2 ≤ D) :
    a ^ 2 ≤ 2 * D ∧ b ^ 2 ≤ 2 * D := by
  constructor <;> nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b)]
end OAI.ShortDraftLatticeCount
