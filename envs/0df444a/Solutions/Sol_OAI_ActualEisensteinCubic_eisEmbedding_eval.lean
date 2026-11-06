-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.eisEmbedding_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:15.951601+00:00
-- url     : https://prove2.me/submissions/b7d3fa61-38cd-4e3e-9d39-d7006268aad3

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace

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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b : ℤ) :
    eisEmbedding (ActualEisensteinCoordinates.eval a b) =
      (a : ℂ) + (b : ℂ) * omega3 := by
  have hgen : ActualEisensteinCoordinates.omega =
      EisensteinEmbedding.pb.gen := by
    rw [← ActualEisensteinCoordinates.pb_gen]
    rfl
  rw [ActualEisensteinCoordinates.eval, hgen]
  change EisensteinEmbedding.embedding omega3 omega3_sq
    (a + b * EisensteinEmbedding.pb.gen : O) = _
  exact EisensteinEmbedding.embedding_apply_ab omega3 omega3_sq a b
end OAI.ActualEisensteinCubic
