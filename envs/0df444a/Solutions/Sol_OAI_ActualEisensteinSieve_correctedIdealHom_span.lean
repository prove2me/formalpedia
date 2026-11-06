-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.correctedIdealHom_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:25.704883+00:00
-- url     : https://prove2.me/submissions/42d2135c-b112-42ea-84cc-9080da20b008

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
namespace ActualEisensteinSieve
example (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
example (P : Ideal O) [P.IsMaximal] : Finite (O ⧸ P) := inferInstance
private theorem idealGeneratorClass_span (x : O) :
    idealGeneratorClass (Ideal.span {x}) = Associates.mk x := by
  apply (Ideal.associatesMulEquivIsPrincipal O).injective
  simp [idealGeneratorClass]
  apply Subtype.ext
  rfl
end ActualEisensteinSieve
end
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ActualEisensteinSieve
namespace OAI.ActualEisensteinSieve
theorem _root_.solution
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) :
    correctedIdealHom P (Ideal.span {x}) =
      correctedQuadraticProduct P x := by
  simp [correctedIdealHom, idealGeneratorClass_span, correctedAssociatesHom]
end OAI.ActualEisensteinSieve
