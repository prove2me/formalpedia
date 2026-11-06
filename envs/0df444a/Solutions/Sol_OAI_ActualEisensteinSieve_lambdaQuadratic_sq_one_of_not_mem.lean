-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.lambdaQuadratic_sq_one_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:32:26.669956+00:00
-- url     : https://prove2.me/submissions/284721e2-6b04-4174-ae89-e394029a97df

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
private theorem localQuadratic_zero_iff (P : Ideal O) [P.IsMaximal] (x : O) :
    localQuadratic P x = 0 ↔ x ∈ P := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = 0 ↔ x ∈ P
  rw [quadraticChar_eq_zero_iff]
  exact Ideal.Quotient.eq_zero_iff_mem
private theorem localQuadratic_trichotomy (P : Ideal O) [P.IsMaximal]
    (x : O) :
    localQuadratic P x = 0 ∨ localQuadratic P x = 1 ∨
      localQuadratic P x = -1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = 0 ∨
    quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = 1 ∨
    quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = -1
  exact quadraticChar_isQuadratic (O ⧸ P) _
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
theorem _root_.solution (x : O)
    (hx : x ∉ lambdaIdeal) :
    localQuadratic lambdaIdeal x ^ 2 = 1 := by
  rcases localQuadratic_trichotomy lambdaIdeal x with hzero | hone | hminus
  · exact False.elim (hx ((localQuadratic_zero_iff lambdaIdeal x).mp hzero))
  · simp [hone]
  · simp [hminus]
end OAI.ActualEisensteinSieve
