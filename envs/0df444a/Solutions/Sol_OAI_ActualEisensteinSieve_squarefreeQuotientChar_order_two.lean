-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.squarefreeQuotientChar_order_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:31.446475+00:00
-- url     : https://prove2.me/submissions/0a81fa54-870f-46c6-9caa-4fa433a50396

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Theorems.Thm_OAI_ActualEisensteinSieve_squarefreeQuotientChar_isQuadratic

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
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    squarefreeQuotientChar P hpair ^ 2 = 1 :=
  (squarefreeQuotientChar_isQuadratic P hpair).sq_eq_one
end OAI.ActualEisensteinSieve
