-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.squarefreeQuotientChar_isQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:32:20.577471+00:00
-- url     : https://prove2.me/submissions/2563120e-03ff-4966-82d7-4780ef8eca96

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Theorems.Thm_OAI_ActualEisensteinSieve_squarefreeQuotientChar_mk
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
private theorem finite_prod_trichotomy {ι : Type*} (s : Finset ι)
    (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 0 ∨ f i = 1 ∨ f i = -1) :
    s.prod f = 0 ∨ s.prod f = 1 ∨ s.prod f = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, f j = 0 ∨ f j = 1 ∨ f j = -1 := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have ih' := ih hfs
      rcases hfi with h0 | h1 | hm
      · left; simp [Finset.prod_insert his, h0]
      · simpa [Finset.prod_insert his, h1] using ih'
      · rcases ih' with h0 | h1 | hm'
        · left; simp [Finset.prod_insert his, hm, h0]
        · right; right; simp [Finset.prod_insert his, hm, h1]
        · right; left; simp [Finset.prod_insert his, hm, hm']
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
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    (squarefreeQuotientChar P hpair).IsQuadratic := by
  classical
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [squarefreeQuotientChar_mk]
  apply finite_prod_trichotomy
  intro i _
  exact localQuadratic_trichotomy (P i) x
end OAI.ActualEisensteinSieve
