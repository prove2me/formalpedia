-- Prove2me | solution 1 for HatAffineGenericCore.g2_puncturedBox_decomposition_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:16:40.324307+00:00
-- url     : https://prove2.me/submissions/b5097b22-6f87-4836-9764-97a79bf5a48e

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
import Theorems.Thm_HatAffineGenericCore_puncturedGrid_eq_puncturedPower
import Theorems.Thm_HatAffineGenericCore_g2_puncturedBox_decomposition
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card

set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial
namespace HatAffineGenericCore
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (g : Fin m → K) (P : MvPolynomial (Fin m) K)
    (hdeg : P.totalDegree ≤ Fintype.card K - 1)
    (hvanish : ∀ y : Fin m → K,
      (∀ j, y j ≠ g j) → MvPolynomial.eval y P = 0) :
    ∃ lambda : Fin m → K,
      P = ∑ j, C (lambda j) * puncturedPower g j := by
  obtain ⟨lambda, hlambda⟩ :=
    g2_puncturedBox_decomposition hm g P hdeg hvanish
  refine ⟨lambda, ?_⟩
  simpa only [puncturedGrid_eq_puncturedPower] using hlambda
end HatAffineGenericCore
