-- Prove2me | solution 1 for HatAffineConstantRows.rowSeparating_obstruction_totalDegree_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:23:19.516865+00:00
-- url     : https://prove2.me/submissions/5a175bf1-b30d-4029-8181-3e3db9962f8d

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_rowSeparating_obstruction_totalDegree
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial
namespace HatAffineConstantRows
theorem _root_.solution
    {K : Type u} [Field K] {m : Nat} {I : Type v} [Fintype I]
    (A : I → Fin m → K) (b : I → K)
    (i0 : I) (hi0 : A i0 = 0) :
    (affineObstruction A b (rowSeparatingOffset A b)).totalDegree <
      Fintype.card I := by
  classical
  rw [rowSeparating_obstruction_totalDegree]
  unfold nonzeroRowCount
  have hproper :
      (Finset.univ.filter fun i => A i ≠ 0) ⊂ (Finset.univ : Finset I) :=
    Finset.filter_ssubset.mpr ⟨i0, Finset.mem_univ i0, by simp [hi0]⟩
  simpa using Finset.card_lt_card hproper
end HatAffineConstantRows
