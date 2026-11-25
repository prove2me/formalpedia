-- Prove2me | solution 1 for HatAffineGenericCore.g2_puncturedBox_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:15:27.329064+00:00
-- url     : https://prove2.me/submissions/301efe64-4aeb-4e3a-a3ab-d7103c4ba3c9

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
import Theorems.Thm_HatAffineGenericCore_puncturedSet_nonempty
import Theorems.Thm_HatAffineGenericCore_puncturedGrid_ne_zero
import Theorems.Thm_HatAffineGenericCore_puncturedGrid_totalDegree
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
      P = ∑ j, C (lambda j) * puncturedGrid g j := by
  classical
  have hgrid : ∀ y : Fin m → K,
      (∀ j, y j ∈ puncturedSet g j) → MvPolynomial.eval y P = 0 := by
    intro y hy
    apply hvanish y
    intro j
    simpa [puncturedSet] using hy j
  obtain ⟨h, hterm, hcomb⟩ :=
    MvPolynomial.combinatorial_nullstellensatz_exists_linearCombination
      (puncturedSet g) (puncturedSet_nonempty g) P hgrid
  have hconst : ∀ j, h j = C ((h j).coeff 0) := by
    intro j
    by_cases hj : h j = 0
    · simp [hj]
    · apply (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
      have ht := (hterm j).trans hdeg
      change (puncturedGrid g j * h j).totalDegree ≤ Fintype.card K - 1 at ht
      rw [MvPolynomial.totalDegree_mul_of_isDomain (puncturedGrid_ne_zero g j) hj,
        puncturedGrid_totalDegree] at ht
      omega
  refine ⟨fun j => (h j).coeff 0, ?_⟩
  calc
    P = Finsupp.linearCombination (MvPolynomial (Fin m) K)
        (fun j => puncturedGrid g j) h := by
      simpa [puncturedGrid, puncturedSet] using hcomb
    _ = ∑ j, h j * puncturedGrid g j := by
      simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype, smul_eq_mul]
    _ = ∑ j, C ((h j).coeff 0) * puncturedGrid g j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun z => z * puncturedGrid g j) (hconst j)
end HatAffineGenericCore
