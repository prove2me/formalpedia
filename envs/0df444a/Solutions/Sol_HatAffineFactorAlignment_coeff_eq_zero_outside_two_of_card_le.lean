-- Prove2me | solution 1 for HatAffineFactorAlignment.coeff_eq_zero_outside_two_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:15:35.377085+00:00
-- url     : https://prove2.me/submissions/93c5fcdc-085f-40fa-a1a7-03cc5359e8df

import Definitions.Def_HatAffineGenericCore_G3A
import Definitions.Def_HatAffineFactorAlignment_FactorShape
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_coeffSupport



set_option autoImplicit true
open scoped BigOperators
open HatAffineFactorAlignment
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore
namespace HatAffineFactorAlignment
theorem _root_.solution
    {K : Type*} [Zero K] {m : Nat}
    (a : Fin m → K) (u v j : Fin m)
    (hcard : (coeffSupport a).card ≤ 2)
    (hau : a u ≠ 0) (hav : a v ≠ 0)
    (huv : u ≠ v) (hju : j ≠ u) (hjv : j ≠ v) :
    a j = 0 := by
  classical
  by_contra haj
  have hthree : 2 < (coeffSupport a).card :=
    Finset.two_lt_card_iff.mpr
      ⟨u, v, j,
        (mem_coeffSupport a u).mpr hau,
        (mem_coeffSupport a v).mpr hav,
        (mem_coeffSupport a j).mpr haj,
        huv, Ne.symm hju, Ne.symm hjv⟩
  omega
end HatAffineFactorAlignment
