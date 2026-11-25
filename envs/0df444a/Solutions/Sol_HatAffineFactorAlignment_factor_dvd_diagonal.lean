-- Prove2me | solution 1 for HatAffineFactorAlignment.factor_dvd_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:15:28.720903+00:00
-- url     : https://prove2.me/submissions/13a2b2fb-8611-45b7-b5b0-a0512abfc22d

import Definitions.Def_HatAffineGenericCore_G3A
import Definitions.Def_HatAffineFactorAlignment_FactorShape

set_option autoImplicit true
open scoped BigOperators
open HatAffineFactorAlignment
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore
namespace HatAffineFactorAlignment
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (lambda : Fin m → K)
    (hidentity : (∏ i, linearForm (A i)) = diagonalForm lambda)
    (i : Fin (Fintype.card K - 1)) :
    linearForm (A i) ∣ diagonalForm lambda := by
  rw [← hidentity]
  exact Finset.dvd_prod_of_mem (fun k => linearForm (A k)) (Finset.mem_univ i)
end HatAffineFactorAlignment
