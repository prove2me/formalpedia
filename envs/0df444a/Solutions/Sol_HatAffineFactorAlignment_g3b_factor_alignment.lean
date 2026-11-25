-- Prove2me | solution 1 for HatAffineFactorAlignment.g3b_factor_alignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:18:58.931085+00:00
-- url     : https://prove2.me/submissions/bb6a2351-3cae-4941-99cf-818e9dc4991a

import Definitions.Def_HatAffineFactorAlignment_FactorShape
import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Theorems.Thm_HatAffineFactorAlignment_genericTypeII_of_shape
import Theorems.Thm_HatAffineFactorAlignment_g3b_factor_shape


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
    (hm : 1 ≤ m) (hq : 3 ≤ Fintype.card K)
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (lambda : Fin m → K)
    (hrows : ∀ i, A i ≠ 0)
    (hlambda : lambda ≠ 0)
    (hidentity : (∏ i, linearForm (A i)) = diagonalForm lambda) :
    GenericTypeI A lambda ∨ GenericTypeII A lambda := by
  rcases g3b_factor_shape hm hq A lambda hrows hlambda hidentity with hI | hII
  · exact Or.inl hI
  · exact Or.inr (genericTypeII_of_shape hq A lambda hidentity hII)
end HatAffineFactorAlignment
