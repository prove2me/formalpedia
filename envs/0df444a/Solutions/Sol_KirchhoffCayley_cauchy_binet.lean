-- Prove2me | solution 1 for KirchhoffCayley.cauchy_binet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:31:31.767796+00:00
-- url     : https://prove2.me/submissions/012f2381-a79c-4bec-b27c-c220b34e0994

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Definitions.Def_MatrixTree_Solution
public import Theorems.Thm_MatrixTree_cauchy_binet


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open KirchhoffCayley
namespace KirchhoffCayley
theorem _root_.solution {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ S : {S : Finset (Fin k) // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) id).det :=
  MatrixTree.cauchy_binet A B
end KirchhoffCayley
