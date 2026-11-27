-- Prove2me | solution 1 for MohP3.HilbertBurch.augment_submatrix_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:58.367811+00:00
-- url     : https://prove2.me/submissions/88340837-07a1-4b0c-ba3b-458d20285126

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
attribute [local simp] MohP3.HilbertBurch.rowMap_apply

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
variable {S : Type*} [CommRing S]
omit [CommRing S]
namespace MohP3.HilbertBurch
theorem _root_.solution (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) (i : Fin 4) :
    (augment a Φ).submatrix i.succAbove Fin.succ = Φ.submatrix i.succAbove id := by
  ext r c
  simp [augment]
end MohP3.HilbertBurch
