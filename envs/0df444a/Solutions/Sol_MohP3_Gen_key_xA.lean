-- Prove2me | solution 1 for MohP3.Gen.key_xA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:10.988324+00:00
-- url     : https://prove2.me/submissions/d16e70bf-df2b-4207-9c0b-5a2af911c2fd

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_GenClosure
public import Theorems.Thm_MohP3_Gen_key_xA_0
public import Theorems.Thm_MohP3_Gen_key_xA_1
public import Theorems.Thm_MohP3_Gen_key_xA_2
public import Theorems.Thm_MohP3_Gen_key_xA_3
public import Theorems.Thm_MohP3_Gen_key_xA_4
public import Theorems.Thm_MohP3_Gen_key_xA_5
public import Theorems.Thm_MohP3_Gen_key_xA_6
public import Theorems.Thm_MohP3_Gen_key_xA_7

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
namespace MohP3.Gen
theorem _root_.solution (i : Fin 8) :
    (18 : A) * (x * hh x y z i) =
      (∑ j, qxA y i j * hh x y z j) + ∑ j, wxA x y z i j * ff x y z j := by
  fin_cases i
  exacts [key_xA_0 x y z, key_xA_1 x y z, key_xA_2 x y z, key_xA_3 x y z,
    key_xA_4 x y z, key_xA_5 x y z, key_xA_6 x y z, key_xA_7 x y z]
end MohP3.Gen
