-- Prove2me | solution 1 for MohP3.Gen.key_zA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:25:54.896047+00:00
-- url     : https://prove2.me/submissions/4a4e9d70-8fc5-4500-ad21-2eaeeb59f1c4

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_GenClosure
public import Theorems.Thm_MohP3_Gen_key_zA_0
public import Theorems.Thm_MohP3_Gen_key_zA_1
public import Theorems.Thm_MohP3_Gen_key_zA_2
public import Theorems.Thm_MohP3_Gen_key_zA_3
public import Theorems.Thm_MohP3_Gen_key_zA_4
public import Theorems.Thm_MohP3_Gen_key_zA_5
public import Theorems.Thm_MohP3_Gen_key_zA_6
public import Theorems.Thm_MohP3_Gen_key_zA_7

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
namespace MohP3.Gen
theorem _root_.solution (i : Fin 8) :
    (18 : A) * (z * hh x y z i) =
      (∑ j, qzA y i j * hh x y z j) + ∑ j, wzA x y z i j * ff x y z j := by
  fin_cases i
  exacts [key_zA_0 x y z, key_zA_1 x y z, key_zA_2 x y z, key_zA_3 x y z,
    key_zA_4 x y z, key_zA_5 x y z, key_zA_6 x y z, key_zA_7 x y z]
end MohP3.Gen
