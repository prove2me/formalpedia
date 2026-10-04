-- Prove2me | solution 1 for MSKleene.kleene_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T09:31:33.452851+00:00
-- url     : https://prove2.me/submissions/e3a9a0c2-6f0f-463d-947d-44a5861ecd8e

import Theorems.Thm_MSKleene_rec_subset_reg
import Theorems.Thm_MSKleene_reg_subset_rec

theorem solution {S : Type} [Finite S] (sig : MSKleene.Signature S)
    (X : MSKleene.SSet S) (hsig : MSKleene.SigFinite sig)
    (hX : MSKleene.SFinite X) (s : S) :
    MSKleene.RecS (MSKleene.freeAlgebra sig X) s =
      MSKleene.RegS sig X s := by
  apply Set.Subset.antisymm
  · exact MSKleene.rec_subset_reg sig X hsig hX s
  · exact MSKleene.reg_subset_rec sig X hsig hX s
