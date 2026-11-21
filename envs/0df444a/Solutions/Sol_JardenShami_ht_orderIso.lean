-- Prove2me | solution 1 for JardenShami.ht_orderIso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:17.206607+00:00
-- url     : https://prove2.me/submissions/921aa530-c06d-4d0d-a3e2-3d7990317cc6

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {P Q : Type u} [PartialOrder P] [IsTree P] [PartialOrder Q] [IsTree Q]
    (e : P ≃o Q) (t : P) : ht (e t) = ht t := by
  unfold ht
  refine (RelIso.ordinalType_congr ?_).symm
  exact
    { toFun := fun x => ⟨e x.1, e.lt_iff_lt.2 x.2⟩
      invFun := fun y => ⟨e.symm y.1, by simpa using e.symm.lt_iff_lt.2 y.2⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_rel_iff' := e.lt_iff_lt }
end JardenShami
