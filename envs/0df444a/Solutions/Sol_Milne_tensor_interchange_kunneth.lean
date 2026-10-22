-- Prove2me | solution 1 for Milne.tensor_interchange_kunneth
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:13:42.423893+00:00
-- url     : https://prove2.me/submissions/67579ac0-7818-45bc-bd55-eb91f61bdf81

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta
universe u v

open Milne

theorem solution (W : CorrWorld.{u, v}) (X Y : W.Var)
    (M M' N N' P P' : MotElem W)
    (f : Hom W M N) (g : Hom W N P) (f' : Hom W M' N') (g' : Hom W N' P') :
    crossHom W (homComp W f g) (homComp W f' g') =
      homComp W (crossHom W f f') (crossHom W g g')
      ∧ crossHom W (idM W M) (idM W N) = idM W (tensorObj W M N)
      ∧ tensorObj W (hOf W X) (hOf W Y) = hOf W (W.prod X Y) := by
  refine ⟨Subtype.ext ?_, Subtype.ext rfl, ?_⟩
  · exact (W.cross_cc f.val g.val f'.val g'.val).symm
  · show MotElem.mk _ _ _ _ = MotElem.mk _ _ _ _
    congr 1
    exact W.cross_delta X Y
