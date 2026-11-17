-- Prove2me | solution 1 for N25.cusp_geometric_contraction
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:05.091475+00:00
-- url     : https://prove2.me/submissions/0b0df160-f895-4d73-b7ee-0b4917388a78

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Theorems.Thm_N25_Endgame_rational_geometric_constant_extension25
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve

namespace N25

open Endgame

/-- Every actual geometric cusp contracts to a unique closed cusp over the rationals. -/
theorem _root_.solution (P : GPlace)
    (hP : ModularCurve.IsCusp (emb25 j25) P) :
    ∃! Q : QPlace, ModularCurve.IsCusp j25 Q ∧
      Q.toValuationSubring = P.toValuationSubring.comap emb25.toRingHom := by
  let : Algebra FQ FG := emb25.toRingHom.toAlgebra
  obtain ⟨ht,hi,_⟩ := rational_geometric_constant_extension25
  have := ht
  have := hi
  let Q : QPlace := P.restrictConstants FQ
  have hQ : Q.toValuationSubring = P.toValuationSubring.comap emb25.toRingHom := rfl
  refine ⟨Q,⟨?_,hQ⟩,?_⟩
  · change j25 ∉ Q.toValuationSubring
    rw [hQ]
    exact hP
  · intro R hR
    exact Place.ext (hR.2.trans hQ.symm)

end N25
