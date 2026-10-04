-- Prove2me | solution 1 for MSKleene.rec_subst_single
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T06:39:19.103441+00:00
-- url     : https://prove2.me/submissions/57031233-9710-443e-82f5-98467ad71b05

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Subst
import Definitions.Def_MSKleene_SubstGlobal
import Theorems.Thm_MSKleene_rec_basic
import Theorems.Thm_MSKleene_rec_subst

open MSKleene
open Classical

theorem solution {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hX : SFinite X) {s t : S} (z : X t) (L : Set (Term sig X t))
    (K : Set (Term sig X s)) (hL : sRecognizable (freeAlgebra sig X) t L)
    (hK : sRecognizable (freeAlgebra sig X) s K) :
    sRecognizable (freeAlgebra sig X) s (substP z L s K) := by
  have hassign : ∀ (u : S) (x : X u),
      sRecognizable (freeAlgebra sig X) u (substAssign z L u x) := by
    intro u x
    by_cases hu : u = t
    · subst u
      by_cases hx : x = z
      · subst x
        simpa [substAssign] using hL
      · have heq : (show Set (Term sig X t) from substAssign z L t x) =
            {Term.var x} := by
          ext R
          simp [substAssign, hx]
        exact Eq.mpr (congrArg
          (fun Q : Set (Term sig X t) =>
            sRecognizable (freeAlgebra sig X) t Q) heq)
          ((rec_basic sig X t).1 x)
    · have heq : (show Set (Term sig X u) from substAssign z L u x) =
          {Term.var x} := by
        ext R
        simp [substAssign, hu]
      exact Eq.mpr (congrArg
        (fun Q : Set (Term sig X u) =>
          sRecognizable (freeAlgebra sig X) u Q) heq)
        ((rec_basic sig X u).1 x)
  have h := rec_subst sig X hX K hK (substAssign z L) hassign
  simpa [substGlobalP, substP, substGlobalHom, substHom] using h
