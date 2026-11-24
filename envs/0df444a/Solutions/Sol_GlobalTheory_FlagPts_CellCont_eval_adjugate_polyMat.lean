-- Prove2me | solution 1 for GlobalTheory.FlagPts.CellCont.eval_adjugate_polyMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:09:39.913652+00:00
-- url     : https://prove2.me/submissions/54b2b37b-063f-4835-a90c-18bcdf7090f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
import Theorems.Thm_GlobalTheory_FlagPts_CellCont_map_polyMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace GlobalTheory.FlagPts
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.CellCont
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
namespace GlobalTheory.FlagPts.CellCont
theorem _root_.solution (u : AffPts k (CellIdx k V)) (i : ι) (a c : Fin (finrank k (V i))) :
    MvPolynomial.eval u ((polyMat (k := k) (V := V) i).adjugate a c) = (uniMat u i).adjugate a c := by
  have := RingHom.map_adjugate (MvPolynomial.eval u) (polyMat (k := k) (V := V) i)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_polyMat] at this
  exact congrFun (congrFun this a) c
end GlobalTheory.FlagPts.CellCont
