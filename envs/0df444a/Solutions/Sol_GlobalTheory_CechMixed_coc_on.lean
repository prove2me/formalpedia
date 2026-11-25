-- Prove2me | solution 1 for GlobalTheory.CechMixed.coc_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:27.71963+00:00
-- url     : https://prove2.me/submissions/7e5d5286-607e-4e61-a660-16cb44f235f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCechOneCocycleOnAffineCoverMixed
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_kerEquiv_val
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_KS_rsT_add
import Theorems.Thm_GlobalTheory_KS_rsT_rsT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AbLaw.CechOne.kerEquiv_val
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory GlobalTheory.CechMixed
open GlobalTheory.KS
namespace GlobalTheory.CechMixed
theorem _root_.solution {X : Scheme.{0}} {J : Type} {V : J → X.Opens} {z : C1 V} (hz : IsCoc V z) (i j l : J)
    {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j) (hl : W ≤ V l) :
    rsT (z i j) W + rsT (z j l) W = rsT (z i l) W := by
  have e : W ≤ V i ⊓ V j ⊓ V l := le_inf (le_inf hi hj) hl
  have h := congrArg (fun s => rsT s W) (hz i j l)
  simp only [rsT_add] at h
  rwa [rsT_rsT inf_le_left e, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) e,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) e] at h
end GlobalTheory.CechMixed
