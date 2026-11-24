-- Prove2me | solution 1 for GlobalTheory.CuspGL.finsum_le_oneValue_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:49:59.155878+00:00
-- url     : https://prove2.me/submissions/b95599b8-9c02-4c8d-afc1-f641f986a2cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspaces
import Theorems.Thm_GlobalTheory_CuspGL_sum_oneValue_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (A : Submodule K U) :
    ∑ᶠ B : {B : Submodule K U // B ≤ A}, oneValue (Nat.card K) (Module.finrank K B.1) =
      (Module.finrank K A : ℂ) := by
  classical
  haveI : Finite A := Module.finite_of_finite K
  haveI : Fintype (Submodule K A) := Fintype.ofFinite _
  rw [← sum_oneValue_finrank K A, ← finsum_eq_sum_of_fintype,
    ← finsum_comp_equiv (Submodule.MapSubtype.orderIso A).toEquiv]
  refine finsum_congr fun W => ?_
  congr 1
  exact Submodule.finrank_map_subtype_eq A W
end GlobalTheory.CuspGL
