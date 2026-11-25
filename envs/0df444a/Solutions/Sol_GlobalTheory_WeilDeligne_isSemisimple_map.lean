-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.isSemisimple_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:39.201323+00:00
-- url     : https://prove2.me/submissions/379d933a-a0df-44b4-a6ac-92000bbeb31a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
namespace GlobalTheory.WeilDeligne
theorem _root_.solution [FiniteDimensional ℂ V] (φ : End ℂ V →ₐ[ℂ] End ℂ V') {f : End ℂ V}
    (hf : f.IsSemisimple) : (φ f).IsSemisimple :=
  End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree (by
    rw [aeval_algHom_apply, minpoly.aeval, map_zero])
end GlobalTheory.WeilDeligne
