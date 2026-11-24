-- Prove2me | solution 1 for GlobalTheory.CuspGL.psi_of_irreducible_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:04:34.021816+00:00
-- url     : https://prove2.me/submissions/b69f24c7-e920-4e11-9d37-04b9eb7e5755

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduci
import Theorems.Thm_GlobalTheory_CuspGL_psi_of_finrank_eq_zero
import Theorems.Thm_GlobalTheory_CuspGL_finrank_eq_zero_of_irreducible_charpoly
import Theorems.Thm_GlobalTheory_CuspGL_psi_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ g : Module.End F V, Irreducible (LinearMap.charpoly g) → psi s V g = s (LinearMap.charpoly g) := by
  intro F _ _ V _ _ _ s hs g hg
  rw [psi_eq, finsum_eq_zero_of_forall_eq_zero, sub_zero]
  intro W
  exact psi_of_finrank_eq_zero s hs _ _ (finrank_eq_zero_of_irreducible_charpoly g hg W.1 W.2.1 W.2.2)
end GlobalTheory.CuspGL
