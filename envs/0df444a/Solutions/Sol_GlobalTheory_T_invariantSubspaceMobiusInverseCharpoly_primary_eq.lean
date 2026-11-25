-- Prove2me | solution 1 for GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_primary_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:38:41.701114+00:00
-- url     : https://prove2.me/submissions/18ad3021-1f6a-46e1-8053-b2768abdac65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEqStatement
import Theorems.Thm_GlobalTheory_CuspGL_psi_primary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ (g : Module.End F V) (f : F[X]) (m t : ℕ), f.Monic → Irreducible f → 0 < m → LinearMap.charpoly g = f ^ m → Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t → psi s V g = s f * ∏ i ∈ Finset.Ico 1 t, (1 - (Nat.card F : ℂ) ^ (f.natDegree * i)) := by
  first | exact @GlobalTheory.CuspGL.psi_primary | exact GlobalTheory.CuspGL.psi_primary | (intros; apply GlobalTheory.CuspGL.psi_primary <;> assumption)
end _root_.GlobalTheory.T
