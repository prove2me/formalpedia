-- Prove2me | solution 1 for GlobalTheory.CuspGL.MassMult.mass_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:04:06.342785+00:00
-- url     : https://prove2.me/submissions/84b8bbfb-72e4-4b27-8973-ec8009101b47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivial
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_mass_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.MassMult
namespace GlobalTheory.CuspGL.MassMult
theorem _root_.solution {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (φ : Module.End F V → ℂ) (P : F[X]) (h : Module.finrank F V ≠ P.natDegree) : mass φ P = 0 := by
  rw [mass_eq]
  refine finsum_eq_zero_of_forall_eq_zero fun g => if_neg ?_
  rintro rfl
  exact h (LinearMap.charpoly_natDegree g).symm
end GlobalTheory.CuspGL.MassMult
