-- Prove2me | solution 1 for GlobalTheory.CuspGL.PsiPrimitive.res_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:28.040671+00:00
-- url     : https://prove2.me/submissions/5a5702a9-ad4e-49f7-b7b7-e6d27bfa385c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyTransversalSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobi
import Theorems.Thm_GlobalTheory_T_invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.PsiPrimitive
namespace GlobalTheory.CuspGL.PsiPrimitive
theorem _root_.solution {F : Type} [Field F] (s : F[X] → ℂ) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (k : Module.End F V) : res s ⊤ k = psi s V k := by
  have htop : ∀ x ∈ (⊤ : Submodule F V), k x ∈ (⊤ : Submodule F V) := fun _ _ => Submodule.mem_top
  unfold res
  rw [dif_pos htop]
  have hconj := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s (⊤ : Submodule F V) V Submodule.topEquiv (k.restrict htop)
  rw [← hconj]
  congr 1
end GlobalTheory.CuspGL.PsiPrimitive
