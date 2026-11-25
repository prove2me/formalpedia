-- Prove2me | solution 1 for GlobalTheory.CuspGL.irrChar_eq_one_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:48:39.168907+00:00
-- url     : https://prove2.me/submissions/0dcee394-3491-4089-94b3-d964abde10d0

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqOfIsPrimitiveOfEqOnEllipticFiniteGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrrCharEqOneOfSubsingleton

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
theorem _root_.solution {G : Type} [Group G] [Fintype G] [Subsingleton G] (χ : G → ℂ)
    (h : CuspElliptic.IsIrrChar χ) (x : G) : χ x = 1 := by
  obtain ⟨⟨n, ρ, hρ⟩, hs⟩ := h
  have hx : x = 1 := Subsingleton.elim _ _
  subst hx
  have h1 : χ 1 = (n : ℂ) := by rw [hρ]; simp
  rw [Fintype.sum_subsingleton _ (1 : G), Fintype.card_eq_one_iff_nonempty_unique.2
    ⟨uniqueOfSubsingleton (1 : G)⟩, h1] at hs
  have h2 : n * n = 1 := by
    have : ((n * n : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by simpa using hs
    exact_mod_cast this
  have h3 : n = 1 := Nat.eq_one_of_mul_eq_one_right h2
  rw [h1, h3]; simp
end GlobalTheory.CuspGL
