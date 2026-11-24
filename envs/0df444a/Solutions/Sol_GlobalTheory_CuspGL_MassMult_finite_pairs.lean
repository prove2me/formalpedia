-- Prove2me | solution 1 for GlobalTheory.CuspGL.MassMult.finite_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:02:53.105609+00:00
-- url     : https://prove2.me/submissions/78cb7038-c9ea-4060-bd67-03ccbdf05c92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivial

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
theorem _root_.solution {F : Type} [Field F] (P : F[X]) (hP : P.Monic) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  have h : {g : F[X] | g.Monic ∧ g ∣ P}.Finite := by
    have := Polynomial.fintypeSubtypeMonicDvd P hP.ne_zero
    exact Set.finite_coe_iff.mp (Finite.of_fintype {g : F[X] // g.Monic ∧ g ∣ P})
  refine (h.prod h).subset ?_
  rintro x ⟨h1, h2, h3⟩
  exact ⟨⟨h1, h3 ▸ dvd_mul_right _ _⟩, ⟨h2, h3 ▸ dvd_mul_left _ _⟩⟩
end GlobalTheory.CuspGL.MassMult
