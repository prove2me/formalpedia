-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGLChar.mul_mul_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:00:44.785252+00:00
-- url     : https://prove2.me/submissions/67f8070e-9ca0-4988-831b-5342a9c24283

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGLChar
namespace GlobalTheory.CompanionTheory.FinGLChar
theorem _root_.solution {G : Type} [Group G] (a x g : G) :
    a * (x * g) = x ↔ a⁻¹ = x * g * x⁻¹ := by
  constructor
  · intro h
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← mul_assoc, ← mul_assoc, mul_assoc a x g, h, mul_inv_cancel]
  · intro h
    have e : a = (x * g * x⁻¹)⁻¹ := by rw [← h, inv_inv]
    rw [e]
    group
end GlobalTheory.CompanionTheory.FinGLChar
