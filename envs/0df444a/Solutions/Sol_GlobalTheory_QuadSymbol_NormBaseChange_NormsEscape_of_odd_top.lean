-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.NormsEscape.of_odd_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:04.845723+00:00
-- url     : https://prove2.me/submissions/580a87e4-afa9-4170-a400-c66f252295a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormBaseChange
open NormIndex
variable {A B C : Type} [Field A] [Field B] [Field C]
namespace GlobalTheory.QuadSymbol.NormBaseChange
namespace NormsEscape
theorem _root_.solution [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [FiniteDimensional A B] [FiniteDimensional B C]
    (hodd : Odd (Module.finrank B C)) (h : NormsEscape A C) : NormsEscape A B := by
  intro d hd
  obtain ⟨x, hx0, hx⟩ := h d (by
    rintro ⟨r, hr⟩
    have h1 := congrArg (Algebra.norm B) hr
    obtain ⟨k, hk⟩ := hodd
    rw [IsScalarTower.algebraMap_apply A B C, Algebra.norm_algebraMap, map_mul, hk] at h1
    have h0 : algebraMap A B d ≠ 0 := fun h => hd (h ▸ IsSquare.zero)
    refine hd ⟨Algebra.norm B r / algebraMap A B d ^ k, ?_⟩
    field_simp
    linear_combination h1)
  exact ⟨Algebra.norm B x, Algebra.norm_ne_zero_iff.2 hx0, by rwa [Algebra.norm_norm]⟩
end NormsEscape
end GlobalTheory.QuadSymbol.NormBaseChange
