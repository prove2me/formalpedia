-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.normsEscape_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:10.054111+00:00
-- url     : https://prove2.me/submissions/dbd3015c-a198-48d6-96cc-472d05d66077

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
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_mul
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_sq


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
theorem _root_.solution [Algebra A B] (hA : IndexTwo A) (hodd : Odd (Module.finrank A B)) :
    NormsEscape A B := by
  intro d hd
  obtain ⟨c, hc0, hc⟩ := (hA d fun h => hd (h.map _)).1
  refine ⟨algebraMap A B c, (map_ne_zero _).2 hc0, fun h => hc ?_⟩
  obtain ⟨k, hk⟩ := hodd
  rw [Algebra.norm_algebraMap, hk] at h
  refine Nm.of_mul (pow_ne_zero 2 (pow_ne_zero k hc0)) (Nm.sq _ _) ?_
  rwa [show c * (c ^ k) ^ 2 = c ^ (2 * k + 1) by ring]
end GlobalTheory.QuadSymbol.NormBaseChange
