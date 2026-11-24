-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.nm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:06:04.909384+00:00
-- url     : https://prove2.me/submissions/b6f6731a-7ea7-462d-adbd-4022823140bc

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
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_nm_norm
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_isSquare_left
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_mul


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
theorem _root_.solution [CharZero A] [Algebra A B] [FiniteDimensional A B] (hB : IndexTwo B)
    (h : NormsEscape A B) {d : A} (hd : d ≠ 0) {x : B} (hx : x ≠ 0) :
    Nm (algebraMap A B d) x ↔ Nm d (Algebra.norm A x) := by
  haveI : CharZero B := charZero_of_injective_algebraMap (algebraMap A B).injective
  refine ⟨nm_norm, fun hn => ?_⟩
  by_cases hs : IsSquare (algebraMap A B d)
  · exact Nm.of_isSquare_left two_ne_zero ((map_ne_zero _).2 hd) hs x
  obtain ⟨y, hy0, hy⟩ := h d hs
  by_contra hc
  have := nm_norm ((hB _ hs).2 y x hy0 hx (fun h => hy (nm_norm h)) hc)
  rw [map_mul] at this
  exact hy (Nm.of_mul (Algebra.norm_ne_zero_iff.2 hx) hn this)
end GlobalTheory.QuadSymbol.NormBaseChange
