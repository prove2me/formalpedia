-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.finite_Ks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:33.654846+00:00
-- url     : https://prove2.me/submissions/e4b73c49-b43a-44e5-bb9a-8e636112a837

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.DiffSmall
theorem _root_.solution (K : FinExt l) (i : ℕ) : FiniteDimensional ℚ_[l] (Ks K i) := by
  classical
  have hl : l.Prime := Fact.out
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  haveI : Finite {x : Om l | x ^ (l ^ i) = 1} := by
    refine ((Polynomial.nthRoots (l ^ i) (1 : Om l)).toFinset.finite_toSet.subset ?_).to_subtype
    intro x hx
    simpa [mem_nthRoots (pow_pos hl.pos i)] using hx
  haveI := IntermediateField.finiteDimensional_adjoin (K := ℚ_[l]) (S := {x : Om l | x ^ (l ^ i) = 1})
    fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _
end GlobalTheory.Cyc.DiffSmall
