-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.finite_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:28:14.946686+00:00
-- url     : https://prove2.me/submissions/50f8f61f-6343-4b4a-829d-9b54bc5a5244

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
theorem _root_.solution (y : Om l) : (Set.range fun g : GQ l => g y).Finite := by
  have hy : IsIntegral ℚ_[l] y := Algebra.IsIntegral.isIntegral y
  refine ((minpoly ℚ_[l] y).rootSet_finite (Om l)).subset ?_
  rintro _ ⟨g, rfl⟩
  rw [mem_rootSet]
  refine ⟨minpoly.ne_zero hy, ?_⟩
  change aeval ((g : Om l →ₐ[ℚ_[l]] Om l) y) _ = 0
  rw [aeval_algHom_apply, minpoly.aeval, map_zero]
end GlobalTheory.Cyc.DiffSmall
