-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.prim_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:31:36.35+00:00
-- url     : https://prove2.me/submissions/96db1d3c-f7ef-456f-86f8-e7ba3feef4ea

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_exists_prim
import Theorems.Thm_GlobalTheory_Cyc_TateS_coe_inj
import Theorems.Thm_GlobalTheory_TateDecomp_exists_prim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.TateS
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.TateS
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ n) :
    ∃ z : Om l, algebraMap _ _ z = ζ ∧ IsPrimitiveRoot z n := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨z, hz⟩ := exists_prim (l := l) n hn
  have hz' := hz.map_of_injective (coe_inj (l := l))
  obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨z ^ i, by rw [map_pow, hi], ?_⟩
  apply IsPrimitiveRoot.of_map_of_injective _ (coe_inj (l := l))
  rw [map_pow, hi]
  exact h
end GlobalTheory.Cyc.TateS
