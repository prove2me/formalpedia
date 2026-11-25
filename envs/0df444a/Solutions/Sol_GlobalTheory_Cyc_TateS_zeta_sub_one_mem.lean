-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.zeta_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:56:31.281876+00:00
-- url     : https://prove2.me/submissions/be27d0fc-fac2-4671-a884-7c901468e2e4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_root_mem
import Theorems.Thm_GlobalTheory_Cyc_TateS_prim_lift
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono


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
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
namespace GlobalTheory.Cyc.TateS
theorem _root_.solution (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (hζ : IsPrimitiveRoot ζ l) : ζ - 1 ∈ intC (Ks K j) := by
  have hp : l.Prime := Fact.out
  refine ⟨?_, ?_⟩
  · obtain ⟨ζ₀, rfl, hζ₀⟩ := prim_lift hp.ne_zero hζ
    exact mem_inC.2 ⟨ζ₀ - 1, sub_mem (Ks_mono K hj (root_mem K (by rw [pow_one, hζ₀.pow_eq_one])))
      (one_mem _), by rw [map_sub, map_one]⟩
  · have h1 : ‖ζ‖ = 1 := by
      have := congrArg norm hζ.pow_eq_one
      rw [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 this
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    simp [h1]
end GlobalTheory.Cyc.TateS
