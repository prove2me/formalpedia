-- Prove2me | solution 1 for GlobalTheory.CycEigen.aeval_prod_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:55:55.53494+00:00
-- url     : https://prove2.me/submissions/c4ade28c-9dd7-4906-bce3-b372417320d4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrame
import Theorems.Thm_GlobalTheory_CycEigen_aeval_eq_zero_of_eigenbasis
import Theorems.Thm_GlobalTheory_CycEigen_eigen_of_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.CycEigen
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → Polynomial.aeval (U g) (∏ u ∈ J, (Polynomial.X - Polynomial.C (chiC χ (-u) g))) = 0 := by
  intro l _ act χ hact hχ K m r hm U g hF J ⟨e, u, he, hu, hfix⟩
  refine aeval_eq_zero_of_eigenbasis (U g) e he (fun k => chiC χ (-(u k)) g)
    (fun k => eigen_of_fixed hact hχ hm hF (u k) (e k) fun σ hσ => hfix σ hσ k) _ fun k => ?_
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_coe.1 (hu k)) (by simp)
end GlobalTheory.CycEigen
