-- Prove2me | solution 1 for GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:44:59.952706+00:00
-- url     : https://prove2.me/submissions/f9d4b636-77d4-4ff9-b987-81603ea3f7c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Theorems.Thm_GlobalTheory_Cyc_gen_dense


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → (∃ g, IsGen χ K j g) ∧ ∀ g, IsGen χ K j g → ((∀ b : ℕ, IsGen χ K (j + b) (g ^ (l ^ b))) ∧ (∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n) ∧ (Gj K j : Set (GQ l)) ⊆ closure {x | ∃ h ∈ Hinf K, ∃ a : ℕ, x = h * g ^ a}) := by
  first | exact @GlobalTheory.Cyc.gen_dense | exact GlobalTheory.Cyc.gen_dense | (intros; apply GlobalTheory.Cyc.gen_dense <;> assumption)
end _root_.GlobalTheory.T
