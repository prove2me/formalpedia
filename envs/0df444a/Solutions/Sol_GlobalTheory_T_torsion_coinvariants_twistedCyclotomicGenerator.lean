-- Prove2me | solution 1 for GlobalTheory.T.torsion_coinvariants_twistedCyclotomicGenerator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:36:07.961382+00:00
-- url     : https://prove2.me/submissions/7e884dca-0691-4281-8fbb-f489494f89d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGeneratorStatement
import Theorems.Thm_GlobalTheory_CycCoinv_torsion_coinvariants


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (w w' : Fin r → PadicComplex l) (k : ℕ), (∀ a, w a ∈ Ohat K) → (∀ a, w' a ∈ Ohat K) → twAct act χ i U g w' - w' = (l : PadicComplex l) ^ k • w → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Ohat K) ∧ twAct act χ i U g y - y = (l : PadicComplex l) ^ (max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • w := by
  first | exact @GlobalTheory.CycCoinv.torsion_coinvariants | exact GlobalTheory.CycCoinv.torsion_coinvariants | (intros; apply GlobalTheory.CycCoinv.torsion_coinvariants <;> assumption)
end _root_.GlobalTheory.T
