-- Prove2me | solution 1 for GlobalTheory.CycEigen.root_mem_inC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:28:41.950888+00:00
-- url     : https://prove2.me/submissions/1127da14-fb51-43ee-a2b8-2e08ee05a74e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis

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
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycEigen
theorem _root_.solution (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {ζ : PadicComplex l}
    (h : IsPrimitiveRoot ζ l) : ζ ∈ inC (Ks K j) := by
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hη' := hη.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  obtain ⟨k, -, hk⟩ := hη'.eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨η ^ k, ?_, ?_⟩
  · refine pow_mem (?_ : η ∈ Ks K j) k
    refine (le_sup_right : _ ≤ Ks K j) (IntermediateField.subset_adjoin _ _ ?_)
    exact (hη.pow_eq_one_iff_dvd _).2 (dvd_pow_self l (by omega))
  · simp only [PadicComplex.coe_eq, map_pow]
    exact hk
end GlobalTheory.CycEigen
