-- Prove2me | solution 1 for GlobalTheory.Cyc.Ks_eq_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:23.50066+00:00
-- url     : https://prove2.me/submissions/f4168304-4292-4c40-9eee-fd7da62b8a74

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (K : FinExt l) (j : ℕ) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) :
    Ks K j = ((↥(K0 K))⟮ζ⟯).restrictScalars ℚ_[l] := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ j) := ⟨(pow_pos hlp.pos j).ne'⟩
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, Ks]
  congr 1
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ ζ) i
  · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2 hζ.pow_eq_one)
end GlobalTheory.Cyc
