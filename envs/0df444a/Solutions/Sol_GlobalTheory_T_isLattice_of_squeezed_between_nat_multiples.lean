-- Prove2me | solution 1 for GlobalTheory.T.isLattice_of_squeezed_between_nat_multiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:10.917259+00:00
-- url     : https://prove2.me/submissions/96c7d5be-36c8-4f98-9361-19a70a32f477

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLatticeOfSqueezedBetweenNatMultiples
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLatticeOfSqueezedBetweenNatMultiplesStatement
import Theorems.Thm_GlobalTheory_glue_latt_isLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E], ∀ (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → (∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ) → (∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) → Submodule.IsLattice E Γ := by
  first | exact @GlobalTheory.glue_latt_isLattice | exact GlobalTheory.glue_latt_isLattice | (intros; apply GlobalTheory.glue_latt_isLattice <;> assumption)
end _root_.GlobalTheory.T
