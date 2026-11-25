-- Prove2me | solution 1 for GlobalTheory.T.localLattice_le_completion_glued_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:14.621662+00:00
-- url     : https://prove2.me/submissions/320d4c47-ccd2-40cd-a40b-6fe30ccd4294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeLeCompletionGluedLattice
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeLeCompletionGluedLatticeStatement
import Theorems.Thm_GlobalTheory_HL_Glue_local_le_lat_of_approx


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
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), (∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p) → (∀ p (v : Fin n → (A.loc p).Ep), (∀ i, v i ∈ (A.L p).O) → (N : (A.loc p).Ep) • v ∈ Λ p) → (∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite → ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = (N : (A.loc p).Ep) * o) → ∀ p, Λ p ≤ A.lat p Γ := by
  first | exact @GlobalTheory.HL.Glue.local_le_lat_of_approx | exact GlobalTheory.HL.Glue.local_le_lat_of_approx | (intros; apply GlobalTheory.HL.Glue.local_le_lat_of_approx <;> assumption)
end _root_.GlobalTheory.T
