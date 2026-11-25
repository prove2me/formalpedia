-- Prove2me | solution 1 for GlobalTheory.T.local_lattice_between_scaled_standard_lattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:06.385588+00:00
-- url     : https://prove2.me/submissions/afe780bd-4941-43f6-8543-e6352e5fc6c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeBetweenScaledStandardLattices
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeBetweenScaledStandardLatticesStatement
import Theorems.Thm_GlobalTheory_HL_Glue_lat_between


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
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (p : HeightOneSpectrum (𝓞 F)) (n : ℕ) (Λ : Submodule (A.L p).O (Fin n → (A.loc p).Ep)), IsLat (A.L p) Λ → (∀ y : (A.loc p).Ep, ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O) → ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (m : (A.loc p).Ep) • v ∈ Λ) ∧ ∀ v ∈ Λ, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O := by
  first | exact @GlobalTheory.HL.Glue.lat_between | exact GlobalTheory.HL.Glue.lat_between | (intros; apply GlobalTheory.HL.Glue.lat_between <;> assumption)
end _root_.GlobalTheory.T
