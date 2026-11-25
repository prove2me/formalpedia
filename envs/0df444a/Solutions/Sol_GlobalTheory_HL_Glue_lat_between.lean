-- Prove2me | solution 1 for GlobalTheory.HL.Glue.lat_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:15.380106+00:00
-- url     : https://prove2.me/submissions/d60d01f7-6029-4b41-a26d-5cafdbdbfac5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeBetweenScaledStandardLattices
import Theorems.Thm_GlobalTheory_HL_Glue_exists_nat_between

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Glue
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.Glue
theorem _root_.solution (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (Λ : Submodule (A.L p).O (Fin n → (A.loc p).Ep)) (hΛ : IsLat (A.L p) Λ)
    (hd : ∀ y : (A.loc p).Ep, ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O) :
    ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (m : (A.loc p).Ep) • v ∈ Λ) ∧
      ∀ v ∈ Λ, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O :=
  exists_nat_between Λ hΛ.1 hΛ.2 hd
end GlobalTheory.HL.Glue
