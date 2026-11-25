-- Prove2me | solution 1 for GlobalTheory.HL.GlueInt.sig_ne_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:38:27.246662+00:00
-- url     : https://prove2.me/submissions/cbf6b723-3523-40bf-b60d-6cb25b386086

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfIntegralAllQuadraticCompletions
import Theorems.Thm_P2M_GlobalTheory_HL_GlueInt_nonempty_place__c700acea4894
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlueInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.GlueInt
theorem _root_.solution (A : Places F E sig) : ¬ ∀ y, sig y = y := by
  intro h
  obtain ⟨p⟩ := nonempty_place' (F := F)
  have hcj : (A.L p).cj.toLinearMap = LinearMap.id :=
    LinearMap.ext_on_range (A.loc p).span fun y => by
      simp [A.L_cj, (A.loc p).cj_ιE, h]
  have hall : ∀ z : (A.loc p).Ep, ∃ c : (A.loc p).Fp, c • (1 : (A.loc p).Ep) = z := fun z => by
    obtain ⟨a, ha⟩ := ((A.L p).cj_fix z).1 (by simpa using LinearMap.congr_fun hcj z)
    exact ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
  have := finrank_le_one (1 : (A.loc p).Ep) hall
  rw [(A.loc p).rank] at this
  norm_num at this
end GlobalTheory.HL.GlueInt
