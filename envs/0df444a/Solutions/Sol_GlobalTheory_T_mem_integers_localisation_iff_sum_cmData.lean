-- Prove2me | solution 1 for GlobalTheory.T.mem_integers_localisation_iff_sum_cmData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:12:05.079795+00:00
-- url     : https://prove2.me/submissions/3d4a250d-0b75-408d-854c-97d149561a02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmData
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmDataStatement
import Theorems.Thm_GlobalTheory_LocSpan_mem_O_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), ∀ y : A.Ep, y ∈ A.O ↔ ∃ (n : ℕ) (c : Fin n → 𝒪[A.Fp]) (x : Fin n → 𝓞 E), y = ∑ i, algebraMap A.Fp A.Ep (c i : A.Fp) * A.ιE (x i : E) := by
  first | exact @GlobalTheory.LocSpan.mem_O_iff | exact GlobalTheory.LocSpan.mem_O_iff | (intros; apply GlobalTheory.LocSpan.mem_O_iff <;> assumption)
end _root_.GlobalTheory.T
