-- Prove2me | solution 1 for GlobalTheory.HL.SAN.bc_eQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:42:32.390658+00:00
-- url     : https://prove2.me/submissions/685cbcd9-838c-4393-a285-a86b219d4eeb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_RatExt_rational_extend
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SAN
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.SAN
namespace _root_.GlobalTheory.HL.SAN
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (x u : Fin N → E) (s : E) (v : Fin N → E) :
    A.bc p (_root_.GlobalTheory.HL.SAN.eQ sig Hm x u s v) =
      _root_.GlobalTheory.HL.eich (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p u) ((A.loc p).ιE s) (A.bc p v) := by
  have h5 := (_root_.GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm
  have hu := h5 v u
  have hx := h5 v x
  unfold _root_.GlobalTheory.HL.eich
  rw [hu, hx]
  funext i
  simp [_root_.GlobalTheory.HL.Places.bc, _root_.GlobalTheory.HL.SAN.eQ, _root_.GlobalTheory.HL.SAN.hq]
end _root_.GlobalTheory.HL.SAN
end GlobalTheory.HL.SAN
