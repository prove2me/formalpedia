-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.sig_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:18.594855+00:00
-- url     : https://prove2.me/submissions/03bfb555-1af3-4736-b79e-ca37cc9f9eb6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Theorems.Thm_GlobalTheory_HL_StrongApprox_exists_place
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.StrongApprox
theorem _root_.solution (A : Places F E sig) : ∃ e : E, sig e ≠ e := by
  by_contra hne
  push_neg at hne
  obtain ⟨p⟩ := exists_place F
  have h2 : ∀ z, (A.loc p).cj z = z := by
    intro z
    have hz : z ∈ Submodule.span (A.loc p).Fp (Set.range (A.loc p).ιE) := by
      rw [(A.loc p).span]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨y, rfl⟩ := hz; rw [(A.loc p).cj_ιE, hne]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  have h3 : Function.Surjective (Algebra.linearMap (A.loc p).Fp (A.loc p).Ep) := by
    intro z
    exact ((A.L p).cj_fix z).1 (by rw [A.L_cj]; exact h2 z)
  have h4 := LinearMap.finrank_le_finrank_of_surjective h3
  rw [(A.loc p).rank, Module.finrank_self] at h4
  omega
end GlobalTheory.HL.StrongApprox
