-- Prove2me | solution 1 for GlobalTheory.HL.PlacesRec.lat_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:45.451706+00:00
-- url     : https://prove2.me/submissions/0f56498d-f8b0-4333-90c1-1b01cbcd0a5f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLattices
import Theorems.Thm_GlobalTheory_HL_PlacesRec_bc_add
import Theorems.Thm_GlobalTheory_HL_PlacesRec_bc_int_smul
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PlacesRec
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {n : ℕ}
variable (A : Places F E sig)
namespace GlobalTheory.HL.PlacesRec
theorem _root_.solution (p : HeightOneSpectrum (𝓞 F)) (S : Set (Fin n → E)) :
    A.lat p (Submodule.span (𝓞 E) S) = Submodule.span (A.L p).O (A.bc p '' S) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span (𝓞 E) S := hy
    induction hy' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : A.bc p (0 : Fin n → E) = 0 := by ext i; simp [Places.bc]
      simp [this]
    | add a b ha' hb' ha hb =>
      rw [SetLike.mem_coe, bc_add]
      exact Submodule.add_mem _ (ha ha') (hb hb')
    | smul o a ha' ha =>
      rw [SetLike.mem_coe, bc_int_smul]
      exact Submodule.smul_mem _ _ (ha ha')
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
end GlobalTheory.HL.PlacesRec
