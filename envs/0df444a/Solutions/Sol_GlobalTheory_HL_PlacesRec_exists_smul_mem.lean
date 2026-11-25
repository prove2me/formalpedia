-- Prove2me | solution 1 for GlobalTheory.HL.PlacesRec.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:39:25.274417+00:00
-- url     : https://prove2.me/submissions/ce7eebc9-e290-42f7-b7f2-b97c032b58a3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLattices
import Theorems.Thm_GlobalTheory_SaturatedSublattice_main


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PlacesRec
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {n : ℕ}
namespace GlobalTheory.HL.PlacesRec
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E))
    (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ D : 𝓞 E, D ≠ 0 ∧ D • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.SaturatedSublattice.main
  | exact _root_.GlobalTheory.SaturatedSublattice.main
  | (apply _root_.GlobalTheory.SaturatedSublattice.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedSublattice.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedSublattice.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedSublattice.main ..)
end GlobalTheory.HL.PlacesRec
