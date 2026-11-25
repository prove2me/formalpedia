-- Prove2me | solution 1 for GlobalTheory.HL.PlacesRec.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:26.304377+00:00
-- url     : https://prove2.me/submissions/5629413a-69f3-4ee3-8600-30806c3e8374

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLattices
import Theorems.Thm_GlobalTheory_HL_PlacesRec_exists_smul_mem

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
    (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ D : 𝓞 E, D ≠ 0 ∧ ∀ k, D • (Pi.single k 1 : Fin n → E) ∈ Λ := by
  choose Dk h m using fun k => exists_smul_mem Λ hs (Pi.single k 1 : Fin n → E)
  refine ⟨∏ k, Dk k, Finset.prod_ne_zero_iff.2 fun k _ => h k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), mul_comm, mul_smul]
  exact Λ.smul_mem _ (m k)
end GlobalTheory.HL.PlacesRec
