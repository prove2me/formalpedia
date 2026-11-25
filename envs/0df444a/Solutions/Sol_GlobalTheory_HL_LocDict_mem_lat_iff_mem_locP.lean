-- Prove2me | solution 1 for GlobalTheory.HL.LocDict.mem_lat_iff_mem_locP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:58.711175+00:00
-- url     : https://prove2.me/submissions/c344f099-05ec-47df-bf3e-3747b992716a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Theorems.Thm_GlobalTheory_HL_LocDict_exists_smul_mem
import Theorems.Thm_GlobalTheory_HL_LocDict_exists_base_smul_mem
import Theorems.Thm_GlobalTheory_HL_LocDict_bc_mem_of_smul_mem

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocDict
namespace GlobalTheory.HL.LocDict
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG → ∀ (p : HeightOneSpectrum (𝓞 F)) (x : Fin n → E), (A.bc p x ∈ A.lat p Λ ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) := by
  intro F E _ _ _ _ _ sig A n Λ hΛ p x
  constructor
  · intro hx P hP
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem A p Λ hΛ x hx
    haveI := P.isPrime
    refine ⟨algebraMap (𝓞 F) (𝓞 E) s, fun h => hs ?_, hsx⟩
    rw [← hP]
    exact h
  · intro h
    obtain ⟨a, ha, hax⟩ := exists_base_smul_mem A p Λ x fun P hP => by
      haveI := P.isPrime
      obtain ⟨s, hs, hsx⟩ := h P hP
      exact ⟨s, hs, hsx⟩
    exact bc_mem_of_smul_mem A p Λ x a ha hax
end GlobalTheory.HL.LocDict
