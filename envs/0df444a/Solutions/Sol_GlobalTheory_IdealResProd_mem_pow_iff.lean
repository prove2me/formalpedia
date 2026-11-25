-- Prove2me | solution 1 for GlobalTheory.IdealResProd.mem_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:43.748081+00:00
-- url     : https://prove2.me/submissions/6c3897c3-d4a6-4fda-b44c-ba29465fe9da

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AbsNormEqFinprod
import Theorems.Thm_GlobalTheory_IdealResProd_val_le_iff
import Theorems.Thm_GlobalTheory_IdealResProd_val_unif
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_val_le_iff
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
open GlobalTheory GlobalTheory.IdealResProd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable {p : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.IdealResProd
theorem _root_.solution (A : LocAt F E sig p) {ϖ : 𝒪[A.Fp]} (hϖ : Irreducible ϖ) (x : 𝓞 F) (n : ℕ) :
    x ∈ p.asIdeal ^ n ↔ valuation A.Fp (A.ιF x) ≤ valuation A.Fp ϖ ^ n := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer F
  rw [← val_unif A hϖ hπ, ← map_pow, ← map_pow, val_le_iff, map_pow, hπ, ← WithZero.exp_nsmul,
    ← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  simp
end GlobalTheory.IdealResProd
