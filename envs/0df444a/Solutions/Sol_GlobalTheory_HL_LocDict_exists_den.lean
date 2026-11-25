-- Prove2me | solution 1 for GlobalTheory.HL.LocDict.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:58.48112+00:00
-- url     : https://prove2.me/submissions/5b62c57d-fd8c-4103-ad71-49ffbb11d6e4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_exists_trace_norm
import Theorems.Thm_GlobalTheory_HL_PlacesInt_isIntegral_of_quad
import Theorems.Thm_GlobalTheory_HL_PlacesInt_mem_O_iff
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocDict
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.LocDict
theorem _root_.solution (c : E) (hc : (A.loc p).ιE c ∈ (A.L p).O) :
    ∃ s : 𝓞 F, s ∉ p.asIdeal ∧ ∃ o : 𝓞 E, algebraMap (𝓞 F) E s * c = algebraMap (𝓞 E) E o := by
  obtain ⟨t, k, ht, hk⟩ := PlacesInt.exists_trace_norm A c
  obtain ⟨h1, h2⟩ := (PlacesInt.mem_O_iff A p c t k ht hk).1 hc
  obtain ⟨a, d, had⟩ := p.exists_primeCompl_mul_eq_of_integer t h1
  obtain ⟨b, e, hbe⟩ := p.exists_primeCompl_mul_eq_of_integer k h2
  have e1 : algebraMap (𝓞 F) E a = algebraMap F E t * algebraMap (𝓞 F) E d := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, ← had, map_mul,
      ← IsScalarTower.algebraMap_apply]
  have e2 : algebraMap (𝓞 F) E b = algebraMap F E k * algebraMap (𝓞 F) E e := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, ← hbe, map_mul,
      ← IsScalarTower.algebraMap_apply]
  have hi : IsIntegral (𝓞 F) (algebraMap (𝓞 F) E ((d : 𝓞 F) * e) * c) :=
    PlacesInt.isIntegral_of_quad _ (algebraMap (𝓞 F) E ((d : 𝓞 F) * e) * sig c)
      (a * e) ((d : 𝓞 F) ^ 2 * e * b)
      (by simp only [map_mul, e1, ht]; ring)
      (by simp only [map_mul, map_pow, e2, hk]; ring)
  exact ⟨(d : 𝓞 F) * e, fun h => (p.isPrime.mem_or_mem h).elim d.2 e.2,
    ⟨_, isIntegral_trans (R := ℤ) _ hi⟩, rfl⟩
end GlobalTheory.HL.LocDict
