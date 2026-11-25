-- Prove2me | solution 1 for GlobalTheory.HL.LocDict.bc_mem_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:45:10.135793+00:00
-- url     : https://prove2.me/submissions/14a538c4-a2a7-4f46-a267-c46370553938

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Theorems.Thm_GlobalTheory_HL_PlacesInt_mem_int_iff


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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.LocDict
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) (a : 𝓞 F)
    (ha : a ∉ p.asIdeal) (h : algebraMap (𝓞 F) (𝓞 E) a • x ∈ Λ) : A.bc p x ∈ A.lat p Λ := by
  have hv : p.valuation F (algebraMap (𝓞 F) F a) = 1 :=
    le_antisymm (p.valuation_le_one a)
      (not_lt.1 fun hlt => ha ((p.valuation_lt_one_iff_mem (K := F) a).1 hlt))
  have hinv : p.valuation F (algebraMap (𝓞 F) F a)⁻¹ ≤ 1 := by rw [map_inv₀, hv, inv_one]
  have hO := (PlacesInt.mem_int_iff (A.loc p) _).2 hinv
  have ha0 : algebraMap (𝓞 F) F a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  let w : (A.L p).O := ⟨algebraMap (A.loc p).Fp (A.loc p).Ep
      ((A.loc p).ιF (algebraMap (𝓞 F) F a)⁻¹), ((A.L p).O_def _).2 (by
    have : IsIntegral 𝒪[(A.loc p).Fp] (algebraMap 𝒪[(A.loc p).Fp] (A.loc p).Ep ⟨_, hO⟩) :=
      isIntegral_algebraMap
    exact this)⟩
  have e : A.bc p x = w • A.bc p (algebraMap (𝓞 F) (𝓞 E) a • x) := by
    funext i
    have h1 : (A.loc p).ιE (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)) =
        algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF (algebraMap (𝓞 F) F a)) := by
      rw [← (A.loc p).compat, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 F) F E]
    change (A.loc p).ιE (x i) = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((A.loc p).ιF (algebraMap (𝓞 F) F a)⁻¹) *
        (A.loc p).ιE (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) * x i)
    rw [map_mul, h1, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ ha0, map_one, map_one,
      one_mul]
  rw [e]
  exact Submodule.smul_mem _ w (Submodule.subset_span ⟨_, h, rfl⟩)
end GlobalTheory.HL.LocDict
