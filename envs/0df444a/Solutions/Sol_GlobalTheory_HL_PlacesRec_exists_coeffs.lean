-- Prove2me | solution 1 for GlobalTheory.HL.PlacesRec.exists_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:30.916391+00:00
-- url     : https://prove2.me/submissions/8ddb198d-7a9c-47a5-844d-b09d3afab39f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLattices
import Theorems.Thm_GlobalTheory_HL_PlacesRec_exists_common
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
namespace GlobalTheory.HL.PlacesRec
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E))
    (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (φ : Λ →ₗ[𝓞 E] 𝓞 E) :
    ∃ c : Fin n → E, ∀ y : Λ, ∑ k, c k * (y : Fin n → E) k = ((φ y : 𝓞 E) : E) := by
  obtain ⟨D, hD, m⟩ := exists_common Λ hs
  refine ⟨fun k => ((φ ⟨_, m k⟩ : 𝓞 E) : E) / (D : E), fun y => ?_⟩
  obtain ⟨B, hB⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E))
    (fun k => (y : Fin n → E) k)
  choose b hb using hB
  have hDE : (D : E) ≠ 0 := by simpa using hD
  have hB0 : (B : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero B.2
  have hBE : (((B : 𝓞 E)) : E) ≠ 0 := by simpa using hB0
  have hb' : ∀ k, ((b k : 𝓞 E) : E) = ((B : 𝓞 E) : E) * (y : Fin n → E) k := by
    intro k
    have := hb k
    simpa [Algebra.smul_def] using this
  have hb'' : ∀ k, algebraMap (𝓞 E) E (b k) =
      algebraMap (𝓞 E) E (B : 𝓞 E) * (y : Fin n → E) k := hb'
  have h1 : ((B : 𝓞 E) * D) • y = ∑ k, b k • (⟨_, m k⟩ : Λ) := by
    apply Subtype.ext
    ext i
    simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Algebra.smul_def (R := 𝓞 E) (A := E), Pi.single_apply]
    have h4 : ∀ x, algebraMap (𝓞 E) E (b x) * (algebraMap (𝓞 E) E D * if i = x then 1 else 0) =
        if i = x then algebraMap (𝓞 E) E (b x) * algebraMap (𝓞 E) E D else 0 := by
      intro x
      split_ifs <;> simp
    simp only [h4, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul]
    rw [hb'' i]
    ring
  have h2 := congrArg φ h1
  rw [map_smul, map_sum] at h2
  simp only [map_smul, smul_eq_mul] at h2
  have h3 := congrArg (fun t : 𝓞 E => (t : E)) h2
  simp only [map_mul, map_sum] at h3
  have hBD : algebraMap (𝓞 E) E (B : 𝓞 E) * algebraMap (𝓞 E) E D ≠ 0 := mul_ne_zero hBE hDE
  apply mul_left_cancel₀ hBD
  refine Eq.trans ?_ h3.symm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hb'' k]
  have hDE' : algebraMap (𝓞 E) E D ≠ 0 := hDE
  change _ * (algebraMap (𝓞 E) E (φ _) / algebraMap (𝓞 E) E D * _) = _
  field_simp
end GlobalTheory.HL.PlacesRec
