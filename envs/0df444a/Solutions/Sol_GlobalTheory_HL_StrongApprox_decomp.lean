-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:09:20.676314+00:00
-- url     : https://prove2.me/submissions/4c5717ba-ea34-4144-ad83-03090b96127a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Theorems.Thm_GlobalTheory_HL_StrongApprox_mem_int_of_O
import Theorems.Thm_GlobalTheory_HL_StrongApprox_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.StrongApprox
theorem _root_.solution (A : Places F E sig) (d : E) (hd : sig d = -d) (hd0 : d ≠ 0) (p : HeightOneSpectrum (𝓞 F))
    (y : (A.loc p).Ep) : ∃ a b : (A.loc p).Fp,
      y = algebraMap _ _ a + algebraMap _ _ b * (A.loc p).ιE d ∧
      algebraMap _ _ a = (A.loc p).ιE (algebraMap F E 2⁻¹) * (y + (A.L p).cj y) ∧
      (y ∈ (A.L p).O → (A.loc p).ιE d⁻¹ ∈ (A.L p).O → (A.loc p).ιF 2⁻¹ ∈ 𝒪[(A.loc p).Fp] →
        a ∈ 𝒪[(A.loc p).Fp] ∧ b ∈ 𝒪[(A.loc p).Fp]) := by
  have cjE : ∀ x, (A.L p).cj ((A.loc p).ιE x) = (A.loc p).ιE (sig x) := by
    intro x; rw [A.L_cj]; exact (A.loc p).cj_ιE x
  obtain ⟨u, hu⟩ := ((A.L p).cj_fix (y + (A.L p).cj y)).1 (by rw [map_add, (A.L p).cj_cj, add_comm])
  obtain ⟨w, hw⟩ := ((A.L p).cj_fix ((y - (A.L p).cj y) * (A.loc p).ιE d⁻¹)).1 (by
    rw [map_mul, map_sub, (A.L p).cj_cj, cjE, map_inv₀, hd, inv_neg, map_neg]; ring)
  have hh : algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF 2⁻¹) = (A.loc p).ιE (algebraMap F E 2⁻¹) :=
    ((A.loc p).compat _).symm
  have e1 : (A.loc p).ιE d⁻¹ * (A.loc p).ιE d = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hd0, map_one]
  have e2 : (A.loc p).ιE (algebraMap F E 2⁻¹) * 2 = 1 := by
    have : algebraMap F E 2⁻¹ * 2 = 1 := by
      rw [map_inv₀, map_ofNat]; exact inv_mul_cancel₀ two_ne_zero
    rw [← map_ofNat (A.loc p).ιE 2, ← map_mul, this, map_one]
  refine ⟨u * (A.loc p).ιF 2⁻¹, w * (A.loc p).ιF 2⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, hu, hw, hh]
    linear_combination (-((A.loc p).ιE (algebraMap F E 2⁻¹) * (y - (A.L p).cj y))) * e1 + (-y) * e2
  · rw [map_mul, hu, hh, mul_comm]
  · intro hy hdi h2i
    have hcy := cj_mem A p y hy
    refine ⟨mul_mem (mem_int_of_O A p u (hu ▸ add_mem hy hcy)) h2i,
      mul_mem (mem_int_of_O A p w (hw ▸ mul_mem (sub_mem hy hcy) hdi)) h2i⟩
end GlobalTheory.HL.StrongApprox
