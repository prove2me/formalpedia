-- Prove2me | solution 1 for GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:17.251329+00:00
-- url     : https://prove2.me/submissions/9cade42d-e3ee-4659-9f95-3716f73227ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeckeCharOnIdMulSqrtAbsNormInvMemSubring
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeckeCharOnIdMulSqrtAbsNormInvMemSubringStatement
import Theorems.Thm_GlobalTheory_HeckeIdealValue_inv_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (O : Subring ℂ) (cc : Ideal (𝓞 L)), cc ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 L), cc ≤ P.asIdeal → (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) → (((χ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc) : ℝ) : ℂ))⁻¹ ∈ O := by
  first | exact @GlobalTheory.HeckeIdealValue.inv_mem | exact GlobalTheory.HeckeIdealValue.inv_mem | (intros; apply GlobalTheory.HeckeIdealValue.inv_mem <;> assumption)
end _root_.GlobalTheory.T
