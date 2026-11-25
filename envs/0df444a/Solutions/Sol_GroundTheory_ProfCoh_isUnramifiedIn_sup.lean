-- Prove2me | solution 1 for GroundTheory.ProfCoh.isUnramifiedIn_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:22.458704+00:00
-- url     : https://prove2.me/submissions/a8e10464-79e5-4fee-878d-bbd11f9bc4b7

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedIn_iff_le_fixedField
import Theorems.Thm_GroundTheory_ProfCoh_exists_finiteGalois_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable [IsGalois F Ω]
namespace GroundTheory.ProfCoh
theorem _root_.solution {E₁ E₂ : IntermediateField F Ω} [FiniteDimensional F E₁]
    [FiniteDimensional F E₂] (v : HeightOneSpectrum (𝓞 F))
    (h₁ : Algebra.IsUnramifiedIn (𝓞 E₁) v.asIdeal) (h₂ : Algebra.IsUnramifiedIn (𝓞 E₂) v.asIdeal) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E₁ ⊔ E₂)) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le (E₁ ⊔ E₂)
  rw [isUnramifiedIn_iff_le_fixedField hM]
  rw [isUnramifiedIn_iff_le_fixedField (le_sup_left.trans hM)] at h₁
  rw [isUnramifiedIn_iff_le_fixedField (le_sup_right.trans hM)] at h₂
  exact fun Q hQ hQv => sup_le (h₁ Q hQ hQv) (h₂ Q hQ hQv)
end GroundTheory.ProfCoh
