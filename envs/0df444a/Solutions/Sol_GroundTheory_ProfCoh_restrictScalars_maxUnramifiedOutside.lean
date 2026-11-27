-- Prove2me | solution 1 for GroundTheory.ProfCoh.restrictScalars_maxUnramifiedOutside
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:50:57.905898+00:00
-- url     : https://prove2.me/submissions/75da1a94-8cfb-405e-acad-9bbbe30b0bbf

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedOutside_iff_le_maxUnramifiedOutside
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedOutside_restrictScalars_iff
import Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_sup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable [IsGalois F Ω]
namespace GroundTheory.ProfCoh
theorem _root_.solution {L : IntermediateField F Ω} [FiniteDimensional F L]
    (hL : L ≤ maxUnramifiedOutside F Ω S) :
    (maxUnramifiedOutside L Ω (placesOver S)).restrictScalars F = maxUnramifiedOutside F Ω S := by
  have := NumberField.of_module_finite F L
  have hLu : IsUnramifiedOutside S L :=
    (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hL
  ext x
  rw [IntermediateField.mem_restrictScalars]
  constructor
  · intro hx
    obtain ⟨M, hf, hu, hxM⟩ := (mem_maxUnramifiedOutside_iff (placesOver S)).1 hx
    have : FiniteDimensional F (M.restrictScalars F) := FiniteDimensional.trans F L M
    exact le_maxUnramifiedOutside S
      ((isUnramifiedOutside_restrictScalars_iff S hLu M).2 hu) hxM
  · intro hx
    obtain ⟨E, hf, hu, hxE⟩ := (mem_maxUnramifiedOutside_iff S).1 hx
    let M : IntermediateField L Ω := IntermediateField.extendScalars (le_sup_left : L ≤ L ⊔ E)
    have : FiniteDimensional F M := (inferInstance : FiniteDimensional F ↥(L ⊔ E))
    have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
    have hMu : IsUnramifiedOutside S (M.restrictScalars F) := hLu.sup hu
    exact le_maxUnramifiedOutside (placesOver S)
      ((isUnramifiedOutside_restrictScalars_iff S hLu M).1 hMu)
      (le_sup_right (α := IntermediateField F Ω) hxE)
end GroundTheory.ProfCoh
