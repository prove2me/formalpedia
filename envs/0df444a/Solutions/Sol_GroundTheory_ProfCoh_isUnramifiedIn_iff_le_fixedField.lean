-- Prove2me | solution 1 for GroundTheory.ProfCoh.isUnramifiedIn_iff_le_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:37.68225+00:00
-- url     : https://prove2.me/submissions/c64418f5-9b28-4f71-ae17-dd7620bf2d5b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedIn_iff_inertia
import Theorems.Thm_GroundTheory_ProfCoh_mem_map_fixedField_iff

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
namespace GroundTheory.ProfCoh
theorem _root_.solution {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        E ≤ (IntermediateField.fixedField (Q.inertia Gal(M/F))).map M.val := by
  rw [isUnramifiedIn_iff_inertia h]
  refine forall_congr' fun Q => forall_congr' fun _ => forall_congr' fun _ => ?_
  constructor
  · intro hI x hx
    exact (mem_map_fixedField_iff _ x).2 ⟨h hx, fun σ hσ => hI σ hσ x hx⟩
  · intro hle σ hσ x hx
    obtain ⟨_, hfix⟩ := (mem_map_fixedField_iff _ x).1 (hle hx)
    exact hfix σ hσ
end GroundTheory.ProfCoh
