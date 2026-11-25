-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_map_fixedField_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:44.260301+00:00
-- url     : https://prove2.me/submissions/05b7b93d-a009-43ca-a985-a9f71b4eb444

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified

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
omit [NumberField F]
namespace GroundTheory.ProfCoh
theorem _root_.solution {M : IntermediateField F Ω} (H : Subgroup Gal(M/F)) (x : Ω) :
    x ∈ (IntermediateField.fixedField H).map M.val ↔ ∃ hx : x ∈ M, ∀ σ ∈ H, σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
  rw [IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun σ hσ => (IntermediateField.mem_fixedField_iff H y).1 hy σ hσ⟩
  · rintro ⟨hx, hfix⟩
    exact ⟨⟨x, hx⟩, (IntermediateField.mem_fixedField_iff H _).2 hfix, rfl⟩
end GroundTheory.ProfCoh
