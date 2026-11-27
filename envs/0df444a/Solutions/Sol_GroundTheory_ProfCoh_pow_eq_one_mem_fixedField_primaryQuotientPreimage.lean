-- Prove2me | solution 1 for GroundTheory.ProfCoh.pow_eq_one_mem_fixedField_primaryQuotientPreimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:50:49.028815+00:00
-- url     : https://prove2.me/submissions/96b4da74-f4dc-4a89-8201-90dbba46fe0d

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_mem_primaryPart_iff_of_comm
import Theorems.Thm_GroundTheory_ProfCoh_algEquiv_apply_eq_of_pow_prime_pow_apply_eq
import Theorems.Thm_GroundTheory_ProfCoh_natCast_residueField_ne_zero
import Theorems.Thm_GroundTheory_ProfCoh_apply_eq_of_mem_lowerRamificationGroup_zero

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
open GroundTheory.LocalField ValuativeRel IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution {l : ℕ} (hl : l.Prime)
    (hlp : l ≠ ringChar 𝓀[K]) {ζ : L} (hζ : ζ ^ l = 1) :
    ζ ∈ fixedField (primaryQuotientPreimage (lowerRamificationGroup K L 0) l) := by
  refine (mem_fixedField_iff _ _).2 fun σ hσ ↦ ?_
  have hcomm : ∀ a b : (L ≃ₐ[K] L) ⧸ lowerRamificationGroup K L 0, a * b = b * a :=
    fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  rw [primaryQuotientPreimage, Subgroup.mem_comap, mem_primaryPart_iff_of_comm hl hcomm] at hσ
  obtain ⟨n, hn⟩ := hσ
  have h0 : σ ^ l ^ n ∈ lowerRamificationGroup K L 0 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← QuotientGroup.mk'_apply, ← hn,
      pow_orderOf_eq_one]
  exact algEquiv_apply_eq_of_pow_prime_pow_apply_eq hl hζ σ
    (apply_eq_of_mem_lowerRamificationGroup_zero (natCast_residueField_ne_zero K L hl hlp) h0 hζ)
end GroundTheory.ProfCoh
