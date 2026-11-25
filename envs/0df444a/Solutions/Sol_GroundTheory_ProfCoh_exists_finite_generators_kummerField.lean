-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_finite_generators_kummerField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:58.459141+00:00
-- url     : https://prove2.me/submissions/98cb73d8-fe9e-484b-a3fb-30006d77b266

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerCorrespondence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial IntermediateField
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω]
namespace GroundTheory.ProfCoh
theorem _root_.solution [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) :
    ∃ r : Δ → Ω, (∀ x : Δ, ∃ a : Kˣ, (a : UnitsModPow K n) = x ∧ r x ^ n = algebraMap K Ω a) ∧
      kummerField K n Ω Δ = adjoin K (Set.range r) := by
  choose r hr using fun x : Δ => exists_pow_eq_algebraMap K n Ω (x : UnitsModPow K n).out
  refine ⟨r, fun x => ⟨_, QuotientGroup.out_eq' _, hr x⟩, le_antisymm ?_ ?_⟩
  · rw [kummerField, adjoin_le_iff]
    rintro α ⟨a, ha, hα⟩
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_mul (K := K)
      (QuotientGroup.out_eq' (a : UnitsModPow K n)).symm hα (hr ⟨_, ha⟩)
    rw [SetLike.mem_coe, hc]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (subset_adjoin _ _ ⟨_, rfl⟩)
  · rw [kummerField, adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    refine subset_adjoin _ _ ⟨(x : UnitsModPow K n).out, ?_, hr x⟩
    rw [QuotientGroup.out_eq']
    exact x.2
end GroundTheory.ProfCoh
