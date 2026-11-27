-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.exists_finset_sup_sIdeles_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:31.474071+00:00
-- url     : https://prove2.me/submissions/84e33290-beb8-4db3-a8cd-c4b12bf16f22

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroup_le_sIdeles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S : Set (HeightOneSpectrum (𝓞 K)))
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  classical
  choose x hx using toClassGroup_surjective (K := K)
  let S : Finset (HeightOneSpectrum (𝓞 K)) := Finset.univ.biUnion fun c ↦
    (Filter.eventually_cofinite.1 (eventually_ord_eq_zero (x c))).toFinset
  have hxS : ∀ c, x c ∈ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro c v hv
    by_contra h
    exact hv (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ c, Set.Finite.mem_toFinset _ |>.2 h⟩)
  refine ⟨S, eq_top_iff.2 fun y _ ↦ ?_⟩
  have hker : y * (x (toClassGroup y))⁻¹ ∈ (toClassGroup (K := K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]
  rw [ker_toClassGroup] at hker
  have h := mul_mem (sup_le_sup_left (standardOpenSubgroup_le_sIdeles _) _ hker)
    (Subgroup.mem_sup_right (hxS (toClassGroup y)))
  rwa [inv_mul_cancel_right] at h
end GroundTheory.Global.IdeleGroup
