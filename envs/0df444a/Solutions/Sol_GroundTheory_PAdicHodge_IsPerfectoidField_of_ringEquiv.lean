-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:26:43.292851+00:00
-- url     : https://prove2.me/submissions/2d4a9616-c317-4697-ab7a-78d090734b04

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_pow_of_norm
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_norm_sub_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {F F' : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [NontriviallyNormedField F'] [IsUltrametricDist F'] (p : ℕ) [Fact p.Prime]
    [IsPerfectoidField F p] (e : F ≃+* F') (he : ∀ x, ‖e x‖ = ‖x‖) : IsPerfectoidField F' p := by
  have := completeSpace (K := F) p
  have hiso : Isometry e := Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, he]
  let ie : F ≃ᵢ F' := { e.toEquiv with isometry_toFun := hiso }
  have he' : ∀ y, ‖e.symm y‖ = ‖y‖ := fun y => by
    conv_rhs => rw [← e.apply_symm_apply y]
    rw [he]
  have hpF : ‖(p : F')‖ = ‖(p : F)‖ := by rw [← map_natCast e p, he]
  exact
    { complete := ie.symm.completeSpace
      norm_natCast_lt_one := hpF ▸ norm_natCast_lt_one (K := F) (p := p)
      exists_norm_mem_Ioo := fun r hr => by
        obtain ⟨x, h1, h2⟩ := exists_norm_mem_Ioo (K := F) (p := p) r hr
        exact ⟨e x, by rwa [he], by rwa [he]⟩
      surjective_pow := surjective_pow_of_norm p fun y hy => by
        obtain ⟨x, hx1, hx⟩ := exists_norm_sub_pow_le p (x := e.symm y) (by rwa [he'])
        refine ⟨e x, by rwa [he], ?_⟩
        have hyx : y - e x ^ p = e (e.symm y - x ^ p) := by
          rw [map_sub, map_pow, e.apply_symm_apply]
        rw [hpF, hyx, he]
        exact hx }
end GroundTheory.PAdicHodge.IsPerfectoidField
