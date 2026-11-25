-- Prove2me | solution 1 for GroundTheory.Global.range_powMonoidHom_sup_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:56.69744+00:00
-- url     : https://prove2.me/submissions/d641831e-eb16-41d2-84db-81ab49afdd2c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex

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
open NumberField IsDedekindDomain Module
noncomputable section
variable {G : Type*} [CommGroup G]
namespace GroundTheory.Global
theorem _root_.solution (n : ℕ) :
    (powMonoidHom n : G →* G).range ⊔ CommGroup.torsion G =
      (powMonoidHom n : G ⧸ CommGroup.torsion G →* G ⧸ CommGroup.torsion G).range.comap
        (QuotientGroup.mk' (CommGroup.torsion G)) := by
  ext x
  simp only [Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · intro hx
    obtain ⟨_, ⟨b, rfl⟩, t, ht, rfl⟩ := Subgroup.mem_sup.1 hx
    refine ⟨QuotientGroup.mk' _ b, ?_⟩
    have h1 : QuotientGroup.mk' (CommGroup.torsion G) t = 1 := (QuotientGroup.eq_one_iff t).2 ht
    rw [map_mul, h1, mul_one, powMonoidHom_apply, map_pow]
  · rintro ⟨q, hq⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion G) q
    have ht : (b ^ n)⁻¹ * x ∈ CommGroup.torsion G := by
      rw [← QuotientGroup.eq]
      rw [← map_pow] at hq
      exact hq
    have h := Subgroup.mul_mem_sup (S := (powMonoidHom n : G →* G).range)
      (T := CommGroup.torsion G) ⟨b, rfl⟩ ht
    rwa [powMonoidHom_apply, mul_inv_cancel_left] at h
end GroundTheory.Global
