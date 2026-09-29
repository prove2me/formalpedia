-- Prove2me | solution 1 for MonoidHom.index_range_powMonoidHom_eq_mul_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/965eca21-6cc6-5fc1-b92a-ce0bc5779bc9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem solution {G U F : Type*} [CommGroup G] [CommGroup U]
    [CommGroup F] (ι : U →* G) (φ : G →* F) (hι : Function.Injective ι) (hφ : Function.Surjective φ)
    (hexact : ι.range = φ.ker) {n : ℕ} (hF : ∀ x : F, x ^ n = 1 → x = 1) :
    (powMonoidHom n : G →* G).range.index
      = (powMonoidHom n : F →* F).range.index * (powMonoidHom n : U →* U).range.index := by
  classical

  have h1 : φ.ker ⊔ (powMonoidHom n : G →* G).range = ((powMonoidHom n : F →* F).range).comap φ := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro g hg
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hg]; exact one_mem _
      · rintro _ ⟨g, rfl⟩
        rw [Subgroup.mem_comap, powMonoidHom_apply, map_pow]; exact ⟨φ g, rfl⟩
    · intro g hg
      rw [Subgroup.mem_comap] at hg
      obtain ⟨z, hz⟩ := hg
      obtain ⟨g', rfl⟩ := hφ z
      rw [powMonoidHom_apply, ← map_pow] at hz
      refine Subgroup.mem_sup.2 ⟨g * (g' ^ n)⁻¹, ?_, g' ^ n, ⟨g', rfl⟩, inv_mul_cancel_right g (g' ^ n)⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hz, mul_inv_cancel]

  have h3 : ((powMonoidHom n : G →* G).range).relIndex (φ.ker ⊔ (powMonoidHom n : G →* G).range)
      = ((powMonoidHom n : G →* G).range ⊓ φ.ker).relIndex φ.ker := by
    rw [Subgroup.relIndex_sup_right, Subgroup.inf_relIndex_right]

  have h4 : (powMonoidHom n : G →* G).range ⊓ φ.ker = ((powMonoidHom n : U →* U).range).map ι := by
    apply le_antisymm
    · intro x hx'
      obtain ⟨⟨g, rfl⟩, hx⟩ := Subgroup.mem_inf.1 hx'
      rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow] at hx
      have hg' : g ∈ ι.range := by rw [hexact]; exact hF _ hx
      obtain ⟨u, rfl⟩ := hg'
      exact ⟨u ^ n, ⟨u, rfl⟩, by rw [map_pow, powMonoidHom_apply]⟩
    · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨⟨ι u, by rw [powMonoidHom_apply, powMonoidHom_apply, map_pow]⟩, ?_⟩
      rw [← hexact]; exact ⟨u ^ n, by rw [powMonoidHom_apply, map_pow]⟩

  have h5 : (((powMonoidHom n : U →* U).range).map ι).relIndex φ.ker = ((powMonoidHom n : U →* U).range).index := by
    rw [← hexact, MonoidHom.range_eq_map ι, ← Subgroup.relIndex_comap,
      Subgroup.comap_map_eq_self_of_injective hι, Subgroup.relIndex_top_right]
  calc ((powMonoidHom n : G →* G).range).index
      = ((powMonoidHom n : G →* G).range).relIndex (φ.ker ⊔ (powMonoidHom n : G →* G).range)
          * (φ.ker ⊔ (powMonoidHom n : G →* G).range).index := (Subgroup.relIndex_mul_index le_sup_right).symm
    _ = ((powMonoidHom n : G →* G).range ⊓ φ.ker).relIndex φ.ker * ((powMonoidHom n : F →* F).range).index := by
          rw [h3, h1, Subgroup.index_comap_of_surjective _ hφ]
    _ = _ := by rw [h4, h5, mul_comm]

end S_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact
end P2MW
export P2MW.S_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact (solution)
