-- Prove2me | solution 1 for MonoidHom.exists_subfield_units_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/09dab6f3-524d-5568-9ec0-29a1df1a5f08

import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Group.Units.Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MonoidHom_exists_subfield_units_coe_eq

set_option autoImplicit false

theorem solution
    {G : Type*} [Group G] {L : Type*} [Field L] (K : Subfield L)
    (F : G →* G →* Lˣ) (hF : ∀ α β : G, ((F α β : Lˣ) : L) ∈ K) :
    ∃ F' : G →* G →* (↥K)ˣ, ∀ α β : G, (((F' α β : (↥K)ˣ) : ↥K) : L) = F α β := by

  have hinv : ∀ α β : G, ((F α β : Lˣ) : L)⁻¹ ∈ K := fun α β => K.inv_mem (hF α β)
  let u : G → G → (↥K)ˣ := fun α β =>
    ⟨⟨(F α β : L), hF α β⟩, ⟨((F α β : Lˣ) : L)⁻¹, hinv α β⟩,
      Subtype.ext (by simp), Subtype.ext (by simp)⟩
  have hu : ∀ α β, (((u α β : (↥K)ˣ) : ↥K) : L) = F α β := fun _ _ => rfl
  refine ⟨{ toFun := fun α => { toFun := u α, map_one' := ?_, map_mul' := ?_ }, map_one' := ?_, map_mul' := ?_ }, hu⟩
  · ext; simp [u]
  · intro β₁ β₂; ext; simp [u, Units.val_mul]
  · ext β; simp [u]
  · intro α₁ α₂; ext β; simp [u, Units.val_mul]

end S_MonoidHom_exists_subfield_units_coe_eq
end P2MW
export P2MW.S_MonoidHom_exists_subfield_units_coe_eq (solution)
