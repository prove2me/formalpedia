-- Prove2me | solution 1 for GroundTheory.GroupCoh.natCard_hexagon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:41.270804+00:00
-- url     : https://prove2.me/submissions/cff979f9-50a1-4fe6-a828-751e30d51aa9

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_natCard_eq_ker_mul_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
namespace GroundTheory.GroupCoh
theorem _root_.solution {X₁ X₂ X₃ X₄ X₅ X₆ : Type*} [AddGroup X₁] [AddGroup X₂] [AddGroup X₃]
    [AddGroup X₄] [AddGroup X₅] [AddGroup X₆]
    (d₁ : X₁ →+ X₂) (d₂ : X₂ →+ X₃) (d₃ : X₃ →+ X₄) (d₄ : X₄ →+ X₅) (d₅ : X₅ →+ X₆)
    (d₆ : X₆ →+ X₁) (e₁ : d₁.ker = d₆.range) (e₂ : d₂.ker = d₁.range) (e₃ : d₃.ker = d₂.range)
    (e₄ : d₄.ker = d₃.range) (e₅ : d₅.ker = d₄.range) (e₆ : d₆.ker = d₅.range) :
    Nat.card X₁ * Nat.card X₃ * Nat.card X₅ = Nat.card X₂ * Nat.card X₄ * Nat.card X₆ := by
  rw [natCard_eq_ker_mul_range d₁, natCard_eq_ker_mul_range d₂, natCard_eq_ker_mul_range d₃,
    natCard_eq_ker_mul_range d₄, natCard_eq_ker_mul_range d₅, natCard_eq_ker_mul_range d₆,
    e₁, e₂, e₃, e₄, e₅, e₆]
  ring
end GroundTheory.GroupCoh
