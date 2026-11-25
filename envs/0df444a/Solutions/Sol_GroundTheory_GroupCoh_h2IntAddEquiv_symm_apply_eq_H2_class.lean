-- Prove2me | solution 1 for GroundTheory.GroupCoh.h2IntAddEquiv_symm_apply_eq_H2_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:25:16.493678+00:00
-- url     : https://prove2.me/submissions/742f718f-04af-4c61-8d48-1f6bee37ff9c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_Characters
import Theorems.Thm_GroundTheory_GroupCoh_h1RatModIntIso_inv_apply
import Theorems.Thm_GroundTheory_GroupCoh_h2IntAddEquiv_symm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
variable (G : Type) [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (χ : Additive G →+ AddCircle (1 : ℚ)) (y : G → ℚ)
    (hy : ∀ g : G, (y g : AddCircle (1 : ℚ)) = χ (Additive.ofMul g)) (x : G × G → ℤ)
    (hx : ∀ g h : G, (x (g, h) : ℚ) = y g + y h - y (g * h)) :
    ∃ hc : x ∈ cocycles₂ (Rep.trivial ℤ G ℤ),
      (h2IntAddEquiv G).symm χ = H2π (Rep.trivial ℤ G ℤ) ⟨x, hc⟩ := by
  have hfx : (ratSES G).f.hom ∘ x = d₁₂ (ratSES G).X₂ y := by
    funext p
    change ((x p : ℤ) : ℚ) = y p.2 - y (p.1 * p.2) + y p.1
    rw [hx]; ring
  refine ⟨mem_cocycles₂_of_comp_eq_d₁₂ (ratSES_shortExact G) hfx, ?_⟩
  rw [h2IntAddEquiv_symm_apply, h1RatModIntIso_inv_apply]
  refine δ₁_apply (ratSES_shortExact G)
    ((cocycles₁IsoOfIsTrivial (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv χ) y ?_ x hfx
  funext g
  change ((y g : ℚ) : AddCircle (1 : ℚ)) = χ (Additive.ofMul g)
  exact hy g
end GroundTheory.GroupCoh
