-- Prove2me | solution 1 for GlobalTheory.SatBlocks.inv_mem_of_val_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:17.997688+00:00
-- url     : https://prove2.me/submissions/f9646bee-06ac-4905-82ab-d1ec2b8a12eb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SaturatedBlocksSummand
import Theorems.Thm_GlobalTheory_SatBlocks_ne_zero_of_val_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.SatBlocks
namespace GlobalTheory.SatBlocks
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z⁻¹ ∈ intRing v := by
  have h1 : v (z * z⁻¹) = 0 := by rw [mul_inv_cancel₀ (ne_zero_of_val_zero v h)]; simp
  rw [v.map_mul, h, zero_add] at h1
  exact h1.ge
end GlobalTheory.SatBlocks
