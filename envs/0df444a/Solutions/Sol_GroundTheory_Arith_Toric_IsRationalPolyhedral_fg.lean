-- Prove2me | solution 1 for GroundTheory.Arith.Toric.IsRationalPolyhedral.fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:34.083455+00:00
-- url     : https://prove2.me/submissions/4f19c7ba-94d9-4ceb-a829-802741da345c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {L E : Type*} [AddCommGroup L] [AddCommGroup E] [Module ℝ E]
namespace GroundTheory.Arith.Toric
namespace IsRationalPolyhedral
theorem _root_.solution {ι : L →ₗ[ℤ] E} {σ : PointedCone ℝ E}
    (hσ : IsRationalPolyhedral ι σ) : σ.FG := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  exact ⟨S.image ι, by rw [Finset.coe_image]⟩
end IsRationalPolyhedral
end GroundTheory.Arith.Toric
