-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.mem_frobImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:58.109388+00:00
-- url     : https://prove2.me/submissions/6efd8c99-5862-4b34-99ac-9d18eafbe544

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
variable [PerfectRing F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {K : IntermediateField F E.toAffine.FunctionField}
    {z : E.toAffine.FunctionField} : z ∈ frobImage E p K ↔ ∃ g ∈ K, g ^ p = z := by
  show z ∈ K.toSubfield.map (frobenius E.toAffine.FunctionField p) ↔ _
  rw [Subfield.mem_map]
  rfl
end GroundTheory.Arith.Abelian
