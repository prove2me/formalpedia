-- Prove2me | solution 1 for GlobalTheory.ClosedResidueExt.Unram.isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:31.300326+00:00
-- url     : https://prove2.me/submissions/dcf527ea-e692-4e1e-ae64-80841b2f10a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
namespace GlobalTheory.ClosedResidueExt
namespace Unram
theorem _root_.solution {R : Subalgebra W Ω} {u : Ω} (hu : u ∈ R) (hu' : u⁻¹ ∈ R) (h0 : u ≠ 0) :
    IsUnit (⟨u, hu⟩ : R) :=
  IsUnit.of_mul_eq_one ⟨u⁻¹, hu'⟩ (Subtype.ext (mul_inv_cancel₀ h0))
end Unram
end GlobalTheory.ClosedResidueExt
