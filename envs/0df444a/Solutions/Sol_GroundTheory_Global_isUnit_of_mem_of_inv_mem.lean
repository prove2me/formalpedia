-- Prove2me | solution 1 for GroundTheory.Global.isUnit_of_mem_of_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:54.063356+00:00
-- url     : https://prove2.me/submissions/146313cd-08e5-41db-a2de-6fab50c81e10

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization

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
open NumberField IsDedekindDomain Polynomial
noncomputable section
variable (L : Type*) [Field L] [NumberField L]
variable {L}
omit [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution {R : Type*} [CommRing R] [Algebra R L] {S : Subalgebra R L}
    {x : L} (hx : x ≠ 0) (h : x ∈ S) (h' : x⁻¹ ∈ S) : IsUnit (⟨x, h⟩ : S) :=
  isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, h'⟩, Subtype.ext (mul_inv_cancel₀ hx)⟩
end GroundTheory.Global
