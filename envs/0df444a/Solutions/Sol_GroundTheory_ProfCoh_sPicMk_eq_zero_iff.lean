-- Prove2me | solution 1 for GroundTheory.ProfCoh.sPicMk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:56.366015+00:00
-- url     : https://prove2.me/submissions/160ce875-06c6-4451-8a6c-1ff4fcf89a0c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type*} [Field F] [NumberField F]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
namespace GroundTheory.ProfCoh
theorem _root_.solution (D : sDivisor S) : sPicMk S D = 0 ↔ ∃ x : Fˣ, divS S (Additive.ofMul x) = D := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨Additive.toMul x, hx⟩, fun ⟨x, hx⟩ => ⟨Additive.ofMul x, hx⟩⟩
end GroundTheory.ProfCoh
