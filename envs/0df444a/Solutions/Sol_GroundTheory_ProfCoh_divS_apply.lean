-- Prove2me | solution 1 for GroundTheory.ProfCoh.divS_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:23.534257+00:00
-- url     : https://prove2.me/submissions/7a4a2728-f880-4e43-9130-b3d42a951c6e

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
theorem _root_.solution (x : Additive Fˣ) (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    divS S x v = ordAt v.1 (Additive.toMul x) :=
  rfl
end GroundTheory.ProfCoh
