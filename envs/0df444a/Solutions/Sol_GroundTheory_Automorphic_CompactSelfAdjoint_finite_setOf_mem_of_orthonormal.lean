-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.finite_setOf_mem_of_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:59.041531+00:00
-- url     : https://prove2.me/submissions/9f2bc074-6f6b-42a4-b00e-341506035ac5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.CompactSelfAdjoint
open Module End Submodule Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
namespace GroundTheory.Automorphic.CompactSelfAdjoint
theorem _root_.solution {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v)
    (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W] : {i | v i ∈ W}.Finite := by
  let f : {i | v i ∈ W} → W := fun i => ⟨v i, i.2⟩
  have hf : LinearIndependent 𝕜 f := by
    apply LinearIndependent.of_comp W.subtype
    exact hv.linearIndependent.comp _ Subtype.val_injective
  exact Set.finite_coe_iff.1 hf.finite_of_isNoetherian
end GroundTheory.Automorphic.CompactSelfAdjoint
