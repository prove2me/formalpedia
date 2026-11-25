-- Prove2me | solution 1 for GroundTheory.LocalField.toAdditive_cycSubOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:25:43.618402+00:00
-- url     : https://prove2.me/submissions/0f4bfd35-1cee-4547-b5b0-0573522ac2cf

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_LocalField_toMul_cycSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
variable {N : Type*} [CommGroup N] [MulDistribMulAction G N]
omit [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution (i : M →* N) (hi : ∀ (g : G) (x : M), i (g • x) = g • i x) (τ : G)
    (x : Additive M) :
    MonoidHom.toAdditive i (cycSubOne (Representation.ofMulDistribMulAction G M) τ x) =
      cycSubOne (Representation.ofMulDistribMulAction G N) τ (MonoidHom.toAdditive i x) := by
  apply Additive.toMul.injective
  rw [toMul_cycSubOne]
  change i (cycSubOne (Representation.ofMulDistribMulAction G M) τ x).toMul = _
  rw [toMul_cycSubOne, map_div, hi]
  rfl
end GroundTheory.LocalField
