-- Prove2me | solution 1 for GroundTheory.LocalField.toAdditive_cycNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:28.235879+00:00
-- url     : https://prove2.me/submissions/cd921e4a-70ad-480d-9c67-5eea983be80c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_LocalField_toMul_cycNorm
import Theorems.Thm_GroundTheory_LocalField_tateNorm_apply


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
namespace GroundTheory.LocalField
theorem _root_.solution (i : M →* N) (hi : ∀ (g : G) (x : M), i (g • x) = g • i x)
    (x : Additive M) :
    MonoidHom.toAdditive i (cycNorm (Representation.ofMulDistribMulAction G M) x) =
      cycNorm (Representation.ofMulDistribMulAction G N) (MonoidHom.toAdditive i x) := by
  apply Additive.toMul.injective
  rw [toMul_cycNorm]
  change i (cycNorm (Representation.ofMulDistribMulAction G M) x).toMul = _
  rw [toMul_cycNorm, tateNorm_apply, tateNorm_apply, map_prod]
  simp_rw [hi]
  rfl
end GroundTheory.LocalField
