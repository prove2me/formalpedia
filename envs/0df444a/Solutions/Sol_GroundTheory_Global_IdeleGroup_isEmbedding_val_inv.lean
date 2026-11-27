-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.isEmbedding_val_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:40.424715+00:00
-- url     : https://prove2.me/submissions/ae8a9190-77e5-445e-8a76-79675a2f090b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe

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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution :
    IsEmbedding (fun x : IdeleGroup K ↦ ((x : 𝔸[K]), ((x⁻¹ : IdeleGroup K) : 𝔸[K]))) :=
  ((Homeomorph.refl (𝔸[K])).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp
    (Units.isEmbedding_embedProduct (M := 𝔸[K]))
end GroundTheory.Global.IdeleGroup
