-- Prove2me | solution 1 for GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:23.158608+00:00
-- url     : https://prove2.me/submissions/5ad5ea58-fee5-41f7-93ad-8423d0b1f6d1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted

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
open Filter Topology NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.RestrictedProduct
variable {ι : Type*} {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
  {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] {B : Π i, S i}
namespace GroundTheory.Global.RestrictedProduct
theorem _root_.solution (hBopen : ∀ i, IsOpen (B i : Set (R i)))
    (x : (Πʳ i, [R i, B i])ˣ) (i : ι) :
    ((continuousUnitsEquiv hBopen x i : (R i)ˣ) : R i) = (x : Πʳ i, [R i, B i]) i :=
  rfl
end GroundTheory.Global.RestrictedProduct
