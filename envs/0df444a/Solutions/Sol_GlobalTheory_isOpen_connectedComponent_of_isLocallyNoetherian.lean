-- Prove2me | solution 1 for GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:04:44.628382+00:00
-- url     : https://prove2.me/submissions/adb1dad2-a1d1-4acb-a7c5-85331dcd1d38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherian
import Theorems.Thm_GlobalTheory_ConnOpen_isOpen_connectedComponent_noetherian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option autoImplicit false
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by
  intro X hX x
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := y) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let y' : (U : Set X) := ⟨y, hyU⟩
  refine ⟨Subtype.val '' connectedComponent y', ?_,
    U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ (GlobalTheory.ConnOpen.isOpen_connectedComponent_noetherian y'),
    ⟨y', mem_connectedComponent, rfl⟩⟩
  have hc : _root_.IsPreconnected (Subtype.val '' connectedComponent y' : Set X) :=
    isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have := hc.subset_connectedComponent ⟨y', mem_connectedComponent, rfl⟩
  rwa [← connectedComponent_eq hy] at this
end GlobalTheory
