-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:47.494856+00:00
-- url     : https://prove2.me/submissions/6af2052f-34c7-4885-99e2-0a67aa555073

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_AutomorphicForms_RestrictedProductMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Filter Topology Set
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Automorphic.RestrictedProduct
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
variable (m : Type*) [Fintype m] [DecidableEq m]
variable [∀ i, Ring (R i)] {S : ι → Type*} [∀ i, SetLike (S i) (R i)]
  [∀ i, SubringClass (S i) (R i)] {B : Π i, S i} {C : Π i, Subring (Matrix m m (R i))}
namespace GroundTheory.Automorphic.RestrictedProduct
theorem _root_.solution (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) (g : GL m (Πʳ i, [R i, B i])) (i : ι) (a b : m) :
    (matrixUnitsEquiv m hC hB g i : Matrix m m (R i)) a b = g a b i :=
  rfl
end GroundTheory.Automorphic.RestrictedProduct
