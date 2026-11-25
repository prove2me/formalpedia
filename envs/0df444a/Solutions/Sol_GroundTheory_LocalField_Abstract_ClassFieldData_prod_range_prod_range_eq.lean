-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.prod_range_prod_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:07:30.444288+00:00
-- url     : https://prove2.me/submissions/5e3b6382-80da-455a-b0a3-3f1f522ead8f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution {M : Type*} [CommMonoid M] (f : ℕ → M) (g D0 : ℕ) :
    ∏ i ∈ Finset.range g, ∏ j ∈ Finset.range D0, f (D0 * i + j) =
      ∏ m ∈ Finset.range (g * D0), f m := by
  induction g with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.succ_mul, Finset.prod_range_add, mul_comm D0 k]
end GroundTheory.LocalField.Abstract.ClassFieldData
