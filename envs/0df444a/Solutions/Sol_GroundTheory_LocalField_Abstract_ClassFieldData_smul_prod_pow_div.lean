-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.smul_prod_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:27.268948+00:00
-- url     : https://prove2.me/submissions/85493d8d-69bd-4ad4-aa4b-cc1a13a211e7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
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
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [((L : Subgroup G).subgroupOf K).Normal]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (φ : G) (y : A) (n : ℕ) :
    φ • (∏ ν : Fin n, φ ^ (ν : ℕ) • y) / ∏ ν : Fin n, φ ^ (ν : ℕ) • y = φ ^ n • y / y := by
  rw [Finset.smul_prod']
  simp only [Fin.prod_univ_eq_prod_range (fun j => φ • φ ^ j • y),
    Fin.prod_univ_eq_prod_range (fun j => φ ^ j • y)]
  have hs := Finset.prod_range_succ (fun j => φ ^ j • y) n
  have hs' := Finset.prod_range_succ' (fun j => φ ^ j • y) n
  simp only [pow_zero, one_smul] at hs'
  have : ∏ j ∈ Finset.range n, φ • φ ^ j • y = ∏ j ∈ Finset.range n, φ ^ (j + 1) • y := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [smul_smul, ← pow_succ']
  rw [this, div_eq_div_iff_mul_eq_mul, ← hs', hs, mul_comm]
end GroundTheory.LocalField.Abstract.ClassFieldData
