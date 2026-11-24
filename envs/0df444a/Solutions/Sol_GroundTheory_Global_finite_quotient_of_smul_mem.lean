-- Prove2me | solution 1 for GroundTheory.Global.finite_quotient_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:30:33.204241+00:00
-- url     : https://prove2.me/submissions/509efc7d-fa26-4e1e-b654-aa0e1812f7b0

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_RationalForm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice

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
open GroundTheory.GroupCoh
open scoped TensorProduct
namespace GroundTheory.Global
theorem _root_.solution {B : Type*} [AddCommGroup B] [Module.Finite ℤ B]
    (S : AddSubgroup B) {n : ℤ} (hn : n ≠ 0) (h : ∀ y, n • y ∈ S) : Finite (B ⧸ S) := by
  have : Module.Finite ℤ (B ⧸ S) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' S).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective S y
  refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
  show n • (QuotientAddGroup.mk' S x) = 0
  rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact h x
end GroundTheory.Global
