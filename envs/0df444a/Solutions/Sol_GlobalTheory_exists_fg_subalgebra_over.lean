-- Prove2me | solution 1 for GlobalTheory.exists_fg_subalgebra_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:39.288629+00:00
-- url     : https://prove2.me/submissions/069a28f8-a081-4cfd-abaf-804757ef0610

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k L : Type*} [Field k] [Field L] [Algebra k L]
    (F : IntermediateField k L) (R : Subalgebra k L) (hR : R.FG) (u : L) :
    ∃ A : Subalgebra F L, Algebra.FiniteType F A ∧ R ≤ A.restrictScalars k ∧ u ∈ A := by
  classical
  obtain ⟨s, rfl⟩ := hR
  refine ⟨Algebra.adjoin F (↑(insert u s) : Set L), ?_, ?_, ?_⟩
  · exact (Subalgebra.fg_iff_finiteType _).1 ⟨_, rfl⟩
  · refine Algebra.adjoin_le fun x hx => ?_
    have : x ∈ Algebra.adjoin F (↑(insert u s) : Set L) :=
      Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
    exact this
  · exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
end GlobalTheory
