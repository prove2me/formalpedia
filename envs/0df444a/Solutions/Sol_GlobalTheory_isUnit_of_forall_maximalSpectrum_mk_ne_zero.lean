-- Prove2me | solution 1 for GlobalTheory.isUnit_of_forall_maximalSpectrum_mk_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:42.375831+00:00
-- url     : https://prove2.me/submissions/55f17986-26b5-4f53-a0e5-7cf59e88094e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {R : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {x : R}
    (h : ∀ m : MaximalSpectrum R, Ideal.Quotient.mk m.asIdeal x ≠ 0) : IsUnit x := by
  by_contra hx
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  exact h ⟨m, hm⟩ (Ideal.Quotient.eq_zero_iff_mem.2 hxm)
end GlobalTheory
