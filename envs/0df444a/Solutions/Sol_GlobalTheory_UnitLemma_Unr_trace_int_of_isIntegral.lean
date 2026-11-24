-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.trace_int_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:50.677028+00:00
-- url     : https://prove2.me/submissions/da1d25fa-5260-4651-b1ae-7d1ef7f1aae4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceIntOfIsIntegral
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IsUnrExt_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (z : K'.E)
    (hz : @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra z) :
    ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra z = algebraMap K.O K.E a := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact Nat.pos_of_ne_zero hU.ne_zero)
  have h := Algebra.isIntegral_trace (R := K.O) (L := K.E) hz
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨a, ha.symm⟩
end GlobalTheory.UnitLemma.Unr
