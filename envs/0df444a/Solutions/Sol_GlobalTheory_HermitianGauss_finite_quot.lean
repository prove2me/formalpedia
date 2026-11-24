-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:08.503703+00:00
-- url     : https://prove2.me/submissions/2e6cc8c0-22c2-4e85-8c73-187539d174e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
namespace GlobalTheory.HermitianGauss
theorem _root_.solution {D : Submodule R M} {x : M} {P : Ideal R} (hP : ∀ r, r • x ∈ D ↔ r ∈ P) :
    Finite (R ⧸ P) := by
  have hout : ∀ a : R ⧸ P, Ideal.Quotient.mk P (Quotient.out a) = a := fun a => Quotient.out_eq a
  refine Finite.of_injective (fun a : R ⧸ P => (Quotient.out a : R) • x) fun a b hab => ?_
  have hab' : (Quotient.out a : R) • x = (Quotient.out b : R) • x := hab
  have h : (Quotient.out a - Quotient.out b : R) ∈ P := by
    rw [← hP, sub_smul, hab', sub_self]
    exact D.zero_mem
  rw [← hout a, ← hout b]
  exact Ideal.Quotient.eq.mpr h
end GlobalTheory.HermitianGauss
