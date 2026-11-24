-- Prove2me | solution 1 for GlobalTheory.UnitLemma.StabIndex.relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:57.096025+00:00
-- url     : https://prove2.me/submissions/83e45c6a-eab7-4669-8318-5a99a6305a7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexNeZeroOfBetween
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexUnitStabilizerIntegralUnitsNeZero
import Theorems.Thm_GlobalTheory_T_finite_submodules_between_mulLeftImage_lattice
import Theorems.Thm_GlobalTheory_UnitLemma_StabIndex_relIndex_ne_zero_of_between


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.StabIndex
namespace GlobalTheory.UnitLemma.StabIndex
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 →
    (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) →
    (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  intro K B L hL c hc h
  have hfin : {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A (c * c)) L ≤ M ∧ M ≤ L}.Finite :=
    GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B L hL (c * c) (mul_ne_zero hc hc)
  exact relIndex_ne_zero_of_between K B L c hc hfin h
end GlobalTheory.UnitLemma.StabIndex
