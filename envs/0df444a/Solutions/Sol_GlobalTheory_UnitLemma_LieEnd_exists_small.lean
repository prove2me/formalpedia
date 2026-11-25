-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.exists_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:21.37755+00:00
-- url     : https://prove2.me/submissions/a5cc35ed-de25-4c78-8f33-7ca3a9ebce92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.LieEnd
open GlobalTheory.UnitLemma Polynomial Filter Topology
namespace GlobalTheory.UnitLemma.LieEnd
theorem _root_.solution (K : UQ) : ∃ a : K.O, K.Small a := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨y, hy⟩ := K.c_int p
  have hinj := IsFractionRing.injective K.O K.E
  have hy' : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E p := by rw [← hy, K.c_c]
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : algebraMap K.O K.E p = 0 := by simpa using hy
    exact hp.ne_zero ((map_eq_zero_iff _ hinj).1 h0)
  refine ⟨p * y, mul_ne_zero hp.ne_zero hy0, Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hp.not_isUnit), ?_⟩
  rw [map_mul, map_mul, hy, hy', mul_comm]
end GlobalTheory.UnitLemma.LieEnd
