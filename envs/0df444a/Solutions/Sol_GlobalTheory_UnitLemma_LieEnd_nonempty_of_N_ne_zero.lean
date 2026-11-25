-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.nonempty_of_N_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:52.775444+00:00
-- url     : https://prove2.me/submissions/daf6c1fa-50b3-4e93-bc88-74cea80bd52b

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
variable {K : UQ}
namespace GlobalTheory.UnitLemma.LieEnd
theorem _root_.solution (B : InvAlg K) (x : B.A) (h : B.N x ≠ 0) : (B.X x).Nonempty := by
  by_contra he
  apply h
  have : IsEmpty (B.X x) := Set.isEmpty_coe_sort.2 (Set.not_nonempty_iff_eq_empty.1 he)
  have : IsEmpty (Orb K.O B.T (B.X x)) := ⟨fun o => isEmptyElim (Quot.out o)⟩
  exact finsum_of_isEmpty _
end GlobalTheory.UnitLemma.LieEnd
