-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.q_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:56:11.219151+00:00
-- url     : https://prove2.me/submissions/1add822c-0547-410c-88fa-4fd8699152ef

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
theorem _root_.solution (K : UQ) : K.q ≠ 0 := by
  intro hq
  have hc := K.card_res
  have hpos : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
  rw [hq] at hc
  simp at hc
  omega
end GlobalTheory.UnitLemma.LieEnd
