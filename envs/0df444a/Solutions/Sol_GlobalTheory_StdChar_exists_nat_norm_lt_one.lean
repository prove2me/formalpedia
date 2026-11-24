-- Prove2me | solution 1 for GlobalTheory.StdChar.exists_nat_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:58:31.762869+00:00
-- url     : https://prove2.me/submissions/9a0f6091-486b-4aea-955e-9b6e7401ee8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.StdChar
variable {F : Type} [NontriviallyNormedField F]
namespace GlobalTheory.StdChar
theorem _root_.solution [IsUltrametricDist F] [ProperSpace F] [CharZero F] :
    ∃ N : ℕ, 0 < N ∧ ‖(N : F)‖ < 1 := by
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : F) 1).tendsto_subseq
    (x := fun n : ℕ => (n : F)) (fun n => by simpa using IsUltrametricDist.norm_natCast_le_one F n)
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq 1 one_pos
  have h := hM (M + 1) (by omega)
  have hlt : φ M < φ (M + 1) := hφ (by omega)
  refine ⟨φ (M + 1) - φ M, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le, ← dist_eq_norm]
  simpa using h
end GlobalTheory.StdChar
