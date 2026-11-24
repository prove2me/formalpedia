-- Prove2me | solution 1 for GlobalTheory.isCompact_Upq_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:29.424901+00:00
-- url     : https://prove2.me/submissions/91635cc1-2b7a-485f-9090-24c46c82e124

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqDefiniteCompact
import Theorems.Thm_GlobalTheory_Jpq_zero_left_eq_neg_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_isCompact_units_of_unitary
import Theorems.Thm_Formalism_UG_P_mem_Upq_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (q : ℕ) :
    IsCompact (Formalism.UG.Upq 0 q : Set (GL (Fin 0 ⊕ Fin q) ℂ)) := by
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Fin 0 ⊕ Fin q)
    (T := {M | star M * M = 1})
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const) (fun _ h => h)
  convert hc using 1
  ext g
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
  rw [Formalism.UG.P.mem_Upq_iff, Jpq_zero_left_eq_neg_one, Matrix.mul_neg, Matrix.mul_one,
    Matrix.neg_mul, neg_inj]
end GlobalTheory
