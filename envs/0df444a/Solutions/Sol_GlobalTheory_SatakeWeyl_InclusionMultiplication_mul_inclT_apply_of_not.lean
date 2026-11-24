-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.InclusionMultiplication.mul_inclT_apply_of_not
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:31:29.042325+00:00
-- url     : https://prove2.me/submissions/e8696e14-0691-46c0-855f-a1f179057624

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallerUnitaryGroupEmbedding
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open Matrix
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.InclusionMultiplication
variable {L : Type} [Field L] {n r : ℕ}
namespace GlobalTheory.SatakeWeyl.InclusionMultiplication
theorem _root_.solution {p : Type} {e : Fin r → Fin n} (M : Matrix p (Fin r) L)
    (i : p) {a : Fin n} (ha : a ∉ Set.range e) : (M * (incl L e)ᵀ) i a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : a ≠ e j := fun h => ha ⟨j, h.symm⟩
  simp [incl, this]
end GlobalTheory.SatakeWeyl.InclusionMultiplication
