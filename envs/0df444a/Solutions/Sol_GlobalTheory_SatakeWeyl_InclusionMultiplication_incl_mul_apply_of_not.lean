-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.InclusionMultiplication.incl_mul_apply_of_not
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:31:26.467844+00:00
-- url     : https://prove2.me/submissions/e393c538-3288-416a-b80e-e20ed284f453

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
theorem _root_.solution {p : Type} {e : Fin r → Fin n} (M : Matrix (Fin r) p L)
    {a : Fin n} (ha : a ∉ Set.range e) (j : p) : (incl L e * M) a j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : a ≠ e i := fun h => ha ⟨i, h.symm⟩
  simp [incl, this]
end GlobalTheory.SatakeWeyl.InclusionMultiplication
