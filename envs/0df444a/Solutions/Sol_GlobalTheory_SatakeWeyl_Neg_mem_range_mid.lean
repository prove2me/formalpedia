-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Neg.mem_range_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:33:07.051994+00:00
-- url     : https://prove2.me/submissions/25aecf27-65d9-43d2-a653-b6c8adcbd938

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReduction
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
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Neg
namespace GlobalTheory.SatakeWeyl.Neg
theorem _root_.solution {n k r : ℕ} (h : n = 2 * k + r) (x : Fin n) :
    x ∈ Set.range (mid k r h) ↔ k ≤ x.val ∧ x.val < k + r := by
  constructor
  · rintro ⟨j, rfl⟩
    have := j.2
    simp only [mid]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x.val - k, by omega⟩, Fin.ext (by simp only [mid]; omega)⟩
end GlobalTheory.SatakeWeyl.Neg
