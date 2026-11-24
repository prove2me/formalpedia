-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.ContractProof.conj_mem_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:12:27.789459+00:00
-- url     : https://prove2.me/submissions/8486b022-01b9-46da-bae3-5e02fb7bea42

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDominantDiagonalConjugationContracts
import Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_mat_conj
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
noncomputable section
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.ContractProof
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.SatakeWeyl.ContractProof
theorem _root_.solution {ϖ : L} (h0 : ϖ ≠ 0) (γ : Fin r → ℕ) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (hg : g ∈ rootU σ γ) : s * g * s⁻¹ ∈ rootU σ γ := by
  refine ⟨fun i l h => ?_, fun i l h => ?_⟩
  · rw [mat_conj h0 c s g hs, hg.1 i l h]
    by_cases e : i = l
    · subst e; simp
    · rw [Matrix.one_apply_ne e, mul_zero]
  · rw [mat_conj h0 c s g hs, hg.2 i l h, mul_zero]
end GlobalTheory.SatakeWeyl.ContractProof
