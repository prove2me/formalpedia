-- Prove2me | solution 1 for GlobalTheory.Phase.VacShape.isMu_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:09:28.890813+00:00
-- url     : https://prove2.me/submissions/931b0761-40eb-4a4a-affe-aea25009528c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
import Theorems.Thm_P2M_GlobalTheory_Phase_VacShape_semi__f1f6dd4150d6
import Theorems.Thm_GlobalTheory_SW_Vac_ex_zero
import Theorems.Thm_GlobalTheory_SW_Vac_pr_smul_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_smul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
  {A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)} {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ}
  {φ : Matrix κ ι ℚ → ℂ}
omit [DecidableEq ι]
namespace GlobalTheory.Phase.VacShape
theorem _root_.solution (h : VacS A ε φ) {y} (hy : y ∈ A) : IsMu (ε y) := by
  obtain ⟨m, hm, hm'⟩ := h.ord
  have h0 : ε 0 = 1 := by simpa using hm' 0 A.zero_mem
  have hpow : ∀ n : ℕ, ε (n • y) = ε y ^ n := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, pow_zero]; exact h0
    | succ n ih =>
      rw [succ_nsmul, semi' h _ (A.nsmul_mem hy n) _ hy, ih, pow_succ, Prod.smul_fst, Prod.smul_snd,
        ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, pr_smul_left, pr_smul_right,
        sub_self, ex_zero, mul_one]
  exact ⟨m, hm, by rw [← hpow, hm' y hy]⟩
end GlobalTheory.Phase.VacShape
