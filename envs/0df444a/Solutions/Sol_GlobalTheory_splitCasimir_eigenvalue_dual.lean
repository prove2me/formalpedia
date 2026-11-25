-- Prove2me | solution 1 for GlobalTheory.splitCasimir_eigenvalue_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:04.290936+00:00
-- url     : https://prove2.me/submissions/42b6ced8-ebd2-4a84-aa00-8bdf1b9b55c4

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LastComatrixRowInvertsDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorDualStandardRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirEigenvalueDual
import Theorems.Thm_GlobalTheory_lastComatrixRow_inverts_dual
import Theorems.Thm_GlobalTheory_tensor_dual_standard_rel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + (n : ℂ) := by
  intro V _ _ _ n E Et Om m hrel hunit hdet hEt hOm lam x hx hxe
  obtain ⟨-, -, -, hcomm⟩ := tensor_dual_standard_rel V n E Et Om hrel hunit hEt hOm
  obtain ⟨K, hK, -⟩ := lastComatrixRow_inverts_dual V n E Om m hrel hdet hOm
  have key : ∀ z : PiLp 2 (fun _ : Fin (n + 1) => V), Om z = lam • z →
      z (Fin.last n) ≠ 0 → ∃ j, lam = m j + (n : ℂ) := by
    intro z hz hzl
    have h0 := hK ((n : ℂ) - lam) z
    have hzero : ((n : ℂ) - lam - (n : ℂ)) • z + Om z = 0 := by
      rw [hz, ← add_smul]
      simp
    rw [hzero, map_zero] at h0
    have hprod : (∏ j, ((n : ℂ) - lam + m j)) = 0 := by
      rcases (smul_eq_zero.mp h0.symm) with h | h
      · exact h
      · exact absurd h hzl
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hprod
    exact ⟨j, by linear_combination -hj⟩
  by_cases hl : x (Fin.last n) = 0
  · have hc : ∃ c, x c ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      apply hx
      ext c
      simp [hne c]
    obtain ⟨c, hc⟩ := hc
    apply key (Et c (Fin.last n) x)
    · have h1 := congrArg (fun f => f x) (hcomm c (Fin.last n))
      simp only [Module.End.mul_apply] at h1
      rw [h1, hxe, map_smul]
    · rw [hEt, hl, map_zero]
      simpa using hc
  · exact key x hxe hl
end GlobalTheory
