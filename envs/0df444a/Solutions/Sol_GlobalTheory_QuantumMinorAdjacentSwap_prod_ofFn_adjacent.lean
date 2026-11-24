-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.prod_ofFn_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:48:36.163505+00:00
-- url     : https://prove2.me/submissions/cbd1deda-e192-4d76-9c7c-3dcf7b515420

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]
omit [Algebra ℂ A]
namespace GlobalTheory.QuantumMinorAdjacentSwap
theorem _root_.solution : ∀ (m : ℕ) (i : Fin m) (g₁ g₂ g₃ g₄ : Fin (m + 1) → A),
    (∀ k, k ≠ i.castSucc → k ≠ i.succ → g₂ k = g₁ k ∧ g₃ k = g₁ k ∧ g₄ k = g₁ k) →
    g₁ i.castSucc * g₁ i.succ + g₂ i.castSucc * g₂ i.succ =
      g₃ i.castSucc * g₃ i.succ + g₄ i.castSucc * g₄ i.succ →
    (List.ofFn g₁).prod + (List.ofFn g₂).prod = (List.ofFn g₃).prod + (List.ofFn g₄).prod
  | 0, i, _, _, _, _, _, _ => i.elim0
  | m + 1, i, g₁, g₂, g₃, g₄, h, e => by
    refine Fin.cases (motive := fun i : Fin (m + 1) =>
      (∀ k, k ≠ i.castSucc → k ≠ i.succ → g₂ k = g₁ k ∧ g₃ k = g₁ k ∧ g₄ k = g₁ k) →
      g₁ i.castSucc * g₁ i.succ + g₂ i.castSucc * g₂ i.succ =
        g₃ i.castSucc * g₃ i.succ + g₄ i.castSucc * g₄ i.succ →
      (List.ofFn g₁).prod + (List.ofFn g₂).prod = (List.ofFn g₃).prod + (List.ofFn g₄).prod)
      ?_ ?_ i h e
    · intro h e
      have hk : ∀ k : Fin m, g₂ k.succ.succ = g₁ k.succ.succ ∧ g₃ k.succ.succ = g₁ k.succ.succ ∧
          g₄ k.succ.succ = g₁ k.succ.succ := fun k =>
        h _ (Fin.succ_ne_zero _) (fun hh => Fin.succ_ne_zero _ (Fin.succ_injective _ hh))
      rw [List.ofFn_succ (f := g₁), List.ofFn_succ (f := g₂), List.ofFn_succ (f := g₃),
        List.ofFn_succ (f := g₄), List.ofFn_succ (f := fun k => g₁ (Fin.succ k)),
        List.ofFn_succ (f := fun k => g₂ (Fin.succ k)),
        List.ofFn_succ (f := fun k => g₃ (Fin.succ k)),
        List.ofFn_succ (f := fun k => g₄ (Fin.succ k))]
      simp only [List.prod_cons, (hk _).1, (hk _).2.1, (hk _).2.2, ← mul_assoc, ← add_mul]
      congr 1
    · intro j h e
      have h0 := h 0 (by
        rw [← Fin.succ_castSucc]; exact (Fin.succ_ne_zero _).symm) (Fin.succ_ne_zero _).symm
      have ih := solution m j (fun k => g₁ k.succ) (fun k => g₂ k.succ)
        (fun k => g₃ k.succ) (fun k => g₄ k.succ)
        (fun k h1 h2 => h _
          (by rw [← Fin.succ_castSucc]; exact fun hh => h1 (Fin.succ_injective _ hh))
          (fun hh => h2 (Fin.succ_injective _ hh)))
        (by simpa only [Fin.succ_castSucc] using e)
      rw [List.ofFn_succ (f := g₁), List.ofFn_succ (f := g₂), List.ofFn_succ (f := g₃),
        List.ofFn_succ (f := g₄)]
      simp only [List.prod_cons, h0.1, h0.2.1, h0.2.2, ← mul_add, ih]
end GlobalTheory.QuantumMinorAdjacentSwap
