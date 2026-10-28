-- Prove2me | solution 1 for MultiPurchase.Hardness.theta_transformation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:18:25.060563+00:00
-- url     : https://prove2.me/submissions/f86dc6dc-b48f-492a-a282-be6dbbe0cb9c

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

open MultiPurchase.Hardness in
theorem solution {m : ℕ} (G : SimpleGraph (Fin m)) (kappa : ℚ) (r : Fin (m + 1) → ℚ)
    (h0 : kappa < r 0) (hhalf : ∀ i : Fin m, r i.succ < kappa / 2)
    (hpos : ∀ i : Fin m, 0 < r i.succ) (hanti : StrictAnti fun i : Fin m => r i.succ) :
    (∀ i j, 0 ≤ redTheta G kappa r i j) ∧ (∀ i, redTheta G kappa r i i = 0) ∧
    (∀ i j, i ≠ j → redTheta G kappa r i j * (r i + r j - kappa) = hubQ G i j) := by
  have hdeg : ∀ i : Fin m, (0 : ℚ) ≤ (nodeDeg G i : ℚ) / 2 := fun i => by positivity
  refine ⟨fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp only [redTheta, hubQ, Fin.cases_zero, Fin.cases_succ]
    · simp
    · have := hpos j'
      exact div_nonneg (hdeg j') (by linarith)
    · have := hpos i'
      exact div_nonneg (hdeg i') (by linarith)
    · have h1 := hhalf i'
      have h2 := hhalf j'
      split_ifs
      · exact div_nonneg_of_nonpos (by norm_num) (by linarith)
      · simp
  · refine Fin.cases ?_ (fun i' => ?_) i <;>
      simp only [redTheta, hubQ, Fin.cases_zero, Fin.cases_succ]
    · simp
    · simp [G.irrefl]
  · revert hij
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> intro hij <;>
      simp only [redTheta, hubQ, Fin.cases_zero, Fin.cases_succ]
    · exact absurd rfl hij
    · have := hpos j'
      exact div_mul_cancel₀ _ (by linarith)
    · have := hpos i'
      exact div_mul_cancel₀ _ (by linarith)
    · have h1 := hhalf i'
      have h2 := hhalf j'
      exact div_mul_cancel₀ _ (by linarith)
