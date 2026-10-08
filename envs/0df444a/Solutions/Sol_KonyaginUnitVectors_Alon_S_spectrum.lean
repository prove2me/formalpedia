-- Prove2me | solution 1 for KonyaginUnitVectors.Alon.S_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:38:40.467902+00:00
-- url     : https://prove2.me/submissions/cc92e423-84ca-4bc7-abd0-d386f08f0c7b

import Mathlib
import Definitions.Def_KonyaginUnitVectors_AlonConstruction
import Theorems.Thm_KonyaginUnitVectors_Alon_gold_charsum_sq_le

set_option autoImplicit false

/-!
Lemma 6 (c), (d) of the Alon-type construction: spectral lower bound for `S` and `|m₀ - m₁| ≤ R`
with `R = 8 √q + 1`.  Uses only the Gold-form character-sum bound `gold_charsum_sq_le`.
-/

namespace KonyaginUnitVectors.Alon

variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

theorem pk_psi_zero : psi F 0 = 1 := by simp [psi]

theorem pk_psi_add (y z : F) : psi F (y + z) = psi F y * psi F z := by
  unfold psi
  rw [map_add]
  generalize Algebra.trace (ZMod 2) F y = a
  generalize Algebra.trace (ZMod 2) F z = b
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;> simp [h11]

theorem pk_chi_add (w g h : F × F × F) : chi F w (g + h) = chi F w g * chi F w h := by
  unfold chi
  rw [← pk_psi_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem pk_chi_zero (g : F × F × F) : chi F 0 g = 1 := by
  simp [chi, pk_psi_zero]

theorem pk_chi_gamma (w : F × F × F) (x : F) :
    chi F w (gamma F x) = psi F (w.1 * x + w.2.1 * x ^ 3 + w.2.2 * x ^ 5) := rfl

variable [Fintype F]

/-- `λ_w = X_w Y_w` (PROOF.md Lemma 6(a)); uses injectivity of `(x,y) ↦ γ x + γ y`. -/
theorem pk_lambda
    (hinj : Set.InjOn (fun p : F × F => gamma F p.1 + gamma F p.2) ↑(W0 F ×ˢ W1 F))
    (w : F × F × F) :
    ∑ s ∈ Sset F, chi F w s =
      (∑ x ∈ W0 F, chi F w (gamma F x)) * ∑ y ∈ W1 F, chi F w (gamma F y) := by
  classical
  unfold Sset
  rw [Finset.sum_image hinj, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  exact pk_chi_add F w _ _

/-- `X_w - Y_w = Σ(w) - 1` (PROOF.md Lemma 6(b)), stated as `Σ(w) = 1 + X_w - Y_w`. -/
theorem pk_charsum_eq (w : F × F × F) :
    ∑ x : F, psi F (w.1 * x + w.2.1 * x ^ 3 + w.2.2 * x ^ 5 + x ^ 9) =
      1 + (∑ x ∈ W0 F, chi F w (gamma F x)) - ∑ x ∈ W1 F, chi F w (gamma F x) := by
  classical
  have hpt : ∀ x : F, psi F (w.1 * x + w.2.1 * x ^ 3 + w.2.2 * x ^ 5 + x ^ 9) =
      (if x = 0 then (1 : ℝ) else 0) + (if x ∈ W0 F then chi F w (gamma F x) else 0) -
        (if x ∈ W1 F then chi F w (gamma F x) else 0) := by
    intro x
    rw [pk_psi_add, ← pk_chi_gamma]
    by_cases hx : x = 0
    · subst hx
      simp [W0, W1, pk_psi_zero, chi, gamma]
    · by_cases ht : Algebra.trace (ZMod 2) F (x ^ 9) = 0
      · have h0 : x ∈ W0 F := by simp [W0, hx, ht]
        have h1 : x ∉ W1 F := by simp [W1, ht]
        simp [hx, h0, h1, psi, ht]
      · have h0 : x ∉ W0 F := by simp [W0, ht]
        have h1 : x ∈ W1 F := by simp [W1, hx, ht]
        simp [hx, h0, h1, psi, ht]
  rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.univ_inter]
  simp

variable [CharP F 2]

/-- `|X_w - Y_w| ≤ 8 √q + 1`, from the Gold-form bound C1. -/
theorem pk_diff_bound (w : F × F × F) :
    |(∑ x ∈ W0 F, chi F w (gamma F x)) - ∑ x ∈ W1 F, chi F w (gamma F x)| ≤
      8 * Real.sqrt (Fintype.card F) + 1 := by
  have hC1 := gold_charsum_sq_le F w.1 w.2.1 w.2.2
  have hs0 : 0 ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (Fintype.card F) ^ 2 = (Fintype.card F : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hSig : |∑ x : F, psi F (w.1 * x + w.2.1 * x ^ 3 + w.2.2 * x ^ 5 + x ^ 9)| ≤
      8 * Real.sqrt (Fintype.card F) := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    nlinarith
  rw [pk_charsum_eq] at hSig
  have := abs_le.mp hSig
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

end KonyaginUnitVectors.Alon

open KonyaginUnitVectors.Alon

theorem solution (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (hinj : Set.InjOn (fun p : F × F => gamma F p.1 + gamma F p.2) ↑(W0 F ×ˢ W1 F)) :
    (∀ w : F × F × F, -((8 * Real.sqrt (Fintype.card F) + 1) ^ 2 / 4) ≤ ∑ s ∈ Sset F, chi F w s) ∧
    |((W0 F).card : ℝ) - ((W1 F).card : ℝ)| ≤ 8 * Real.sqrt (Fintype.card F) + 1 := by
  refine ⟨fun w => ?_, ?_⟩
  · rw [pk_lambda F hinj w]
    have hb := abs_le.mp (pk_diff_bound F w)
    generalize (∑ x ∈ W0 F, chi F w (gamma F x)) = X at hb ⊢
    generalize (∑ x ∈ W1 F, chi F w (gamma F x)) = Y at hb ⊢
    generalize 8 * Real.sqrt (Fintype.card F) + 1 = R at hb ⊢
    nlinarith [sq_nonneg (X + Y), mul_nonneg (sub_nonneg.2 hb.2) (by linarith [hb.1] : 0 ≤ R + (X - Y))]
  · have h := pk_diff_bound F 0
    simpa [pk_chi_zero] using h

#print axioms solution
