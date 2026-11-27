-- Prove2me | solution 1 for NadlerCLS.theorem_C_2_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:13:30.488011+00:00
-- url     : https://prove2.me/submissions/0cc82146-73e0-4dc5-a538-fdc3f01f9a28

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_l1
import Definitions.Def_NadlerCLS_kuhnInterp
import Theorems.Thm_NadlerCLS_lemma_C_1

set_option autoImplicit false

namespace NadlerCLS.C2TransferHelpers

open NetworkEquilibriumCLS.LinearNash

theorem l1_fin_one (a b : Fin 1 → ℝ) : l1 a b = |a 0 - b 0| := by
  unfold l1; simp

end NadlerCLS.C2TransferHelpers

open NadlerCLS NetworkEquilibriumCLS.LinearNash in
theorem solution (n : ℕ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (f : (Fin n → ℝ) → (Fin n → ℝ)) (p : (Fin n → ℝ) → ℝ)
    (hf : ∀ x, InCube x → InCube (f x)) (hp : ∀ x, InCube x → 0 ≤ p x ∧ p x ≤ 1)
    (lam δ : ℝ) (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (m : ℕ) (hm : 1 ≤ m) (hnh : (n : ℝ) * kuhnH m ≤ 1)
    (hC4 : 3 * (max 1 lam) ^ 2 * ((n : ℝ) * kuhnH m) ^ (β ^ 2) ≤ δ / 2)
    (x : Fin n → ℝ) (hx : InCube x)
    (h1 : ∀ j, l1 (f x) (f (kuhnVertex m x j)) ≤ lam * (l1 x (kuhnVertex m x j)) ^ β)
    (h2 : ∀ j, |p x - p (kuhnVertex m x j)| ≤ lam * (l1 x (kuhnVertex m x j)) ^ β)
    (h3 : ∀ j, |p (kuhnInterp m f x) - p (kuhnVertex m (kuhnInterp m f x) j)| ≤
      lam * (l1 (kuhnInterp m f x) (kuhnVertex m (kuhnInterp m f x) j)) ^ β)
    (h4 : |p (f x) - p (kuhnInterp m f x)| ≤ lam * (l1 (f x) (kuhnInterp m f x)) ^ β)
    (htarget : kuhnInterp m (fun v (_ : Fin 1) => p v) (kuhnInterp m f x) 0 ≥
      kuhnInterp m (fun v (_ : Fin 1) => p v) x 0 - δ / 2) :
    p (f x) ≥ p x - δ := by
  set P : (Fin n → ℝ) → (Fin 1 → ℝ) := fun v _ => p v with hPdef
  have hP : ∀ v, InCube v → InCube (P v) := fun v hv i => hp v hv
  have hlP : ∀ a b, l1 (P a) (P b) = |p a - p b| := by
    intro a b; rw [C2TransferHelpers.l1_fin_one]
  obtain ⟨hfi, -, hfiii⟩ := lemma_C_1 n n m hm f hf
  obtain ⟨-, -, hPiii⟩ := lemma_C_1 n 1 m hm P hP
  set z := kuhnInterp m f x with hz
  have hzc : InCube z := (hfi x hx).2.2.2.2.2
  set s : ℝ := (n : ℝ) * kuhnH m with hs
  have hs0 : 0 ≤ s := by
    rw [hs]; unfold kuhnH; positivity
  set η : ℝ := lam * s ^ β with hη
  -- (iii) for f at x
  have hfz : l1 (f x) z ≤ η := hfiii lam β hβ0 hβ1 x hx h1
  -- (iii) for P at x
  have hPx : |p x - kuhnInterp m P x 0| ≤ η := by
    have := hPiii lam β hβ0 hβ1 x hx (fun j => by rw [hlP]; exact h2 j)
    rw [C2TransferHelpers.l1_fin_one] at this
    simpa [P] using this
  have hPz : |p z - kuhnInterp m P z 0| ≤ η := by
    have := hPiii lam β hβ0 hβ1 z hzc (fun j => by rw [hlP]; exact h3 j)
    rw [C2TransferHelpers.l1_fin_one] at this
    simpa [P] using this
  have hl1nn : 0 ≤ l1 (f x) z := by
    unfold l1; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have h4' : |p (f x) - p z| ≤ lam * η ^ β := by
    refine h4.trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hl1nn hfz hβ0.le) hlam.le
  -- bound 2η + lam η^β ≤ δ/2
  set L : ℝ := max 1 lam with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hlamL : lam ≤ L := le_max_right _ _
  have hβ2 : β ^ 2 ≤ β := by nlinarith
  have hsβ : s ^ β ≤ s ^ (β ^ 2) :=
    Real.rpow_le_rpow_of_exponent_ge' hs0 hnh (by positivity) hβ2
  have hsβ0 : 0 ≤ s ^ β := Real.rpow_nonneg hs0 _
  have hsβ20 : 0 ≤ s ^ (β ^ 2) := Real.rpow_nonneg hs0 _
  have hlamβ : lam ^ β ≤ L := by
    rcases le_total lam 1 with h | h
    · exact (Real.rpow_le_one hlam.le h hβ0.le).trans hL1
    · exact (Real.rpow_le_self_of_one_le h hβ1).trans hlamL
  have hηβ : η ^ β = lam ^ β * s ^ (β ^ 2) := by
    rw [hη, Real.mul_rpow hlam.le hsβ0, ← Real.rpow_mul hs0, sq]
  have hA : η ≤ L ^ 2 * s ^ (β ^ 2) := by
    rw [hη]
    calc lam * s ^ β ≤ L * s ^ (β ^ 2) :=
          mul_le_mul hlamL hsβ hsβ0 (by linarith)
      _ ≤ L ^ 2 * s ^ (β ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hsβ20; nlinarith
  have hB : lam * η ^ β ≤ L ^ 2 * s ^ (β ^ 2) := by
    rw [hηβ, ← mul_assoc, sq L]
    apply mul_le_mul_of_nonneg_right _ hsβ20
    exact mul_le_mul hlamL hlamβ (Real.rpow_nonneg hlam.le _) (by linarith)
  have hsum : 2 * η + lam * η ^ β ≤ δ / 2 := by nlinarith
  have hPz' : kuhnInterp m P z 0 ≤ p z + η := by
    have := (abs_le.mp hPz); linarith
  have hPx' : p x - η ≤ kuhnInterp m P x 0 := by
    have := (abs_le.mp hPx); linarith
  have h4'' : p z - lam * η ^ β ≤ p (f x) := by
    have := (abs_le.mp h4'); linarith
  have ht : kuhnInterp m P z 0 ≥ kuhnInterp m P x 0 - δ / 2 := htarget
  linarith
