-- Prove2me | solution 1 for NamikiStretch.Lossy.eq_23_coherent
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:27:04.886042+00:00
-- url     : https://prove2.me/submissions/dd698a16-c62e-49c3-9e3a-1d2b7f07f3fa

import Definitions.Def_NamikiStretch_Lossy_Protocol
import Theorems.Thm_NamikiStretch_Lossy_eq_20_coherent
import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P21_coherentOutput

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21
open NamikiStretch.Lossy

theorem solution (η ξ : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (α β : ℂ) :
    let ρα : Unit × ℕ → Unit × ℕ → ℂ := fun p q => coherentDensity α p.2 q.2
    let w : ℂ := (((1 - ξ ^ 2) / (2 * Real.pi) *
      Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star β)) : ℝ) : ℂ)
    (∀ p q : Unit × ℕ, Summable (bellTerm (tmsvKernel ξ) ρα β p q)) ∧
    ∀ b b' : ℕ, HasSum
      (vacuumLossTerm η (fun m n => bellBranch (tmsvKernel ξ) ρα β ((), m) ((), n)) b b')
      (w * coherentDensity (((Real.sqrt η * ξ : ℝ) : ℂ) * (α - star β)) b b') := by
  intro ρα w
  constructor
  · intro ⟨(), p2⟩ ⟨(), q2⟩
    exact (eq_20_coherent ξ hξ0 hξ1 α β p2 q2).summable
  · intro b b'
    have h_term : vacuumLossTerm η (fun m n => bellBranch (tmsvKernel ξ) ρα β ((), m) ((), n)) b b' =
        fun ell => w * vacuumLossTerm η (coherentDensity ((ξ : ℂ) * (α - star β))) b b' ell := by
      ext ell
      dsimp [vacuumLossTerm, bellBranch]
      rw [(eq_20_coherent ξ hξ0 hξ1 α β (b + ell) (b' + ell)).tsum_eq]
      rw [mul_left_comm]
      rfl
    rw [h_term]
    have h_arg : (Real.sqrt η : ℂ) * ((ξ : ℂ) * (α - star β)) =
        (((Real.sqrt η * ξ : ℝ) : ℂ) * (α - star β)) := by
      push_cast
      ring
    have h_cs := (coherentOutput η hη0.le hη1.le ((ξ : ℂ) * (α - star β))).2.2.1 b b'
    have h_mul := HasSum.mul_left w h_cs
    rw [h_arg] at h_mul
    exact h_mul
