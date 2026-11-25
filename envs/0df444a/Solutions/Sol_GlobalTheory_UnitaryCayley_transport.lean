-- Prove2me | solution 1 for GlobalTheory.UnitaryCayley.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:23.855674+00:00
-- url     : https://prove2.me/submissions/a1ae0d6d-25d8-43c1-af18-b1f31ad500d7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsIsCayleyUIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.UnitaryCayley
namespace GlobalTheory.UnitaryCayley
theorem _root_.solution {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : IsCayleyU k r ε P)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (P⁻¹ * g * P ∈ UH (Hpk k r) ↔ g ∈ UJset ε) ∧
    (P⁻¹ * g * P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ ↔
      g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) := by
  obtain ⟨⟨-, hH⟩, hu⟩ := hP
  have hl : Pᴴ * P = 1 := Unitary.star_mul_self_of_mem hu
  have hr : P * Pᴴ = 1 := Unitary.mul_star_self_of_mem hu
  have hi : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hl
  have key : ∀ A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Pᴴ * A * P = Pᴴ * B * P ↔ A = B := by
    intro A B
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    have e : ∀ C : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P * (Pᴴ * C * P) * Pᴴ = C := by
      intro C
      calc P * (Pᴴ * C * P) * Pᴴ = (P * Pᴴ) * C * (P * Pᴴ) := by simp only [Matrix.mul_assoc]
        _ = C := by rw [hr]; simp
    rw [← e A, h, e]
  have gen : ∀ J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      (Pᴴ * g * P)ᴴ * (Pᴴ * J * P) * (Pᴴ * g * P) = Pᴴ * (gᴴ * J * g) * P := by
    intro J
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Pᴴ * (gᴴ * P) * (Pᴴ * J * P) * (Pᴴ * g * P)
        = Pᴴ * (gᴴ * (P * Pᴴ) * J * (P * Pᴴ) * g) * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hr]; simp
  rw [hi]
  constructor
  · show (Pᴴ * g * P)ᴴ * Hpk k r * (Pᴴ * g * P) = Hpk k r ↔ gᴴ * Jm ε * g = Jm ε
    rw [← hH, gen, key]
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.star_eq_conjTranspose]
    have := gen 1
    rw [Matrix.mul_one, hl, Matrix.mul_one, Matrix.mul_one] at this
    rw [this, ← key (gᴴ * g) 1, Matrix.mul_one, hl]
end GlobalTheory.UnitaryCayley
