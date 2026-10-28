-- Prove2me | solution 1 for MonopolyDemandUncertainty.SBSMP.fact_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:31:31.943254+00:00
-- url     : https://prove2.me/submissions/70777904-73ed-440b-b505-aadc9fa6f7bb

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

open MeasureTheory Set

namespace Aux_MDU_F1
open MonopolyDemandUncertainty.SBSMP

lemma key (E : Economy) (M : Mechanism) (i : Fin 2) (v' u : ℝ) (hu : u ∈ E.onlySet M i) :
    E.payoff M v' u = (v' - M.t i u) * (E.prob i * E.dens i v') := by
  obtain ⟨_, hxi, hxj⟩ := hu
  unfold Economy.payoff
  rw [Fin.sum_univ_two]
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · have h1 : M.x 1 u = false := hxj 1 (by decide)
    simp [ind, hxi, h1] <;> ring
  · have h0 : M.x 0 u = false := hxj 0 (by decide)
    simp [ind, hxi, h0] <;> ring

lemma pos (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (v : ℝ)
    (hv : v ∈ E.V) : 0 < E.prob i * E.dens i v := by
  have hd : 0 < E.dens i v := by
    unfold Economy.dens
    linarith [h1.2 i v hv]
  have hp : 0 < E.prob i := by
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · simp [Economy.prob] <;> linarith [hE.α₁_pos, hE.α₁_lt_one]
    · simp [Economy.prob] <;> linarith [hE.α₁_pos, hE.α₁_lt_one]
  exact mul_pos hp hd

end Aux_MDU_F1

open MonopolyDemandUncertainty.SBSMP Aux_MDU_F1 in
theorem solution (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (M : Mechanism)
    (hBIC : E.IsBIC M) (i : Fin 2) :
    ∀ v ∈ E.onlySet M i, ∀ w ∈ E.onlySet M i, M.t i v = M.t i w := by
  intro v hv w hw
  have hvV : v ∈ E.V := hv.1
  have hwV : w ∈ E.V := hw.1
  have hab : ∀ a ∈ E.onlySet M i, ∀ b ∈ E.onlySet M i, M.t i a ≤ M.t i b := by
    intro a ha b hb
    have h := hBIC a ha.1 b hb.1
    rw [key E M i a b hb, key E M i a a ha] at h
    have hc := pos E hE h1 i a ha.1
    have := le_of_mul_le_mul_right h hc
    linarith
  exact le_antisymm (hab v hv w hw) (hab w hw v hv)
