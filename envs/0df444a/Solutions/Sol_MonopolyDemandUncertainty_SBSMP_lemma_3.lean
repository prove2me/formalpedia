-- Prove2me | solution 1 for MonopolyDemandUncertainty.SBSMP.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:47:22.337615+00:00
-- url     : https://prove2.me/submissions/eab1ac0c-7b63-45a3-a28b-77c02c232203

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting
import Theorems.Thm_MonopolyDemandUncertainty_SBSMP_fact_1

open MeasureTheory Set

namespace Aux_MDU_L3
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
    fin_cases i
    · simp [Economy.prob]; linarith [hE.α₁_pos]
    · simp [Economy.prob]; linarith [hE.α₁_lt_one]
  exact mul_pos hp hd

lemma payoff_none (E : Economy) (M : Mechanism) (u : ℝ) (hu : ∀ j, M.x j u = false) :
    E.payoff M u u = 0 := by
  unfold Economy.payoff
  rw [Fin.sum_univ_two]
  simp [ind, hu 0, hu 1]

end Aux_MDU_L3

open MonopolyDemandUncertainty.SBSMP Aux_MDU_L3 in
theorem solution (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (M : Mechanism) (hBIC : E.IsBIC M) (hEIR : E.IsEIR M) (i : Fin 2)
    (hne : (E.onlySet M i).Nonempty) (hlo : E.vlo < sInf (E.onlySet M i))
    (hbelow : ∀ v ∈ E.V, v < sInf (E.onlySet M i) → ∀ j, M.x j v = false) :
    ∀ v ∈ E.onlySet M i, M.t i v = sInf (E.onlySet M i) := by
  intro v hv
  set S := E.onlySet M i with hS
  have hbdd : BddBelow S := ⟨E.vlo, fun w hw => hw.1.1⟩
  have hconst := MonopolyDemandUncertainty.SBSMP.fact_1 E hE h1 M hBIC i
  apply le_antisymm
  · apply le_csInf hne
    intro w hw
    rw [hconst v hv w hw]
    exact (hEIR i w hw.1).2
  · by_contra hlt
    rw [not_le] at hlt
    have hsle : sInf S ≤ E.vhi := le_trans (csInf_le hbdd hv) hv.1.2
    set u := (max (M.t i v) E.vlo + sInf S) / 2 with hu
    have hmax1 : M.t i v ≤ max (M.t i v) E.vlo := le_max_left _ _
    have hmax2 : E.vlo ≤ max (M.t i v) E.vlo := le_max_right _ _
    have hmaxlt : max (M.t i v) E.vlo < sInf S := max_lt hlt hlo
    have huV : u ∈ E.V := ⟨by linarith, by linarith⟩
    have hus : u < sInf S := by linarith
    have hup : M.t i v < u := by linarith
    have hb := hBIC u huV v hv.1
    rw [key E M i u v hv, payoff_none E M u (hbelow u huV hus)] at hb
    have := mul_pos (sub_pos.mpr hup) (pos E hE h1 i u huV)
    linarith
