-- Prove2me | solution 1 for LoockCVQEC.RepCode.syndrome_table
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:40:46.290247+00:00
-- url     : https://prove2.me/submissions/f8b078d9-c7d5-47cf-8c8d-595aab3ea944

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

namespace Aux_LoockSyn

open LoockCVQEC.RepCode Real

theorem hs : √(2 / 3) = 2 / √6 := by
  have h6 : (0:ℝ) < √6 := Real.sqrt_pos.mpr (by norm_num)
  rw [eq_div_iff h6.ne', ← Real.sqrt_mul (by norm_num),
    show (2 / 3 : ℝ) * 6 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem syn_eq (d : ℝ) (S : Finset (Fin 3)) :
    syndrome d S = ((2 * (if (0:Fin 3) ∈ S then (1:ℝ) else 0) - (if (1:Fin 3) ∈ S then (1:ℝ) else 0)
        - (if (2:Fin 3) ∈ S then (1:ℝ) else 0)) * (d / √6),
      ((if (1:Fin 3) ∈ S then (1:ℝ) else 0) - (if (2:Fin 3) ∈ S then (1:ℝ) else 0)) * (d / √2)) := by
  unfold syndrome errVec tritter
  rw [hs]
  by_cases h0 : (0 : Fin 3) ∈ S <;> by_cases h1 : (1 : Fin 3) ∈ S <;>
    by_cases h2 : (2 : Fin 3) ∈ S <;>
    (ext <;> simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> simp [h0, h1, h2] <;>
      first | ring1 | (ring_nf; simp) | simp)

theorem fin_ext (S T : Finset (Fin 3)) :
    S = T ↔ ((0:Fin 3) ∈ S ↔ (0:Fin 3) ∈ T) ∧ ((1:Fin 3) ∈ S ↔ (1:Fin 3) ∈ T) ∧
      ((2:Fin 3) ∈ S ↔ (2:Fin 3) ∈ T) := by
  rw [Finset.ext_iff]
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨a, b, c⟩ i
    fin_cases i
    · exact a
    · exact b
    · exact c

theorem fin_empty (S : Finset (Fin 3)) :
    S = ∅ ↔ (0:Fin 3) ∉ S ∧ (1:Fin 3) ∉ S ∧ (2:Fin 3) ∉ S := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨a, b, c⟩ i
    fin_cases i
    · exact a
    · exact b
    · exact c

theorem fin_univ (S : Finset (Fin 3)) :
    S = Finset.univ ↔ (0:Fin 3) ∈ S ∧ (1:Fin 3) ∈ S ∧ (2:Fin 3) ∈ S := by
  rw [Finset.eq_univ_iff_forall]
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨a, b, c⟩ i
    fin_cases i
    · exact a
    · exact b
    · exact c

end Aux_LoockSyn

open LoockCVQEC.RepCode Real in
theorem solution (d : ℝ) (hd : 0 < d) :
    (syndrome d ∅ = (0, 0)
      ∧ syndrome d {0} = (√(2 / 3) * d, 0)
      ∧ syndrome d {1} = (-(1 / √6 * d), 1 / √2 * d)
      ∧ syndrome d {2} = (-(1 / √6 * d), -(1 / √2 * d))
      ∧ syndrome d {0, 1} = (1 / √6 * d, 1 / √2 * d)
      ∧ syndrome d {0, 2} = (1 / √6 * d, -(1 / √2 * d))
      ∧ syndrome d {1, 2} = (-(√(2 / 3) * d), 0)
      ∧ syndrome d Finset.univ = (0, 0))
    ∧ ∀ S T : Finset (Fin 3), syndrome d S = syndrome d T ↔
        (S = T ∨ (S = ∅ ∧ T = Finset.univ) ∨ (S = Finset.univ ∧ T = ∅)) := by
  have ha : 0 < d / √6 := div_pos hd (Real.sqrt_pos.mpr (by norm_num))
  have hb : 0 < d / √2 := div_pos hd (Real.sqrt_pos.mpr (by norm_num))
  refine ⟨?_, ?_⟩
  · simp only [Aux_LoockSyn.syn_eq, Aux_LoockSyn.hs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (ext <;> simp <;> first | ring1 | (ring_nf; simp) | simp)
  · intro S T
    rw [Aux_LoockSyn.syn_eq, Aux_LoockSyn.syn_eq, Prod.ext_iff, Aux_LoockSyn.fin_ext,
      Aux_LoockSyn.fin_empty, Aux_LoockSyn.fin_empty, Aux_LoockSyn.fin_univ, Aux_LoockSyn.fin_univ]
    rw [mul_left_inj' ha.ne', mul_left_inj' hb.ne']
    by_cases h0 : (0:Fin 3) ∈ S <;> by_cases h1 : (1:Fin 3) ∈ S <;> by_cases h2 : (2:Fin 3) ∈ S <;>
    by_cases k0 : (0:Fin 3) ∈ T <;> by_cases k1 : (1:Fin 3) ∈ T <;> by_cases k2 : (2:Fin 3) ∈ T <;>
    norm_num [h0, h1, h2, k0, k1, k2]
