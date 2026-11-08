-- Prove2me | solution 1 for Max3CutHard.weight_J
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:19:41.439212+00:00
-- url     : https://prove2.me/submissions/34aa9db2-376d-4b28-abb2-294fedbffab1

import Mathlib
import Definitions.Def_Max3CutHard_J
import Definitions.Def_Max3CutHard_wR
import Definitions.Def_Max3CutHard_IsNonneg
import Definitions.Def_Max3CutHard_WInst_IsWeighting
import Definitions.Def_Max3CutHard_WInst_Balanced

namespace Max3CutHard.Aux_WJ

open Max3CutHard

theorem wR_flatMap {α V : Type} (l : List α) (f : α → RGraph V) :
    wR (l.flatMap f) = (l.map fun a => wR (f a)).sum := by
  induction l with
  | nil => simp [wR]
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    simp [wR, List.map_append, List.sum_append]

end Max3CutHard.Aux_WJ

open Max3CutHard Max3CutHard.Aux_WJ in
theorem solution {U W : Type} {k : ℕ} (F : Family k) (hF : ∀ t, IsNonneg (F t).edges)
    (Φ : WInst U W) (hΦ : Φ.IsWeighting) (hbal : Φ.Balanced) :
    wR (J Φ F) = (1 / 3) * ∑ t : ZMod 3, wR (F t).edges := by
  have hb : ∀ t : ZMod 3, ∑ i : Fin Φ.eqs.length,
      (if (Φ.eqs.get i).1.t = t then (Φ.eqs.get i).2 else 0) = 1 / 3 := by
    intro t
    have := hbal t
    rw [← Fin.sum_univ_fun_getElem] at this
    simpa using this
  unfold J
  rw [wR_flatMap, ← Fin.sum_univ_def]
  trans (∑ i : Fin Φ.eqs.length, (Φ.eqs.get i).2 * wR (F (Φ.eqs.get i).1.t).edges)
  · apply Finset.sum_congr rfl
    intro i _
    simp only [wR, List.map_map, Function.comp_def]
    rw [List.sum_map_mul_left]
  calc ∑ i : Fin Φ.eqs.length, (Φ.eqs.get i).2 * wR (F (Φ.eqs.get i).1.t).edges
      = ∑ i : Fin Φ.eqs.length, ∑ t : ZMod 3,
          (if (Φ.eqs.get i).1.t = t then (Φ.eqs.get i).2 else 0) * wR (F t).edges := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ t : ZMod 3, ∑ i : Fin Φ.eqs.length,
          (if (Φ.eqs.get i).1.t = t then (Φ.eqs.get i).2 else 0) * wR (F t).edges :=
        Finset.sum_comm
    _ = ∑ t : ZMod 3, (1 / 3) * wR (F t).edges := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← Finset.sum_mul, hb t]
    _ = (1 / 3) * ∑ t : ZMod 3, wR (F t).edges := by rw [Finset.mul_sum]
