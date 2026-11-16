-- Prove2me | solution 1 for MMSImpossibility.Goods.Supplement.mmsCh_ge_prop
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:45:03.554867+00:00
-- url     : https://prove2.me/submissions/ecd47c34-caa0-42be-b2bd-3e5b8006885d

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Supplement_Setting

open LittleCharity.MMS MMSImpossibility.Goods MMSImpossibility.Goods.Supplement

theorem solution {n m : ℕ} (c : Fin n → Finset (Fin m) → ℝ) (hc : IsAdditive c)
    (i : Fin n) :
    c i Finset.univ / n ≤ mmsCh (c i) n := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have : Nonempty (Fin n) := ⟨i⟩
  have : Nonempty (Fin m → Fin n) := ⟨fun _ => i⟩
  unfold mmsCh
  apply le_ciInf
  intro A
  have hsum : c i Finset.univ = ∑ t : Fin n, c i (bundle A t) := by
    rw [hc.1 i Finset.univ]
    simp_rw [hc.1 i (bundle A _)]
    unfold bundle
    rw [← Finset.sum_fiberwise (Finset.univ) A (fun g => c i {g})]
  have hle : ∀ t, c i (bundle A t) ≤ ⨆ t : Fin n, c i (bundle A t) :=
    fun t => le_ciSup (f := fun t => c i (bundle A t)) (Finite.bddAbove_range _) t
  have : c i Finset.univ ≤ n * ⨆ t : Fin n, c i (bundle A t) := by
    rw [hsum]
    calc ∑ t : Fin n, c i (bundle A t) ≤ ∑ _t : Fin n, ⨆ t : Fin n, c i (bundle A t) :=
          Finset.sum_le_sum (fun t _ => hle t)
      _ = n * ⨆ t : Fin n, c i (bundle A t) := by simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  linarith
