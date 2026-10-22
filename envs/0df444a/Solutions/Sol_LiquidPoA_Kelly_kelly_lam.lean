-- Prove2me | solution 1 for LiquidPoA.Kelly.kelly_lam
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-22T03:48:36.389891+00:00
-- url     : https://prove2.me/submissions/598ef31e-de90-4f09-ac49-f05cc5a2a984

import Definitions.Def_LiquidPoA_Kelly_Setting
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset Set LiquidPoA.Kelly

namespace D22KellyDerivative

theorem sum_update {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    ∑ j, Function.update s i b j = b + ∑ j ∈ univ.erase i, s j := by
  rw [← sum_erase_add _ _ (mem_univ i)]
  simp only [Function.update_self]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j hj
  exact Function.update_of_ne (mem_erase.1 hj).1 b s

theorem others_pos {n : ℕ} (s : Fin n → ℝ) (hs : InX s) (i : Fin n) :
    0 < ∑ j ∈ univ.erase i, s j := by
  obtain ⟨j, k, hjk, hj, hk⟩ := hs.2
  apply sum_pos'
  · intro l _
    exact hs.1 l
  · by_cases hji : j = i
    · exact ⟨k, mem_erase.2 ⟨by simpa [hji] using Ne.symm hjk, mem_univ _⟩, hk⟩
    · exact ⟨j, mem_erase.2 ⟨hji, mem_univ _⟩, hj⟩

end D22KellyDerivative

theorem solution {n : ℕ} (s : Fin n → ℝ) (hs : InX s) (i : Fin n) :
    lam (kelly n) s i =
      (s i + ∑ t ∈ Finset.univ.erase i, s t) ^ 2 /
        (∑ t ∈ Finset.univ.erase i, s t) := by
  let b := ∑ t ∈ univ.erase i, s t
  have hb : 0 < b := D22KellyDerivative.others_pos s hs i
  have hden : s i + b ≠ 0 := by linarith [hs.1 i]
  have halloc : allocIn (kelly n) s i = fun y => y / (y + b) := by
    funext y
    simp [allocIn, kelly, D22KellyDerivative.sum_update, b]
  have hpay : payIn (kelly n) s i = fun y => y := by
    funext y
    simp [payIn, kelly]
  have hder : HasDerivAt (fun y : ℝ => y / (y + b)) (b / (s i + b) ^ 2) (s i) := by
    simpa only [id_eq, one_mul, mul_one, add_sub_cancel_left] using
      (hasDerivAt_id (s i)).fun_div ((hasDerivAt_id (s i)).add_const b) hden
  have huniq : UniqueDiffWithinAt ℝ (Ici 0) (s i) := uniqueDiffOn_Ici 0 (s i) (hs.1 i)
  have hpayder : derivWithin (fun y : ℝ => y) (Ici 0) (s i) = 1 := by
    exact (hasDerivAt_id' (s i)).hasDerivWithinAt.derivWithin huniq
  simp only [lam, halloc, hpay, hder.hasDerivWithinAt.derivWithin huniq,
    hpayder]
  simp only [mul_one, inv_div]
  rfl

#print axioms solution
