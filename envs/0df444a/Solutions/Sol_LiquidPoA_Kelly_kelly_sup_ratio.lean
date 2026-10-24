-- Prove2me | solution 1 for LiquidPoA.Kelly.kelly_sup_ratio
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:51:14.189999+00:00
-- url     : https://prove2.me/submissions/8b44fccf-8b1a-4674-8815-db817b76399e

import Definitions.Def_LiquidPoA_Kelly_Setting
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Finset Set LiquidPoA.Kelly Filter Topology
open scoped ENNReal

namespace D24KellySup

namespace Core

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

end Core

lemma lam_formula {n : ℕ} (s : Fin n → ℝ) (hs : InX s) (i : Fin n) :
    lam (kelly n) s i =
      (s i + ∑ t ∈ Finset.univ.erase i, s t) ^ 2 /
        (∑ t ∈ Finset.univ.erase i, s t) := by
  let b := ∑ t ∈ univ.erase i, s t
  have hb : 0 < b := Core.others_pos s hs i
  have hden : s i + b ≠ 0 := by linarith [hs.1 i]
  have halloc : allocIn (kelly n) s i = fun y => y / (y + b) := by
    funext y
    simp [allocIn, kelly, Core.sum_update, b]
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

lemma ratio_formula {n : ℕ} (s : Fin n → ℝ) (hs : InX s) (j : Fin n) :
    ratio (kelly n) s j = ENNReal.ofReal
      ((2 * (∑ i ∈ univ.erase j, s i) ^ 2 + 2 * s j * (∑ i ∈ univ.erase j, s i) + s j ^ 2) /
        ((∑ i ∈ univ.erase j, s i) ^ 2 + s j * (∑ i ∈ univ.erase j, s i) + s j ^ 2)) := by
  let B := ∑ i ∈ univ.erase j, s i
  have hB : 0 < B := Core.others_pos s hs j
  have ht : 0 ≤ s j := hs.1 j
  have hT : (∑ i, s i) = s j + B := by
    rw [← sum_erase_add _ _ (mem_univ j)]
    dsimp only [B]
    ring
  have hT0 : 0 < s j + B := by linarith
  have hD : 0 < B + (s j + B) ^ 2 / B * (s j / (s j + B)) := by positivity
  have hD2 : 0 < B ^ 2 + s j * B + s j ^ 2 := by positivity
  rw [ratio, lam_formula s hs j]
  change ENNReal.ofReal (B + (s j + B) ^ 2 / B) /
      ENNReal.ofReal (B + (s j + B) ^ 2 / B * (s j / ∑ i, s i)) = _
  rw [hT, ← ENNReal.ofReal_div_of_pos hD]
  congr 1
  dsimp only [B] at hB hT0 hD hD2 ⊢
  field_simp [ne_of_gt hB, ne_of_gt hT0, ne_of_gt hD, ne_of_gt hD2]
  ring

def profile (n : ℕ) (ε : ℝ) : Fin n → ℝ :=
  fun i => if i.val = 0 then ε else if i.val = 1 then 1 else 0

lemma profile_inX (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) : InX (profile n ε) := by
  refine ⟨?_, ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, ?_⟩⟩
  · intro i
    simp only [profile]
    split_ifs <;> positivity
  · intro h
    have := congrArg Fin.val h
    norm_num at this
  · simpa [profile] using hε
  · norm_num [profile]

lemma profile_others (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) :
    ∑ i ∈ univ.erase (⟨0, by omega⟩ : Fin n), profile n ε i = 1 := by
  let j0 : Fin n := ⟨0, by omega⟩
  let j1 : Fin n := ⟨1, by omega⟩
  have h10 : j1 ≠ j0 := by
    intro h
    have := congrArg Fin.val h
    norm_num [j0, j1] at this
  calc
    ∑ i ∈ univ.erase j0, profile n ε i = profile n ε j1 := by
      apply sum_eq_single
      · intro i hi hij
        have hi0 : i.val ≠ 0 := by
          intro h
          exact (mem_erase.mp hi).1 (Fin.ext h)
        have hi1 : i.val ≠ 1 := by
          intro h
          exact hij (Fin.ext h)
        simp [profile, hi0, hi1]
      · intro h
        exact False.elim (h (mem_erase.mpr ⟨h10, mem_univ _⟩))
    _ = 1 := by norm_num [profile, j1]

lemma profile_ratio (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ratio (kelly n) (profile n ε) (⟨0, by omega⟩ : Fin n) =
      ENNReal.ofReal ((2 + 2 * ε + ε ^ 2) / (1 + ε + ε ^ 2)) := by
  rw [ratio_formula _ (profile_inX n hn ε hε), profile_others n hn ε]
  simp [profile]

end D24KellySup

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    (⨆ (s : Fin n → ℝ) (_ : InX s),
      ratio (kelly n) s (⟨0, by omega⟩ : Fin n)) = 2 := by
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    rw [D24KellySup.ratio_formula s hs]
    let B := ∑ i ∈ univ.erase (⟨0, by omega⟩ : Fin n), s i
    let t := s (⟨0, by omega⟩ : Fin n)
    have hB : 0 < B :=
      D24KellySup.Core.others_pos s hs _
    have ht : 0 ≤ t := hs.1 _
    have hden : 0 < B ^ 2 + t * B + t ^ 2 := by positivity
    have hr : (2 * B ^ 2 + 2 * t * B + t ^ 2) / (B ^ 2 + t * B + t ^ 2) ≤ (2 : ℝ) :=
      (div_le_iff₀ hden).2 (by nlinarith [sq_nonneg t])
    have hENN := ENNReal.ofReal_le_ofReal hr
    simpa [B, t] using hENN
  · let ε : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
    have heps : ∀ k, 0 < ε k := by intro k; dsimp [ε]; positivity
    have hlim : Tendsto ε atTop (𝓝 0) := by
      simpa only [ε, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hnum : Tendsto (fun k => 2 + 2 * ε k + ε k ^ 2) atTop (𝓝 (2 : ℝ)) := by
      convert (tendsto_const_nhds.add (tendsto_const_nhds.mul hlim)).add (hlim.pow 2) using 1 <;> norm_num
    have hden : Tendsto (fun k => 1 + ε k + ε k ^ 2) atTop (𝓝 (1 : ℝ)) := by
      convert (tendsto_const_nhds.add hlim).add (hlim.pow 2) using 1 <;> norm_num
    have hratio : Tendsto
        (fun k => ratio (kelly n) (D24KellySup.profile n (ε k)) (⟨0, by omega⟩ : Fin n))
        atTop (𝓝 (2 : ℝ≥0∞)) := by
      simp_rw [D24KellySup.profile_ratio n hn _ (heps _)]
      convert ENNReal.tendsto_ofReal (hnum.div hden (by norm_num)) using 1 <;> norm_num
    apply le_of_tendsto hratio
    exact Filter.Eventually.of_forall fun k =>
      le_iSup_of_le (D24KellySup.profile n (ε k))
        (le_iSup_of_le (D24KellySup.profile_inX n hn (ε k) (heps k)) le_rfl)

#print axioms solution

