-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_real_step_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:21:01.976833+00:00
-- url     : https://prove2.me/submissions/38b95e9d-0406-47af-a395-01783f7f3b53

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD
import Theorems.Thm_WhittFLT_Composition_billingsley_lemma_1
import Theorems.Thm_Kyprianou_Ch04_ito43_partition_threshold_sum
open Set Filter
open scoped Topology ENNReal NNReal
set_option autoImplicit false
/-- Use Billingsley’s finite small-oscillation partition; choose coefficients as differences of consecutive sampled values. -/
theorem solution
    (Y : ℝ → ℝ) (U : ℝ) (hU : 0 < U)
    (hY : WhittFLT.Composition.IsCadlagOn (Icc 0 U) Y)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (b c : ℕ → ℝ), (∀ i, 0 ≤ b i) ∧
      ∀ s, 0 ≤ s → s < U →
        |Y s - ∑ i ∈ Finset.range m, c i * (if b i ≤ s then (1:ℝ) else 0)| ≤ δ := by
  obtain ⟨n,p,hp0,hpn,hmono,hosc⟩ :=
    WhittFLT.Composition.billingsley_lemma_1 0 U hU Y hY δ hδ
  let b : ℕ → ℝ := fun k => p ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩
  have hbmon : Monotone b := by
    intro a d had
    apply hmono.monotone
    exact min_le_min_right n had
  have hb0 : b 0 = 0 := by simpa [b] using hp0
  have hbn : b n = U := by
    rw [← hpn]
    apply congrArg p
    apply Fin.ext
    simp
  refine ⟨n+1,b,fun i => if i=0 then Y (b 0) else Y (b i)-Y (b (i-1)),?_,?_⟩
  · intro i
    rw [← hb0]
    exact hbmon (Nat.zero_le i)
  intro s hs hsU
  obtain ⟨j,hj,hjs,hsj,he⟩ := Kyprianou.Ch04.ito43_partition_threshold_sum
    b hbmon Y n s (by simpa [hb0] using hs) (by simpa [hbn] using hsU)
  rw [he]
  let k : Fin n := ⟨j,hj⟩
  have h1 : b j = p k.castSucc := by
    apply congrArg p
    apply Fin.ext
    exact min_eq_left hj.le
  have h2 : b (j+1) = p k.succ := by
    apply congrArg p
    apply Fin.ext
    exact min_eq_left (Nat.succ_le_of_lt hj)
  have ha : s ∈ Ico (p k.castSucc) (p k.succ) := by
    rw [← h1, ← h2]
    exact ⟨hjs,hsj⟩
  have hb : b j ∈ Ico (p k.castSucc) (p k.succ) := by
    rw [← h1, ← h2]
    exact ⟨le_rfl,hjs.trans_lt hsj⟩
  have hd : edist (Y s) (Y (b j)) < ENNReal.ofReal δ := by
    refine lt_of_le_of_lt ?_ (hosc k)
    exact le_iSup_of_le s (le_iSup_of_le ha
      (le_iSup_of_le (b j) (le_iSup_of_le hb le_rfl)))
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hδ, Real.dist_eq] at hd
  exact hd.le
