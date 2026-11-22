-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_adjacent_grid_increments_near_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:03:35.507179+00:00
-- url     : https://prove2.me/submissions/889ecc64-98a9-44bf-96ff-15a8bc0ace72

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (d : ℕ → ℝ≥0) (hd : ∀ n, 0 < d n)
    (hd0 : Tendsto d atTop (𝓝 0)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (M : ℕ) (t : ℝ≥0) (l : ℝ) (ht : 0 < t) (hM : t ≤ M)
    (hR : ContinuousWithinAt f (Ici t) t) (hL : Tendsto f (𝓝[<] t) (𝓝 l))
    (hj : l < f t) :
    ∀ᶠ n in atTop, ∃ k < ⌈(M : ℝ≥0) / d n⌉₊,
      ε n ≤ f ((k : ℝ≥0) * d n + d n) - f ((k : ℝ≥0) * d n) := by
  let c (n : ℕ) := ⌈t / d n⌉₊
  let k (n : ℕ) := c n - 1
  let s (n : ℕ) := (k n : ℝ≥0) * d n
  let u (n : ℕ) := s n + d n
  have hc (n : ℕ) : 1 ≤ c n := Nat.one_le_ceil_iff.2 (div_pos ht (hd n))
  have hk (n : ℕ) : k n + 1 = c n := Nat.sub_add_cancel (hc n)
  have hkc (n : ℕ) : k n < c n := by
    rw [← hk n]
    exact Nat.lt_succ_self _
  have hst (n : ℕ) : s n < t :=
    (lt_div_iff₀ (hd n)).1 (Nat.lt_ceil.1 (hkc n))
  have htu (n : ℕ) : t ≤ u n := by
    have heq : u n = (c n : ℝ≥0) * d n := by rw [← hk n, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    rw [heq]
    exact (div_le_iff₀ (hd n)).1 (Nat.le_ceil _)
  have hu0 : Tendsto u atTop (𝓝 t) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using tendsto_const_nhds.add hd0)
      htu (fun n => add_le_add (hst n).le le_rfl)
  have hs0 : Tendsto s atTop (𝓝 t) := by
    have heq : (fun n => u n - d n) = s := funext fun n => add_tsub_cancel_right (s n) (d n)
    simpa only [heq, tsub_zero] using hu0.sub hd0
  have hright := hR.tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hu0, Eventually.of_forall htu⟩)
  have hleft := hL.comp
    (tendsto_nhdsWithin_iff.2 ⟨hs0, Eventually.of_forall hst⟩)
  have hgap : 0 < f t - l - 0 := by
    simpa only [sub_zero] using sub_pos.mpr hj
  have hpos : ∀ᶠ n in atTop, 0 < f (u n) - f (s n) - ε n :=
    ((hright.sub hleft).sub hε) (Ioi_mem_nhds hgap)
  filter_upwards [hpos] with n hn
  exact ⟨k n, (hkc n).trans_le
    (Nat.ceil_mono (div_le_div_of_nonneg_right hM (hd n).le)), sub_nonneg.mp hn.le⟩
