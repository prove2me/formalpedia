-- Prove2me | solution 1 for KServer.chunk_regrid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T14:14:32.127169+00:00
-- url     : https://prove2.me/submissions/5a383af9-d895-4ec6-9fe8-666eaf729a41

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_chunk_saturate
import Definitions.Def_KServer_chunk_var

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open KServer

namespace Regrid

variable {X : Type*} [MetricSpace X] {s t : X} {cA cB T pe : ℝ} {mL : ℕ}

section Setup

variable (C : ChunkSystemB X s t cA cB T pe mL) (M : ℕ) (δ : ℝ)

/-- First time the cumulative mass reaches the grid line `2δ·j`
(with the input length as a sentinel). -/
noncomputable def gtime (j : ℕ) (ω : C.Ω) : ℕ :=
  sInf {h | 2 * δ * j ≤ C.pastSize h ω ∨ h = C.m}

/-- Window boundaries: grid hitting times, forced strictly increasing and
capped so that exactly `M` nonempty windows partition `[0, C.m)`. -/
noncomputable def τ3 : ℕ → C.Ω → ℕ
  | 0 => fun _ => 0
  | (k + 1) => fun ω =>
      if M ≤ k + 1 then C.m
      else min (C.m - (M - (k + 1)))
        (max (τ3 k ω + 1) (gtime C δ (k + 1) ω))

/-- The mass of window `k`. -/
noncomputable def gm (k : ℕ) (ω : C.Ω) : ℝ :=
  C.pastSize (τ3 C M δ (k + 1) ω) ω - C.pastSize (τ3 C M δ k ω) ω

end Setup

section Bounds

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem τ3_zero (ω : C.Ω) : τ3 C M δ 0 ω = 0 := rfl

theorem τ3_last {k : ℕ} (hk : M ≤ k) (hM0 : 0 < M) (ω : C.Ω) :
    τ3 C M δ k ω = C.m := by
  rcases k with - | k
  · omega
  · unfold τ3
    rw [if_pos hk]

theorem τ3_le {k : ℕ} (hk : k ≤ M) (hMm : M ≤ C.m) (ω : C.Ω) :
    τ3 C M δ k ω ≤ C.m - (M - k) := by
  induction k with
  | zero =>
    rw [τ3_zero]
    omega
  | succ k ih =>
    unfold τ3
    by_cases hM : M ≤ k + 1
    · rw [if_pos hM]
      omega
    · rw [if_neg hM]
      omega

theorem τ3_le_m {k : ℕ} (hk : k ≤ M) (hMm : M ≤ C.m) (ω : C.Ω) :
    τ3 C M δ k ω ≤ C.m := by
  have h1 : τ3 C M δ k ω ≤ C.m - (M - k) := τ3_le hk hMm ω
  omega

theorem τ3_succ_def (C : ChunkSystemB X s t cA cB T pe mL) (M : ℕ) (δ : ℝ)
    (k : ℕ) (ω : C.Ω) :
    τ3 C M δ (k + 1) ω = if M ≤ k + 1 then C.m
      else min (C.m - (M - (k + 1)))
        (max (τ3 C M δ k ω + 1) (gtime C δ (k + 1) ω)) := rfl

theorem τ3_lt_succ {k : ℕ} (hk : k + 1 ≤ M) (hMm : M ≤ C.m) (ω : C.Ω) :
    τ3 C M δ k ω < τ3 C M δ (k + 1) ω := by
  have hkle : τ3 C M δ k ω ≤ C.m - (M - k) := τ3_le (by omega) hMm ω
  rw [τ3_succ_def]
  by_cases hM : M ≤ k + 1
  · rw [if_pos hM]
    omega
  · rw [if_neg hM]
    omega

theorem τ3_mono {k k' : ℕ} (hkk : k ≤ k') (hk : k' ≤ M) (hMm : M ≤ C.m)
    (ω : C.Ω) : τ3 C M δ k ω ≤ τ3 C M δ k' ω := by
  induction k', hkk using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
    exact le_trans (ih (by omega)) (le_of_lt (τ3_lt_succ hk hMm ω))

theorem gtime_le_m (j : ℕ) (ω : C.Ω) : gtime C δ j ω ≤ C.m :=
  Nat.sInf_le (by simp)

/-- The cumulative mass is monotone in time. -/
theorem pastSize_mono (hcA0 : 0 ≤ cA) {h h' : ℕ} (hh : h ≤ h') (ω : C.Ω) :
    C.pastSize h ω ≤ C.pastSize h' ω := by
  unfold ChunkSystemB.pastSize
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  · intro i _ _
    exact le_trans hcA0 (C.hsize ω i).1

/-- Cumulative mass at the input end is the total. -/
theorem pastSize_m (ω : C.Ω) : C.pastSize C.m ω = C.totalSize ω := by
  unfold ChunkSystemB.pastSize ChunkSystemB.totalSize
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact i.2

/-- Cumulative mass starts at zero. -/
theorem pastSize_zero (ω : C.Ω) : C.pastSize 0 ω = 0 := by
  unfold ChunkSystemB.pastSize
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_filter] at hi
  omega

/-- Below the grid time, the cumulative mass is below the grid line. -/
theorem pastSize_lt_of_lt_gtime {j h : ℕ} {ω : C.Ω}
    (hh : h < gtime C δ j ω) (hm : h ≠ C.m) :
    C.pastSize h ω < 2 * δ * j := by
  by_contra hcon
  push_neg at hcon
  have hmem : h ∈ {h | 2 * δ * j ≤ C.pastSize h ω ∨ h = C.m} := Or.inl hcon
  have hle : gtime C δ j ω ≤ h := Nat.sInf_le hmem
  omega

/-- At a grid hit (not the sentinel-only case), the line is reached. -/
theorem le_pastSize_gtime {j : ℕ} {ω : C.Ω} (hlt : gtime C δ j ω < C.m) :
    2 * δ * j ≤ C.pastSize (gtime C δ j ω) ω := by
  have hmem : gtime C δ j ω ∈ {h | 2 * δ * j ≤ C.pastSize h ω ∨ h = C.m} :=
    Nat.sInf_mem (⟨C.m, by simp⟩ :
      {h | 2 * δ * j ≤ C.pastSize h ω ∨ h = C.m}.Nonempty)
  rcases hmem with h1 | h1
  · exact h1
  · omega

/-- The overhang at a grid hit is at most one chunk: the cumulative mass at
the grid time is below the line plus the chunk ceiling. -/
theorem pastSize_gtime_lt (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hδ : 0 < δ)
    {j : ℕ} (hj : 0 < j) (ω : C.Ω) :
    C.pastSize (gtime C δ j ω) ω < 2 * δ * j + cB := by
  set g := gtime C δ j ω with hg
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · rw [h0]
    show C.pastSize 0 ω < _
    rw [pastSize_zero]
    have h1 : (0:ℝ) < 2 * δ * j := by
      have : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
      nlinarith
    linarith
  · -- g ≥ 1: the previous step was below the line and one chunk is ≤ cB
    have hprev : C.pastSize (g - 1) ω < 2 * δ * j := by
      refine pastSize_lt_of_lt_gtime (by omega) ?_
      have hgm : g ≤ C.m := gtime_le_m j ω
      -- g - 1 = C.m would give g > C.m
      omega
    have hstep : C.pastSize g ω = C.pastSize (g - 1) ω + C.sizeN (g - 1) ω := by
      have := C.pastSize_succ (g - 1) ω
      rw [show g - 1 + 1 = g by omega] at this
      exact this
    have hsz : C.sizeN (g - 1) ω ≤ cB := by
      by_cases hlt : g - 1 < C.m
      · exact C.sizeN_le hlt ω
      · unfold ChunkSystemB.sizeN
        rw [dif_neg hlt]
        exact hcB0
    rw [hstep]
    linarith

end Bounds

section GridInvariant

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

/-- Upper invariant: boundary masses overshoot their grid lines by at most
one chunk. -/
theorem pastSize_τ3_le (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hδ : 0 < δ)
    (hMm : M ≤ C.m) (hcB2δ : cB ≤ 2 * δ)
    (hTmax : ∀ ω, C.totalSize ω ≤ 2 * δ * M)
    {k : ℕ} (hk : k ≤ M) (ω : C.Ω) :
    C.pastSize (τ3 C M δ k ω) ω ≤ 2 * δ * k + cB := by
  induction k with
  | zero =>
    rw [τ3_zero, pastSize_zero]
    positivity
  | succ k ih =>
    rw [τ3_succ_def]
    by_cases hM : M ≤ k + 1
    · rw [if_pos hM]
      rw [pastSize_m]
      have h1 := hTmax ω
      have h2 : M = k + 1 := by omega
      rw [h2] at h1
      linarith
    · rw [if_neg hM]
      have hbound : C.pastSize (max (τ3 C M δ k ω + 1) (gtime C δ (k + 1) ω)) ω
          ≤ 2 * δ * (k + 1) + cB := by
        rcases max_cases (τ3 C M δ k ω + 1) (gtime C δ (k + 1) ω) with
          ⟨hmax, _⟩ | ⟨hmax, _⟩
        · rw [hmax]
          have hstep : C.pastSize (τ3 C M δ k ω + 1) ω
              = C.pastSize (τ3 C M δ k ω) ω + C.sizeN (τ3 C M δ k ω) ω :=
            C.pastSize_succ _ ω
          have hsz : C.sizeN (τ3 C M δ k ω) ω ≤ cB := by
            by_cases hlt : τ3 C M δ k ω < C.m
            · exact C.sizeN_le hlt ω
            · unfold ChunkSystemB.sizeN
              rw [dif_neg hlt]
              exact hcB0
          have hih := ih (by omega)
          rw [hstep]
          have hcast : (2:ℝ) * δ * (k + 1) = 2 * δ * k + 2 * δ := by
            push_cast
            ring
          rw [hcast]
          linarith
        · rw [hmax]
          have := pastSize_gtime_lt (C := C) hcA0 hcB0 hδ
            (j := k + 1) (by omega) ω
          have hcast : (2:ℝ) * δ * ((k:ℝ) + 1) = 2 * δ * ((k + 1 : ℕ) : ℝ) := by
            push_cast
            ring
          linarith [this]
      refine le_trans (pastSize_mono hcA0 (min_le_right _ _) ω) ?_
      push_cast
      push_cast at hbound
      linarith

/-- Lower invariant: a boundary is on the cap chain or has reached its grid
line. -/
theorem τ3_lower (hcA0 : 0 ≤ cA) (hMm : M ≤ C.m) (hδ : 0 < δ)
    {k : ℕ} (hk : k ≤ M) (ω : C.Ω) :
    τ3 C M δ k ω = C.m - (M - k) ∨
      2 * δ * k ≤ C.pastSize (τ3 C M δ k ω) ω := by
  rcases k with - | k
  · right
    rw [τ3_zero, pastSize_zero]
    simp
  · rw [τ3_succ_def]
    by_cases hM : M ≤ k + 1
    · rw [if_pos hM]
      left
      omega
    · rw [if_neg hM]
      rcases min_cases (C.m - (M - (k + 1)))
        (max (τ3 C M δ k ω + 1) (gtime C δ (k + 1) ω)) with
        ⟨hmin, _⟩ | ⟨hmin, hlt⟩
      · rw [hmin]
        left
        rfl
      · rw [hmin]
        right
        have hcap : max (τ3 C M δ k ω + 1) (gtime C δ (k + 1) ω) < C.m := by
          omega
        have hgt : gtime C δ (k + 1) ω < C.m :=
          lt_of_le_of_lt (le_max_right _ _) hcap
        have hline := le_pastSize_gtime (C := C) (j := k + 1) hgt
        have hmono : C.pastSize (gtime C δ (k + 1) ω) ω
            ≤ C.pastSize (max (τ3 C M δ k ω + 1) (gtime C δ (k + 1) ω)) ω :=
          pastSize_mono hcA0 (le_max_right _ _) ω
        push_cast at hline ⊢
        linarith

/-- On the cap chain, windows are single chunks. -/
theorem τ3_cap_succ (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M) {ω : C.Ω}
    (hcap : τ3 C M δ k ω = C.m - (M - k)) :
    τ3 C M δ (k + 1) ω = τ3 C M δ k ω + 1 := by
  by_cases hM : M ≤ k + 1
  · rw [τ3_last hM (by omega) ω]
    omega
  · rw [τ3_succ_def, if_neg hM]
    have h1 : τ3 C M δ k ω + 1 = C.m - (M - (k + 1)) := by omega
    have h2 : min (C.m - (M - (k + 1)))
        (max (τ3 C M δ k ω + 1) (gtime C δ (k + 1) ω))
        = C.m - (M - (k + 1)) := by
      refine min_eq_left ?_
      omega
    omega

/-- **Pointwise window-mass ceiling**: every window mass is at most
`2δ + cB`. -/
theorem gm_le (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hδ : 0 < δ)
    (hMm : M ≤ C.m) (hcB2δ : cB ≤ 2 * δ)
    (hTmax : ∀ ω, C.totalSize ω ≤ 2 * δ * M)
    {k : ℕ} (hk : k + 1 ≤ M) (ω : C.Ω) :
    gm C M δ k ω ≤ 2 * δ + cB := by
  unfold gm
  rcases τ3_lower (C := C) hcA0 hMm hδ (k := k) (by omega) ω with hcap | hline
  · -- cap chain: single chunk
    have hsucc := τ3_cap_succ (C := C) (δ := δ) hMm hk hcap
    rw [hsucc]
    have hstep : C.pastSize (τ3 C M δ k ω + 1) ω
        = C.pastSize (τ3 C M δ k ω) ω + C.sizeN (τ3 C M δ k ω) ω :=
      C.pastSize_succ _ ω
    rw [hstep]
    have hsz : C.sizeN (τ3 C M δ k ω) ω ≤ cB := by
      by_cases hlt : τ3 C M δ k ω < C.m
      · exact C.sizeN_le hlt ω
      · unfold ChunkSystemB.sizeN
        rw [dif_neg hlt]
        exact hcB0
    linarith
  · -- grid-aligned start
    have hup := pastSize_τ3_le (C := C) hcA0 hcB0 hδ hMm hcB2δ hTmax
      (k := k + 1) hk ω
    have hcast : (2:ℝ) * δ * ((k:ℝ) + 1) = 2 * δ * k + 2 * δ := by ring
    push_cast at hup hline ⊢
    linarith

/-- Window masses are nonnegative. -/
theorem gm_nonneg (hcA0 : 0 ≤ cA) (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M)
    (ω : C.Ω) : 0 ≤ gm C M δ k ω := by
  unfold gm
  have h1 : τ3 C M δ k ω ≤ τ3 C M δ (k + 1) ω :=
    le_of_lt (τ3_lt_succ hk hMm ω)
  linarith [pastSize_mono (C := C) hcA0 h1 ω]

/-- The window masses telescope to the total. -/
theorem sum_gm (hM0 : 0 < M) (ω : C.Ω) :
    ∑ k ∈ Finset.range M, gm C M δ k ω = C.totalSize ω := by
  have htel : ∀ n : ℕ, ∑ k ∈ Finset.range n, gm C M δ k ω
      = C.pastSize (τ3 C M δ n ω) ω - C.pastSize (τ3 C M δ 0 ω) ω := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold gm
      ring
  rw [htel M, τ3_zero, τ3_last (le_refl M) hM0 ω, pastSize_m, pastSize_zero]
  ring

end GridInvariant

section Congr

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem chunk_agree3 {b : ℕ} {ω ω' : C.Ω} (hh : C.hist b ω = C.hist b ω')
    {j : Fin C.m} (hj : (j : ℕ) < b) : C.chunk ω j = C.chunk ω' j :=
  C.hadapt j ω ω' (C.href ((j : ℕ) + 1) b (by omega) ω ω' hh)

theorem take_ofFn_agree {b : ℕ} {ω ω' : C.Ω} (hh : C.hist b ω = C.hist b ω') :
    (List.ofFn (C.chunk ω)).take b = (List.ofFn (C.chunk ω')).take b := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    have hkb : k < b := by
      simp only [List.length_take, List.length_ofFn] at h1
      omega
    exact chunk_agree3 hh hkb

theorem pastSize_congr_le {b : ℕ} {ω ω' : C.Ω}
    (hh : C.hist b ω' = C.hist b ω) {h : ℕ} (hb : h ≤ b) :
    C.pastSize h ω' = C.pastSize h ω :=
  C.pastSize_congr (C.href h b hb ω' ω hh)

theorem gtime_congr {b : ℕ} {ω ω' : C.Ω}
    (hh : C.hist b ω' = C.hist b ω) {j : ℕ}
    (hle : gtime C δ j ω ≤ b) : gtime C δ j ω' = gtime C δ j ω := by
  have hiff : ∀ {h : ℕ}, h ≤ b →
      ((2 * δ * j ≤ C.pastSize h ω ∨ h = C.m)
        ↔ (2 * δ * j ≤ C.pastSize h ω' ∨ h = C.m)) := by
    intro h hb
    rw [pastSize_congr_le hh hb]
  have h1 : gtime C δ j ω' ≤ gtime C δ j ω := by
    refine Nat.sInf_le ?_
    have hmem : gtime C δ j ω ∈
        {h | 2 * δ * j ≤ C.pastSize h ω ∨ h = C.m} :=
      Nat.sInf_mem (⟨C.m, by simp⟩ :
        {h | 2 * δ * j ≤ C.pastSize h ω ∨ h = C.m}.Nonempty)
    exact (hiff hle).mp hmem
  rcases Nat.lt_or_ge (gtime C δ j ω') (gtime C δ j ω) with hlt | hge
  · exfalso
    have hmem' : gtime C δ j ω' ∈
        {h | 2 * δ * j ≤ C.pastSize h ω' ∨ h = C.m} :=
      Nat.sInf_mem (⟨C.m, by simp⟩ :
        {h | 2 * δ * j ≤ C.pastSize h ω' ∨ h = C.m}.Nonempty)
    have hmem : gtime C δ j ω' ∈
        {h | 2 * δ * j ≤ C.pastSize h ω ∨ h = C.m} :=
      (hiff (by omega)).mpr hmem'
    have h2 : gtime C δ j ω ≤ gtime C δ j ω' := Nat.sInf_le hmem
    omega
  · omega

theorem gtime_gt {b : ℕ} {ω ω' : C.Ω}
    (hh : C.hist b ω' = C.hist b ω) {j : ℕ}
    (hgt : b < gtime C δ j ω) : b < gtime C δ j ω' := by
  by_contra hcon
  push_neg at hcon
  have h1 : gtime C δ j ω = gtime C δ j ω' :=
    gtime_congr (by rw [hh]) hcon
  omega

theorem τ3_congr (hMm : M ≤ C.m) :
    ∀ (k : ℕ), k ≤ M → ∀ {b : ℕ} {ω ω' : C.Ω},
    C.hist b ω' = C.hist b ω → τ3 C M δ k ω ≤ b →
    τ3 C M δ k ω' = τ3 C M δ k ω := by
  intro k
  induction k with
  | zero =>
    intro _ b ω ω' hh _
    rw [τ3_zero, τ3_zero]
  | succ k ih =>
    intro hk b ω ω' hh hle
    by_cases hM : M ≤ k + 1
    · rw [τ3_succ_def, τ3_succ_def, if_pos hM, if_pos hM]
    · have hklt : τ3 C M δ k ω < τ3 C M δ (k + 1) ω := τ3_lt_succ (by omega) hMm ω
      have hkb : τ3 C M δ k ω ≤ b := by omega
      have hτk : τ3 C M δ k ω' = τ3 C M δ k ω := ih (by omega) hh hkb
      rw [τ3_succ_def, τ3_succ_def, if_neg hM, if_neg hM, hτk]
      set a := τ3 C M δ k ω
      rcases Nat.lt_or_ge b (gtime C δ (k + 1) ω) with htr | htr
      · have htr' : b < gtime C δ (k + 1) ω' := gtime_gt hh htr
        have hval : τ3 C M δ (k + 1) ω
            = min (C.m - (M - (k + 1))) (max (a + 1) (gtime C δ (k + 1) ω)) := by
          rw [τ3_succ_def, if_neg hM]
        rw [hval] at hle hklt
        omega
      · have htr' : gtime C δ (k + 1) ω' = gtime C δ (k + 1) ω := gtime_congr hh htr
        rw [htr']

theorem gm_congr (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M) {b : ℕ}
    {ω ω' : C.Ω} (hh : C.hist b ω' = C.hist b ω)
    (hle : τ3 C M δ (k + 1) ω ≤ b) : gm C M δ k ω' = gm C M δ k ω := by
  have hklt : τ3 C M δ k ω < τ3 C M δ (k + 1) ω := τ3_lt_succ hk hMm ω
  have hτ1 : τ3 C M δ (k + 1) ω' = τ3 C M δ (k + 1) ω :=
    τ3_congr hMm (k + 1) hk hh hle
  have hτ0 : τ3 C M δ k ω' = τ3 C M δ k ω :=
    τ3_congr hMm k (by omega) hh (by omega)
  unfold gm
  rw [hτ1, hτ0, pastSize_congr_le hh hle,
    pastSize_congr_le hh (by omega)]

end Congr

section Output

variable (C : ChunkSystemB X s t cA cB T pe mL) (M : ℕ) (δ : ℝ)

/-- Output history: boundary time paired with the fine history there. -/
noncomputable def ghist (n : ℕ) (ω : C.Ω) : ℕ :=
  Nat.pair (τ3 C M δ n ω) (C.hist (τ3 C M δ n ω) ω)

/-- Output chunks: the input chunks of one window, concatenated. -/
noncomputable def gchunk (ω : C.Ω) (k : ℕ) : List (Set X) :=
  (((List.ofFn (C.chunk ω)).take (τ3 C M δ (k + 1) ω)).drop (τ3 C M δ k ω)).flatten

/-- Output sizes: conditional window masses. -/
noncomputable def gsize (k : ℕ) (ω : C.Ω) : ℝ :=
  C.condExp (gm C M δ k) (τ3 C M δ k ω) ω

end Output

section OutputLemmas

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem ghist_pair {n : ℕ} {ω ω' : C.Ω} :
    ghist C M δ n ω = ghist C M δ n ω'
      ↔ τ3 C M δ n ω = τ3 C M δ n ω'
        ∧ C.hist (τ3 C M δ n ω) ω = C.hist (τ3 C M δ n ω) ω' := by
  unfold ghist
  rw [Nat.pair_eq_pair]
  constructor
  · rintro ⟨he, hf⟩
    rw [← he] at hf
    exact ⟨he, hf⟩
  · rintro ⟨he, hf⟩
    rw [← he]
    exact ⟨rfl, hf⟩

theorem ghist_ref (hMm : M ≤ C.m) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ M)
    {ω ω' : C.Ω} (hh : ghist C M δ j ω = ghist C M δ j ω') :
    ghist C M δ i ω = ghist C M δ i ω' := by
  obtain ⟨he, hf⟩ := ghist_pair.mp hh
  have hτi : τ3 C M δ i ω ≤ τ3 C M δ j ω := τ3_mono hij hj hMm ω
  have hτeq : τ3 C M δ i ω' = τ3 C M δ i ω :=
    τ3_congr hMm i (by omega) hf.symm hτi
  rw [ghist_pair]
  refine ⟨hτeq.symm, ?_⟩
  exact C.href (τ3 C M δ i ω) (τ3 C M δ j ω) hτi ω ω' hf

theorem gchunk_congr (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M) {ω ω' : C.Ω}
    (hh : ghist C M δ (k + 1) ω = ghist C M δ (k + 1) ω') :
    gchunk C M δ ω k = gchunk C M δ ω' k := by
  obtain ⟨he, hf⟩ := ghist_pair.mp hh
  have hτk : τ3 C M δ k ω ≤ τ3 C M δ (k + 1) ω :=
    le_of_lt (τ3_lt_succ hk hMm ω)
  have hτeq : τ3 C M δ k ω' = τ3 C M δ k ω :=
    τ3_congr hMm k (by omega) hf.symm hτk
  unfold gchunk
  rw [← he, hτeq, take_ofFn_agree hf]

theorem gsize_congr (hMm : M ≤ C.m) {k : ℕ} {ω ω' : C.Ω}
    (hh : ghist C M δ k ω = ghist C M δ k ω') :
    gsize C M δ k ω = gsize C M δ k ω' := by
  obtain ⟨he, hf⟩ := ghist_pair.mp hh
  unfold gsize
  rw [← he]
  exact (C.condExp_congr _ hf.symm).symm

/-- Windows partition the input sequence. -/
theorem gchunk_prefix (hMm : M ≤ C.m) (ω : C.Ω) (i : ℕ) (hi : i ≤ M) :
    ((List.ofFn (fun k : Fin M => gchunk C M δ ω (k : ℕ))).take i).flatten
      = ((List.ofFn (C.chunk ω)).take (τ3 C M δ i ω)).flatten := by
  induction i with
  | zero =>
    rw [τ3_zero]
    simp
  | succ i ih =>
    have hiM : i < M := by omega
    have htake : (List.ofFn (fun k : Fin M => gchunk C M δ ω (k : ℕ))).take (i + 1)
        = (List.ofFn (fun k : Fin M => gchunk C M δ ω (k : ℕ))).take i
          ++ [gchunk C M δ ω i] := by
      rw [List.take_succ]
      congr 1
      rw [List.getElem?_eq_getElem (by simp [hiM])]
      simp only [List.getElem_ofFn]
      rfl
    rw [htake, List.flatten_append, ih (by omega)]
    unfold gchunk
    rw [List.flatten_cons, List.flatten_nil, List.append_nil]
    have hτi : τ3 C M δ i ω ≤ τ3 C M δ (i + 1) ω :=
      le_of_lt (τ3_lt_succ (by omega) hMm ω)
    rw [← List.flatten_append]
    congr 1
    have hsplit := List.take_append_drop (τ3 C M δ i ω)
      ((List.ofFn (C.chunk ω)).take (τ3 C M δ (i + 1) ω))
    rw [List.take_take, min_eq_left hτi] at hsplit
    exact hsplit

theorem gchunk_flatten (hMm : M ≤ C.m) (hM0 : 0 < M) (ω : C.Ω) :
    (List.ofFn (fun k : Fin M => gchunk C M δ ω (k : ℕ))).flatten
      = (List.ofFn (C.chunk ω)).flatten := by
  have h1 := gchunk_prefix (C := C) (δ := δ) hMm ω M (le_refl M)
  rw [List.take_of_length_le (by simp)] at h1
  rw [τ3_last (le_refl M) hM0 ω, List.take_of_length_le (by simp)] at h1
  exact h1

theorem gchunk_ne (ω : C.Ω) (k : ℕ) : ∀ S ∈ gchunk C M δ ω k, S.Nonempty := by
  intro S hS
  unfold gchunk at hS
  rw [List.mem_flatten] at hS
  obtain ⟨l, hl, hSl⟩ := hS
  have hl2 : l ∈ List.ofFn (C.chunk ω) :=
    List.mem_of_mem_take (List.mem_of_mem_drop hl)
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hl2
  refine C.hne ω j S ?_
  rw [hj]
  exact hSl

/-- Pointwise size bounds: nonnegative and at most `2δ + cB`. -/
theorem gsize_nonneg (hcA0 : 0 ≤ cA) (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M)
    (ω : C.Ω) : 0 ≤ gsize C M δ k ω :=
  C.le_condExp fun ω' _ => gm_nonneg hcA0 hMm hk ω'

theorem gsize_le (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hδ : 0 < δ)
    (hMm : M ≤ C.m) (hcB2δ : cB ≤ 2 * δ)
    (hTmax : ∀ ω, C.totalSize ω ≤ 2 * δ * M)
    {k : ℕ} (hk : k + 1 ≤ M) (ω : C.Ω) :
    gsize C M δ k ω ≤ 2 * δ + cB :=
  C.condExp_le fun ω' _ => gm_le hcA0 hcB0 hδ hMm hcB2δ hTmax hk ω'

end OutputLemmas

section Charge

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem τ3_gt (hMm : M ≤ C.m) {k : ℕ} (hk : k ≤ M) {b : ℕ}
    {ω ω' : C.Ω} (hh : C.hist b ω' = C.hist b ω)
    (hgt : b < τ3 C M δ k ω) : b < τ3 C M δ k ω' := by
  by_contra hcon
  push_neg at hcon
  have h1 := τ3_congr hMm k hk (show C.hist b ω = C.hist b ω' from hh.symm) hcon
  omega

/-- Interval mass telescopes through the cumulative mass. -/
theorem sum_Ico_sizeN {a b : ℕ} (hab : a ≤ b) (ω : C.Ω) :
    ∑ i ∈ Finset.Ico a b, C.sizeN i ω = C.pastSize b ω - C.pastSize a ω := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, ih, C.pastSize_succ b ω]
    ring

/-- The bail-aware cost of the rest of window `k` from input position `j`. -/
noncomputable def gcost (C : ChunkSystemB X s t cA cB T pe mL) (M : ℕ) (δ : ℝ)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (p' : ℝ) (k j : ℕ) (ω : C.Ω) : ℝ :=
  E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
    ((((List.ofFn (C.chunk ω)).take (τ3 C M δ (k + 1) ω)).drop j).flatten) p'

theorem take_flatten_succ3 (ω : C.Ω) {j : ℕ} (hj : j < C.m) :
    ((List.ofFn (C.chunk ω)).take (j + 1)).flatten
      = ((List.ofFn (C.chunk ω)).take j).flatten ++ C.chunk ω ⟨j, hj⟩ := by
  have h1 : (List.ofFn (C.chunk ω)).take (j + 1)
      = (List.ofFn (C.chunk ω)).take j ++ [C.chunk ω ⟨j, hj⟩] := by
    rw [List.take_succ]
    congr 1
    rw [List.getElem?_eq_getElem (by simp [hj])]
    simp only [List.getElem_ofFn]
    rfl
  rw [h1, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]

theorem window_cons3 (hMm : M ≤ C.m) (ω : C.Ω) {k j : ℕ} (hk : k + 1 ≤ M)
    (hj : j < τ3 C M δ (k + 1) ω) :
    (((List.ofFn (C.chunk ω)).take (τ3 C M δ (k + 1) ω)).drop j)
      = C.chunk ω ⟨j, lt_of_lt_of_le hj (τ3_le_m hk hMm ω)⟩
        :: (((List.ofFn (C.chunk ω)).take (τ3 C M δ (k + 1) ω)).drop (j + 1)) := by
  have hjm : j < C.m := lt_of_lt_of_le hj (τ3_le_m hk hMm ω)
  have hlen : j < ((List.ofFn (C.chunk ω)).take (τ3 C M δ (k + 1) ω)).length := by
    simp only [List.length_take, List.length_ofFn]
    omega
  rw [List.drop_eq_getElem_cons hlen]
  congr 1
  rw [List.getElem_take, List.getElem_ofFn]

theorem gcost_step_no_bail (hMm : M ≤ C.m)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (p' : ℝ)
    {k j : ℕ} (hk : k + 1 ≤ M) (ω : C.Ω) (hj : j < τ3 C M δ (k + 1) ω)
    (hbail : bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
      (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ3_le_m hk hMm ω)⟩) = none) :
    gcost C M δ E bail p' k j ω
      = E.costOn (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ3_le_m hk hMm ω)⟩)
        + gcost C M δ E bail p' k (j + 1) ω := by
  have hjm : j < C.m := lt_of_lt_of_le hj (τ3_le_m hk hMm ω)
  unfold gcost
  rw [window_cons3 hMm ω hk hj, List.flatten_cons,
    E.bailCost_append_of_no_bail bail _ _ _ _ hbail,
    ← take_flatten_succ3 ω hjm]

theorem gcost_step_bail (hMm : M ≤ C.m)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (p' : ℝ)
    {k j q : ℕ} (hk : k + 1 ≤ M) (ω : C.Ω) (hj : j < τ3 C M δ (k + 1) ω)
    (hbail : bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
      (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ3_le_m hk hMm ω)⟩) = some q) :
    gcost C M δ E bail p' k j ω
      = E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ3_le_m hk hMm ω)⟩) pe
        + (p' - pe) := by
  have hjm : j < C.m := lt_of_lt_of_le hj (τ3_le_m hk hMm ω)
  unfold gcost
  rw [window_cons3 hMm ω hk hj, List.flatten_cons,
    E.bailCost_append_of_bail bail _ _ _ _ hbail,
    E.bailCost_price_of_bail bail _ _ pe p' hbail]

theorem gcost_nonneg (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {p' : ℝ} (hp' : 0 ≤ p') (k j : ℕ) (ω : C.Ω) :
    0 ≤ gcost C M δ E bail p' k j ω :=
  E.bailCost_nonneg bail _ _ hp'

/-- The bail rule is quiet on all complete input chunks in `[a, j)`. -/
def quiet3 (bail : List (Set X) → Bool) (a j : ℕ) (ω : C.Ω) : Prop :=
  ∀ k, a ≤ k → k < j → ∀ hk : k < C.m,
    bailTime bail (((List.ofFn (C.chunk ω)).take k).flatten)
      (C.chunk ω ⟨k, hk⟩) = none

open Classical in
/-- The charging induction: remaining window mass is dominated by the
bail-aware cost, with escapes financed pointwise. -/
theorem charge3 (hMm : M ≤ C.m) (hM0 : 0 < M)
    (hcA0 : 0 ≤ cA) (hδ : 0 < δ) (hcB0 : 0 ≤ cB) (hcB2δ : cB ≤ 2 * δ)
    (hTmax : ∀ ω, C.totalSize ω ≤ 2 * δ * M)
    {p' : ℝ} (hp : pe + (2 * δ + cB) ≤ p') (hpe : 0 ≤ pe)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {k : ℕ} (hk : k + 1 ≤ M) (ω₀ : C.Ω) :
    ∀ d j, τ3 C M δ k ω₀ ≤ j → C.m ≤ j + d →
    ∑ ω ∈ (C.atom (τ3 C M δ k ω₀) ω₀).filter
        (fun ω => j < τ3 C M δ (k + 1) ω ∧ quiet3 bail (τ3 C M δ k ω₀) j ω),
      C.P ω * (∑ i ∈ Finset.Ico j (τ3 C M δ (k + 1) ω), C.sizeN i ω)
    ≤ ∑ ω ∈ (C.atom (τ3 C M δ k ω₀) ω₀).filter
        (fun ω => j < τ3 C M δ (k + 1) ω ∧ quiet3 bail (τ3 C M δ k ω₀) j ω),
      C.P ω * gcost C M δ E bail p' k j ω := by
  have hp0 : 0 ≤ p' := by linarith
  have hempty : ∀ j, C.m ≤ j →
      (C.atom (τ3 C M δ k ω₀) ω₀).filter
        (fun ω => j < τ3 C M δ (k + 1) ω ∧ quiet3 bail (τ3 C M δ k ω₀) j ω) = ∅ := by
    intro j hj
    rw [Finset.filter_eq_empty_iff]
    rintro ω - ⟨h1, -⟩
    have h3 : τ3 C M δ (k + 1) ω ≤ C.m := τ3_le_m hk hMm ω
    omega
  intro d
  induction d with
  | zero =>
    intro j haj hjd
    rw [hempty j (by omega)]
    simp
  | succ d ih =>
    intro j haj hjd
    by_cases hjm : C.m ≤ j
    · rw [hempty j hjm]
      simp
    · push_neg at hjm
      set a := τ3 C M δ k ω₀ with ha_def
      set NBW := (C.atom a ω₀).filter
        (fun ω => j < τ3 C M δ (k + 1) ω ∧ quiet3 bail a j ω) with hNBW_def
      have hmemA : ∀ ω ∈ NBW, C.hist a ω = C.hist a ω₀ := by
        intro ω hm
        rw [hNBW_def, Finset.mem_filter] at hm
        exact C.mem_atom.mp hm.1
      have hb_NBW : ∀ ω ∈ NBW, j < τ3 C M δ (k + 1) ω := by
        intro ω hm
        rw [hNBW_def, Finset.mem_filter] at hm
        exact hm.2.1
      have hpeel : ∀ ω ∈ NBW,
          ∑ i ∈ Finset.Ico j (τ3 C M δ (k + 1) ω), C.sizeN i ω
            = C.sizeN j ω
              + ∑ i ∈ Finset.Ico (j + 1) (τ3 C M δ (k + 1) ω), C.sizeN i ω := by
        intro ω hm
        exact Finset.sum_eq_sum_Ico_succ_bot (hb_NBW ω hm) _
      have hsat_NBW : ∀ ω ∈ NBW, ∀ ω', C.hist j ω' = C.hist j ω → ω' ∈ NBW := by
        intro ω hm ω' hh
        rw [hNBW_def, Finset.mem_filter] at hm ⊢
        have hA := hm.1
        have hb := hm.2.1
        have hq := hm.2.2
        refine ⟨?_, ?_, ?_⟩
        · rw [C.mem_atom] at hA ⊢
          exact (C.href a j haj ω' ω hh).trans hA
        · exact τ3_gt hMm hk hh hb
        · intro i hai hij hi
          have hhk : C.hist i ω' = C.hist i ω := C.href i j (by omega) ω' ω hh
          have hhk1 : C.hist (i + 1) ω' = C.hist (i + 1) ω :=
            C.href (i + 1) j (by omega) ω' ω hh
          rw [take_ofFn_agree hhk, chunk_agree3 hhk1 (Nat.lt_succ_self i)]
          exact hq i hai hij hi
      have hprem : ∑ ω ∈ NBW, C.P ω * C.sizeN j ω
          ≤ ∑ ω ∈ NBW, C.P ω *
              E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe := by
        refine ChunkSystemB.sum_saturated_le C j NBW hsat_NBW _ _ fun ω₁ _ => ?_
        have hpre : C.size ω₁ ⟨j, hjm⟩ * C.mass (C.atom j ω₁)
            ≤ ∑ ω' ∈ C.atom j ω₁, C.P ω' *
                E.bailCost bail (((List.ofFn (C.chunk ω')).take j).flatten)
                  (C.chunk ω' ⟨j, hjm⟩) pe := C.hcost ⟨j, hjm⟩ ω₁ E bail
        refine le_trans (le_of_eq ?_) hpre
        unfold ChunkSystemB.mass
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω' hm' => ?_
        unfold ChunkSystemB.sizeN
        rw [dif_pos hjm, C.hsmeas ⟨j, hjm⟩ ω' ω₁ (C.mem_atom.mp hm')]
        ring
      set cond1 : C.Ω → Prop := fun ω =>
        bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, hjm⟩) = none with hcond1_def
      set S1 := NBW.filter (fun ω => cond1 ω ∧ j + 1 < τ3 C M δ (k + 1) ω) with hS1_def
      set S2 := NBW.filter (fun ω => cond1 ω ∧ ¬ j + 1 < τ3 C M δ (k + 1) ω) with hS2_def
      set S3 := NBW.filter (fun ω => ¬ cond1 ω) with hS3_def
      have hS1_eq : S1 = (C.atom a ω₀).filter
          (fun ω => j + 1 < τ3 C M δ (k + 1) ω ∧ quiet3 bail a (j + 1) ω) := by
        rw [hS1_def, hNBW_def, Finset.filter_filter]
        ext ω
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hA, ⟨hb, hq⟩, hc1, hb1⟩
          refine ⟨hA, hb1, ?_⟩
          intro i hai hij hi
          rcases Nat.lt_or_ge i j with hij' | hij'
          · exact hq i hai hij' hi
          · have hieq : i = j := by omega
            subst hieq
            exact hc1
        · rintro ⟨hA, hb1, hq⟩
          have hc1 : cond1 ω := hq j haj (by omega) hjm
          exact ⟨hA, ⟨by omega, fun i hai hij hi => hq i hai (by omega) hi⟩, hc1, hb1⟩
      have hsplit0 : ∀ f : C.Ω → ℝ, ∑ ω ∈ NBW, f ω
          = (∑ ω ∈ S1, f ω + ∑ ω ∈ S2, f ω) + ∑ ω ∈ S3, f ω := by
        intro f
        have e1 : NBW.filter cond1 = S1 ∪ S2 := by
          rw [hS1_def, hS2_def]
          ext ω
          simp only [Finset.mem_filter, Finset.mem_union]
          tauto
        have hdisj : Disjoint S1 S2 := by
          rw [hS1_def, hS2_def, Finset.disjoint_filter]
          tauto
        rw [← Finset.sum_filter_add_sum_filter_not NBW cond1 f, e1,
          Finset.sum_union hdisj, hS3_def]
      have hS2_b : ∀ ω ∈ S2, τ3 C M δ (k + 1) ω = j + 1 := by
        intro ω hm
        rw [hS2_def, Finset.mem_filter] at hm
        have h2 := hb_NBW ω hm.1
        have h1 := hm.2.2
        omega
      have htail_le : ∀ ω ∈ NBW,
          ∑ i ∈ Finset.Ico (j + 1) (τ3 C M δ (k + 1) ω), C.sizeN i ω
            ≤ p' - pe := by
        intro ω hm
        have haω : τ3 C M δ k ω = a :=
          τ3_congr hMm k (by omega) (hmemA ω hm) (le_refl a)
        have haj' : τ3 C M δ k ω ≤ j + 1 := by omega
        have hend : j + 1 ≤ τ3 C M δ (k + 1) ω := hb_NBW ω hm
        have hsub : ∑ i ∈ Finset.Ico (j + 1) (τ3 C M δ (k + 1) ω), C.sizeN i ω
            ≤ ∑ i ∈ Finset.Ico (τ3 C M δ k ω) (τ3 C M δ (k + 1) ω), C.sizeN i ω := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun i _ _ => C.sizeN_nonneg hcA0 i ω)
          refine Finset.Ico_subset_Ico (by omega) (le_refl _)
        have hgm : ∑ i ∈ Finset.Ico (τ3 C M δ k ω) (τ3 C M δ (k + 1) ω), C.sizeN i ω
            = gm C M δ k ω := by
          rw [sum_Ico_sizeN (le_of_lt (τ3_lt_succ hk hMm ω)) ω]
          rfl
        have hcap : gm C M δ k ω ≤ 2 * δ + cB :=
          gm_le hcA0 hcB0 hδ hMm hcB2δ hTmax hk ω
        linarith
      have hcost_S12 : ∀ ω ∈ NBW, cond1 ω →
          C.P ω * gcost C M δ E bail p' k j ω
            = C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe
              + C.P ω * gcost C M δ E bail p' k (j + 1) ω := by
        intro ω hm hc
        have hb := hb_NBW ω hm
        simp only [hcond1_def] at hc
        rw [gcost_step_no_bail hMm E bail p' hk ω hb hc,
          E.bailCost_of_no_bail bail _ _ pe hc]
        ring
      have hcost_S3 : ∀ ω ∈ S3,
          C.P ω * gcost C M δ E bail p' k j ω
            = C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe
              + C.P ω * (p' - pe) := by
        intro ω hm
        rw [hS3_def, Finset.mem_filter] at hm
        have hb := hb_NBW ω hm.1
        have hc := hm.2
        simp only [hcond1_def] at hc
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
        rw [gcost_step_bail hMm E bail p' hk ω hb hq]
        ring
      have hS1_mem : ∀ ω ∈ S1, ω ∈ NBW ∧ cond1 ω := by
        intro ω hm
        rw [hS1_def, Finset.mem_filter] at hm
        exact ⟨hm.1, hm.2.1⟩
      have hS2_mem : ∀ ω ∈ S2, ω ∈ NBW ∧ cond1 ω := by
        intro ω hm
        rw [hS2_def, Finset.mem_filter] at hm
        exact ⟨hm.1, hm.2.1⟩
      have hS_sub : ∀ ω ∈ S3, ω ∈ NBW := by
        intro ω hm
        rw [hS3_def, Finset.mem_filter] at hm
        exact hm.1
      have hLHS : ∑ ω ∈ NBW, C.P ω *
            (∑ i ∈ Finset.Ico j (τ3 C M δ (k + 1) ω), C.sizeN i ω)
          = ∑ ω ∈ NBW, C.P ω * C.sizeN j ω
            + ((∑ ω ∈ S1, C.P ω *
                  (∑ i ∈ Finset.Ico (j + 1) (τ3 C M δ (k + 1) ω), C.sizeN i ω)
              + ∑ ω ∈ S2, C.P ω *
                  (∑ i ∈ Finset.Ico (j + 1) (τ3 C M δ (k + 1) ω), C.sizeN i ω))
              + ∑ ω ∈ S3, C.P ω *
                  (∑ i ∈ Finset.Ico (j + 1) (τ3 C M δ (k + 1) ω), C.sizeN i ω)) := by
        rw [Finset.sum_congr rfl fun ω hm => by rw [hpeel ω hm, mul_add],
          Finset.sum_add_distrib,
          hsplit0 (fun ω => C.P ω *
            (∑ i ∈ Finset.Ico (j + 1) (τ3 C M δ (k + 1) ω), C.sizeN i ω))]
      have hRHS : ∑ ω ∈ NBW, C.P ω * gcost C M δ E bail p' k j ω
          = ∑ ω ∈ NBW, C.P ω * E.bailCost bail
              (((List.ofFn (C.chunk ω)).take j).flatten) (C.chunk ω ⟨j, hjm⟩) pe
            + ((∑ ω ∈ S1, C.P ω * gcost C M δ E bail p' k (j + 1) ω
              + ∑ ω ∈ S2, C.P ω * gcost C M δ E bail p' k (j + 1) ω)
              + ∑ ω ∈ S3, C.P ω * (p' - pe)) := by
        rw [hsplit0 (fun ω => C.P ω * gcost C M δ E bail p' k j ω),
          hsplit0 (fun ω => C.P ω * E.bailCost bail
            (((List.ofFn (C.chunk ω)).take j).flatten) (C.chunk ω ⟨j, hjm⟩) pe)]
        rw [Finset.sum_congr rfl fun ω hm =>
            hcost_S12 ω (hS1_mem ω hm).1 (hS1_mem ω hm).2,
          Finset.sum_congr rfl fun ω hm =>
            hcost_S12 ω (hS2_mem ω hm).1 (hS2_mem ω hm).2,
          Finset.sum_congr rfl (hcost_S3),
          Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
        ring
      rw [hLHS, hRHS]
      have hIH : ∑ ω ∈ S1, C.P ω *
            (∑ i ∈ Finset.Ico (j + 1) (τ3 C M δ (k + 1) ω), C.sizeN i ω)
          ≤ ∑ ω ∈ S1, C.P ω * gcost C M δ E bail p' k (j + 1) ω := by
        rw [hS1_eq]
        exact ih (j + 1) (by omega) (by omega)
      have hS2_zero : ∑ ω ∈ S2, C.P ω *
            (∑ i ∈ Finset.Ico (j + 1) (τ3 C M δ (k + 1) ω), C.sizeN i ω)
          ≤ ∑ ω ∈ S2, C.P ω * gcost C M δ E bail p' k (j + 1) ω := by
        refine Finset.sum_le_sum fun ω hm => ?_
        rw [hS2_b ω hm, Finset.Ico_self, Finset.sum_empty, mul_zero]
        exact mul_nonneg (le_of_lt (C.hP ω)) (gcost_nonneg E bail hp0 k (j+1) ω)
      have hS3_fin : ∑ ω ∈ S3, C.P ω *
            (∑ i ∈ Finset.Ico (j + 1) (τ3 C M δ (k + 1) ω), C.sizeN i ω)
          ≤ ∑ ω ∈ S3, C.P ω * (p' - pe) := by
        refine Finset.sum_le_sum fun ω hm => ?_
        exact mul_le_mul_of_nonneg_left (htail_le ω (hS_sub ω hm))
          (le_of_lt (C.hP ω))
      linarith [hprem, hIH, hS2_zero, hS3_fin]

end Charge

section Wrap

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem τ3_isStopping (hMm : M ≤ C.m) {k : ℕ} (hk : k ≤ M) :
    C.IsStopping (τ3 C M δ k) := by
  intro h ω ω' hh
  constructor
  · intro hle
    rw [τ3_congr hMm k hk (show C.hist h ω' = C.hist h ω from hh.symm) hle]
    exact hle
  · intro hle
    rw [τ3_congr hMm k hk (show C.hist h ω = C.hist h ω' from hh) hle]
    exact hle

open Classical in
/-- The output conditional cost bound, over the fine boundary atom. -/
theorem gcost_bound (hMm : M ≤ C.m) (hM0 : 0 < M)
    (hcA0 : 0 ≤ cA) (hδ : 0 < δ) (hcB0 : 0 ≤ cB) (hcB2δ : cB ≤ 2 * δ)
    (hTmax : ∀ ω, C.totalSize ω ≤ 2 * δ * M)
    {p' : ℝ} (hp : pe + (2 * δ + cB) ≤ p') (hpe : 0 ≤ pe)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {k : ℕ} (hk : k + 1 ≤ M) (ω₀ : C.Ω) :
    gsize C M δ k ω₀ * C.mass (C.atom (τ3 C M δ k ω₀) ω₀)
      ≤ ∑ ω ∈ C.atom (τ3 C M δ k ω₀) ω₀,
          C.P ω * E.bailCost bail
            (((List.ofFn (fun i : Fin M => gchunk C M δ ω (i : ℕ))).take k).flatten)
            (gchunk C M δ ω k) p' := by
  set a := τ3 C M δ k ω₀ with ha_def
  have hτmem : ∀ ω ∈ C.atom a ω₀, τ3 C M δ k ω = a := fun ω hm =>
    τ3_congr hMm k (by omega) (C.mem_atom.mp hm) (le_refl a)
  have hL : gsize C M δ k ω₀ * C.mass (C.atom a ω₀)
      = ∑ ω ∈ C.atom a ω₀, C.P ω * gm C M δ k ω := by
    unfold ChunkSystemB.mass
    rw [Finset.mul_sum, ← C.sum_atom_mul_condExp (gm C M δ k) a ω₀]
    refine Finset.sum_congr rfl fun ω hm => ?_
    have he : C.condExp (gm C M δ k) a ω = gsize C M δ k ω₀ := by
      unfold gsize
      exact C.condExp_congr _ (C.mem_atom.mp hm)
    rw [he]
    ring
  have hNBWa : (C.atom a ω₀).filter
      (fun ω => a < τ3 C M δ (k + 1) ω ∧ quiet3 bail a a ω) = C.atom a ω₀ := by
    rw [Finset.filter_eq_self]
    intro ω hm
    refine ⟨?_, ?_⟩
    · have h1 : τ3 C M δ k ω < τ3 C M δ (k + 1) ω := τ3_lt_succ hk hMm ω
      have h2 := hτmem ω hm
      omega
    · intro i hai hia hi
      exact absurd hia (by omega)
  have hclaim := charge3 hMm hM0 hcA0 hδ hcB0 hcB2δ hTmax hp hpe E bail hk ω₀
    C.m a (le_refl a) (by omega)
  rw [hNBWa] at hclaim
  have hwm : ∀ ω ∈ C.atom a ω₀,
      gm C M δ k ω = ∑ i ∈ Finset.Ico a (τ3 C M δ (k + 1) ω), C.sizeN i ω := by
    intro ω hm
    have hab : a ≤ τ3 C M δ (k + 1) ω := by
      have h1 := τ3_lt_succ (C := C) (M := M) (δ := δ) hk hMm ω
      have h2 := hτmem ω hm
      omega
    rw [sum_Ico_sizeN hab ω]
    unfold gm
    rw [hτmem ω hm]
  have hR : ∀ ω ∈ C.atom a ω₀, gcost C M δ E bail p' k a ω
      = E.bailCost bail
          (((List.ofFn (fun i : Fin M => gchunk C M δ ω (i : ℕ))).take k).flatten)
          (gchunk C M δ ω k) p' := by
    intro ω hm
    have hτω := hτmem ω hm
    have h1 := gchunk_prefix (C := C) (δ := δ) hMm ω k (by omega)
    rw [hτω] at h1
    unfold gcost
    rw [h1]
    unfold gchunk
    rw [hτω]
  rw [hL, Finset.sum_congr rfl fun ω hm => by rw [hwm ω hm]]
  refine le_trans hclaim (le_of_eq ?_)
  exact Finset.sum_congr rfl fun ω hm => by rw [hR ω hm]

/-- Expected output sizes equal expected window masses. -/
theorem sum_gsize (hMm : M ≤ C.m) {k : ℕ} (hk : k ≤ M) :
    ∑ ω, C.P ω * gsize C M δ k ω = ∑ ω, C.P ω * gm C M δ k ω := by
  show ∑ ω, C.P ω * C.condExp (gm C M δ k) (τ3 C M δ k ω) ω = _
  exact ChunkSystemB.sum_stopped_condExp C (τ3_isStopping hMm hk) _

end Wrap

section VarianceLemmas

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

/-- The conditional expectation of a time-`h` measurable function is the
function itself. -/
theorem condExp_of_meas {f : C.Ω → ℝ} {h : ℕ} {ω : C.Ω}
    (hf : ∀ ω', C.hist h ω' = C.hist h ω → f ω' = f ω) :
    C.condExp f h ω = f ω := by
  unfold ChunkSystemB.condExp
  have h1 : ∑ ω' ∈ C.atom h ω, C.P ω' * f ω'
      = f ω * C.mass (C.atom h ω) := by
    unfold ChunkSystemB.mass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' hm => ?_
    rw [hf ω' (C.mem_atom.mp hm)]
    ring
  rw [h1, mul_div_assoc, div_self (ne_of_gt (C.mass_atom_pos h ω)), mul_one]

/-- Total size is measurable at the end of time. -/
theorem totalSize_congr {ω ω' : C.Ω} (hh : C.hist C.m ω' = C.hist C.m ω) :
    C.totalSize ω' = C.totalSize ω := by
  rw [← pastSize_m, ← pastSize_m]
  exact C.pastSize_congr hh

/-- Conditional expectations commute with finite sums. -/
theorem condExp_finset_sum {ι : Type*} (sset : Finset ι) (F : ι → C.Ω → ℝ)
    (h : ℕ) (ω : C.Ω) :
    C.condExp (fun ω' => ∑ i ∈ sset, F i ω') h ω
      = ∑ i ∈ sset, C.condExp (F i) h ω := by
  unfold ChunkSystemB.condExp
  rw [← Finset.sum_div]
  congr 1
  calc ∑ ω' ∈ C.atom h ω, C.P ω' * ∑ i ∈ sset, F i ω'
      = ∑ ω' ∈ C.atom h ω, ∑ i ∈ sset, C.P ω' * F i ω' :=
        Finset.sum_congr rfl fun ω' _ => by rw [Finset.mul_sum]
    _ = ∑ i ∈ sset, ∑ ω' ∈ C.atom h ω, C.P ω' * F i ω' := Finset.sum_comm

/-- Conditional Jensen for squares. -/
theorem condExp_sq_le (f : C.Ω → ℝ) (h : ℕ) (ω : C.Ω) :
    (C.condExp f h ω) ^ 2 ≤ C.condExp (fun ω' => f ω' ^ 2) h ω := by
  unfold ChunkSystemB.condExp
  set A := C.atom h ω with hA
  have hm : 0 < C.mass A := C.mass_atom_pos h ω
  rw [div_pow, div_le_div_iff₀ (by positivity) hm]
  have hCS : (∑ ω' ∈ A, Real.sqrt (C.P ω') * (Real.sqrt (C.P ω') * f ω')) ^ 2
      ≤ (∑ ω' ∈ A, Real.sqrt (C.P ω') ^ 2)
        * ∑ ω' ∈ A, (Real.sqrt (C.P ω') * f ω') ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq A _ _
  have e1 : ∀ ω' ∈ A, Real.sqrt (C.P ω') * (Real.sqrt (C.P ω') * f ω')
      = C.P ω' * f ω' := by
    intro ω' _
    rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt (C.hP ω'))]
  have e2 : ∀ ω' ∈ A, Real.sqrt (C.P ω') ^ 2 = C.P ω' := by
    intro ω' _
    rw [Real.sq_sqrt (le_of_lt (C.hP ω'))]
  have e3 : ∀ ω' ∈ A, (Real.sqrt (C.P ω') * f ω') ^ 2 = C.P ω' * f ω' ^ 2 := by
    intro ω' _
    rw [mul_pow, Real.sq_sqrt (le_of_lt (C.hP ω'))]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2,
    Finset.sum_congr rfl e3] at hCS
  have hfin : (∑ ω' ∈ A, C.P ω' * f ω') ^ 2 * C.mass A
      ≤ (∑ ω' ∈ A, C.P ω' * f ω' ^ 2) * C.mass A ^ 2 := by
    have hCS' : (∑ ω' ∈ A, C.P ω' * f ω') ^ 2
        ≤ C.mass A * ∑ ω' ∈ A, C.P ω' * f ω' ^ 2 := hCS
    nlinarith [hm, hCS', Finset.sum_nonneg
      (fun ω' (_ : ω' ∈ A) => mul_nonneg (le_of_lt (C.hP ω')) (sq_nonneg (f ω')))]
  exact hfin

/-- With a trivial time-`0` history, conditioning at `0` is the mean. -/
theorem condExp_zero_triv (h0 : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (f : C.Ω → ℝ) (ω : C.Ω) : C.condExp f 0 ω = C.expVal f := by
  have hatom : C.atom 0 ω = Finset.univ := by
    ext ω'
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      exact C.mem_atom.mpr (h0 ω' ω)
  unfold ChunkSystemB.condExp ChunkSystemB.expVal ChunkSystemB.mass
  rw [hatom, C.hPsum, div_one]

theorem dinc_telescope (f : C.Ω → ℝ) (n : ℕ) (ω : C.Ω) :
    ∑ h ∈ Finset.range n, C.dinc f h ω
      = C.condExp f n ω - C.condExp f 0 ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold ChunkSystemB.dinc
    ring

theorem dinc_Ico (f : C.Ω → ℝ) {a b : ℕ} (hab : a ≤ b) (ω : C.Ω) :
    ∑ h ∈ Finset.Ico a b, C.dinc f h ω
      = C.condExp f b ω - C.condExp f a ω := by
  rw [Finset.sum_Ico_eq_sub _ hab, dinc_telescope, dinc_telescope]
  ring

/-- Expectation commutes with finite sums. -/
theorem expVal_finset_sum {ι : Type*} (sset : Finset ι) (F : ι → C.Ω → ℝ) :
    C.expVal (fun ω => ∑ i ∈ sset, F i ω) = ∑ i ∈ sset, C.expVal (F i) := by
  unfold ChunkSystemB.expVal
  calc ∑ ω, C.P ω * ∑ i ∈ sset, F i ω
      = ∑ ω, ∑ i ∈ sset, C.P ω * F i ω :=
        Finset.sum_congr rfl fun ω _ => by rw [Finset.mul_sum]
    _ = ∑ i ∈ sset, ∑ ω, C.P ω * F i ω := Finset.sum_comm

/-- Push a weighted expectation through a conditional expectation when the
first factor is measurable. -/
theorem expVal_meas_mul {XX Y : C.Ω → ℝ} {h : ℕ}
    (hX : ∀ ω ω', C.hist h ω' = C.hist h ω → XX ω' = XX ω) :
    C.expVal (fun ω => XX ω * Y ω)
      = C.expVal (fun ω => XX ω * C.condExp Y h ω) := by
  have hpull : ∀ ω, C.condExp (fun ω' => XX ω' * Y ω') h ω
      = XX ω * C.condExp Y h ω := by
    intro ω
    have h1 : C.condExp (fun ω' => XX ω' * Y ω') h ω
        = C.condExp (fun ω' => Y ω' * XX ω) h ω := by
      refine C.condExp_congr_fun fun ω' hm => ?_
      rw [hX ω ω' (C.mem_atom.mp hm)]
      ring
    rw [h1, C.condExp_mul_const]
    ring
  unfold ChunkSystemB.expVal
  rw [← C.sum_mul_condExp (fun ω => XX ω * Y ω) h]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [hpull ω]

/-- The conditional expectation of a Doob increment vanishes. -/
theorem condExp_dinc (f : C.Ω → ℝ) (h : ℕ) (ω : C.Ω) :
    C.condExp (C.dinc f h) h ω = 0 := by
  unfold ChunkSystemB.dinc
  rw [C.condExp_sub, C.condExp_condExp (Nat.le_succ h),
    C.condExp_condExp (le_refl h), sub_self]

/-- Pull a time-`h` measurable guard out of a conditional expectation. -/
theorem condExp_ite_meas {P' : C.Ω → Prop} [DecidablePred P'] {g : C.Ω → ℝ}
    {h : ℕ} {ω : C.Ω}
    (hP : ∀ ω ω', C.hist h ω' = C.hist h ω → (P' ω' ↔ P' ω)) :
    C.condExp (fun ω' => if P' ω' then g ω' else 0) h ω
      = if P' ω then C.condExp g h ω else 0 := by
  by_cases hp : P' ω
  · rw [if_pos hp]
    refine C.condExp_congr_fun fun ω' hm => ?_
    rw [if_pos ((hP ω ω' (C.mem_atom.mp hm)).mpr hp)]
  · rw [if_neg hp]
    have h1 : C.condExp (fun ω' => if P' ω' then g ω' else 0) h ω
        = C.condExp (fun _ => (0:ℝ)) h ω := by
      refine C.condExp_congr_fun fun ω' hm => ?_
      rw [if_neg (fun hc => hp ((hP ω ω' (C.mem_atom.mp hm)).mp hc))]
    rw [h1]
    have h2 := C.condExp_const 0 h ω
    rw [h2]

/-- **Orthogonal-increment second moment**: a family of martingale
differences has additive second moments. -/
theorem expVal_sq_sum_of_orth (W : ℕ → C.Ω → ℝ) (N : ℕ)
    (hmeas : ∀ h, h < N → ∀ ω ω', C.hist (h + 1) ω' = C.hist (h + 1) ω →
      W h ω' = W h ω)
    (hzero : ∀ h, h < N → ∀ ω, C.condExp (W h) h ω = 0) :
    C.expVal (fun ω => (∑ h ∈ Finset.range N, W h ω) ^ 2)
      = ∑ h ∈ Finset.range N, C.expVal (fun ω => W h ω ^ 2) := by
  have hcross : ∀ h h', h < N → h' < N → h ≠ h' →
      C.expVal (fun ω => W h ω * W h' ω) = 0 := by
    have key : ∀ h h', h < N → h' < N → h < h' →
        C.expVal (fun ω => W h ω * W h' ω) = 0 := by
      intro h h' hN hN' hlt
      have hXmeas : ∀ ω ω', C.hist h' ω' = C.hist h' ω → W h ω' = W h ω := by
        intro ω ω' hh
        exact hmeas h hN ω ω' (C.href (h + 1) h' (by omega) ω' ω hh)
      rw [expVal_meas_mul hXmeas]
      unfold ChunkSystemB.expVal
      refine Finset.sum_eq_zero fun ω _ => ?_
      show C.P ω * (W h ω * C.condExp (W h') h' ω) = 0
      rw [hzero h' hN' ω, mul_zero, mul_zero]
    intro h h' hN hN' hne
    rcases Nat.lt_or_ge h h' with hlt | hge
    · exact key h h' hN hN' hlt
    · have hlt' : h' < h := by omega
      have h1 := key h' h hN' hN hlt'
      rw [← h1]
      unfold ChunkSystemB.expVal
      refine Finset.sum_congr rfl fun ω _ => by ring
  have hexp : C.expVal (fun ω => (∑ h ∈ Finset.range N, W h ω) ^ 2)
      = ∑ h ∈ Finset.range N, ∑ h' ∈ Finset.range N,
          C.expVal (fun ω => W h ω * W h' ω) := by
    have h1 : ∀ ω : C.Ω, (∑ h ∈ Finset.range N, W h ω) ^ 2
        = ∑ h ∈ Finset.range N, ∑ h' ∈ Finset.range N, W h ω * W h' ω := by
      intro ω
      rw [pow_two, Finset.sum_mul_sum]
    rw [show (fun ω => (∑ h ∈ Finset.range N, W h ω) ^ 2)
        = fun ω => ∑ h ∈ Finset.range N, ∑ h' ∈ Finset.range N,
            W h ω * W h' ω from funext h1]
    rw [expVal_finset_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [expVal_finset_sum]
  rw [hexp]
  refine Finset.sum_congr rfl fun h hm => ?_
  simp only [Finset.mem_range] at hm
  rw [Finset.sum_eq_single h]
  · refine congrArg _ (funext fun ω => ?_)
    rw [pow_two]
  · intro h' hm' hne
    simp only [Finset.mem_range] at hm'
    exact hcross h h' hm hm' (fun hc => hne hc.symm)
  · intro hc
    exact absurd (Finset.mem_range.mpr hm) hc

end VarianceLemmas

section Variance

variable (C : ChunkSystemB X s t cA cB T pe mL) (M : ℕ) (δ : ℝ)

open Classical in
/-- Window-restricted Doob increments of the window masses. -/
noncomputable def wD (k h : ℕ) (ω : C.Ω) : ℝ :=
  if τ3 C M δ k ω ≤ h ∧ h < τ3 C M δ (k + 1) ω
  then C.dinc (gm C M δ k) h ω else 0

/-- The martingale differences of the output total. -/
noncomputable def wW (h : ℕ) (ω : C.Ω) : ℝ :=
  C.dinc C.totalSize h ω - ∑ k ∈ Finset.range M, wD C M δ k h ω

/-- The output total. -/
noncomputable def gtotal (ω : C.Ω) : ℝ :=
  ∑ k ∈ Finset.range M, gsize C M δ k ω

end Variance

section VarianceMain

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem dinc_congr (f : C.Ω → ℝ) {h : ℕ} {ω ω' : C.Ω}
    (hh : C.hist (h + 1) ω' = C.hist (h + 1) ω) :
    C.dinc f h ω' = C.dinc f h ω := by
  unfold ChunkSystemB.dinc
  rw [C.condExp_congr f hh,
    C.condExp_congr f (C.href h (h + 1) (Nat.le_succ h) ω' ω hh)]

/-- The window sums of the restricted increments telescope. -/
theorem sum_wD (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M) (ω : C.Ω) :
    ∑ h ∈ Finset.range C.m, wD C M δ k h ω
      = gm C M δ k ω - gsize C M δ k ω := by
  have hab : τ3 C M δ k ω ≤ τ3 C M δ (k + 1) ω :=
    le_of_lt (τ3_lt_succ hk hMm ω)
  have hbm : τ3 C M δ (k + 1) ω ≤ C.m := τ3_le_m hk hMm ω
  have hfilter : (Finset.range C.m).filter
      (fun h => τ3 C M δ k ω ≤ h ∧ h < τ3 C M δ (k + 1) ω)
      = Finset.Ico (τ3 C M δ k ω) (τ3 C M δ (k + 1) ω) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hsum : ∑ h ∈ Finset.range C.m, wD C M δ k h ω
      = ∑ h ∈ Finset.Ico (τ3 C M δ k ω) (τ3 C M δ (k + 1) ω),
          C.dinc (gm C M δ k) h ω := by
    rw [← hfilter, Finset.sum_filter]
    rfl
  rw [hsum, dinc_Ico _ hab ω]
  have h1 : C.condExp (gm C M δ k) (τ3 C M δ (k + 1) ω) ω = gm C M δ k ω :=
    condExp_of_meas (fun ω' hh => gm_congr hMm hk hh (le_refl _))
  rw [h1]
  rfl

/-- The main pointwise identity: the increments sum to the centred output
total. -/
theorem sum_wW (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hMm : M ≤ C.m) (hM0 : 0 < M) (ω : C.Ω) :
    ∑ h ∈ Finset.range C.m, wW C M δ h ω
      = gtotal C M δ ω - C.expVal C.totalSize := by
  unfold wW
  rw [Finset.sum_sub_distrib, dinc_telescope, Finset.sum_comm,
    Finset.sum_congr rfl (fun k hk =>
      sum_wD hMm (Finset.mem_range.mp hk) ω),
    Finset.sum_sub_distrib, sum_gm hM0 ω]
  have hT : C.condExp C.totalSize C.m ω = C.totalSize ω :=
    condExp_of_meas (fun ω' hh => totalSize_congr hh)
  have h0 : C.condExp C.totalSize 0 ω = C.expVal C.totalSize :=
    condExp_zero_triv h0triv _ ω
  rw [hT, h0]
  unfold gtotal
  ring

/-- The increments are known one step later. -/
theorem wW_meas (hMm : M ≤ C.m) {h : ℕ} {ω ω' : C.Ω}
    (hh : C.hist (h + 1) ω' = C.hist (h + 1) ω) :
    wW C M δ h ω' = wW C M δ h ω := by
  have hhh : C.hist h ω' = C.hist h ω :=
    C.href h (h + 1) (Nat.le_succ h) ω' ω hh
  unfold wW
  rw [dinc_congr _ hh]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  unfold wD
  have hs0 : τ3 C M δ k ω' ≤ h ↔ τ3 C M δ k ω ≤ h :=
    (τ3_isStopping (C := C) (δ := δ) hMm
      (le_of_lt (by omega : k < M))) h ω' ω hhh
  have hs1 : τ3 C M δ (k + 1) ω' ≤ h ↔ τ3 C M δ (k + 1) ω ≤ h :=
    (τ3_isStopping (C := C) (δ := δ) hMm (by omega : k + 1 ≤ M)) h ω' ω hhh
  by_cases hc : τ3 C M δ k ω ≤ h ∧ h < τ3 C M δ (k + 1) ω
  · rw [if_pos hc, if_pos ⟨hs0.mpr hc.1, by
      have := hs1
      omega⟩]
    exact dinc_congr _ hh
  · rw [if_neg hc, if_neg (fun hc' => hc ⟨hs0.mp hc'.1, by
      have := hs1
      omega⟩)]

/-- The increments are conditionally centred. -/
theorem condExp_wW (hMm : M ≤ C.m) (h : ℕ) (ω : C.Ω) :
    C.condExp (wW C M δ h) h ω = 0 := by
  unfold wW
  rw [C.condExp_sub, condExp_dinc, condExp_finset_sum]
  have hzero : ∀ k ∈ Finset.range M, C.condExp (wD C M δ k h) h ω = 0 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hguard : ∀ ω₁ ω₂ : C.Ω, C.hist h ω₂ = C.hist h ω₁ →
        ((τ3 C M δ k ω₂ ≤ h ∧ h < τ3 C M δ (k + 1) ω₂)
          ↔ (τ3 C M δ k ω₁ ≤ h ∧ h < τ3 C M δ (k + 1) ω₁)) := by
      intro ω₁ ω₂ hh
      have hs0 := (τ3_isStopping (C := C) (δ := δ) hMm
        (le_of_lt (by omega : k < M))) h ω₂ ω₁ hh
      have hs1 := (τ3_isStopping (C := C) (δ := δ) hMm
        (by omega : k + 1 ≤ M)) h ω₂ ω₁ hh
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hs0.mp h1, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨hs0.mpr h1, by omega⟩
    have := condExp_ite_meas (C := C)
      (P' := fun ω' => τ3 C M δ k ω' ≤ h ∧ h < τ3 C M δ (k + 1) ω')
      (g := C.dinc (gm C M δ k) h) (h := h) (ω := ω) hguard
    unfold wD
    rw [this]
    by_cases hc : τ3 C M δ k ω ≤ h ∧ h < τ3 C M δ (k + 1) ω
    · rw [if_pos hc, condExp_dinc]
    · rw [if_neg hc]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const, smul_zero, sub_zero]

/-- Disjoint windows: the square of the sum is the sum of squares. -/
theorem sq_sum_wD (hMm : M ≤ C.m) (h : ℕ) (ω : C.Ω) :
    (∑ k ∈ Finset.range M, wD C M δ k h ω) ^ 2
      = ∑ k ∈ Finset.range M, wD C M δ k h ω ^ 2 := by
  have hdisj : ∀ j ∈ Finset.range M, ∀ k ∈ Finset.range M, j ≠ k →
      wD C M δ j h ω * wD C M δ k h ω = 0 := by
    intro j hj k hk hne
    simp only [Finset.mem_range] at hj hk
    unfold wD
    by_cases hcj : τ3 C M δ j ω ≤ h ∧ h < τ3 C M δ (j + 1) ω
    · by_cases hck : τ3 C M δ k ω ≤ h ∧ h < τ3 C M δ (k + 1) ω
      · exfalso
        rcases Nat.lt_or_ge j k with hlt | hge
        · have hmono : τ3 C M δ (j + 1) ω ≤ τ3 C M δ k ω :=
            τ3_mono hlt (le_of_lt hk) hMm ω
          omega
        · have hlt : k < j := by omega
          have hmono : τ3 C M δ (k + 1) ω ≤ τ3 C M δ j ω :=
            τ3_mono hlt (le_of_lt hj) hMm ω
          omega
      · rw [if_neg hck, mul_zero]
    · rw [if_neg hcj, zero_mul]
  rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => rfl]
  have hred : ∀ j ∈ Finset.range M,
      ∑ k ∈ Finset.range M, wD C M δ j h ω * wD C M δ k h ω
        = wD C M δ j h ω ^ 2 := by
    intro j hj
    rw [Finset.sum_eq_single j]
    · rw [pow_two]
    · intro k hk hne
      exact hdisj j hj k hk (fun hc => hne hc.symm)
    · intro hc
      exact absurd hj hc
  exact Finset.sum_congr rfl hred

end VarianceMain

section VarianceBound

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem expVal_congr {f g : C.Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    C.expVal f = C.expVal g := by
  unfold ChunkSystemB.expVal
  exact Finset.sum_congr rfl fun ω _ => by rw [h ω]

theorem expVal_mono {f g : C.Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    C.expVal f ≤ C.expVal g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (le_of_lt (C.hP ω))

theorem expVal_add (f g : C.Ω → ℝ) :
    C.expVal (fun ω => f ω + g ω) = C.expVal f + C.expVal g := by
  unfold ChunkSystemB.expVal
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem expVal_smul (c : ℝ) (f : C.Ω → ℝ) :
    C.expVal (fun ω => c * f ω) = c * C.expVal f := by
  unfold ChunkSystemB.expVal
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem wD_congr (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M) {h : ℕ}
    {ω ω' : C.Ω} (hh : C.hist (h + 1) ω' = C.hist (h + 1) ω) :
    wD C M δ k h ω' = wD C M δ k h ω := by
  have hhh : C.hist h ω' = C.hist h ω :=
    C.href h (h + 1) (Nat.le_succ h) ω' ω hh
  unfold wD
  have hs0 : τ3 C M δ k ω' ≤ h ↔ τ3 C M δ k ω ≤ h :=
    (τ3_isStopping (C := C) (δ := δ) hMm (by omega : k ≤ M)) h ω' ω hhh
  have hs1 : τ3 C M δ (k + 1) ω' ≤ h ↔ τ3 C M δ (k + 1) ω ≤ h :=
    (τ3_isStopping (C := C) (δ := δ) hMm (by omega : k + 1 ≤ M)) h ω' ω hhh
  by_cases hc : τ3 C M δ k ω ≤ h ∧ h < τ3 C M δ (k + 1) ω
  · rw [if_pos hc, if_pos ⟨hs0.mpr hc.1, by
      have := hs1
      omega⟩]
    exact dinc_congr _ hh
  · rw [if_neg hc, if_neg (fun hc' => hc ⟨hs0.mp hc'.1, by
      have := hs1
      omega⟩)]

theorem condExp_wD (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M) (h : ℕ)
    (ω : C.Ω) : C.condExp (wD C M δ k h) h ω = 0 := by
  have hguard : ∀ ω₁ ω₂ : C.Ω, C.hist h ω₂ = C.hist h ω₁ →
      ((τ3 C M δ k ω₂ ≤ h ∧ h < τ3 C M δ (k + 1) ω₂)
        ↔ (τ3 C M δ k ω₁ ≤ h ∧ h < τ3 C M δ (k + 1) ω₁)) := by
    intro ω₁ ω₂ hh
    have hs0 := (τ3_isStopping (C := C) (δ := δ) hMm
      (by omega : k ≤ M)) h ω₂ ω₁ hh
    have hs1 := (τ3_isStopping (C := C) (δ := δ) hMm
      (by omega : k + 1 ≤ M)) h ω₂ ω₁ hh
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hs0.mp h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hs0.mpr h1, by omega⟩
  have := condExp_ite_meas (C := C)
    (P' := fun ω' => τ3 C M δ k ω' ≤ h ∧ h < τ3 C M δ (k + 1) ω')
    (g := C.dinc (gm C M δ k) h) (h := h) (ω := ω) hguard
  unfold wD
  rw [this]
  by_cases hc : τ3 C M δ k ω ≤ h ∧ h < τ3 C M δ (k + 1) ω
  · rw [if_pos hc, condExp_dinc]
  · rw [if_neg hc]

/-- Per-window energy: bounded by the ceiling times the expected mass. -/
theorem sum_sq_wD (hMm : M ≤ C.m) (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB)
    (hδ : 0 < δ) (hcB2δ : cB ≤ 2 * δ)
    (hTmax : ∀ ω, C.totalSize ω ≤ 2 * δ * M)
    {k : ℕ} (hk : k + 1 ≤ M) :
    ∑ h ∈ Finset.range C.m, C.expVal (fun ω => wD C M δ k h ω ^ 2)
      ≤ 4 * ((2 * δ + cB) * C.expVal (gm C M δ k)) := by
  have horth := expVal_sq_sum_of_orth (C := C) (wD C M δ k) C.m
    (fun h _ ω ω' hh => wD_congr hMm hk hh)
    (fun h _ ω => condExp_wD hMm hk h ω)
  rw [← horth]
  have hrw : C.expVal (fun ω => (∑ h ∈ Finset.range C.m, wD C M δ k h ω) ^ 2)
      = C.expVal (fun ω => (gm C M δ k ω - gsize C M δ k ω) ^ 2) :=
    expVal_congr fun ω => by rw [sum_wD hMm hk ω]
  rw [hrw]
  have hjensen : C.expVal (fun ω => gsize C M δ k ω ^ 2)
      ≤ C.expVal (fun ω => gm C M δ k ω ^ 2) := by
    have hpt : ∀ ω, gsize C M δ k ω ^ 2
        ≤ C.condExp (fun ω' => gm C M δ k ω' ^ 2) (τ3 C M δ k ω) ω := by
      intro ω
      exact condExp_sq_le (gm C M δ k) (τ3 C M δ k ω) ω
    refine le_trans (expVal_mono hpt) (le_of_eq ?_)
    exact ChunkSystemB.sum_stopped_condExp C
      (τ3_isStopping hMm (by omega : k ≤ M)) _
  have hceil : C.expVal (fun ω => gm C M δ k ω ^ 2)
      ≤ (2 * δ + cB) * C.expVal (gm C M δ k) := by
    rw [← expVal_smul]
    refine expVal_mono fun ω => ?_
    have h1 := gm_le hcA0 hcB0 hδ hMm hcB2δ hTmax hk ω
    have h2 := gm_nonneg (δ := δ) hcA0 hMm hk ω
    nlinarith
  have hsplit : C.expVal (fun ω => (gm C M δ k ω - gsize C M δ k ω) ^ 2)
      ≤ C.expVal (fun ω => 2 * gm C M δ k ω ^ 2 + 2 * gsize C M δ k ω ^ 2) := by
    refine expVal_mono fun ω => ?_
    nlinarith [sq_nonneg (gm C M δ k ω + gsize C M δ k ω)]
  have hlin : C.expVal (fun ω => 2 * gm C M δ k ω ^ 2 + 2 * gsize C M δ k ω ^ 2)
      = 2 * C.expVal (fun ω => gm C M δ k ω ^ 2)
        + 2 * C.expVal (fun ω => gsize C M δ k ω ^ 2) := by
    rw [expVal_add, expVal_smul, expVal_smul]
  linarith

/-- **Output variance bound**: the variance of the output total is bounded
by `5/4` of the input variance plus a ceiling-scale term. -/
theorem gtotal_var (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hMm : M ≤ C.m) (hM0 : 0 < M) (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB)
    (hδ : 0 < δ) (hcB2δ : cB ≤ 2 * δ)
    (hTmax : ∀ ω, C.totalSize ω ≤ 2 * δ * M) :
    C.expVal (fun ω => (gtotal C M δ ω - C.expVal C.totalSize) ^ 2)
      ≤ (5 / 4) * (C.expVal (fun ω => C.totalSize ω ^ 2)
          - C.expVal C.totalSize ^ 2)
        + 20 * ((2 * δ + cB) * C.expVal C.totalSize) := by
  have hrw : C.expVal (fun ω => (gtotal C M δ ω - C.expVal C.totalSize) ^ 2)
      = C.expVal (fun ω => (∑ h ∈ Finset.range C.m, wW C M δ h ω) ^ 2) :=
    expVal_congr fun ω => by rw [sum_wW h0triv hMm hM0 ω]
  rw [hrw, expVal_sq_sum_of_orth (C := C) (wW C M δ) C.m
    (fun h _ ω ω' hh => wW_meas hMm hh)
    (fun h _ ω => condExp_wW hMm h ω)]
  -- pointwise (a - b)² ≤ (5/4)a² + 5b², with the disjoint-window collapse
  have hstep : ∀ h ∈ Finset.range C.m,
      C.expVal (fun ω => wW C M δ h ω ^ 2)
        ≤ (5 / 4) * C.expVal (fun ω => C.dinc C.totalSize h ω ^ 2)
          + 5 * C.expVal (fun ω => ∑ k ∈ Finset.range M, wD C M δ k h ω ^ 2) := by
    intro h _
    have hpw : ∀ ω, wW C M δ h ω ^ 2
        ≤ (5 / 4) * C.dinc C.totalSize h ω ^ 2
          + 5 * ∑ k ∈ Finset.range M, wD C M δ k h ω ^ 2 := by
      intro ω
      have hsq := sq_sum_wD (C := C) (δ := δ) hMm h ω
      rw [← hsq]
      show (C.dinc C.totalSize h ω - ∑ k ∈ Finset.range M, wD C M δ k h ω) ^ 2 ≤ _
      nlinarith [sq_nonneg (C.dinc C.totalSize h ω / 2
        + 2 * ∑ k ∈ Finset.range M, wD C M δ k h ω)]
    refine le_trans (expVal_mono hpw) (le_of_eq ?_)
    rw [expVal_add, expVal_smul, expVal_smul]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the energy term
  have henergy : ∑ h ∈ Finset.range C.m,
      C.expVal (fun ω => C.dinc C.totalSize h ω ^ 2)
        = C.expVal (fun ω => C.totalSize ω ^ 2) - C.expVal C.totalSize ^ 2 := by
    have h1 : C.doobEnergy C.totalSize C.m
        = C.expVal (fun ω => (C.condExp C.totalSize C.m ω) ^ 2)
          - C.expVal (fun ω => (C.condExp C.totalSize 0 ω) ^ 2) :=
      C.doobEnergy_eq C.totalSize C.m
    have h2 : C.expVal (fun ω => (C.condExp C.totalSize C.m ω) ^ 2)
        = C.expVal (fun ω => C.totalSize ω ^ 2) :=
      expVal_congr fun ω => by
        rw [condExp_of_meas (fun ω' hh => totalSize_congr hh)]
    have h3 : C.expVal (fun ω => (C.condExp C.totalSize 0 ω) ^ 2)
        = C.expVal C.totalSize ^ 2 := by
      have h4 : C.expVal (fun ω => (C.condExp C.totalSize 0 ω) ^ 2)
          = C.expVal (fun _ => C.expVal C.totalSize ^ 2) :=
        expVal_congr fun ω => by rw [condExp_zero_triv h0triv _ ω]
      rw [h4]
      unfold ChunkSystemB.expVal
      rw [← Finset.sum_mul, C.hPsum, one_mul]
    unfold ChunkSystemB.doobEnergy at h1
    rw [h1, h2, h3]
  rw [henergy]
  -- the window term
  have hwindow : ∑ h ∈ Finset.range C.m,
      C.expVal (fun ω => ∑ k ∈ Finset.range M, wD C M δ k h ω ^ 2)
        ≤ 4 * ((2 * δ + cB) * C.expVal C.totalSize) := by
    have hswap : ∑ h ∈ Finset.range C.m,
        C.expVal (fun ω => ∑ k ∈ Finset.range M, wD C M δ k h ω ^ 2)
          = ∑ k ∈ Finset.range M, ∑ h ∈ Finset.range C.m,
              C.expVal (fun ω => wD C M δ k h ω ^ 2) := by
      rw [Finset.sum_congr rfl fun h _ =>
        expVal_finset_sum (Finset.range M) (fun k ω => wD C M δ k h ω ^ 2)]
      exact Finset.sum_comm
    rw [hswap]
    have hk_bound : ∀ k ∈ Finset.range M,
        ∑ h ∈ Finset.range C.m, C.expVal (fun ω => wD C M δ k h ω ^ 2)
          ≤ 4 * ((2 * δ + cB) * C.expVal (gm C M δ k)) := by
      intro k hkm
      exact sum_sq_wD hMm hcA0 hcB0 hδ hcB2δ hTmax
        (Finset.mem_range.mp hkm)
    refine le_trans (Finset.sum_le_sum hk_bound) (le_of_eq ?_)
    have hsum_gm : ∑ k ∈ Finset.range M, C.expVal (gm C M δ k)
        = C.expVal C.totalSize := by
      rw [← expVal_finset_sum (Finset.range M) (gm C M δ)]
      exact expVal_congr fun ω => sum_gm hM0 ω
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum_gm]
  linarith [hwindow]

end VarianceBound

section Assemble

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem ghist_atom (hMm : M ≤ C.m) {k : ℕ} (hk : k ≤ M) (ω₀ ω : C.Ω) :
    ghist C M δ k ω = ghist C M δ k ω₀
      ↔ C.hist (τ3 C M δ k ω₀) ω = C.hist (τ3 C M δ k ω₀) ω₀ := by
  rw [ghist_pair]
  constructor
  · rintro ⟨he, hf⟩
    rw [he] at hf
    exact hf
  · intro hh
    have hτ : τ3 C M δ k ω = τ3 C M δ k ω₀ :=
      τ3_congr hMm k hk hh (le_refl _)
    rw [hτ]
    exact ⟨rfl, hh⟩

theorem ghist_ref' (hMm : M ≤ C.m) (hM0 : 0 < M) {i j : ℕ} (hij : i ≤ j)
    {ω ω' : C.Ω} (hh : ghist C M δ j ω = ghist C M δ j ω') :
    ghist C M δ i ω = ghist C M δ i ω' := by
  by_cases hjM : j ≤ M
  · exact ghist_ref hMm hij hjM hh
  · push_neg at hjM
    obtain ⟨he, hf⟩ := ghist_pair.mp hh
    have hjω : τ3 C M δ j ω = C.m := τ3_last (by omega) hM0 ω
    rw [hjω] at hf
    by_cases hiM : i ≤ M
    · have hτi : τ3 C M δ i ω ≤ C.m := τ3_le_m hiM hMm ω
      have hτeq : τ3 C M δ i ω' = τ3 C M δ i ω :=
        τ3_congr hMm i hiM (show C.hist C.m ω' = C.hist C.m ω from hf.symm) hτi
      rw [ghist_pair]
      exact ⟨hτeq.symm, C.href _ C.m hτi ω ω' hf⟩
    · push_neg at hiM
      rw [ghist_pair]
      have h1 : τ3 C M δ i ω = C.m := τ3_last (by omega) hM0 ω
      have h2 : τ3 C M δ i ω' = C.m := τ3_last (by omega) hM0 ω'
      rw [h1, h2]
      exact ⟨rfl, hf⟩

/-- The expected output total equals the expected input total: zero loss. -/
theorem expVal_gtotal (hMm : M ≤ C.m) (hM0 : 0 < M) :
    C.expVal (gtotal C M δ) = C.expVal C.totalSize := by
  unfold gtotal
  rw [expVal_finset_sum]
  have h1 : ∀ k ∈ Finset.range M, C.expVal (gsize C M δ k)
      = C.expVal (gm C M δ k) := by
    intro k hk
    exact sum_gsize hMm (le_of_lt (Finset.mem_range.mp hk))
  rw [Finset.sum_congr rfl h1, ← expVal_finset_sum]
  exact expVal_congr fun ω => sum_gm hM0 ω

/-- Variance expands to the second-moment gap. -/
theorem var_expand (f : C.Ω → ℝ) :
    C.expVal (fun ω => (f ω - C.expVal f) ^ 2)
      = C.expVal (fun ω => f ω ^ 2) - C.expVal f ^ 2 := by
  unfold ChunkSystemB.expVal
  set μ := ∑ ω, C.P ω * f ω with hμ
  have h1 : ∑ ω, C.P ω * (f ω - μ) ^ 2
      = ∑ ω, (C.P ω * f ω ^ 2 - 2 * μ * (C.P ω * f ω) + μ ^ 2 * C.P ω) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    ring
  rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← hμ, C.hPsum]
  ring

open Classical in
/-- **Grid regrouping (v3)**: any chunk system regroups on the cumulative
mass grid into `M` windows with pointwise sizes in `[0, 2δ + cB]`, serving
the same request sequence at escape price `pe + 2δ + cB`, preserving the
expected total exactly, with a trivial initial history and with the output
total's variance controlled by `5/4` of the input variance plus a
ceiling-scale term. -/
theorem chunk_regrid (C : ChunkSystemB X s t cA cB T pe mL)
    {M : ℕ} {δ p' V V' : ℝ}
    (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hcB2δ : cB ≤ 2 * δ) (hpe : 0 ≤ pe)
    (hp : pe + (2 * δ + cB) ≤ p')
    (hTmax : ∀ ω, C.totalSize ω ≤ 2 * δ * M)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω *
      (C.totalSize ω - ∑ ω', C.P ω' * C.totalSize ω') ^ 2 ≤ V)
    (hV' : (5 / 4) * V
      + 20 * ((2 * δ + cB) * (∑ ω, C.P ω * C.totalSize ω)) ≤ V') :
    ∃ C' : ChunkSystemB X s t 0 (2 * δ + cB) T p' M,
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V') := by
  refine ⟨{
    Ω := C.Ω
    instFin := C.instFin
    instDec := C.instDec
    P := C.P
    m := M
    hist := fun n ω => ghist C M δ n ω
    chunk := fun ω k => gchunk C M δ ω (k : ℕ)
    size := fun ω k => gsize C M δ (k : ℕ) ω
    hP := C.hP
    hPsum := C.hPsum
    hm := le_refl M
    hm0 := hM0
    href := fun i j hij ω ω' hh => ghist_ref' hMm hM0 hij hh
    hadapt := fun k ω ω' hh => gchunk_congr hMm k.isLt hh
    hsmeas := fun k ω ω' hh => gsize_congr hMm hh
    hne := fun ω k => gchunk_ne ω (k : ℕ)
    hlast := ?_
    hopt := ?_
    hsize := ?_
    hcost := ?_
    htotal := ?_ }, ?_, ?_⟩
  · intro ω
    rw [gchunk_flatten hMm hM0 ω]
    exact C.hlast ω
  · intro ω
    rw [gchunk_flatten hMm hM0 ω]
    exact C.hopt ω
  · intro ω k
    exact ⟨gsize_nonneg hcA0 hMm k.isLt ω,
      gsize_le hcA0 hcB0 hδ hMm hcB2δ hTmax k.isLt ω⟩
  · intro k ω₀ E bail
    have hfilter : Finset.univ.filter
        (fun ω => ghist C M δ (k : ℕ) ω = ghist C M δ (k : ℕ) ω₀)
        = C.atom (τ3 C M δ (k : ℕ) ω₀) ω₀ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ghist_atom hMm (le_of_lt k.isLt) ω₀ ω, C.mem_atom]
    rw [hfilter]
    exact gcost_bound hMm hM0 hcA0 hδ hcB0 hcB2δ hTmax hp hpe E bail k.isLt ω₀
  · -- total: exact preservation
    have h1 : ∑ ω, C.P ω * (∑ k : Fin M, gsize C M δ (k : ℕ) ω)
        = C.expVal (gtotal C M δ) := by
      refine Finset.sum_congr rfl fun ω _ => ?_
      unfold gtotal
      rw [Fin.sum_univ_eq_sum_range (fun k => gsize C M δ k ω) M]
    rw [h1, expVal_gtotal hMm hM0]
    exact C.htotal
  · -- trivial initial history
    intro ω₁ ω₂
    show ghist C M δ 0 ω₁ = ghist C M δ 0 ω₂
    unfold ghist
    rw [τ3_zero, τ3_zero, h0triv ω₁ ω₂]
  · -- output variance
    show ∑ ω, C.P ω * ((∑ i : Fin M, gsize C M δ (i : ℕ) ω)
        - ∑ ω', C.P ω' * (∑ i : Fin M, gsize C M δ (i : ℕ) ω')) ^ 2 ≤ V'
    have hfin : ∀ ω : C.Ω, (∑ i : Fin M, gsize C M δ (i : ℕ) ω)
        = gtotal C M δ ω := by
      intro ω
      unfold gtotal
      rw [Fin.sum_univ_eq_sum_range (fun k => gsize C M δ k ω) M]
    have hμ : ∑ ω', C.P ω' * (∑ i : Fin M, gsize C M δ (i : ℕ) ω')
        = C.expVal C.totalSize := by
      rw [Finset.sum_congr rfl fun ω' _ => by rw [hfin ω']]
      exact expVal_gtotal hMm hM0
    have hgoal : ∑ ω, C.P ω * ((∑ i : Fin M, gsize C M δ (i : ℕ) ω)
        - ∑ ω', C.P ω' * (∑ i : Fin M, gsize C M δ (i : ℕ) ω')) ^ 2
        = C.expVal (fun ω => (gtotal C M δ ω - C.expVal C.totalSize) ^ 2) := by
      rw [hμ]
      exact Finset.sum_congr rfl fun ω _ => by rw [hfin ω]
    rw [hgoal]
    have hvb := gtotal_var (C := C) (M := M) (δ := δ)
      h0triv hMm hM0 hcA0 hcB0 hδ hcB2δ hTmax
    have hvar' : C.expVal (fun ω => C.totalSize ω ^ 2)
        - C.expVal C.totalSize ^ 2 ≤ V := by
      rw [← var_expand]
      exact hVar
    have hET : C.expVal C.totalSize = ∑ ω, C.P ω * C.totalSize ω := rfl
    calc C.expVal (fun ω => (gtotal C M δ ω - C.expVal C.totalSize) ^ 2)
        ≤ (5 / 4) * (C.expVal (fun ω => C.totalSize ω ^ 2)
            - C.expVal C.totalSize ^ 2)
          + 20 * ((2 * δ + cB) * C.expVal C.totalSize) := hvb
      _ ≤ (5 / 4) * V
          + 20 * ((2 * δ + cB) * (∑ ω, C.P ω * C.totalSize ω)) := by
          rw [← hET]
          nlinarith [hvar']
      _ ≤ V' := hV'

end Assemble

end Regrid

namespace KServer

/-- **Grid regrouping**: any chunk system regroups on the cumulative-mass
grid into `M` windows with pointwise sizes in `[0, 2δ + cB]`, serving the
same request sequence at escape price `pe + 2δ + cB`, preserving the
expected total exactly, with a trivial initial history, and with the output
total's variance bounded by `5/4` of the input variance plus a
ceiling-scale term. -/
theorem chunk_regrid {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cA cB T pe mL)
    {M : ℕ} {δ p' V V' : ℝ}
    (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hcB2δ : cB ≤ 2 * δ) (hpe : 0 ≤ pe)
    (hp : pe + (2 * δ + cB) ≤ p')
    (hTmax : ∀ ω, (∑ i, C.size ω i) ≤ 2 * δ * M)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hV' : 5 / 4 * V
      + 20 * ((2 * δ + cB) * ∑ ω, C.P ω * ∑ i, C.size ω i) ≤ V') :
    ∃ C' : ChunkSystemB X s t 0 (2 * δ + cB) T p' M,
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V') :=
  Regrid.chunk_regrid C hMm hM0 hδ hcA0 hcB0 hcB2δ hpe hp hTmax h0triv hVar
    (by
      have h : (5:ℝ) / 4 * V
          + 20 * ((2 * δ + cB) * ∑ ω, C.P ω * ∑ i, C.size ω i) ≤ V' := hV'
      exact h)

end KServer

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : KServer.ChunkSystemB X s t cA cB T pe mL)
    {M : ℕ} {δ p' V V' : ℝ}
    (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hcB2δ : cB ≤ 2 * δ) (hpe : 0 ≤ pe)
    (hp : pe + (2 * δ + cB) ≤ p')
    (hTmax : ∀ ω, (∑ i, C.size ω i) ≤ 2 * δ * M)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hV' : 5 / 4 * V
      + 20 * ((2 * δ + cB) * ∑ ω, C.P ω * ∑ i, C.size ω i) ≤ V') :
    ∃ C' : KServer.ChunkSystemB X s t 0 (2 * δ + cB) T p' M,
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V') :=
  KServer.chunk_regrid C hMm hM0 hδ hcA0 hcB0 hcB2δ hpe hp hTmax h0triv hVar hV'
