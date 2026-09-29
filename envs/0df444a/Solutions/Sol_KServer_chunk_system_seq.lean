-- Prove2me | solution 1 for KServer.chunk_system_seq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T14:50:10.926608+00:00
-- url     : https://prove2.me/submissions/4f13f4ff-f85b-4ecb-9bd4-23fa67d0560a

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open KServer

namespace SeqComp

variable {Y : Type*} [MetricSpace Y]
variable {a b c : Y} {cA1 cB1 cA2 cB2 T1 T2 pe : ℝ} {mL1 mL2 : ℕ}

section Defs

variable (C1 : ChunkSystemB Y a b cA1 cB1 T1 pe mL1)
variable (C2 : ChunkSystemB Y b c cA2 cB2 T2 pe mL2)

/-- The two-phase history: phase 1 verbatim; phase 2 pairs the full phase-1
history with the running phase-2 history. -/
def shist (n : ℕ) (ω : C1.Ω × C2.Ω) : ℕ :=
  if n ≤ C1.m then Nat.pair (C1.hist n ω.1) 0
  else Nat.pair (C1.hist C1.m ω.1) (C2.hist (n - C1.m) ω.2)

/-- The two-phase chunks. -/
def schunk (ω : C1.Ω × C2.Ω) (i : Fin (C1.m + C2.m)) : List (Set Y) :=
  if h : (i : ℕ) < C1.m then C1.chunk ω.1 ⟨i, h⟩
  else C2.chunk ω.2 ⟨(i : ℕ) - C1.m, by omega⟩

/-- The two-phase sizes. -/
def ssize (ω : C1.Ω × C2.Ω) (i : Fin (C1.m + C2.m)) : ℝ :=
  if h : (i : ℕ) < C1.m then C1.size ω.1 ⟨i, h⟩
  else C2.size ω.2 ⟨(i : ℕ) - C1.m, by omega⟩

end Defs

section Basic

variable {C1 : ChunkSystemB Y a b cA1 cB1 T1 pe mL1}
variable {C2 : ChunkSystemB Y b c cA2 cB2 T2 pe mL2}

theorem shist_le {n : ℕ} (hn : n ≤ C1.m) (ω : C1.Ω × C2.Ω) :
    shist C1 C2 n ω = Nat.pair (C1.hist n ω.1) 0 := by
  unfold shist
  rw [if_pos hn]

theorem shist_gt {n : ℕ} (hn : ¬ n ≤ C1.m) (ω : C1.Ω × C2.Ω) :
    shist C1 C2 n ω
      = Nat.pair (C1.hist C1.m ω.1) (C2.hist (n - C1.m) ω.2) := by
  unfold shist
  rw [if_neg hn]

/-- Phase-1 chunks are constant on the full phase-1 atom. -/
theorem chunk1_const {ω ω' : C1.Ω} (hh : C1.hist C1.m ω = C1.hist C1.m ω')
    (i : Fin C1.m) : C1.chunk ω i = C1.chunk ω' i :=
  C1.hadapt i ω ω' (C1.href ((i : ℕ) + 1) C1.m i.isLt ω ω' hh)

/-- The full phase-1 request sequence is constant on the full atom. -/
theorem flat1_const {ω ω' : C1.Ω} (hh : C1.hist C1.m ω = C1.hist C1.m ω') :
    (List.ofFn (C1.chunk ω)).flatten = (List.ofFn (C1.chunk ω')).flatten := by
  congr 1
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_ofFn]
    exact chunk1_const hh _

theorem shref : ∀ i j : ℕ, i ≤ j → ∀ ω ω' : C1.Ω × C2.Ω,
    shist C1 C2 j ω = shist C1 C2 j ω' → shist C1 C2 i ω = shist C1 C2 i ω' := by
  intro i j hij ω ω' hh
  by_cases hj : j ≤ C1.m
  · have hi : i ≤ C1.m := le_trans hij hj
    rw [shist_le hj ω, shist_le hj ω'] at hh
    rw [shist_le hi ω, shist_le hi ω']
    obtain ⟨h1, -⟩ := Nat.pair_eq_pair.mp hh
    rw [C1.href i j hij ω.1 ω'.1 h1]
  · rw [shist_gt hj ω, shist_gt hj ω'] at hh
    obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp hh
    by_cases hi : i ≤ C1.m
    · rw [shist_le hi ω, shist_le hi ω',
        C1.href i C1.m hi ω.1 ω'.1 h1]
    · rw [shist_gt hi ω, shist_gt hi ω', h1,
        C2.href (i - C1.m) (j - C1.m) (by omega) ω.2 ω'.2 h2]

/-- The combined request list decomposes into the two phases. -/
theorem ofFn_schunk (ω : C1.Ω × C2.Ω) :
    List.ofFn (schunk C1 C2 ω)
      = List.ofFn (C1.chunk ω.1) ++ List.ofFn (C2.chunk ω.2) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.length_ofFn] at h1
    rw [List.getElem_ofFn, List.getElem_append]
    simp only [List.length_ofFn]
    unfold schunk
    by_cases hk : k < C1.m
    · rw [dif_pos (show ((⟨k, h1⟩ : Fin (C1.m + C2.m)) : ℕ) < C1.m from hk),
        dif_pos hk, List.getElem_ofFn]
    · rw [dif_neg (show ¬ ((⟨k, h1⟩ : Fin (C1.m + C2.m)) : ℕ) < C1.m from hk),
        dif_neg hk, List.getElem_ofFn]

end Basic

section Offline

variable {a b : Y}

open Classical in
/-- A canonical offline serving path: step into each nonempty request. -/
noncomputable def defaultPath (x₀ : Y) (σ : List (Set Y)) : ℕ → Y
  | 0 => x₀
  | (j + 1) => if h : (σ.getD j ∅).Nonempty then h.choose else defaultPath x₀ σ j

theorem defaultPath_serves (x₀ : Y) (σ : List (Set Y)) :
    EvaderServes x₀ σ (defaultPath x₀ σ) := by
  refine ⟨rfl, ?_⟩
  intro j hne
  have hget : σ.get j = σ.getD (j : ℕ) ∅ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]
    rfl
  show defaultPath x₀ σ ((j : ℕ) + 1) ∈ σ.get j
  rw [hget] at hne ⊢
  unfold defaultPath
  rw [dif_pos hne]
  exact hne.choose_spec

theorem offlineSet_nonempty (x₀ : Y) (σ : List (Set Y)) :
    {c : ℝ | ∃ P : ℕ → Y, EvaderServes x₀ σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))}.Nonempty :=
  ⟨_, defaultPath x₀ σ, defaultPath_serves x₀ σ, rfl⟩

theorem offlineSet_bddBelow (x₀ : Y) (σ : List (Set Y)) :
    BddBelow {c : ℝ | ∃ P : ℕ → Y, EvaderServes x₀ σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))} := by
  refine ⟨0, fun c hc => ?_⟩
  obtain ⟨P, -, hc⟩ := hc
  rw [hc]
  exact Finset.sum_nonneg fun j _ => dist_nonneg

/-- Offline costs concatenate at a pinned junction: if the first sequence
ends with the singleton request `{b}`, serving the concatenation from `a`
costs at most the two offline costs combined. -/
theorem offline_append_le (σ1 σ2 : List (Set Y))
    (hlast : σ1.getLast? = some ({b} : Set Y)) :
    evaderOfflineCost a (σ1 ++ σ2)
      ≤ evaderOfflineCost a σ1 + evaderOfflineCost b σ2 := by
  have hσ1ne : σ1 ≠ [] := by
    intro hc
    rw [hc] at hlast
    simp at hlast
  have hlen1 : 0 < σ1.length := List.length_pos_iff.mpr hσ1ne
  have hget_last : σ1.get ⟨σ1.length - 1, by omega⟩ = ({b} : Set Y) := by
    have h1 : σ1.getLast? = some (σ1.getLast hσ1ne) :=
      List.getLast?_eq_getLast hσ1ne
    rw [h1, Option.some_inj] at hlast
    have h2 : σ1.getLast hσ1ne = σ1[σ1.length - 1] :=
      List.getLast_eq_getElem hσ1ne
    show σ1[σ1.length - 1] = _
    rw [← h2, hlast]
  have key : ∀ c1 ∈ {c : ℝ | ∃ P : ℕ → Y, EvaderServes a σ1 P ∧
        c = ∑ j ∈ Finset.range σ1.length, dist (P j) (P (j + 1))},
      ∀ c2 ∈ {c : ℝ | ∃ P : ℕ → Y, EvaderServes b σ2 P ∧
        c = ∑ j ∈ Finset.range σ2.length, dist (P j) (P (j + 1))},
      evaderOfflineCost a (σ1 ++ σ2) ≤ c1 + c2 := by
    rintro c1 ⟨P1, ⟨hP10, hP1s⟩, hc1⟩ c2 ⟨P2, ⟨hP20, hP2s⟩, hc2⟩
    have hP1b : P1 σ1.length = b := by
      have := hP1s ⟨σ1.length - 1, by omega⟩ (by rw [hget_last]; exact ⟨b, rfl⟩)
      rw [hget_last] at this
      have h2 : σ1.length - 1 + 1 = σ1.length := by omega
      rw [h2] at this
      exact this
    set P : ℕ → Y := fun j => if j ≤ σ1.length then P1 j else P2 (j - σ1.length)
      with hP_def
    have hPmid : ∀ j, σ1.length ≤ j → P j = P2 (j - σ1.length) := by
      intro j hj
      rcases Nat.eq_or_lt_of_le hj with he | hl
      · have h1 : P j = P1 j := by
          rw [hP_def]
          simp only
          rw [if_pos (by omega)]
        have h2 : j - σ1.length = 0 := by omega
        rw [h1, h2, hP20, ← he]
        exact hP1b
      · rw [hP_def]
        simp only
        rw [if_neg (by omega)]
    show evaderOfflineCost a (σ1 ++ σ2) ≤ c1 + c2
    unfold evaderOfflineCost
    refine csInf_le (offlineSet_bddBelow _ _) ?_
    refine ⟨P, ⟨by rw [hP_def]; simp [hP10], ?_⟩, ?_⟩
    · intro j hne
      have hjl : (j : ℕ) < σ1.length + σ2.length := by
        have := j.isLt
        simpa using this
      by_cases hj1 : (j : ℕ) < σ1.length
      · have hget : (σ1 ++ σ2).get j = σ1.get ⟨(j : ℕ), hj1⟩ := by
          show (σ1 ++ σ2)[(j : ℕ)] = _
          rw [List.getElem_append_left hj1]
          rfl
        rw [hget] at hne ⊢
        have := hP1s ⟨(j : ℕ), hj1⟩ hne
        have hP_eq : P ((j : ℕ) + 1) = P1 ((j : ℕ) + 1) := by
          rw [hP_def]
          simp only []
          rw [if_pos (by omega)]
        rw [hP_eq]
        exact this
      · have hget : (σ1 ++ σ2).get j = σ2.get ⟨(j : ℕ) - σ1.length, by omega⟩ := by
          show (σ1 ++ σ2)[(j : ℕ)] = _
          rw [List.getElem_append_right (by omega)]
          rfl
        rw [hget] at hne ⊢
        have := hP2s ⟨(j : ℕ) - σ1.length, by omega⟩ hne
        have hP_eq : P ((j : ℕ) + 1) = P2 ((j : ℕ) + 1 - σ1.length) :=
          hPmid _ (by omega)
        rw [hP_eq]
        have hidx : (j : ℕ) + 1 - σ1.length = ((j : ℕ) - σ1.length) + 1 := by
          omega
        rw [hidx]
        exact this
    · rw [hc1, hc2]
      have hlen : (σ1 ++ σ2).length = σ1.length + σ2.length := by simp
      rw [hlen, Finset.sum_range_add]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_range] at hj
        have h1 : P j = P1 j := by
          rw [hP_def]
          simp only []
          rw [if_pos (by omega)]
        have h2 : P (j + 1) = P1 (j + 1) := by
          rw [hP_def]
          simp only []
          rw [if_pos (by omega)]
        rw [h1, h2]
      · refine Finset.sum_congr rfl fun j hj => ?_
        have h1 : P (σ1.length + j) = P2 j := by
          rw [hPmid _ (by omega)]
          congr 1
          omega
        have h2 : P (σ1.length + j + 1) = P2 (j + 1) := by
          rw [hPmid _ (by omega)]
          congr 1
          omega
        rw [h1, h2]
  have h2 : ∀ c1 ∈ {c : ℝ | ∃ P : ℕ → Y, EvaderServes a σ1 P ∧
        c = ∑ j ∈ Finset.range σ1.length, dist (P j) (P (j + 1))},
      evaderOfflineCost a (σ1 ++ σ2) - evaderOfflineCost b σ2 ≤ c1 := by
    intro c1 hc1
    have h3 : ∀ c2 ∈ {c : ℝ | ∃ P : ℕ → Y, EvaderServes b σ2 P ∧
          c = ∑ j ∈ Finset.range σ2.length, dist (P j) (P (j + 1))},
        evaderOfflineCost a (σ1 ++ σ2) - c1 ≤ c2 := by
      intro c2 hc2
      have := key c1 hc1 c2 hc2
      linarith
    have h4 : evaderOfflineCost a (σ1 ++ σ2) - c1 ≤ evaderOfflineCost b σ2 := by
      show _ ≤ sInf _
      exact le_csInf (offlineSet_nonempty _ _) h3
    linarith
  have h5 : evaderOfflineCost a (σ1 ++ σ2) - evaderOfflineCost b σ2
      ≤ evaderOfflineCost a σ1 := by
    show _ ≤ sInf _
    exact le_csInf (offlineSet_nonempty _ _) h2
  linarith

end Offline

section Product

variable {C1 : ChunkSystemB Y a b cA1 cB1 T1 pe mL1}
variable {C2 : ChunkSystemB Y b c cA2 cB2 T2 pe mL2}

theorem stake_le (ω : C1.Ω × C2.Ω) {i : ℕ} (hi : i ≤ C1.m) :
    (List.ofFn (schunk C1 C2 ω)).take i
      = (List.ofFn (C1.chunk ω.1)).take i := by
  rw [ofFn_schunk, List.take_append_of_le_length (by simpa using hi)]

theorem stake_ge (ω : C1.Ω × C2.Ω) {i : ℕ} (hi : C1.m ≤ i) :
    (List.ofFn (schunk C1 C2 ω)).take i
      = List.ofFn (C1.chunk ω.1)
        ++ (List.ofFn (C2.chunk ω.2)).take (i - C1.m) := by
  rw [ofFn_schunk, List.take_append,
    List.take_of_length_le (by simpa using hi)]
  congr 2
  simp

/-- Sums over the product weighted by the product measure, for functions of
the first component over a first-component event. -/
theorem sum_filter_fst (q1 : C1.Ω → Prop) [DecidablePred q1]
    (F : C1.Ω → ℝ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : C1.Ω × C2.Ω => q1 ω.1),
        (C1.P ω.1 * C2.P ω.2) * F ω.1
      = ∑ ω1 ∈ Finset.univ.filter q1, C1.P ω1 * F ω1 := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω1 _ => ?_
  by_cases hq1 : q1 ω1
  · rw [if_pos hq1]
    calc ∑ ω2, (if q1 ω1 then (C1.P ω1 * C2.P ω2) * F ω1 else 0)
        = ∑ ω2, C2.P ω2 * (C1.P ω1 * F ω1) := by
          refine Finset.sum_congr rfl fun ω2 _ => ?_
          rw [if_pos hq1]
          ring
      _ = C1.P ω1 * F ω1 := by
          rw [← Finset.sum_mul, C2.hPsum, one_mul]
  · rw [if_neg hq1]
    exact Finset.sum_eq_zero fun ω2 _ => by rw [if_neg hq1]

/-- Product sums factor over a rectangular event. -/
theorem sum_filter_rect (q1 : C1.Ω → Prop) (q2 : C2.Ω → Prop)
    [DecidablePred q1] [DecidablePred q2] (F : C1.Ω → C2.Ω → ℝ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : C1.Ω × C2.Ω => q1 ω.1 ∧ q2 ω.2),
        (C1.P ω.1 * C2.P ω.2) * F ω.1 ω.2
      = ∑ ω1 ∈ Finset.univ.filter q1, ∑ ω2 ∈ Finset.univ.filter q2,
          C1.P ω1 * (C2.P ω2 * F ω1 ω2) := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω1 _ => ?_
  by_cases hq1 : q1 ω1
  · rw [if_pos hq1, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ω2 _ => ?_
    by_cases hq2 : q2 ω2
    · rw [if_pos (⟨hq1, hq2⟩ : q1 ω1 ∧ q2 ω2), if_pos hq2]
      ring
    · rw [if_neg (fun hc : q1 ω1 ∧ q2 ω2 => hq2 hc.2), if_neg hq2]
  · rw [if_neg hq1]
    exact Finset.sum_eq_zero fun ω2 _ => by
      rw [if_neg (fun hc : q1 ω1 ∧ q2 ω2 => hq1 hc.1)]

end Product

section Main

variable {C1 : ChunkSystemB Y a b cA1 cB1 T1 pe mL1}
variable {C2 : ChunkSystemB Y b c cA2 cB2 T2 pe mL2}

theorem ssize_split (ω : C1.Ω × C2.Ω) :
    ∑ i : Fin (C1.m + C2.m), ssize C1 C2 ω i
      = (∑ i, C1.size ω.1 i) + ∑ i, C2.size ω.2 i := by
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    unfold ssize
    rw [dif_pos (show ((Fin.castAdd C2.m i : Fin (C1.m + C2.m)) : ℕ) < C1.m
      from i.isLt)]
    simp only [Fin.coe_castAdd, Fin.eta]
  · refine Finset.sum_congr rfl fun i _ => ?_
    unfold ssize
    rw [dif_neg (show ¬ ((Fin.natAdd C1.m i : Fin (C1.m + C2.m)) : ℕ) < C1.m
      by simp)]
    congr 1
    apply Fin.ext
    show C1.m + (i : ℕ) - C1.m = (i : ℕ)
    omega

theorem sum_prod_fst (f : C1.Ω → ℝ) :
    ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2) * f ω.1
      = ∑ ω1, C1.P ω1 * f ω1 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω1 _ => ?_
  calc ∑ ω2, (C1.P ω1 * C2.P ω2) * f ω1
      = (∑ ω2, C2.P ω2) * (C1.P ω1 * f ω1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun ω2 _ => by ring
    _ = C1.P ω1 * f ω1 := by rw [C2.hPsum, one_mul]

theorem sum_prod_snd (g : C2.Ω → ℝ) :
    ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2) * g ω.2
      = ∑ ω2, C2.P ω2 * g ω2 := by
  rw [Fintype.sum_prod_type]
  calc ∑ ω1, ∑ ω2, (C1.P ω1 * C2.P ω2) * g ω2
      = ∑ ω1, C1.P ω1 * ∑ ω2, C2.P ω2 * g ω2 := by
        refine Finset.sum_congr rfl fun ω1 _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω2 _ => by ring
    _ = (∑ ω1, C1.P ω1) * ∑ ω2, C2.P ω2 * g ω2 := by rw [Finset.sum_mul]
    _ = ∑ ω2, C2.P ω2 * g ω2 := by rw [C1.hPsum, one_mul]

theorem sum_prod_mul (f : C1.Ω → ℝ) (g : C2.Ω → ℝ) :
    ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2) * (f ω.1 * g ω.2)
      = (∑ ω1, C1.P ω1 * f ω1) * ∑ ω2, C2.P ω2 * g ω2 := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω1 _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω2 _ => by ring

theorem sum_prod_add (f : C1.Ω → ℝ) (g : C2.Ω → ℝ) :
    ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2) * (f ω.1 + g ω.2)
      = (∑ ω1, C1.P ω1 * f ω1) + ∑ ω2, C2.P ω2 * g ω2 := by
  have h1 : ∀ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2) * (f ω.1 + g ω.2)
      = (C1.P ω.1 * C2.P ω.2) * f ω.1 + (C1.P ω.1 * C2.P ω.2) * g ω.2 :=
    fun ω => by ring
  rw [Finset.sum_congr rfl fun ω _ => h1 ω, Finset.sum_add_distrib,
    sum_prod_fst, sum_prod_snd]


theorem reqMap_id (l : List (Set Y)) : reqMap (fun S : Set Y => S) l = l := by
  unfold reqMap
  exact List.map_id' l

open Classical in
/-- **Sequential composition**: chunk systems `a → b` and `b → c` with the
junction on a geodesic compose over the product sample space, with
concatenated chunks, added totals, and added variances. -/
theorem seq_compose
    (C1 : ChunkSystemB Y a b cA1 cB1 T1 pe mL1)
    (C2 : ChunkSystemB Y b c cA2 cB2 T2 pe mL2)
    {cLo cHi V1 V2 : ℝ}
    (hgeo : dist a b + dist b c ≤ dist a c)
    (hpe : 0 ≤ pe)
    (hlo1 : cLo ≤ cA1) (hlo2 : cLo ≤ cA2)
    (hhi1 : cB1 ≤ cHi) (hhi2 : cB2 ≤ cHi)
    (h0triv1 : ∀ ω₁ ω₂ : C1.Ω, C1.hist 0 ω₁ = C1.hist 0 ω₂)
    (h0triv2 : ∀ ω₁ ω₂ : C2.Ω, C2.hist 0 ω₁ = C2.hist 0 ω₂)
    (hVar1 : ∑ ω, C1.P ω * ((∑ i, C1.size ω i)
      - ∑ ω', C1.P ω' * ∑ i, C1.size ω' i) ^ 2 ≤ V1)
    (hVar2 : ∑ ω, C2.P ω * ((∑ i, C2.size ω i)
      - ∑ ω', C2.P ω' * ∑ i, C2.size ω' i) ^ 2 ≤ V2) :
    ∃ C' : ChunkSystemB Y a c cLo cHi (T1 + T2) pe (mL1 + mL2),
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V1 + V2) := by
  refine ⟨{
    Ω := C1.Ω × C2.Ω
    instFin := inferInstance
    instDec := inferInstance
    P := fun ω => C1.P ω.1 * C2.P ω.2
    m := C1.m + C2.m
    hist := shist C1 C2
    chunk := schunk C1 C2
    size := ssize C1 C2
    hP := fun ω => mul_pos (C1.hP ω.1) (C2.hP ω.2)
    hPsum := ?_
    hm := add_le_add C1.hm C2.hm
    hm0 := by have := C1.hm0; omega
    href := shref
    hadapt := ?_
    hsmeas := ?_
    hne := ?_
    hlast := ?_
    hopt := ?_
    hsize := ?_
    hcost := ?_
    htotal := ?_ }, ?_, ?_⟩
  · -- hPsum
    rw [Fintype.sum_prod_type]
    calc ∑ ω1, ∑ ω2, C1.P ω1 * C2.P ω2
        = ∑ ω1, C1.P ω1 * ∑ ω2, C2.P ω2 := by
          exact Finset.sum_congr rfl fun ω1 _ => by rw [Finset.mul_sum]
      _ = 1 := by
          rw [C2.hPsum]
          simpa using C1.hPsum
  · -- hadapt
    intro i ω ω' hh
    unfold schunk
    by_cases hi : (i : ℕ) < C1.m
    · rw [dif_pos hi, dif_pos hi]
      have hle : (i : ℕ) + 1 ≤ C1.m := hi
      rw [shist_le hle ω, shist_le hle ω'] at hh
      obtain ⟨h1, -⟩ := Nat.pair_eq_pair.mp hh
      exact C1.hadapt _ _ _ h1
    · rw [dif_neg hi, dif_neg hi]
      have hgt : ¬ (i : ℕ) + 1 ≤ C1.m := by omega
      rw [shist_gt hgt ω, shist_gt hgt ω'] at hh
      obtain ⟨-, h2⟩ := Nat.pair_eq_pair.mp hh
      have hidx : (i : ℕ) + 1 - C1.m = ((i : ℕ) - C1.m) + 1 := by omega
      rw [hidx] at h2
      exact C2.hadapt ⟨(i : ℕ) - C1.m, by have := i.isLt; omega⟩ _ _ h2
  · -- hsmeas
    intro i ω ω' hh
    unfold ssize
    by_cases hi : (i : ℕ) < C1.m
    · rw [dif_pos hi, dif_pos hi]
      have hle : (i : ℕ) ≤ C1.m := le_of_lt hi
      rw [shist_le hle ω, shist_le hle ω'] at hh
      obtain ⟨h1, -⟩ := Nat.pair_eq_pair.mp hh
      exact C1.hsmeas _ _ _ h1
    · rw [dif_neg hi, dif_neg hi]
      by_cases him : (i : ℕ) ≤ C1.m
      · refine C2.hsmeas ⟨(i : ℕ) - C1.m, by have := i.isLt; omega⟩ ω.2 ω'.2 ?_
        have h0 : (i : ℕ) - C1.m = 0 := by omega
        show C2.hist ((⟨(i : ℕ) - C1.m, _⟩ : Fin C2.m) : ℕ) ω.2
            = C2.hist ((⟨(i : ℕ) - C1.m, _⟩ : Fin C2.m) : ℕ) ω'.2
        simp only [h0]
        exact h0triv2 ω.2 ω'.2
      · rw [shist_gt him ω, shist_gt him ω'] at hh
        obtain ⟨-, h2⟩ := Nat.pair_eq_pair.mp hh
        exact C2.hsmeas ⟨(i : ℕ) - C1.m, by have := i.isLt; omega⟩ _ _ h2
  · -- hne
    intro ω i S hS
    unfold schunk at hS
    by_cases hi : (i : ℕ) < C1.m
    · rw [dif_pos hi] at hS
      exact C1.hne _ _ _ hS
    · rw [dif_neg hi] at hS
      exact C2.hne _ _ _ hS
  · -- hlast
    intro ω
    show ((List.ofFn (schunk C1 C2 ω)).flatten).getLast? = _
    rw [ofFn_schunk, List.flatten_append]
    have h2 := C2.hlast ω.2
    have hne2 : (List.ofFn (C2.chunk ω.2)).flatten ≠ [] := by
      intro hc
      rw [hc] at h2
      simp at h2
    rw [List.getLast?_append_of_ne_nil _ hne2]
    exact h2
  · -- hopt
    intro ω
    show evaderOfflineCost a ((List.ofFn (schunk C1 C2 ω)).flatten) ≤ _
    rw [ofFn_schunk, List.flatten_append]
    refine le_trans (offline_append_le _ _ (C1.hlast ω.1)) ?_
    have h1 := C1.hopt ω.1
    have h2 := C2.hopt ω.2
    linarith
  · -- hsize
    intro ω i
    unfold ssize
    by_cases hi : (i : ℕ) < C1.m
    · rw [dif_pos hi]
      have := C1.hsize ω.1 ⟨i, hi⟩
      exact ⟨le_trans hlo1 this.1, le_trans this.2 hhi1⟩
    · rw [dif_neg hi]
      have := C2.hsize ω.2 ⟨(i : ℕ) - C1.m, by have := i.isLt; omega⟩
      exact ⟨le_trans hlo2 this.1, le_trans this.2 hhi2⟩
  · -- hcost
    intro i ω₀ E bail
    by_cases hi : (i : ℕ) < C1.m
    · -- phase 1
      have hle : (i : ℕ) ≤ C1.m := le_of_lt hi
      have hfilter : Finset.univ.filter
          (fun ω : C1.Ω × C2.Ω => shist C1 C2 i ω = shist C1 C2 i ω₀)
          = Finset.univ.filter
            (fun ω : C1.Ω × C2.Ω => C1.hist i ω.1 = C1.hist i ω₀.1) := by
        ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [shist_le hle ω, shist_le hle ω₀, Nat.pair_eq_pair]
        constructor
        · rintro ⟨h1, -⟩
          exact h1
        · intro h1
          exact ⟨h1, rfl⟩
      rw [hfilter]
      have hint : ∀ ω : C1.Ω × C2.Ω,
          E.bailCost bail (((List.ofFn (schunk C1 C2 ω)).take i).flatten)
            (schunk C1 C2 ω i) pe
          = E.bailCost bail (((List.ofFn (C1.chunk ω.1)).take i).flatten)
            (C1.chunk ω.1 ⟨i, hi⟩) pe := by
        intro ω
        rw [stake_le ω hle]
        unfold schunk
        rw [dif_pos hi]
      have hL : ssize C1 C2 ω₀ i = C1.size ω₀.1 ⟨i, hi⟩ := by
        unfold ssize
        rw [dif_pos hi]
      have hmass : ∑ ω ∈ Finset.univ.filter
          (fun ω : C1.Ω × C2.Ω => C1.hist i ω.1 = C1.hist i ω₀.1),
          C1.P ω.1 * C2.P ω.2
          = ∑ ω1 ∈ Finset.univ.filter
              (fun ω1 => C1.hist (i : ℕ) ω1 = C1.hist (i : ℕ) ω₀.1), C1.P ω1 := by
        have h := sum_filter_fst (C1 := C1) (C2 := C2)
          (fun ω1 => C1.hist (i : ℕ) ω1 = C1.hist (i : ℕ) ω₀.1) (fun _ => 1)
        rw [Finset.sum_congr rfl (fun ω (_ : ω ∈ Finset.univ.filter
          (fun ω : C1.Ω × C2.Ω => C1.hist (i:ℕ) ω.1 = C1.hist (i:ℕ) ω₀.1)) =>
            (mul_one (C1.P ω.1 * C2.P ω.2)).symm)]
        rw [h]
        exact Finset.sum_congr rfl fun ω1 _ => mul_one _
      have hRHS : ∑ ω ∈ Finset.univ.filter
          (fun ω : C1.Ω × C2.Ω => C1.hist i ω.1 = C1.hist i ω₀.1),
          (C1.P ω.1 * C2.P ω.2) * E.bailCost bail
            (((List.ofFn (schunk C1 C2 ω)).take i).flatten)
            (schunk C1 C2 ω i) pe
          = ∑ ω1 ∈ Finset.univ.filter
              (fun ω1 => C1.hist (i : ℕ) ω1 = C1.hist (i : ℕ) ω₀.1),
            C1.P ω1 * E.bailCost bail
              (((List.ofFn (C1.chunk ω1)).take i).flatten)
              (C1.chunk ω1 ⟨i, hi⟩) pe := by
        rw [Finset.sum_congr rfl (fun ω (_ : ω ∈ Finset.univ.filter
          (fun ω : C1.Ω × C2.Ω => C1.hist (i:ℕ) ω.1 = C1.hist (i:ℕ) ω₀.1)) => by
            rw [hint ω])]
        exact sum_filter_fst (fun ω1 => C1.hist (i:ℕ) ω1 = C1.hist (i:ℕ) ω₀.1)
          (fun ω1 => E.bailCost bail
            (((List.ofFn (C1.chunk ω1)).take i).flatten)
            (C1.chunk ω1 ⟨i, hi⟩) pe)
      rw [hL, hmass, hRHS]
      exact C1.hcost ⟨i, hi⟩ ω₀.1 E bail
    · -- phase 2
      have him : C1.m ≤ (i : ℕ) := by omega
      set j : ℕ := (i : ℕ) - C1.m with hj_def
      have hjlt : j < C2.m := by have := i.isLt; omega
      have hfilter : Finset.univ.filter
          (fun ω : C1.Ω × C2.Ω => shist C1 C2 i ω = shist C1 C2 i ω₀)
          = Finset.univ.filter
            (fun ω : C1.Ω × C2.Ω =>
              (C1.hist C1.m ω.1 = C1.hist C1.m ω₀.1)
              ∧ (C2.hist j ω.2 = C2.hist j ω₀.2)) := by
        ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases heq : (i : ℕ) ≤ C1.m
        · have hieq : (i : ℕ) = C1.m := by omega
          have hj0 : j = 0 := by omega
          rw [shist_le heq ω, shist_le heq ω₀, Nat.pair_eq_pair, hieq, hj0]
          constructor
          · rintro ⟨h1, -⟩
            exact ⟨h1, h0triv2 ω.2 ω₀.2⟩
          · rintro ⟨h1, -⟩
            exact ⟨h1, rfl⟩
        · rw [shist_gt heq ω, shist_gt heq ω₀, Nat.pair_eq_pair]
      rw [hfilter]
      set h₀ : List (Set Y) := (List.ofFn (C1.chunk ω₀.1)).flatten with hh0_def
      have hint : ∀ ω : C1.Ω × C2.Ω,
          C1.hist C1.m ω.1 = C1.hist C1.m ω₀.1 →
          E.bailCost bail (((List.ofFn (schunk C1 C2 ω)).take i).flatten)
            (schunk C1 C2 ω i) pe
          = E.bailCost bail
            (h₀ ++ ((List.ofFn (C2.chunk ω.2)).take j).flatten)
            (C2.chunk ω.2 ⟨j, hjlt⟩) pe := by
        intro ω hω1
        rw [stake_ge ω him, List.flatten_append]
        unfold schunk
        rw [dif_neg hi]
        congr 2
        rw [hh0_def]
        exact flat1_const hω1
      have hL : ssize C1 C2 ω₀ i = C2.size ω₀.2 ⟨j, hjlt⟩ := by
        unfold ssize
        rw [dif_neg hi]
      set E₂ := shadowEvader (fun y : Y => y) (fun S : Set Y => S)
        (fun S y hy => hy) (fun S h => h) E h₀ with hE2_def
      set bail₂ : List (Set Y) → Bool :=
        fun l => bail (h₀ ++ reqMap (fun S : Set Y => S) l) with hbail2_def
      have hshadow : ∀ (h χ : List (Set Y)),
          E₂.bailCost bail₂ h χ pe ≤ E.bailCost bail (h₀ ++ h) χ pe := by
        intro h χ
        have := shadow_bailCost_le (fun y : Y => y) (fun S : Set Y => S)
          (fun y z => le_of_eq rfl) (fun S y hy => hy) (fun S h => h)
          E bail h₀ h χ (le_refl pe)
        rw [reqMap_id, reqMap_id] at this
        exact this
      have hprem := C2.hcost ⟨j, hjlt⟩ ω₀.2 E₂ bail₂
      -- assemble via the rectangular factorization
      set Q : Finset (C1.Ω × C2.Ω) := Finset.univ.filter
        (fun ω : C1.Ω × C2.Ω =>
          (C1.hist C1.m ω.1 = C1.hist C1.m ω₀.1)
          ∧ (C2.hist j ω.2 = C2.hist j ω₀.2)) with hQ_def
      set Q1 : Finset C1.Ω := Finset.univ.filter
        (fun ω1 => C1.hist C1.m ω1 = C1.hist C1.m ω₀.1) with hQ1_def
      set Q2 : Finset C2.Ω := Finset.univ.filter
        (fun ω2 => C2.hist j ω2 = C2.hist j ω₀.2) with hQ2_def
      set BC : C2.Ω → ℝ := fun ω2 => E.bailCost bail
        (h₀ ++ ((List.ofFn (C2.chunk ω2)).take j).flatten)
        (C2.chunk ω2 ⟨j, hjlt⟩) pe with hBC_def
      have hRHS : ∑ ω ∈ Q, (C1.P ω.1 * C2.P ω.2) * E.bailCost bail
            (((List.ofFn (schunk C1 C2 ω)).take i).flatten)
            (schunk C1 C2 ω i) pe
          = ∑ ω1 ∈ Q1, ∑ ω2 ∈ Q2, C1.P ω1 * (C2.P ω2 * BC ω2) := by
        have h1 : ∑ ω ∈ Q, (C1.P ω.1 * C2.P ω.2) * E.bailCost bail
              (((List.ofFn (schunk C1 C2 ω)).take i).flatten)
              (schunk C1 C2 ω i) pe
            = ∑ ω ∈ Q, (C1.P ω.1 * C2.P ω.2) * BC ω.2 := by
          refine Finset.sum_congr rfl fun ω hm => ?_
          rw [hQ_def, Finset.mem_filter] at hm
          rw [hint ω hm.2.1, hBC_def]
        rw [h1, hQ_def, hQ1_def, hQ2_def]
        exact sum_filter_rect
          (fun ω1 => C1.hist C1.m ω1 = C1.hist C1.m ω₀.1)
          (fun ω2 => C2.hist j ω2 = C2.hist j ω₀.2)
          (fun _ ω2 => BC ω2)
      have hmass : ∑ ω ∈ Q, C1.P ω.1 * C2.P ω.2
          = (∑ ω1 ∈ Q1, C1.P ω1) * ∑ ω2 ∈ Q2, C2.P ω2 := by
        have h1 : ∑ ω ∈ Q, C1.P ω.1 * C2.P ω.2
            = ∑ ω ∈ Q, (C1.P ω.1 * C2.P ω.2) * ((1:ℝ)) := by
          exact Finset.sum_congr rfl fun ω _ => by ring
        have h2 : ∑ ω ∈ Q, (C1.P ω.1 * C2.P ω.2) * ((1:ℝ))
            = ∑ ω1 ∈ Q1, ∑ ω2 ∈ Q2, C1.P ω1 * (C2.P ω2 * 1) := by
          rw [hQ_def, hQ1_def, hQ2_def]
          exact sum_filter_rect
            (fun ω1 => C1.hist C1.m ω1 = C1.hist C1.m ω₀.1)
            (fun ω2 => C2.hist j ω2 = C2.hist j ω₀.2)
            (fun _ _ => (1:ℝ))
        rw [h1, h2, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ω1 _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω2 _ => by ring
      have hinner : C2.size ω₀.2 ⟨j, hjlt⟩ * ∑ ω2 ∈ Q2, C2.P ω2
          ≤ ∑ ω2 ∈ Q2, C2.P ω2 * BC ω2 := by
        refine le_trans hprem ?_
        refine Finset.sum_le_sum fun ω2 _ => ?_
        exact mul_le_mul_of_nonneg_left (hshadow _ _) (le_of_lt (C2.hP ω2))
      rw [hL, hmass, hRHS]
      have hfin : C2.size ω₀.2 ⟨j, hjlt⟩
            * ((∑ ω1 ∈ Q1, C1.P ω1) * ∑ ω2 ∈ Q2, C2.P ω2)
          ≤ ∑ ω1 ∈ Q1, ∑ ω2 ∈ Q2, C1.P ω1 * (C2.P ω2 * BC ω2) := by
        have h1 : C2.size ω₀.2 ⟨j, hjlt⟩
              * ((∑ ω1 ∈ Q1, C1.P ω1) * ∑ ω2 ∈ Q2, C2.P ω2)
            = (∑ ω1 ∈ Q1, C1.P ω1)
              * (C2.size ω₀.2 ⟨j, hjlt⟩ * ∑ ω2 ∈ Q2, C2.P ω2) := by ring
        have h2 : (∑ ω1 ∈ Q1, C1.P ω1) * (∑ ω2 ∈ Q2, C2.P ω2 * BC ω2)
            = ∑ ω1 ∈ Q1, ∑ ω2 ∈ Q2, C1.P ω1 * (C2.P ω2 * BC ω2) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun ω1 _ => ?_
          rw [Finset.mul_sum]
        rw [h1, ← h2]
        refine mul_le_mul_of_nonneg_left hinner ?_
        exact Finset.sum_nonneg fun ω1 _ => le_of_lt (C1.hP ω1)
      exact hfin
  · -- htotal
    show T1 + T2 ≤ ∑ ω : C1.Ω × C2.Ω,
      (C1.P ω.1 * C2.P ω.2) * ∑ i, ssize C1 C2 ω i
    have hsum : ∑ ω : C1.Ω × C2.Ω,
        (C1.P ω.1 * C2.P ω.2) * ∑ i, ssize C1 C2 ω i
        = (∑ ω1, C1.P ω1 * ∑ i, C1.size ω1 i)
          + ∑ ω2, C2.P ω2 * ∑ i, C2.size ω2 i := by
      calc ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2) * ∑ i, ssize C1 C2 ω i
          = ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2)
            * ((fun ω1 => ∑ i, C1.size ω1 i) ω.1
              + (fun ω2 => ∑ i, C2.size ω2 i) ω.2) :=
            Finset.sum_congr rfl fun ω _ => by rw [ssize_split ω]
        _ = _ := sum_prod_add (fun ω1 => ∑ i, C1.size ω1 i)
            (fun ω2 => ∑ i, C2.size ω2 i)
    rw [hsum]
    exact add_le_add C1.htotal C2.htotal
  · -- initial history trivial
    intro ω₁ ω₂
    show shist C1 C2 0 ω₁ = shist C1 C2 0 ω₂
    rw [shist_le (Nat.zero_le _) ω₁, shist_le (Nat.zero_le _) ω₂,
      h0triv1 ω₁.1 ω₂.1]
  · -- variance adds
    show ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2)
        * ((∑ i, ssize C1 C2 ω i)
          - ∑ ω', (C1.P ω'.1 * C2.P ω'.2) * ∑ i, ssize C1 C2 ω' i) ^ 2
      ≤ V1 + V2
    set A : C1.Ω → ℝ := fun ω1 => ∑ i, C1.size ω1 i with hA_def
    set B : C2.Ω → ℝ := fun ω2 => ∑ i, C2.size ω2 i with hB_def
    set Am : ℝ := ∑ ω1, C1.P ω1 * A ω1 with hAm_def
    set Bm : ℝ := ∑ ω2, C2.P ω2 * B ω2 with hBm_def
    have hmean : ∑ ω' : C1.Ω × C2.Ω,
        (C1.P ω'.1 * C2.P ω'.2) * ∑ i, ssize C1 C2 ω' i = Am + Bm := by
      rw [Finset.sum_congr rfl fun ω _ => by rw [ssize_split ω]]
      exact sum_prod_add A B
    rw [Finset.sum_congr rfl fun ω _ => by rw [ssize_split ω, hmean]]
    have hpt : ∀ ω : C1.Ω × C2.Ω,
        (A ω.1 + B ω.2 - (Am + Bm)) ^ 2
          = (A ω.1 - Am) ^ 2 + (B ω.2 - Bm) ^ 2
            + 2 * ((A ω.1 - Am) * (B ω.2 - Bm)) := by
      intro ω
      ring
    rw [Finset.sum_congr rfl fun ω _ => by rw [hpt ω]]
    have hsplit : ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2)
        * ((A ω.1 - Am) ^ 2 + (B ω.2 - Bm) ^ 2
          + 2 * ((A ω.1 - Am) * (B ω.2 - Bm)))
        = (∑ ω1, C1.P ω1 * (A ω1 - Am) ^ 2)
          + (∑ ω2, C2.P ω2 * (B ω2 - Bm) ^ 2)
          + 2 * ((∑ ω1, C1.P ω1 * (A ω1 - Am))
            * ∑ ω2, C2.P ω2 * (B ω2 - Bm)) := by
      have h1 : ∀ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2)
          * ((A ω.1 - Am) ^ 2 + (B ω.2 - Bm) ^ 2
            + 2 * ((A ω.1 - Am) * (B ω.2 - Bm)))
          = (C1.P ω.1 * C2.P ω.2) * ((A ω.1 - Am) ^ 2 + (B ω.2 - Bm) ^ 2)
            + 2 * ((C1.P ω.1 * C2.P ω.2) * ((A ω.1 - Am) * (B ω.2 - Bm))) := by
        intro ω
        ring
      rw [Finset.sum_congr rfl fun ω _ => by rw [h1 ω],
        Finset.sum_add_distrib]
      congr 1
      · calc ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2)
            * ((A ω.1 - Am) ^ 2 + (B ω.2 - Bm) ^ 2)
            = ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2)
              * ((fun ω1 => (A ω1 - Am) ^ 2) ω.1
                + (fun ω2 => (B ω2 - Bm) ^ 2) ω.2) := rfl
          _ = _ := sum_prod_add (fun ω1 => (A ω1 - Am) ^ 2)
              (fun ω2 => (B ω2 - Bm) ^ 2)
      · calc ∑ ω : C1.Ω × C2.Ω,
            2 * ((C1.P ω.1 * C2.P ω.2) * ((A ω.1 - Am) * (B ω.2 - Bm)))
            = 2 * ∑ ω : C1.Ω × C2.Ω, (C1.P ω.1 * C2.P ω.2)
              * ((fun ω1 => A ω1 - Am) ω.1 * (fun ω2 => B ω2 - Bm) ω.2) := by
              rw [Finset.mul_sum]
          _ = 2 * ((∑ ω1, C1.P ω1 * (A ω1 - Am))
              * ∑ ω2, C2.P ω2 * (B ω2 - Bm)) := by
              rw [sum_prod_mul (fun ω1 => A ω1 - Am) (fun ω2 => B ω2 - Bm)]
    rw [hsplit]
    have hcen1 : ∑ ω1, C1.P ω1 * (A ω1 - Am) = 0 := by
      have h1 : ∀ ω1, C1.P ω1 * (A ω1 - Am) = C1.P ω1 * A ω1 - Am * C1.P ω1 :=
        fun ω1 => by ring
      rw [Finset.sum_congr rfl fun ω1 _ => by rw [h1 ω1],
        Finset.sum_sub_distrib, ← Finset.mul_sum, C1.hPsum, ← hAm_def]
      ring
    rw [hcen1, zero_mul, mul_zero, add_zero]
    exact add_le_add hVar1 hVar2

end Main

end SeqComp

namespace KServer

/-- Sequential composition of chunk systems at a geodesic junction. -/
theorem chunk_system_seq {Y : Type*} [MetricSpace Y] {a b c : Y}
    {cA1 cB1 cA2 cB2 T1 T2 pe : ℝ} {mL1 mL2 : ℕ}
    (C1 : ChunkSystemB Y a b cA1 cB1 T1 pe mL1)
    (C2 : ChunkSystemB Y b c cA2 cB2 T2 pe mL2)
    {cLo cHi V1 V2 : ℝ}
    (hgeo : dist a b + dist b c ≤ dist a c)
    (hpe : 0 ≤ pe)
    (hlo1 : cLo ≤ cA1) (hlo2 : cLo ≤ cA2)
    (hhi1 : cB1 ≤ cHi) (hhi2 : cB2 ≤ cHi)
    (h0triv1 : ∀ ω₁ ω₂ : C1.Ω, C1.hist 0 ω₁ = C1.hist 0 ω₂)
    (h0triv2 : ∀ ω₁ ω₂ : C2.Ω, C2.hist 0 ω₁ = C2.hist 0 ω₂)
    (hVar1 : ∑ ω, C1.P ω * ((∑ i, C1.size ω i)
      - ∑ ω', C1.P ω' * ∑ i, C1.size ω' i) ^ 2 ≤ V1)
    (hVar2 : ∑ ω, C2.P ω * ((∑ i, C2.size ω i)
      - ∑ ω', C2.P ω' * ∑ i, C2.size ω' i) ^ 2 ≤ V2) :
    ∃ C' : ChunkSystemB Y a c cLo cHi (T1 + T2) pe (mL1 + mL2),
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V1 + V2) :=
  SeqComp.seq_compose C1 C2 hgeo hpe hlo1 hlo2 hhi1 hhi2 h0triv1 h0triv2
    hVar1 hVar2

end KServer

theorem solution {Y : Type*} [MetricSpace Y] {a b c : Y}
    {cA1 cB1 cA2 cB2 T1 T2 pe : ℝ} {mL1 mL2 : ℕ}
    (C1 : KServer.ChunkSystemB Y a b cA1 cB1 T1 pe mL1)
    (C2 : KServer.ChunkSystemB Y b c cA2 cB2 T2 pe mL2)
    {cLo cHi V1 V2 : ℝ}
    (hgeo : dist a b + dist b c ≤ dist a c)
    (hpe : 0 ≤ pe)
    (hlo1 : cLo ≤ cA1) (hlo2 : cLo ≤ cA2)
    (hhi1 : cB1 ≤ cHi) (hhi2 : cB2 ≤ cHi)
    (h0triv1 : ∀ ω₁ ω₂ : C1.Ω, C1.hist 0 ω₁ = C1.hist 0 ω₂)
    (h0triv2 : ∀ ω₁ ω₂ : C2.Ω, C2.hist 0 ω₁ = C2.hist 0 ω₂)
    (hVar1 : ∑ ω, C1.P ω * ((∑ i, C1.size ω i)
      - ∑ ω', C1.P ω' * ∑ i, C1.size ω' i) ^ 2 ≤ V1)
    (hVar2 : ∑ ω, C2.P ω * ((∑ i, C2.size ω i)
      - ∑ ω', C2.P ω' * ∑ i, C2.size ω' i) ^ 2 ≤ V2) :
    ∃ C' : KServer.ChunkSystemB Y a c cLo cHi (T1 + T2) pe (mL1 + mL2),
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V1 + V2) :=
  KServer.chunk_system_seq C1 C2 hgeo hpe hlo1 hlo2 hhi1 hhi2 h0triv1 h0triv2
    hVar1 hVar2
