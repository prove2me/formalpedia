-- Prove2me | solution 1 for KServer.chunk_two_point_expTotal_le
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-10T09:55:06.985074+00:00
-- url     : https://prove2.me/submissions/46a8ff4b-8ddd-41e4-90a2-11dac41d56a5

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping

/-!
# Two-point rigidity for chunk systems with a Doob jump bound

On a metric space with only two points `s ≠ t`, a chunk system with online escapes
whose size floor is `0`, whose initial information is trivial and whose Doob martingale
of the total size has jumps at most `jb`, has expected total size at most `cHi + jb`.

The point is that on two points all the mass of a chunk system comes from a single
crossing: as soon as one request avoids `s`, the offline constraint forces every later
request to contain `t`, so the lazy evader pays `d(s,t)` once and nothing afterwards.
The first time at which the crossing has positive conditional probability is a stopping
time; before it no chunk carries any mass, and at it the conditional future mass is at
most one chunk plus one Doob jump, because on the branch that crosses there the whole
future mass collapses to zero in a single step.
-/

set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

open KServer

namespace TwoPointRigidity

/-! ### Elementary facts about evader costs -/

section EvaderCost

variable {X : Type*} [MetricSpace X]

theorem cost_append (E : EvaderAlgorithm X) (h χ : List (Set X)) :
    E.cost (h ++ χ) = E.cost h
      + ∑ j ∈ Finset.range χ.length,
          dist (E.pos (h ++ χ.take j)) (E.pos (h ++ χ.take (j + 1))) := by
  unfold EvaderAlgorithm.cost
  rw [List.length_append, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (le_of_lt hj), List.take_append_of_le_length hj]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : (h ++ χ).take (h.length + j) = h ++ χ.take j := by
      simp [List.take_append, List.take_of_length_le]
    have e2 : (h ++ χ).take (h.length + j + 1) = h ++ χ.take (j + 1) := by
      have hj : h.length + j + 1 = h.length + (j + 1) := by ring
      rw [hj]
      simp [List.take_append, List.take_of_length_le]
    rw [e1, e2]

theorem costOn_eq (E : EvaderAlgorithm X) (h χ : List (Set X)) :
    E.costOn h χ = ∑ j ∈ Finset.range χ.length,
      dist (E.pos (h ++ χ.take j)) (E.pos (h ++ χ.take (j + 1))) := by
  simp [EvaderAlgorithm.costOn, cost_append]

theorem costOn_nonneg (E : EvaderAlgorithm X) (h χ : List (Set X)) :
    0 ≤ E.costOn h χ := by
  rw [costOn_eq]
  exact Finset.sum_nonneg fun j _ => dist_nonneg

/-- If the evader never moves during the chunk, the chunk is free. -/
theorem costOn_eq_zero_of_pos_const (E : EvaderAlgorithm X) (h χ : List (Set X)) (x : X)
    (hx : ∀ j ≤ χ.length, E.pos (h ++ χ.take j) = x) : E.costOn h χ = 0 := by
  rw [costOn_eq]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [hx j (le_of_lt hj), hx (j + 1) hj, dist_self]

/-- With the never-bailing rule, the bail cost is just the cost of the chunk. -/
theorem bailCost_never (E : EvaderAlgorithm X) (h χ : List (Set X)) (p : ℝ) :
    E.bailCost (fun _ => false) h χ p = E.costOn h χ := by
  unfold EvaderAlgorithm.bailCost bailTime
  have : List.find? (fun _ => false) (List.range χ.length) = none :=
    List.find?_eq_none.mpr (by simp)
  rw [this]

end EvaderCost

/-! ### The two-point space: lazy evaders and the no-return property -/

section TwoPoint

variable {X : Type*} [MetricSpace X] {s t : X}

/-- Some offline path serving `σ`. -/
noncomputable def somePath (x₀ : X) (σ : List (Set X)) (hne : ∀ S ∈ σ, S.Nonempty) : ℕ → X :=
  fun j => if h : 0 < j ∧ j - 1 < σ.length then (hne _ (List.getElem_mem h.2)).some else x₀

theorem somePath_serves (x₀ : X) (σ : List (Set X)) (hne : ∀ S ∈ σ, S.Nonempty) :
    EvaderServes x₀ σ (somePath x₀ σ hne) := by
  constructor
  · simp [somePath]
  · intro j _
    have hj : 0 < (j : ℕ) + 1 ∧ (j : ℕ) + 1 - 1 < σ.length := ⟨Nat.succ_pos _, by simp⟩
    simp only [somePath, dif_pos hj, List.get_eq_getElem]
    exact (hne _ (List.getElem_mem hj.2)).some_mem

/-- On a two point space, an offline path of cost at most `d(s,t)` cannot leave `s`
and come back. -/
theorem no_return_idx (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    (σ : List (Set X)) (hne : ∀ S ∈ σ, S.Nonempty)
    (hopt : evaderOfflineCost s σ ≤ dist s t)
    {a b : ℕ} (hab : a < b) (hbl : b < σ.length)
    (ha : s ∉ σ[a]'(by omega)) (hb : t ∉ σ[b]'hbl) : False := by
  have hal : a < σ.length := by omega
  have hd : 0 < dist s t := dist_pos.mpr hst
  have key : ∀ c ∈ {c : ℝ | ∃ P : ℕ → X, EvaderServes s σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))}, 2 * dist s t ≤ c := by
    rintro c ⟨P, ⟨hP0, hPs⟩, rfl⟩
    have hPa : P (a + 1) = t := by
      have hmem := hPs ⟨a, hal⟩ (by simpa [List.get_eq_getElem] using hne _ (List.getElem_mem hal))
      rw [List.get_eq_getElem] at hmem
      rcases htwo (P (a + 1)) with h | h
      · exact absurd (h ▸ hmem) ha
      · exact h
    have hPb : P (b + 1) = s := by
      have hmem := hPs ⟨b, hbl⟩ (by simpa [List.get_eq_getElem] using hne _ (List.getElem_mem hbl))
      rw [List.get_eq_getElem] at hmem
      rcases htwo (P (b + 1)) with h | h
      · exact h
      · exact absurd (h ▸ hmem) hb
    have h1 : dist s t ≤ ∑ j ∈ Finset.range (a + 1), dist (P j) (P (j + 1)) := by
      have := dist_le_range_sum_dist P (a + 1)
      rw [hP0, hPa] at this
      exact this
    have h2 : dist s t ≤ ∑ j ∈ Finset.Ico (a + 1) (b + 1), dist (P j) (P (j + 1)) := by
      have hre : ∑ j ∈ Finset.Ico (a + 1) (b + 1), dist (P j) (P (j + 1))
          = ∑ i ∈ Finset.range (b - a), dist (P (a + 1 + i)) (P (a + 1 + i + 1)) := by
        rw [Finset.sum_Ico_eq_sum_range, show b + 1 - (a + 1) = b - a from by omega]
      rw [hre]
      have := dist_le_range_sum_dist (fun i => P (a + 1 + i)) (b - a)
      simp only [Nat.add_zero] at this
      have hb' : a + 1 + (b - a) = b + 1 := by omega
      rw [hb'] at this
      rw [hPa, hPb, dist_comm t s] at this
      exact this
    have hsplit : ∑ j ∈ Finset.range (a + 1), dist (P j) (P (j + 1))
        + ∑ j ∈ Finset.Ico (a + 1) (b + 1), dist (P j) (P (j + 1))
        ≤ ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1)) := by
      have hsub : Finset.range (b + 1) ⊆ Finset.range σ.length := by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      have hle : ∑ j ∈ Finset.range (b + 1), dist (P j) (P (j + 1))
          ≤ ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => dist_nonneg)
      have heq : ∑ j ∈ Finset.range (a + 1), dist (P j) (P (j + 1))
          + ∑ j ∈ Finset.Ico (a + 1) (b + 1), dist (P j) (P (j + 1))
          = ∑ j ∈ Finset.range (b + 1), dist (P j) (P (j + 1)) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
        exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
      rw [heq]
      exact hle
    linarith
  have hnonempty : {c : ℝ | ∃ P : ℕ → X, EvaderServes s σ P ∧
      c = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))}.Nonempty :=
    ⟨_, somePath s σ hne, somePath_serves s σ hne, rfl⟩
  have : 2 * dist s t ≤ evaderOfflineCost s σ := le_csInf hnonempty key
  linarith

open Classical in
/-- The evader that sits at `b` whenever the last request allows it, and at `o`
otherwise. -/
noncomputable def posOf (b o : X) (l : List (Set X)) : X :=
  match l.getLast? with
  | none => b
  | some S => if b ∈ S then b else o

theorem posOf_eq_base {b o : X} {l : List (Set X)}
    (h : ∀ S, l.getLast? = some S → b ∈ S) : posOf b o l = b := by
  rcases hl : l.getLast? with - | S
  · simp [posOf, hl]
  · simp [posOf, hl, h S hl]

theorem posOf_serves (htwo : ∀ x : X, x = s ∨ x = t) (b o : X) (hbo : b ≠ o)
    (hb : b = s ∨ b = t) (ho : o = s ∨ o = t)
    (l : List (Set X)) (S : Set X) (hS : S.Nonempty) : posOf b o (l ++ [S]) ∈ S := by
  have hlast : (l ++ [S]).getLast? = some S := by simp
  by_cases hbS : b ∈ S
  · simp [posOf, hlast, hbS]
  · simp only [posOf, hlast, if_neg hbS]
    obtain ⟨x, hx⟩ := hS
    rcases hb with rfl | rfl <;> rcases ho with rfl | rfl <;> rcases htwo x with rfl | rfl <;>
      first
        | exact absurd rfl hbo
        | exact absurd hx hbS
        | exact hx

/-- A lazy evader pays nothing on a chunk all of whose requests it can serve without
moving. -/
theorem costOn_lazy_eq_zero {b o : X} {E : EvaderAlgorithm X} (hE : E.pos = posOf b o)
    (h χ : List (Set X)) (hh : ∀ S, h.getLast? = some S → b ∈ S) (hχ : ∀ S ∈ χ, b ∈ S) :
    E.costOn h χ = 0 := by
  refine costOn_eq_zero_of_pos_const E h χ b fun j _ => ?_
  rw [hE]
  refine posOf_eq_base fun S hS => ?_
  rw [List.getLast?_append] at hS
  rcases hl : (χ.take j).getLast? with - | T
  · rw [hl] at hS
    simp only [Option.none_or] at hS
    exact hh S hS
  · rw [hl] at hS
    simp only [Option.some_or, Option.some.injEq] at hS
    subst hS
    exact hχ _ (List.mem_of_mem_take (List.mem_of_getLast? hl))

/-- List form of the no-return property: after a request that avoids `s`, every request
contains `t`. -/
theorem no_return_list (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    (p r : List (Set X)) (S : Set X)
    (hne : ∀ T ∈ p ++ S :: r, T.Nonempty)
    (hopt : evaderOfflineCost s (p ++ S :: r) ≤ dist s t)
    (hS : s ∉ S) : t ∈ S ∧ ∀ T ∈ r, t ∈ T := by
  have hSa : (p ++ S :: r)[p.length]'(by simp) = S := by
    rw [List.getElem_append_right (le_refl _)]
    simp
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne S (by simp)
    rcases htwo x with rfl | rfl
    · exact absurd hx hS
    · exact hx
  · intro T hT
    by_contra hTt
    obtain ⟨k, hk, hkT⟩ : ∃ k, ∃ _ : k < r.length, r[k] = T := by
      obtain ⟨k, hk⟩ := List.getElem_of_mem hT
      exact ⟨k, hk.choose, hk.choose_spec⟩
    have hb : p.length + 1 + k < (p ++ S :: r).length := by simp; omega
    have hTb : (p ++ S :: r)[p.length + 1 + k]'hb = T := by
      rw [List.getElem_append_right (by omega)]
      have hidx : p.length + 1 + k - p.length = k + 1 := by omega
      simp only [hidx, List.getElem_cons_succ]
      exact hkT
    exact no_return_idx hst htwo (p ++ S :: r) hne hopt (a := p.length) (b := p.length + 1 + k)
      (by omega) hb (by rw [hSa]; exact hS) (by rw [hTb]; exact hTt)

end TwoPoint

end TwoPointRigidity

namespace TwoPointRigidity

/-! ### Structure of a branch on the two-point space -/

section Structure

variable {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ} {mL : ℕ}
variable (C : ChunkSystemB X s t 0 cB T pe mL)

/-- The list of chunks of an outcome. -/
noncomputable def chunks (ω : C.Ω) : List (List (Set X)) := List.ofFn (C.chunk ω)

/-- The history of requests preceding chunk `i`. -/
noncomputable def prefixAt (i : ℕ) (ω : C.Ω) : List (Set X) := ((chunks C ω).take i).flatten

/-- Chunk `i` of `ω` contains a request that avoids `s`: the crossing happens there. -/
def SFree (i : ℕ) (ω : C.Ω) : Prop := ∃ hi : i < C.m, ∃ S ∈ C.chunk ω ⟨i, hi⟩, s ∉ S

/-- The crossing has already happened strictly before chunk `h`. -/
def Sw (h : ℕ) (ω : C.Ω) : Prop := ∃ i < h, SFree C i ω

theorem chunks_length (ω : C.Ω) : (chunks C ω).length = C.m := by
  simp [chunks]

theorem chunks_getElem (ω : C.Ω) {i : ℕ} (hi : i < C.m) :
    (chunks C ω)[i]'(by rw [chunks_length]; exact hi) = C.chunk ω ⟨i, hi⟩ := by
  simp [chunks]

/-- Requests are nonempty. -/
theorem flatten_nonempty (ω : C.Ω) : ∀ S ∈ (chunks C ω).flatten, S.Nonempty := by
  intro S hS
  rw [List.mem_flatten] at hS
  obtain ⟨l, hl, hSl⟩ := hS
  rw [chunks, List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  exact C.hne ω i S hSl

theorem mem_flatten_of_mem_chunk {ω : C.Ω} {i : ℕ} (hi : i < C.m) {S : Set X}
    (hS : S ∈ C.chunk ω ⟨i, hi⟩) : S ∈ (chunks C ω).flatten := by
  refine List.mem_flatten.mpr ⟨C.chunk ω ⟨i, hi⟩, ?_, hS⟩
  rw [chunks, List.mem_ofFn]
  exact ⟨⟨i, hi⟩, rfl⟩

end Structure

end TwoPointRigidity

namespace TwoPointRigidity

/-! ### The crossing time and the rigidity theorem -/

section Rigidity

variable {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ} {mL : ℕ}
variable (C : ChunkSystemB X s t 0 cB T pe mL)

/-- The crossing has positive conditional probability at time `h`: some branch of the
time-`h` atom crosses in chunk `h` and has not crossed before. -/
def Active (h : ℕ) (ω : C.Ω) : Prop := ∃ ω' ∈ C.atom h ω, SFree C h ω' ∧ ¬ Sw C h ω'

theorem chunk_mem_drop {ω : C.Ω} {i j : ℕ} (hij : j < i) (hi : i < C.m) {Tq : Set X}
    (hT : Tq ∈ C.chunk ω ⟨i, hi⟩) : Tq ∈ ((chunks C ω).drop (j + 1)).flatten := by
  refine List.mem_flatten.mpr ⟨C.chunk ω ⟨i, hi⟩, ?_, hT⟩
  have hlen : (chunks C ω).length = C.m := chunks_length C ω
  have hidx : i - (j + 1) < ((chunks C ω).drop (j + 1)).length := by
    rw [List.length_drop, hlen]; omega
  have hsum : j + 1 + (i - (j + 1)) = i := by omega
  have heq : ((chunks C ω).drop (j + 1))[i - (j + 1)]'hidx = C.chunk ω ⟨i, hi⟩ := by
    simp only [chunks, List.getElem_drop, List.getElem_ofFn]
    congr 1
    exact Fin.ext (by simpa using hsum)
  exact heq ▸ List.getElem_mem hidx

/-- After the crossing in chunk `j`, every later request contains `t`, and the last
request of every history reaching past chunk `j` contains `t`. -/
theorem after_switch (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    {j : ℕ} {ω : C.Ω} (hsf : SFree C j ω) :
    (∀ Tq ∈ ((chunks C ω).drop (j + 1)).flatten, t ∈ Tq) ∧
      (∀ i, j < i → ∀ L, (prefixAt C i ω).getLast? = some L → t ∈ L) := by
  classical
  obtain ⟨hj, S, hSmem, hSs⟩ := hsf
  set L0 := chunks C ω with hL0
  have hmemtake : C.chunk ω ⟨j, hj⟩ ∈ L0.take (j + 1) := by
    have hlen : L0.length = C.m := chunks_length C ω
    have hidx : j < (L0.take (j + 1)).length := by
      rw [List.length_take, hlen]; omega
    have heq : (L0.take (j + 1))[j]'hidx = C.chunk ω ⟨j, hj⟩ := by
      simp only [hL0, chunks, List.getElem_take, List.getElem_ofFn]
    exact heq ▸ List.getElem_mem hidx
  have hSA : S ∈ (L0.take (j + 1)).flatten :=
    List.mem_flatten.mpr ⟨C.chunk ω ⟨j, hj⟩, hmemtake, hSmem⟩
  obtain ⟨p, r, hpr⟩ := List.append_of_mem hSA
  have hsplit : L0.flatten = (L0.take (j + 1)).flatten ++ (L0.drop (j + 1)).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  have hflat : L0.flatten = p ++ S :: (r ++ (L0.drop (j + 1)).flatten) := by
    rw [hsplit, hpr]; simp
  have hne : ∀ Tq ∈ p ++ S :: (r ++ (L0.drop (j + 1)).flatten), Tq.Nonempty := by
    intro Tq hT
    exact flatten_nonempty C ω Tq (by rw [← hL0, hflat]; exact hT)
  have hopt : evaderOfflineCost s (p ++ S :: (r ++ (L0.drop (j + 1)).flatten))
      ≤ dist s t := by
    have h1 := C.hopt ω
    have h2 : (List.ofFn (C.chunk ω)).flatten
        = p ++ S :: (r ++ (L0.drop (j + 1)).flatten) := hflat
    rwa [h2] at h1
  obtain ⟨hSt, hrest⟩ :=
    no_return_list hst htwo p (r ++ (L0.drop (j + 1)).flatten) S hne hopt hSs
  refine ⟨fun Tq hTq => hrest Tq (by simp [hTq]), ?_⟩
  intro i hji L hL
  have hi1 : i = (j + 1) + (i - (j + 1)) := by omega
  have htake : L0.take i = L0.take (j + 1) ++ (L0.drop (j + 1)).take (i - (j + 1)) := by
    conv_lhs => rw [hi1]
    exact List.take_add ..
  have hpref : prefixAt C i ω
      = (p ++ S :: r) ++ ((L0.drop (j + 1)).take (i - (j + 1))).flatten := by
    unfold prefixAt
    rw [← hL0, htake, List.flatten_append, hpr]
  rw [hpref, List.getLast?_append] at hL
  rcases hB : (((L0.drop (j + 1)).take (i - (j + 1))).flatten).getLast? with - | L'
  · rw [hB] at hL
    simp only [Option.none_or] at hL
    have hmemL : L ∈ S :: r := by
      have hlast : (S :: r).getLast? = some L := by
        rw [List.getLast?_append] at hL
        rcases hl : (S :: r).getLast? with - | L''
        · simp at hl
        · rw [hl] at hL; simpa using hL
      exact List.mem_of_getLast? hlast
    rcases List.mem_cons.1 hmemL with rfl | hLr
    · exact hSt
    · exact hrest L (List.mem_append_left _ hLr)
  · rw [hB] at hL
    simp only [Option.some_or, Option.some.injEq] at hL
    have hmem : L' ∈ ((L0.drop (j + 1)).take (i - (j + 1))).flatten :=
      List.mem_of_getLast? hB
    rw [List.mem_flatten] at hmem
    obtain ⟨l, hl, hLl⟩ := hmem
    have htL : t ∈ L' :=
      hrest L' (List.mem_append_right _
        (List.mem_flatten.mpr ⟨l, List.mem_of_mem_take hl, hLl⟩))
    rwa [hL] at htL

theorem chunk_congr_hist {i h : ℕ} (hih : i < h) {ω ω' : C.Ω}
    (hh : C.hist h ω = C.hist h ω') (hi : i < C.m) :
    C.chunk ω ⟨i, hi⟩ = C.chunk ω' ⟨i, hi⟩ :=
  C.hadapt ⟨i, hi⟩ ω ω' (C.href (i + 1) h (by omega) ω ω' hh)

theorem SFree_congr {i h : ℕ} (hih : i < h) {ω ω' : C.Ω}
    (hh : C.hist h ω = C.hist h ω') : SFree C i ω ↔ SFree C i ω' := by
  constructor
  · rintro ⟨hi, S, hS, hSs⟩
    exact ⟨hi, S, (chunk_congr_hist C hih hh hi) ▸ hS, hSs⟩
  · rintro ⟨hi, S, hS, hSs⟩
    exact ⟨hi, S, (chunk_congr_hist C hih hh.symm hi) ▸ hS, hSs⟩

theorem Sw_congr {h : ℕ} {ω ω' : C.Ω} (hh : C.hist h ω = C.hist h ω') :
    Sw C h ω ↔ Sw C h ω' := by
  constructor
  · rintro ⟨i, hi, hsf⟩
    exact ⟨i, hi, (SFree_congr C hi hh).mp hsf⟩
  · rintro ⟨i, hi, hsf⟩
    exact ⟨i, hi, (SFree_congr C hi hh).mpr hsf⟩

theorem prefixAt_congr {i h : ℕ} (hih : i ≤ h) {ω ω' : C.Ω}
    (hh : C.hist h ω = C.hist h ω') : prefixAt C i ω = prefixAt C i ω' := by
  unfold prefixAt chunks
  congr 1
  refine List.ext_getElem (by simp) ?_
  intro n h1 h2
  have hnm : n < C.m := by
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at h1
    exact h1.2
  have hn : n < i := by
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at h1
    exact h1.1
  simp only [List.getElem_take, List.getElem_ofFn]
  exact chunk_congr_hist C (lt_of_lt_of_le hn hih) hh hnm

theorem mem_prefixAt {i : ℕ} {ω : C.Ω} {Tq : Set X} (hT : Tq ∈ prefixAt C i ω) :
    ∃ j, ∃ hj : j < C.m, j < i ∧ Tq ∈ C.chunk ω ⟨j, hj⟩ := by
  unfold prefixAt at hT
  rw [List.mem_flatten] at hT
  obtain ⟨l, hl, hTl⟩ := hT
  rw [List.mem_iff_getElem] at hl
  obtain ⟨n, hn, rfl⟩ := hl
  have hn2 : n < i ∧ n < C.m := by
    simpa [chunks, lt_min_iff] using hn
  refine ⟨n, hn2.2, hn2.1, ?_⟩
  simpa [chunks, List.getElem_take, List.getElem_ofFn] using hTl

/-- The chunk-size bound obtained from one evader and the never-bailing rule. -/
theorem sizeN_eq_zero_of_costs_zero {h : ℕ} (hm : h < C.m) (ω : C.Ω)
    (E : EvaderAlgorithm X)
    (hz : ∀ ω' ∈ C.atom h ω, E.costOn (prefixAt C h ω') (C.chunk ω' ⟨h, hm⟩) = 0) :
    C.sizeN h ω = 0 := by
  classical
  have hc := C.hcost ⟨h, hm⟩ ω E (fun _ => false)
  simp only [bailCost_never] at hc
  have hsum : ∑ ω' ∈ C.atom h ω,
      C.P ω' * E.costOn (prefixAt C h ω') (C.chunk ω' ⟨h, hm⟩) = 0 :=
    Finset.sum_eq_zero fun ω' hω' => by rw [hz ω' hω', mul_zero]
  have hcz : C.size ω ⟨h, hm⟩ * C.mass (C.atom h ω) ≤ 0 :=
    le_trans hc (le_of_eq hsum)
  have hmass := C.mass_atom_pos h ω
  have hle : C.size ω ⟨h, hm⟩ ≤ 0 := nonpos_of_mul_nonpos_right
    (by simpa [mul_comm] using hcz) hmass
  have hge : 0 ≤ C.size ω ⟨h, hm⟩ := (C.hsize ω ⟨h, hm⟩).1
  unfold ChunkSystemB.sizeN
  rw [dif_pos hm]
  linarith

/-- If the crossing cannot happen in chunk `h`, that chunk carries no mass. -/
theorem size_zero_of_not_active (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    {h : ℕ} (hm : h < C.m) (ω : C.Ω) (hna : ¬ Active C h ω) : C.sizeN h ω = 0 := by
  classical
  by_cases hsw : Sw C h ω
  · -- the crossing already happened: the lazy `t`-evader pays nothing
    refine sizeN_eq_zero_of_costs_zero C hm ω
      ⟨posOf t s, fun l S hS => posOf_serves htwo t s (Ne.symm hst)
        (Or.inr rfl) (Or.inl rfl) l S hS⟩ ?_
    intro ω' hω'
    have hh : C.hist h ω = C.hist h ω' := (C.mem_atom.mp hω').symm
    obtain ⟨j, hjh, hsf⟩ := (Sw_congr C hh).mp hsw
    obtain ⟨hdrop, hlast⟩ := after_switch C hst htwo hsf
    refine costOn_lazy_eq_zero (b := t) (o := s) rfl _ _ ?_ ?_
    · exact fun L hL => hlast h hjh L hL
    · exact fun Tq hTq => hdrop Tq (chunk_mem_drop C hjh hm hTq)
  · -- the crossing has not happened and cannot happen now: the lazy `s`-evader
    -- pays nothing
    refine sizeN_eq_zero_of_costs_zero C hm ω
      ⟨posOf s t, fun l S hS => posOf_serves htwo s t hst
        (Or.inl rfl) (Or.inr rfl) l S hS⟩ ?_
    intro ω' hω'
    have hh : C.hist h ω = C.hist h ω' := (C.mem_atom.mp hω').symm
    have hsw' : ¬ Sw C h ω' := fun hc => hsw ((Sw_congr C hh).mpr hc)
    have hsf' : ¬ SFree C h ω' := fun hc => hna ⟨ω', hω', hc, hsw'⟩
    have hall : ∀ j, ∀ hj : j < C.m, j ≤ h → ∀ S ∈ C.chunk ω' ⟨j, hj⟩, s ∈ S := by
      intro j hj hjh S hS
      by_contra hSs
      rcases lt_or_eq_of_le hjh with hlt | rfl
      · exact hsw' ⟨j, hlt, hj, S, hS, hSs⟩
      · exact hsf' ⟨hj, S, hS, hSs⟩
    refine costOn_lazy_eq_zero (b := s) (o := t) rfl _ _ ?_ ?_
    · intro L hL
      obtain ⟨j, hj, hjh, hmem⟩ := mem_prefixAt C (List.mem_of_getLast? hL)
      exact hall j hj (le_of_lt hjh) L hmem
    · exact fun Tq hTq => hall h hm (le_refl _) Tq hTq

/-- On the branch where the crossing happens, the whole future mass vanishes, so the
conditional future mass at that time is at most one chunk plus one Doob jump. -/
theorem condFuture_le_of_active (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    {jb : ℝ} (hjb : C.DoobJumpBound jb) {h : ℕ} (hm : h < C.m) (ω : C.Ω)
    (ha : Active C h ω) : C.condFuture h ω ≤ cB + jb := by
  classical
  obtain ⟨w, hw, hsf, -⟩ := ha
  have hh : C.hist h w = C.hist h ω := C.mem_atom.mp hw
  -- on the whole time-`h+1` atom of `w` the crossing has already happened, so no
  -- later chunk can carry mass
  have hzero : ∀ ω'' ∈ C.atom (h + 1) w, C.futureSize (h + 1) ω'' = 0 := by
    intro ω'' hω''
    have hw'' : C.hist (h + 1) ω'' = C.hist (h + 1) w := C.mem_atom.mp hω''
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [Finset.mem_filter] at hi
    have hji : h + 1 ≤ i.val := hi.2
    have hsz : C.sizeN i.val ω'' = 0 := by
      refine size_zero_of_not_active C hst htwo i.2 ω'' ?_
      rintro ⟨w', hw', hsf', hnsw'⟩
      refine hnsw' ⟨h, by omega, ?_⟩
      have h1 : C.hist i.val w' = C.hist i.val ω'' := C.mem_atom.mp hw'
      have h2 : C.hist (h + 1) w' = C.hist (h + 1) ω'' :=
        C.href (h + 1) i.val hji w' ω'' h1
      exact (SFree_congr C (Nat.lt_succ_self h) (h2.trans hw'').symm).mp hsf
    unfold ChunkSystemB.sizeN at hsz
    rwa [dif_pos i.2] at hsz
  have hcf : C.condFuture (h + 1) w = 0 := by
    unfold ChunkSystemB.condFuture
    rw [C.condExp_congr_fun (g := fun _ => (0 : ℝ)) (fun ω'' hmm => hzero ω'' hmm)]
    exact C.condExp_const 0 (h + 1) w
  have hstep := C.le_condFuture_succ hjb h w
  rw [hcf] at hstep
  have hsz : C.sizeN h w ≤ cB := C.sizeN_le hm w
  have hcong : C.condFuture h w = C.condFuture h ω := C.condFuture_congr hh
  linarith [hcong ▸ hstep]

/-! ### The crossing time -/

open Classical in
/-- The first time at which the crossing has positive conditional probability. -/
noncomputable def crossTime (ω : C.Ω) : ℕ := sInf {h | C.m ≤ h ∨ Active C h ω}

theorem crossTime_mem (ω : C.Ω) : C.m ≤ crossTime C ω ∨ Active C (crossTime C ω) ω := by
  have hne : {h | C.m ≤ h ∨ Active C h ω}.Nonempty := ⟨C.m, Or.inl le_rfl⟩
  exact Nat.sInf_mem hne

theorem crossTime_le_m (ω : C.Ω) : crossTime C ω ≤ C.m := Nat.sInf_le (Or.inl le_rfl)

theorem not_active_of_lt_crossTime {h : ℕ} {ω : C.Ω} (hlt : h < crossTime C ω) :
    ¬ Active C h ω := by
  intro ha
  have hle : crossTime C ω ≤ h := Nat.sInf_le (Or.inr ha)
  omega

theorem Active_congr {h : ℕ} {ω ω' : C.Ω} (hh : C.hist h ω = C.hist h ω') :
    Active C h ω ↔ Active C h ω' := by
  unfold Active
  rw [C.atom_eq_of_hist_eq hh]

theorem Active_lt_m {h : ℕ} {ω : C.Ω} (ha : Active C h ω) : h < C.m := by
  obtain ⟨-, -, ⟨hi, -⟩, -⟩ := ha
  exact hi

/-- The crossing time is a stopping time for the chunk filtration. -/
theorem crossTime_isStopping : C.IsStopping (crossTime C) := by
  have key : ∀ (h : ℕ) (ω ω' : C.Ω), C.hist h ω = C.hist h ω' →
      crossTime C ω ≤ h → crossTime C ω' ≤ h := by
    intro h ω ω' hh hle
    rcases crossTime_mem C ω with hm | ha
    · exact Nat.sInf_le (Or.inl (le_trans hm hle))
    · refine le_trans (Nat.sInf_le (Or.inr ?_)) hle
      exact (Active_congr C (C.href _ h hle ω ω' hh)).mp ha
  exact fun h ω ω' hh => ⟨key h ω ω' hh, key h ω' ω hh.symm⟩

/-- The conditional future mass at the crossing time is small. -/
theorem condFuture_crossTime_le (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    {jb : ℝ} (hjb : C.DoobJumpBound jb) (hnn : 0 ≤ cB + jb) (ω : C.Ω) :
    C.condFuture (crossTime C ω) ω ≤ cB + jb := by
  rcases crossTime_mem C ω with hm | ha
  · rw [C.condFuture_of_m_le hm]; exact hnn
  · exact condFuture_le_of_active C hst htwo hjb (Active_lt_m C ha) ω ha

/-- The conditional future mass at time `0` is at most `cHi + jb`. -/
theorem condFuture_zero_le (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    {jb : ℝ} (hjb : C.DoobJumpBound jb) (ω₀ : C.Ω) : C.condFuture 0 ω₀ ≤ cB + jb := by
  classical
  have hnn : 0 ≤ cB + jb := by
    have h1 := (C.hsize ω₀ ⟨0, C.hm0⟩).1
    have h2 := (C.hsize ω₀ ⟨0, C.hm0⟩).2
    have h3 : 0 ≤ jb := le_trans (abs_nonneg _) (hjb 0 ω₀)
    linarith
  have hmass := C.mass_atom_pos 0 ω₀
  have hOS := C.sum_atom_optional_stopping (crossTime C) (crossTime_isStopping C) 0 ω₀
    (fun ω _ => Nat.zero_le _) C.m (Nat.zero_le _) (fun ω _ => crossTime_le_m C ω)
  have hzero : ∀ ω ∈ C.atom 0 ω₀,
      ∑ j ∈ Finset.Ico 0 (crossTime C ω), C.sizeN j ω = 0 := by
    intro ω _
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    have hjm : j < C.m := lt_of_lt_of_le hj.2 (crossTime_le_m C ω)
    exact size_zero_of_not_active C hst htwo hjm ω (not_active_of_lt_crossTime C hj.2)
  have hRHS : ∑ ω ∈ C.atom 0 ω₀,
      C.P ω * (C.condFuture 0 ω - ∑ j ∈ Finset.Ico 0 (crossTime C ω), C.sizeN j ω)
      = C.condFuture 0 ω₀ * C.mass (C.atom 0 ω₀) := by
    rw [Finset.sum_congr rfl (fun ω hmm => by
      rw [hzero ω hmm, sub_zero, C.condFuture_congr (C.mem_atom.mp hmm)]),
      ← Finset.sum_mul]
    exact mul_comm _ _
  have hLHS : ∑ ω ∈ C.atom 0 ω₀, C.P ω * C.condFuture (crossTime C ω) ω
      ≤ (cB + jb) * C.mass (C.atom 0 ω₀) := by
    have h1 : ∑ ω ∈ C.atom 0 ω₀, C.P ω * C.condFuture (crossTime C ω) ω
        ≤ ∑ ω ∈ C.atom 0 ω₀, C.P ω * (cB + jb) :=
      Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left
          (condFuture_crossTime_le C hst htwo hjb hnn ω) (le_of_lt (C.hP ω))
    calc ∑ ω ∈ C.atom 0 ω₀, C.P ω * C.condFuture (crossTime C ω) ω
        ≤ ∑ ω ∈ C.atom 0 ω₀, C.P ω * (cB + jb) := h1
      _ = (cB + jb) * C.mass (C.atom 0 ω₀) := by
          rw [← Finset.sum_mul]; exact mul_comm _ _
  rw [hRHS] at hOS
  rw [hOS] at hLHS
  exact le_of_mul_le_mul_right (by linarith [hLHS]) hmass

/-- **Two-point rigidity.** On a metric space with two points, a chunk system with size
floor `0` and Doob jump bound `jb` has expected total size at most `cHi + jb`. -/
theorem twoPoint_expTotal_le (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    {jb : ℝ} (hjb : C.DoobJumpBound jb) :
    ∑ ω, C.P ω * C.totalSize ω ≤ cB + jb := by
  classical
  have hfut : ∀ ω : C.Ω, C.futureSize 0 ω = C.totalSize ω := by
    intro ω
    have h1 := C.pastSize_add_futureSize 0 ω
    have h2 : C.pastSize 0 ω = 0 := by simp [ChunkSystemB.pastSize]
    linarith
  have h1 : ∑ ω, C.P ω * C.condFuture 0 ω = ∑ ω, C.P ω * C.totalSize ω := by
    rw [show C.condFuture 0 = C.condExp (C.futureSize 0) 0 from rfl,
      C.sum_mul_condExp]
    exact Finset.sum_congr rfl fun ω _ => by rw [hfut ω]
  calc ∑ ω, C.P ω * C.totalSize ω = ∑ ω, C.P ω * C.condFuture 0 ω := h1.symm
    _ ≤ ∑ ω, C.P ω * (cB + jb) :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (condFuture_zero_le C hst htwo hjb ω)
            (le_of_lt (C.hP ω))
    _ = cB + jb := by rw [← Finset.sum_mul, C.hPsum, one_mul]

end Rigidity

end TwoPointRigidity

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t 0 cB T pe mL)
    (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    {jb : ℝ} (hjb : C.DoobJumpBound jb) :
    ∑ ω, C.P ω * ∑ i, C.size ω i ≤ cB + jb :=
  TwoPointRigidity.twoPoint_expTotal_le C hst htwo hjb

