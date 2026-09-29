-- Prove2me | solution 1 for KServer.chunk_two_point_total_le_dist
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-10T10:17:59.739487+00:00
-- url     : https://prove2.me/submissions/18fe0720-96e9-431a-9afd-52d103b04706

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_saturate

set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open KServer


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

/-!
# The expected total size of a chunk system is bounded by any evader's cost

For every chunk system with online escapes `C` and every evader `E`, the expected total
size of `C` is at most the expected cost of `E` on the request sequence of `C`.
-/



namespace EvaderBound

variable {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ} {mL : ℕ}
variable (C : ChunkSystemB X s t cLo cHi total price mL)

/-- The request history preceding chunk `i`. -/
noncomputable def pre (i : ℕ) (ω : C.Ω) : List (Set X) :=
  ((List.ofFn (C.chunk ω)).take i).flatten

/-- Chunk `i`, indexed by a natural number (empty beyond the last chunk). -/
noncomputable def chunkN (i : ℕ) (ω : C.Ω) : List (Set X) :=
  if h : i < C.m then C.chunk ω ⟨i, h⟩ else []

/-- Size of chunk `i`, indexed by a natural number (zero beyond the last chunk). -/
noncomputable def sizeN (i : ℕ) (ω : C.Ω) : ℝ :=
  if h : i < C.m then C.size ω ⟨i, h⟩ else 0

theorem bailCost_never {Y : Type*} [MetricSpace Y] (E : EvaderAlgorithm Y)
    (h χ : List (Set Y)) (p : ℝ) : E.bailCost (fun _ => false) h χ p = E.costOn h χ := by
  unfold EvaderAlgorithm.bailCost bailTime
  have hnone : List.find? (fun _ => false) (List.range χ.length) = none :=
    List.find?_eq_none.mpr (by simp)
  rw [hnone]

theorem cost_nil (E : EvaderAlgorithm X) : E.cost [] = 0 := by
  simp [EvaderAlgorithm.cost]

theorem pre_zero (ω : C.Ω) : pre C 0 ω = [] := by simp [pre]

theorem pre_m (ω : C.Ω) : pre C C.m ω = C.seq ω := by
  unfold pre ChunkSystemB.seq
  rw [List.take_of_length_le (by simp)]

theorem pre_succ (i : ℕ) (ω : C.Ω) :
    pre C (i + 1) ω = pre C i ω ++ chunkN C i ω := by
  unfold pre chunkN
  have hlen : (List.ofFn (C.chunk ω)).length = C.m := by simp
  by_cases hi : i < C.m
  · have h1 : (List.ofFn (C.chunk ω)).take (i + 1)
        = (List.ofFn (C.chunk ω)).take i ++ [C.chunk ω ⟨i, hi⟩] := by
      rw [List.take_add_one]
      congr 1
      rw [List.getElem?_eq_getElem (by rw [hlen]; exact hi)]
      simp
    rw [h1, List.flatten_append, dif_pos hi]
    simp
  · have h1 : (List.ofFn (C.chunk ω)).take (i + 1) = (List.ofFn (C.chunk ω)).take i := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    rw [h1, dif_neg hi]
    simp

/-- One chunk: the expected size is at most the expected cost of the evader on that
chunk. -/
theorem sum_sizeN_le_sum_costOn (E : EvaderAlgorithm X) (i : ℕ) :
    ∑ ω, C.P ω * sizeN C i ω
      ≤ ∑ ω, C.P ω * E.costOn (pre C i ω) (chunkN C i ω) := by
  classical
  by_cases hi : i < C.m
  · refine C.sum_saturated_le i Finset.univ (fun _ _ ω' _ => Finset.mem_univ ω') _ _ ?_
    intro ω₁ _
    have hc := C.hcost ⟨i, hi⟩ ω₁ E (fun _ => false)
    simp only [bailCost_never] at hc
    have hL : ∑ ω' ∈ C.atom i ω₁, C.P ω' * sizeN C i ω'
        = C.size ω₁ ⟨i, hi⟩ * ∑ ω' ∈ C.atom i ω₁, C.P ω' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω' hm' => ?_
      unfold sizeN
      rw [dif_pos hi, C.hsmeas ⟨i, hi⟩ ω' ω₁ (C.mem_atom.mp hm')]
      ring
    have hR : ∑ ω' ∈ C.atom i ω₁, C.P ω' * E.costOn (pre C i ω') (chunkN C i ω')
        = ∑ ω' ∈ C.atom i ω₁, C.P ω' *
            E.costOn (((List.ofFn (C.chunk ω')).take i).flatten) (C.chunk ω' ⟨i, hi⟩) := by
      refine Finset.sum_congr rfl fun ω' _ => ?_
      unfold pre chunkN
      rw [dif_pos hi]
    rw [hL, hR]
    exact hc
  · have hz : ∀ ω : C.Ω, sizeN C i ω = 0 := fun ω => by unfold sizeN; rw [dif_neg hi]
    have hz2 : ∀ ω : C.Ω, E.costOn (pre C i ω) (chunkN C i ω) = 0 := by
      intro ω
      unfold chunkN EvaderAlgorithm.costOn
      rw [dif_neg hi]
      simp
    simp [hz, hz2]

/-- Telescoping: the per-chunk costs of an evader add up to its cost on the whole
request sequence. -/
theorem sum_costOn_eq_cost (E : EvaderAlgorithm X) (ω : C.Ω) :
    ∑ i ∈ Finset.range C.m, E.costOn (pre C i ω) (chunkN C i ω) = E.cost (C.seq ω) := by
  have hstep : ∀ i, E.costOn (pre C i ω) (chunkN C i ω)
      = E.cost (pre C (i + 1) ω) - E.cost (pre C i ω) := by
    intro i
    unfold EvaderAlgorithm.costOn
    rw [pre_succ]
  rw [Finset.sum_congr rfl (fun i _ => hstep i),
    Finset.sum_range_sub (fun i => E.cost (pre C i ω)) C.m,
    pre_m, pre_zero, cost_nil, sub_zero]

/-- **The expected total size is bounded by the expected cost of any evader.** -/
theorem expTotal_le_evader_cost (E : EvaderAlgorithm X) :
    ∑ ω, C.P ω * ∑ i, C.size ω i ≤ ∑ ω, C.P ω * E.cost (C.seq ω) := by
  classical
  have h1 : ∀ ω : C.Ω, ∑ i ∈ Finset.range C.m, C.P ω * sizeN C i ω
      = C.P ω * ∑ i, C.size ω i := by
    intro ω
    rw [← Fin.sum_univ_eq_sum_range (fun i => C.P ω * sizeN C i ω) C.m, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by unfold sizeN; rw [dif_pos i.2]
  have h2 : ∀ ω : C.Ω, ∑ i ∈ Finset.range C.m, C.P ω * E.costOn (pre C i ω) (chunkN C i ω)
      = C.P ω * E.cost (C.seq ω) := by
    intro ω
    rw [← Finset.mul_sum, sum_costOn_eq_cost]
  calc ∑ ω, C.P ω * ∑ i, C.size ω i
      = ∑ ω, ∑ i ∈ Finset.range C.m, C.P ω * sizeN C i ω :=
        Finset.sum_congr rfl fun ω _ => (h1 ω).symm
    _ = ∑ i ∈ Finset.range C.m, ∑ ω, C.P ω * sizeN C i ω := Finset.sum_comm
    _ ≤ ∑ i ∈ Finset.range C.m, ∑ ω, C.P ω * E.costOn (pre C i ω) (chunkN C i ω) :=
        Finset.sum_le_sum fun i _ => sum_sizeN_le_sum_costOn C E i
    _ = ∑ ω, ∑ i ∈ Finset.range C.m, C.P ω * E.costOn (pre C i ω) (chunkN C i ω) :=
        Finset.sum_comm
    _ = ∑ ω, C.P ω * E.cost (C.seq ω) := Finset.sum_congr rfl fun ω _ => h2 ω

end EvaderBound


/-!
# On two points the expected total size of a chunk system is at most `dist s t`

Combining the general bound "expected total size ≤ expected cost of any evader" with the
one-way lazy evader on a two-point space.
-/



namespace TwoPointDist

variable {X : Type*} [MetricSpace X] {s t : X}

open Classical in
/-- The **one-way lazy evader**: it stays at `s` as long as every request so far contains
`s`, and moves to `t` for good afterwards (falling back to `s` if the last request does not
contain `t`, which cannot happen along a two-point request sequence with a cheap offline
solution). -/
noncomputable def oneWayPos (s t : X) (l : List (Set X)) : X :=
  if (∀ S ∈ l, s ∈ S) then s
  else
    match l.getLast? with
    | none => s
    | some S => if t ∈ S then t else s

theorem oneWayPos_of_all (s t : X) {l : List (Set X)} (h : ∀ S ∈ l, s ∈ S) :
    oneWayPos s t l = s := by
  unfold oneWayPos
  rw [if_pos h]

theorem oneWayPos_of_not_all (s t : X) {l : List (Set X)} {S : Set X}
    (h : ¬ ∀ S ∈ l, s ∈ S) (hlast : l.getLast? = some S) (hS : t ∈ S) :
    oneWayPos s t l = t := by
  unfold oneWayPos
  rw [if_neg h, hlast]
  exact if_pos hS

theorem oneWay_serves (htwo : ∀ x : X, x = s ∨ x = t) (l : List (Set X)) (S : Set X)
    (hS : S.Nonempty) : oneWayPos s t (l ++ [S]) ∈ S := by
  classical
  unfold oneWayPos
  by_cases hall : ∀ T ∈ l ++ [S], s ∈ T
  · rw [if_pos hall]
    exact hall S (by simp)
  · rw [if_neg hall]
    have hlast : (l ++ [S]).getLast? = some S := by simp
    rw [hlast]
    show (if t ∈ S then t else s) ∈ S
    by_cases hts : t ∈ S
    · rw [if_pos hts]; exact hts
    · rw [if_neg hts]
      obtain ⟨x, hx⟩ := hS
      rcases htwo x with rfl | rfl
      · exact hx
      · exact absurd hx hts

/-- The one-way lazy evader as an `EvaderAlgorithm`. -/
noncomputable def oneWay (htwo : ∀ x : X, x = s ∨ x = t) : EvaderAlgorithm X where
  pos := oneWayPos s t
  serves := oneWay_serves htwo

section Cost

/-- Along a request sequence with a cheap offline solution, once some request has avoided
`s` the one-way evader sits at `t`. -/
theorem oneWay_pos_eq_t (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    (σ : List (Set X)) (hne : ∀ S ∈ σ, S.Nonempty)
    (hopt : evaderOfflineCost s σ ≤ dist s t) (n : ℕ)
    (hall : ¬ ∀ S ∈ σ.take n, s ∈ S) :
    oneWayPos s t (σ.take n) = t := by
  classical
  have hlen : (σ.take n).length ≤ σ.length := by simp
  obtain ⟨a, ha, haS⟩ : ∃ a, ∃ h : a < (σ.take n).length, s ∉ (σ.take n)[a] := by
    by_contra hcon
    push_neg at hcon
    refine hall fun S hS => ?_
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hS
    exact hcon a ha
  have hk : (σ.take n).length - 1 < (σ.take n).length := by omega
  have hL : (σ.take n).getLast? = some ((σ.take n)[(σ.take n).length - 1]) := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hk]
  refine oneWayPos_of_not_all s t hall hL ?_
  have hkσ : (σ.take n).length - 1 < σ.length := lt_of_lt_of_le hk hlen
  have haσ : a < σ.length := lt_of_lt_of_le ha hlen
  have he1 : (σ.take n)[a] = σ[a]'haσ := by simp
  have he2 : (σ.take n)[(σ.take n).length - 1] = σ[(σ.take n).length - 1]'hkσ := by simp
  rcases (by omega : a < (σ.take n).length - 1 ∨ a = (σ.take n).length - 1) with hlt | heq
  · rw [he2]
    by_contra hcon
    exact TwoPointRigidity.no_return_idx hst htwo σ hne hopt hlt hkσ
      (by rw [← he1]; exact haS) hcon
  · have hmem : (σ.take n)[a] ∈ σ := List.mem_of_mem_take (List.getElem_mem ha)
    obtain ⟨x, hx⟩ := hne _ hmem
    have hta : t ∈ (σ.take n)[a] := by
      rcases htwo x with rfl | rfl
      · exact absurd hx haS
      · exact hx
    have hidx : (σ.take n)[(σ.take n).length - 1] = (σ.take n)[a] := by
      congr 1
      omega
    rw [hidx]
    exact hta

/-- The one-way lazy evader pays at most one crossing on any request sequence with a cheap
offline solution. -/
theorem oneWay_cost_le (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    (σ : List (Set X)) (hne : ∀ S ∈ σ, S.Nonempty)
    (hopt : evaderOfflineCost s σ ≤ dist s t) :
    (oneWay htwo).cost σ ≤ dist s t := by
  classical
  have hmono : ∀ (n : ℕ) (S : Set X), S ∈ σ.take n → S ∈ σ.take (n + 1) := by
    intro n S hS
    have h1 : (σ.take (n + 1)).take n = σ.take n := by
      rw [List.take_take]
      congr 1
      omega
    exact List.mem_of_mem_take (h1 ▸ hS)
  have hval : ∀ n : ℕ, oneWayPos s t (σ.take n) = s ∨ oneWayPos s t (σ.take n) = t := by
    intro n
    by_cases hall : ∀ S ∈ σ.take n, s ∈ S
    · exact Or.inl (oneWayPos_of_all s t hall)
    · exact Or.inr (oneWay_pos_eq_t hst htwo σ hne hopt n hall)
  have hstep : ∀ n : ℕ, oneWayPos s t (σ.take n) = t → oneWayPos s t (σ.take (n + 1)) = t := by
    intro n hn
    by_cases hall : ∀ S ∈ σ.take (n + 1), s ∈ S
    · exfalso
      have h1 : ∀ S ∈ σ.take n, s ∈ S := fun S hS => hall S (hmono n S hS)
      rw [oneWayPos_of_all s t h1] at hn
      exact hst hn
    · exact oneWay_pos_eq_t hst htwo σ hne hopt (n + 1) hall
  have key : ∀ n : ℕ, ∑ j ∈ Finset.range n,
      dist ((oneWay htwo).pos (σ.take j)) ((oneWay htwo).pos (σ.take (j + 1)))
      = dist s (oneWayPos s t (σ.take n)) := by
    intro n
    induction n with
    | zero =>
      have h0 : oneWayPos s t (σ.take 0) = s := oneWayPos_of_all s t (by simp)
      rw [h0]
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      show dist s (oneWayPos s t (σ.take n))
          + dist (oneWayPos s t (σ.take n)) (oneWayPos s t (σ.take (n + 1)))
        = dist s (oneWayPos s t (σ.take (n + 1)))
      rcases hval n with hn | hn
      · rcases hval (n + 1) with hn1 | hn1 <;> rw [hn, hn1] <;> simp
      · have hn1 : oneWayPos s t (σ.take (n + 1)) = t := hstep n hn
        rw [hn, hn1]
        simp
  unfold EvaderAlgorithm.cost
  rw [key σ.length]
  rcases hval σ.length with h | h
  · rw [h]
    simp [dist_nonneg]
  · rw [h]

end Cost

/-- **Two-point mass bound.** On a metric space with exactly two points the expected total
size of any chunk system with online escapes is at most `dist s t`; no size floor, size
ceiling or martingale hypothesis is needed. -/
theorem twoPoint_expTotal_le_dist {cLo cHi total price : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mL)
    (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t) :
    ∑ ω, C.P ω * ∑ i, C.size ω i ≤ dist s t := by
  classical
  have h1 := EvaderBound.expTotal_le_evader_cost C (oneWay htwo)
  have h2 : ∀ ω : C.Ω, (oneWay htwo).cost (C.seq ω) ≤ dist s t := by
    intro ω
    refine oneWay_cost_le hst htwo (C.seq ω) ?_ (C.hopt ω)
    intro S hS
    rw [ChunkSystemB.seq, List.mem_flatten] at hS
    obtain ⟨l, hl, hSl⟩ := hS
    rw [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact C.hne ω i S hSl
  have h3 : ∑ ω, C.P ω * (oneWay htwo).cost (C.seq ω) ≤ ∑ ω, C.P ω * dist s t :=
    Finset.sum_le_sum fun ω _ =>
      mul_le_mul_of_nonneg_left (h2 ω) (le_of_lt (C.hP ω))
  have h4 : ∑ ω, C.P ω * dist s t = dist s t := by
    rw [← Finset.sum_mul, C.hPsum, one_mul]
  linarith

/-- Consequently the declared total of a chunk system on two points is at most
`dist s t`. -/
theorem total_le_dist {cLo cHi total price : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mL)
    (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t) : total ≤ dist s t :=
  le_trans C.htotal (twoPoint_expTotal_le_dist C hst htwo)

end TwoPointDist


theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cLo cHi total price mL)
    (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t) : total ≤ dist s t :=
  TwoPointDist.total_le_dist C hst htwo
