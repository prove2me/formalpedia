-- Prove2me | solution 1 for KServer.chunk_pad4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-02T00:16:33.382465+00:00
-- url     : https://prove2.me/submissions/0a4995fc-9e39-4939-b140-b30e379b707b

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_adjust
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_prophecy
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_absorb
import Definitions.Def_KServer_race_opt

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open KServer KServer.Race

namespace PadSys

open Classical in
/-- The boundary position of the offset shadow: on a history of exact
length `n` whose last request already contains the projected evader
position, the shadow sits at the projected position. -/
theorem shadowFrom_pos_boundary {X Y : Type*} [MetricSpace X]
    [MetricSpace Y] (n : ℕ) (π : Y → X) (G : Set X → Set Y)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) {h : List (Set X)}
    (hh : h.length = n)
    (hmem : ∀ S : Set X, h.getLast? = some S → π (E.pos h₀) ∈ S) :
    (shadowFrom n π G hG hGne E h₀).pos h = π (E.pos h₀) := by
  have hlen : h.length ≤ n := le_of_eq hh
  have hdrop : h.drop n = [] := by
    rw [← hh]
    exact List.drop_length
  have hmap : reqMap G ([] : List (Set X)) = [] := by
    unfold reqMap
    rw [List.map_nil]
  unfold shadowFrom
  simp only [hlen, if_true]
  cases hgl : h.getLast? with
  | none =>
    simp only [hgl]
    rw [hdrop, hmap, List.append_nil]
  | some Sl =>
    simp only [hgl]
    rw [hdrop, hmap, List.append_nil]
    rw [if_pos (hmem Sl hgl)]

variable {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ} {mL : ℕ}

variable (C : ChunkSystemB X s t 0 cB T pe mL)

/-- The padded chunk: empty chunks are replaced by a repeat of the last
consumed request (the entry `{s}` before anything is consumed). -/
noncomputable def pchunk (ω : C.Ω) (i : Fin C.m) : List (Set X) :=
  if C.chunk ω i = [] then [lastXset C ω (i : ℕ)] else C.chunk ω i

theorem pchunk_ne (ω : C.Ω) (i : Fin C.m) : pchunk C ω i ≠ [] := by
  unfold pchunk
  by_cases h : C.chunk ω i = []
  · rw [if_pos h]
    simp
  · rw [if_neg h]
    exact h

theorem lastXset_ne (ω : C.Ω) (idx : ℕ) : (lastXset C ω idx).Nonempty := by
  unfold lastXset
  cases hgl : (((List.ofFn (C.chunk ω)).take idx).flatten).getLast? with
  | none =>
    rw [Option.getD_none]
    exact ⟨s, rfl⟩
  | some S =>
    rw [Option.getD_some]
    refine mem_take_flatten_ne C ω idx ?_
    exact List.mem_of_getLast? hgl

/-- The padded prefix. -/
noncomputable def ppre (ω : C.Ω) (i : ℕ) : List (Set X) :=
  ((List.ofFn (pchunk C ω)).take i).flatten

theorem take_succ_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) {i : ℕ}
    (hi : i < n) :
    (List.ofFn f).take (i + 1) = (List.ofFn f).take i ++ [f ⟨i, hi⟩] := by
  rw [List.take_succ]
  congr 1
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi)]
  rw [List.getElem_ofFn]
  rfl

/-- The padded and original prefixes share the same running last request. -/
theorem ppre_last (ω : C.Ω) {i : ℕ} (hi : i ≤ C.m) :
    (ppre C ω i).getLast?.getD ({s} : Set X) = lastXset C ω i := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rfl
  · have hi' : i - 1 < C.m := by omega
    have hii : i = (i - 1) + 1 := by omega
    rw [hii]
    have hL : ppre C ω ((i - 1) + 1)
        = ppre C ω (i - 1) ++ pchunk C ω ⟨i - 1, hi'⟩ := by
      unfold ppre
      rw [take_succ_ofFn (pchunk C ω) hi', List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil]
    have hR : ((List.ofFn (C.chunk ω)).take ((i - 1) + 1)).flatten
        = ((List.ofFn (C.chunk ω)).take (i - 1)).flatten
          ++ C.chunk ω ⟨i - 1, hi'⟩ := by
      rw [take_succ_ofFn (C.chunk ω) hi', List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hL]
    unfold lastXset
    rw [hR]
    by_cases he : C.chunk ω ⟨i - 1, hi'⟩ = []
    · unfold pchunk
      rw [if_pos he, he, List.append_nil, List.getLast?_concat,
        Option.getD_some]
      rfl
    · unfold pchunk
      rw [if_neg he, List.getLast?_append_of_ne_nil _ he,
        List.getLast?_append_of_ne_nil _ he]

theorem ppre_congr (ω ω' : C.Ω) {i N : ℕ} (hi : i ≤ N)
    (h : C.hist N ω = C.hist N ω') : ppre C ω i = ppre C ω' i := by
  unfold ppre
  congr 1
  apply List.ext_getElem
  · rw [List.length_take, List.length_take, List.length_ofFn,
      List.length_ofFn]
  · intro r h1 h2
    rw [List.getElem_take, List.getElem_take, List.getElem_ofFn,
      List.getElem_ofFn]
    have hr : r < C.m := by
      rw [List.length_take, List.length_ofFn] at h1
      omega
    unfold pchunk
    have hch : C.chunk ω ⟨r, by omega⟩ = C.chunk ω' ⟨r, by omega⟩ :=
      C.hadapt _ _ _ (C.href (r + 1) N (by
        rw [List.length_take, List.length_ofFn] at h1
        omega) _ _ h)
    rw [hch, lastXset_congr C (by
      rw [List.length_take, List.length_ofFn] at h1
      omega : r ≤ N) h]

/-- Bail cost of the empty chunk is zero. -/
theorem bailCost_nil (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h : List (Set X)) (p : ℝ) : E.bailCost bail h [] p = 0 := by
  unfold EvaderAlgorithm.bailCost
  have h1 : bailTime bail h [] = none := by
    unfold bailTime
    rfl
  rw [h1]
  unfold EvaderAlgorithm.costOn
  rw [List.append_nil, sub_self]

theorem chunk_pad4 {V D B flo PE : ℝ} {n₀ : ℕ} (hpe0 : 0 ≤ pe)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hst : C.SturdyL1 n₀ D)
    (hbad : ∀ n ≤ n₀, ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B)
    (hPPE : C.ProphecyBound PE) :
    ∃ C' : ChunkSystemB X s t 0 cB T pe mL,
      C'.m = C.m ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.SturdyL1 n₀ D ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B) ∧
      C'.ProphecyBound PE := by
  refine ⟨{
    Ω := C.Ω
    instFin := C.instFin
    instDec := C.instDec
    P := C.P
    m := C.m
    hist := C.hist
    chunk := pchunk C
    size := C.size
    hP := C.hP
    hPsum := C.hPsum
    hm := C.hm
    hm0 := C.hm0
    href := C.href
    hadapt := ?_
    hsmeas := C.hsmeas
    hne := ?_
    hlast := ?_
    hopt := ?_
    hsize := C.hsize
    hcost := ?_
    htotal := C.htotal }, rfl, h0triv, hVar, ?_, hst, hbad, hPPE⟩
  · -- hadapt
    intro i ω ω' hh
    unfold pchunk
    have hch : C.chunk ω i = C.chunk ω' i := C.hadapt i ω ω' hh
    rw [hch, lastXset_congr C (Nat.le_succ _) hh]
  · -- hne
    intro ω i S hS
    unfold pchunk at hS
    by_cases he : C.chunk ω i = []
    · rw [if_pos he, List.mem_singleton] at hS
      rw [hS]
      exact lastXset_ne C ω _
    · rw [if_neg he] at hS
      exact C.hne ω i S hS
  · -- hlast
    intro ω
    have hfull : (List.ofFn (pchunk C ω)).take C.m
        = List.ofFn (pchunk C ω) := by
      apply List.take_of_length_le
      rw [List.length_ofFn]
    have hinv := ppre_last C ω (le_refl C.m)
    unfold ppre at hinv
    rw [hfull] at hinv
    have hlx : lastXset C ω C.m = {t} := by
      unfold lastXset
      have hfull2 : (List.ofFn (C.chunk ω)).take C.m
          = List.ofFn (C.chunk ω) := by
        apply List.take_of_length_le
        rw [List.length_ofFn]
      rw [hfull2, C.hlast ω, Option.getD_some]
    rw [hlx] at hinv
    have hne1 : (List.ofFn (pchunk C ω)).flatten ≠ [] := by
      intro hcon
      rw [List.flatten_eq_nil_iff] at hcon
      refine pchunk_ne C ω ⟨0, C.hm0⟩ (hcon _ ?_)
      rw [List.mem_ofFn]
      exact ⟨⟨0, C.hm0⟩, rfl⟩
    cases hgl : ((List.ofFn (pchunk C ω)).flatten).getLast? with
    | none =>
      exact absurd (List.getLast?_eq_none_iff.mp hgl) hne1
    | some S =>
      rw [hgl, Option.getD_some] at hinv
      rw [hinv]
  · -- hopt
    intro ω
    refine le_of_forall_pos_le_add ?_
    intro δ hδ
    obtain ⟨P, hP, hPc⟩ := offline_exists_lt s (C.seq ω)
      (lt_of_le_of_lt (C.hopt ω) (by linarith : dist s t < dist s t + δ))
    set F : ℕ → List (Set X) := fun rr =>
      if h : rr < C.m then pchunk C ω ⟨rr, h⟩ else [] with hFdef
    have hcert : ∀ r, 0 ≤ r → r < 0 + C.m →
        ((preLen C ω) (r + 1) = (preLen C ω) r + (F r).length ∧
          ∀ n : ℕ, ∀ hn : n < (F r).length,
            ((F r)[n]'hn).Nonempty → P ((preLen C ω) r + n + 1) ∈ (F r)[n]'hn)
        ∨ ((preLen C ω) (r + 1) = (preLen C ω) r ∧
          ∀ S ∈ F r, S.Nonempty → P ((preLen C ω) r) ∈ S) := by
      intro r hr0 hrm
      have hr : r < C.m := by omega
      have hFr : F r = pchunk C ω ⟨r, hr⟩ := by
        rw [hFdef]
        exact dif_pos hr
      by_cases he : C.chunk ω ⟨r, hr⟩ = []
      · right
        constructor
        · rw [preLen_succ C ω hr, chunkN_lt C ω hr, he]
          rfl
        · intro S hS hSne
          rw [hFr] at hS
          unfold pchunk at hS
          rw [if_pos he, List.mem_singleton] at hS
          rw [hS]
          exact serves_last_pos C ω hP r
      · left
        have hpc : F r = chunkN C ω r := by
          rw [hFr, chunkN_lt C ω hr]
          unfold pchunk
          rw [if_neg he]
        constructor
        · rw [preLen_succ C ω hr, hpc]
        · intro n hn hne
          have hn2 : n < (chunkN C ω r).length := by
            rw [← hpc]
            exact hn
          have hq : (F r)[n]? = (chunkN C ω r)[n]? := by rw [hpc]
          rw [List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hn2] at hq
          have hgeq := Option.some_injective _ hq
          rw [hgeq] at hne ⊢
          exact serves_chunk_pos C ω hP hr hn2 hne
    have habs := absorb_build P F (preLen C ω) C.m 0 hcert
    have hofn : (fun i : Fin C.m => F (0 + (i : ℕ))) = pchunk C ω := by
      funext i
      rw [Nat.zero_add, hFdef]
      show (if h : (i : ℕ) < C.m then pchunk C ω ⟨(i : ℕ), h⟩ else [])
        = pchunk C ω i
      rw [dif_pos i.isLt]
    rw [hofn] at habs
    have hbound := habs.offline_le
    rw [Nat.zero_add, preLen_zero, hP.1] at hbound
    refine le_trans hbound ?_
    rw [preLen_m, ← Finset.range_eq_Ico]
    linarith
  · -- hcost
    intro i ω₀ E bail
    set hOrig := ((List.ofFn (C.chunk ω₀)).take (i : ℕ)).flatten with hOdef
    set hPad := ppre C ω₀ (i : ℕ) with hPdef
    set G0 : Set X → Set X := fun S => S with hG0def
    have hG0 : ∀ S : Set X, ∀ y ∈ G0 S, (fun x : X => x) y ∈ S :=
      fun S y hy => hy
    have hG0ne : ∀ S : Set X, S.Nonempty → (G0 S).Nonempty := fun S h => h
    set E' := shadowFrom hOrig.length (fun x => x) G0 hG0 hG0ne E hPad
      with hE'def
    -- start alignment
    have hstart : E'.pos hOrig = (fun x : X => x) (E.pos hPad) := by
      rw [hE'def]
      refine shadowFrom_pos_boundary hOrig.length (fun x => x) G0 hG0
        hG0ne E hPad rfl ?_
      intro Sl hgl
      show E.pos hPad ∈ Sl
      have hOne : hOrig ≠ [] := by
        intro hcon
        rw [hcon] at hgl
        simp at hgl
      have hSlne : Sl.Nonempty := by
        refine mem_take_flatten_ne C ω₀ (i : ℕ) ?_
        exact List.mem_of_getLast? hgl
      have hSl : (hPad.getLast?).getD ({s} : Set X) = Sl := by
        have h1 := ppre_last C ω₀ (le_of_lt i.isLt)
        rw [← hPdef] at h1
        unfold lastXset at h1
        rw [← hOdef, hgl, Option.getD_some] at h1
        exact h1
      have hPne : hPad ≠ [] := by
        intro hcon
        have hOlen : 0 < hOrig.length := List.length_pos_of_ne_nil hOne
        have hi0 : 0 < (i : ℕ) := by
          by_contra hi0
          have h6 : (i : ℕ) = 0 := by omega
          rw [hOdef, h6] at hOlen
          simp at hOlen
        have hlen0 : 0 < ((List.ofFn (pchunk C ω₀)).take (i : ℕ)).length := by
          rw [List.length_take, List.length_ofFn]
          have := C.hm0
          omega
        have h7 : ((List.ofFn (pchunk C ω₀)).take (i : ℕ))[0]'hlen0
            = pchunk C ω₀ ⟨0, C.hm0⟩ := by
          rw [List.getElem_take, List.getElem_ofFn]
        have hmem3 : pchunk C ω₀ ⟨0, C.hm0⟩
            ∈ (List.ofFn (pchunk C ω₀)).take (i : ℕ) := by
          rw [← h7]
          exact List.getElem_mem _
        have hcon2 : ((List.ofFn (pchunk C ω₀)).take (i : ℕ)).flatten
            = [] := hcon
        rw [List.flatten_eq_nil_iff] at hcon2
        exact pchunk_ne C ω₀ ⟨0, C.hm0⟩ (hcon2 _ hmem3)
      have hglP : hPad.getLast? = some Sl := by
        cases hglP0 : hPad.getLast? with
        | none =>
          exact absurd (List.getLast?_eq_none_iff.mp hglP0) hPne
        | some Z =>
          rw [hglP0, Option.getD_some] at hSl
          rw [hSl]
      have h8 : hPad.getLast hPne = Sl := by
        have h9 := List.getLast?_eq_getLast (l := hPad) hPne
        rw [h9] at hglP
        exact Option.some_injective _ hglP
      have hdecomp : hPad.dropLast ++ [Sl] = hPad := by
        rw [← h8]
        exact List.dropLast_append_getLast hPne
      rw [← hdecomp]
      exact E.serves _ _ hSlne
    have hmain := C.hcost i ω₀ E'
      (fun l => bail (hPad ++ reqMap G0 (l.drop hOrig.length)))
    refine le_trans hmain ?_
    refine Finset.sum_le_sum ?_
    intro ω hω
    rw [Finset.mem_filter] at hω
    have hatom : C.hist (i : ℕ) ω = C.hist (i : ℕ) ω₀ := hω.2
    have hpre1 : ((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten = hOrig := by
      rw [hOdef]
      congr 1
      exact take_congr C (le_refl (i : ℕ)) hatom
    have hpre2 : ((List.ofFn (pchunk C ω)).take (i : ℕ)).flatten = hPad := by
      rw [hPdef]
      exact ppre_congr C ω ω₀ (le_refl (i : ℕ)) hatom
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (C.hP ω))
    rw [hpre1, hpre2]
    by_cases hce : C.chunk ω i = []
    · rw [hce, bailCost_nil]
      exact E.bailCost_nonneg _ _ _ hpe0
    · have hred := shadowFrom_bailCost_le hOrig.length (fun x => x) G0
        (fun y z => le_of_eq rfl) hG0 hG0ne E bail hPad hOrig
        (C.chunk ω i) (le_refl pe) rfl hstart
      have hmap : reqMap G0 (C.chunk ω i) = C.chunk ω i := by
        unfold reqMap
        exact List.map_id' _
      rw [hmap] at hred
      have hpc : pchunk C ω i = C.chunk ω i := by
        unfold pchunk
        rw [if_neg hce]
      rw [hpc]
      exact hred
  · -- the nonempty-chunk conjunct
    intro ω i
    exact pchunk_ne C ω i

end PadSys

namespace KServer

/-- **Chunk padding**: every chunk system with online escapes can be
modified so that no chunk is the empty list, keeping the sample space,
measure, filtration, sizes, and all bounds: empty chunks are replaced by
a single repeat of the last consumed request. -/
theorem chunk_pad4 {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ}
    {mL : ℕ} (C : ChunkSystemB X s t 0 cB T pe mL)
    {V D B flo PE : ℝ} {n₀ : ℕ}
    (hpe0 : 0 ≤ pe)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hst : C.SturdyL1 n₀ D)
    (hbad : ∀ n ≤ n₀, ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B)
    (hPPE : C.ProphecyBound PE) :
    ∃ C' : ChunkSystemB X s t 0 cB T pe mL,
      C'.m = C.m ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.SturdyL1 n₀ D ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B) ∧
      C'.ProphecyBound PE :=
  PadSys.chunk_pad4 C hpe0 h0triv hVar hst hbad hPPE

end KServer

theorem solution {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ}
    {mL : ℕ} (C : KServer.ChunkSystemB X s t 0 cB T pe mL)
    {V D B flo PE : ℝ} {n₀ : ℕ}
    (hpe0 : 0 ≤ pe)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hst : C.SturdyL1 n₀ D)
    (hbad : ∀ n ≤ n₀, ∑ ω, C.P ω * (∑ i ∈ Finset.range n,
        if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B)
    (hPPE : C.ProphecyBound PE) :
    ∃ C' : KServer.ChunkSystemB X s t 0 cB T pe mL,
      C'.m = C.m ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.SturdyL1 n₀ D ∧
      (∀ n ≤ n₀, ∑ ω, C'.P ω * (∑ i ∈ Finset.range n,
          if C'.sizeN i ω < flo then (1 : ℝ) else 0) ≤ B) ∧
      C'.ProphecyBound PE :=
  KServer.chunk_pad4 C hpe0 h0triv hVar hst hbad hPPE
