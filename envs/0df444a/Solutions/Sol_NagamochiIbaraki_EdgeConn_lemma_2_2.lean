-- Prove2me | solution 1 for NagamochiIbaraki.EdgeConn.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:28:42.918517+00:00
-- url     : https://prove2.me/submissions/3f93e143-abc1-4a16-8164-016074788d2a

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

set_option autoImplicit false

namespace NagamochiIbaraki.EdgeConn.L22P

open NagamochiIbaraki.EdgeConn

def Inv {V E : Type*} (ends : E → Sym2 V) (s : State V E) : Prop :=
  (∀ v ∈ s.done, ∀ e, v ∈ ends e → s.idx e ≠ 0) ∧
  (∀ x, s.cur = some x → ∀ y, y ∉ s.done → s.r y ≤ s.r x) ∧
  (∀ v i, 1 ≤ i → ((∃ e, v ∈ ends e ∧ s.idx e = i) ↔ i ≤ s.r v))

theorem inv_init {V E : Type*} (ends : E → Sym2 V) :
    Inv ends (init : State V E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv; simp [init] at hv
  · intro x hx; simp [init] at hx
  · intro v i hi
    constructor
    · rintro ⟨e, _, he⟩
      change 0 = i at he
      omega
    · intro h
      change i ≤ 0 at h
      omega

theorem scan_iff {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) (idx : E → ℕ) (e : E)
    (he0 : idx e = 0) (a : ℕ) (v : V) (i : ℕ) (hi : 1 ≤ i) :
    (∃ f, v ∈ ends f ∧ Function.update idx e a f = i) ↔
      ((v ∈ ends e ∧ a = i) ∨ ∃ f, v ∈ ends f ∧ idx f = i) := by
  constructor
  · rintro ⟨f, hf, hfi⟩
    by_cases hfe : f = e
    · subst hfe
      left; rw [Function.update_self] at hfi; exact ⟨hf, hfi⟩
    · right; rw [Function.update_of_ne hfe] at hfi; exact ⟨f, hf, hfi⟩
  · rintro (⟨hv, ha⟩ | ⟨f, hf, hfi⟩)
    · exact ⟨e, hv, by rw [Function.update_self]; exact ha⟩
    · have hfe : f ≠ e := by
        intro h; subst h; omega
      exact ⟨f, hf, by rw [Function.update_of_ne hfe]; exact hfi⟩

theorem inv_step {V E : Type*} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (s t : State V E)
    (hs : Inv ends s) (hst : Step ends s t) : Inv ends t := by
  obtain ⟨hB, hM, hC⟩ := hs
  rcases hst with ⟨x, hcur, hxd, hmax, ht⟩ | ⟨x, y, e, hcur, he0, hend, ht⟩ |
      ⟨x, hcur, hall, ht⟩
  · have ht_idx : t.idx = s.idx := by rw [ht]
    have ht_r : t.r = s.r := by rw [ht]
    have ht_done : t.done = s.done := by rw [ht]
    have ht_cur : t.cur = some x := by rw [ht]
    refine ⟨?_, ?_, ?_⟩
    · intro v hv f hf; rw [ht_idx]; rw [ht_done] at hv; exact hB v hv f hf
    · intro z hz w hw
      rw [ht_cur] at hz
      cases hz
      rw [ht_r]; rw [ht_done] at hw
      exact hmax w hw
    · intro v i hi; rw [ht_idx, ht_r]; exact hC v i hi
  · have ht_idx : t.idx = Function.update s.idx e (s.r y + 1) := by rw [ht]
    have ht_r : t.r = Function.update
        (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
        y (s.r y + 1) := by rw [ht]
    have ht_done : t.done = s.done := by rw [ht]
    have ht_cur : t.cur = s.cur := by rw [ht]
    have hxy : x ≠ y := by
      intro h; apply hloop e; rw [hend, h]; exact Sym2.mk_isDiag_iff.mpr rfl
    have hyd : y ∉ s.done := fun hy => hB y hy e (by rw [hend]; exact Sym2.mem_mk_right x y) he0
    have hyx : s.r y ≤ s.r x := hM x hcur y hyd
    have hrx : t.r x = (if s.r x = s.r y then s.r x + 1 else s.r x) := by
      rw [ht_r, Function.update_of_ne hxy, Function.update_self]
    have hry : t.r y = s.r y + 1 := by
      rw [ht_r, Function.update_self]
    have hrw : ∀ w, w ≠ x → w ≠ y → t.r w = s.r w := by
      intro w hwx hwy
      rw [ht_r, Function.update_of_ne hwy, Function.update_of_ne hwx]
    refine ⟨?_, ?_, ?_⟩
    · intro v hv f hf
      rw [ht_done] at hv
      rw [ht_idx, Function.update_apply]
      split_ifs
      · omega
      · exact hB v hv f hf
    · intro z hz w hw
      rw [ht_cur, hcur] at hz
      cases hz
      rw [ht_done] at hw
      rw [hrx]
      by_cases hwy : w = y
      · subst hwy; rw [hry]; split_ifs <;> omega
      · by_cases hwx : w = x
        · subst hwx; rw [hrx]
        · rw [hrw w hwx hwy]
          have := hM x hcur w hw
          split_ifs <;> omega
    · intro v i hi
      rw [ht_idx, scan_iff ends s.idx e he0 _ v i hi, hC v i hi]
      by_cases hvy : v = y
      · subst hvy
        rw [hry]
        have : v ∈ ends e := by rw [hend]; exact Sym2.mem_mk_right x v
        constructor
        · rintro (⟨_, h⟩ | h) <;> omega
        · intro h
          rcases Nat.lt_or_ge i (s.r v + 1) with h' | h'
          · right; omega
          · left; exact ⟨this, by omega⟩
      · by_cases hvx : v = x
        · subst hvx
          rw [hrx]
          have : v ∈ ends e := by rw [hend]; exact Sym2.mem_mk_left v y
          constructor
          · rintro (⟨_, h⟩ | h) <;> split_ifs <;> omega
          · intro h
            rcases Nat.lt_or_ge i (s.r v + 1) with h' | h'
            · right; omega
            · left; refine ⟨this, ?_⟩; split_ifs at h <;> omega
        · rw [hrw v hvx hvy]
          have : v ∉ ends e := by
            rw [hend]; intro hm
            rcases Sym2.mem_iff.mp hm with h | h
            · exact hvx h
            · exact hvy h
          constructor
          · rintro (⟨h, _⟩ | h)
            · exact absurd h this
            · exact h
          · intro h; right; exact h
  · have ht_idx : t.idx = s.idx := by rw [ht]
    have ht_r : t.r = s.r := by rw [ht]
    have ht_done : t.done = insert x s.done := by rw [ht]
    have ht_cur : t.cur = none := by rw [ht]
    refine ⟨?_, ?_, ?_⟩
    · intro v hv f hf
      rw [ht_idx]
      rw [ht_done, Finset.mem_insert] at hv
      rcases hv with hv | hv
      · rw [hv] at hf; exact hall f hf
      · exact hB v hv f hf
    · intro z hz; rw [ht_cur] at hz; cases hz
    · intro v i hi; rw [ht_idx, ht_r]; exact hC v i hi

theorem inv_run {V E : Type*} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (σ : ℕ → State V E) (K : ℕ)
    (hrun : IsRun ends σ K) : ∀ k, k ≤ K → Inv ends (σ k) := by
  intro k
  induction k with
  | zero => intro _; rw [hrun.1]; exact inv_init ends
  | succ n ih =>
    intro hn
    exact inv_step ends hloop _ _ (ih (by omega)) (hrun.2 n (by omega))

end NagamochiIbaraki.EdgeConn.L22P

open NagamochiIbaraki.EdgeConn in
theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ (v : V) (i : ℕ), 1 ≤ i → i ≤ Fintype.card E →
      ((∃ e : E, v ∈ ends e ∧ (σ k).idx e = i) ↔ i ≤ (σ k).r v) := by
  intro k hk v i hi _
  exact (NagamochiIbaraki.EdgeConn.L22P.inv_run ends hloop σ K hrun k hk).2.2 v i hi
