-- Prove2me | solution 1 for GeneralizedUniformServer.UnitWeights.lazy_conversion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:27:37.101867+00:00
-- url     : https://prove2.me/submissions/05d2b9fe-a57c-4a1c-84ed-afa24f6a6be0

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Model

section
noncomputable section

namespace GeneralizedUniformServer.Dev.LazyConversion

open GeneralizedUniformServer.UnitWeights

variable {k : ℕ} {M : Fin k → Type*}

open scoped Classical in
theorem dist_eq (x y : Config M) :
    UnitWeights.dist x y = (Finset.univ.filter fun i : Fin k => x i ≠ y i).card := by
  classical
  unfold UnitWeights.dist
  rfl

theorem dist_triangle (x y z : Config M) :
    UnitWeights.dist x z ≤ UnitWeights.dist x y + UnitWeights.dist y z := by
  classical
  rw [dist_eq, dist_eq, dist_eq]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
  by_contra h
  push Not at h
  exact hi (h.1.trans h.2)

theorem dist_repair_lt (x z r : Config M) (i : Fin k) (hxi : x i ≠ z i) (hz : z i = r i) :
    UnitWeights.dist (repair x r i) z < UnitWeights.dist x z := by
  classical
  rw [dist_eq, dist_eq]
  have hsub : (Finset.univ.filter fun j : Fin k => repair x r i j ≠ z j) ⊆
      (Finset.univ.filter fun j : Fin k => x j ≠ z j) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_cases h : j = i
    · subst h; simp [repair, hz] at hj
    · simpa [repair, h] using hj
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨i, ?_, ?_⟩)
  · simpa using hxi
  · simp [repair, ← hz]

def ext (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M) (t : ℕ) : Config M :=
  if h : t < ρ.length + 1 then o ⟨t, h⟩ else o 0

theorem ext_castSucc (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M)
    (s : Fin ρ.length) : ext ρ o s.val = o s.castSucc := by
  unfold ext; rw [dif_pos (by omega)]; rfl

theorem ext_succ (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M)
    (s : Fin ρ.length) : ext ρ o (s.val + 1) = o s.succ := by
  unfold ext; rw [dif_pos (by omega)]; rfl

open scoped Classical in
def req (ρ : List (Config M)) (a : Config M) (t : ℕ) : Config M :=
  if h : t < ρ.length then ρ[t] else a

open scoped Classical in
def idx [NeZero k] (rq oo : ℕ → Config M) (t : ℕ) : Fin k :=
  if h : ∃ i, oo (t+1) i = rq t i then Classical.choose h else ⟨0, NeZero.pos k⟩

open scoped Classical in
def seq [NeZero k] (a : Config M) (rq oo : ℕ → Config M) : ℕ → Config M
  | 0 => a
  | t+1 => if Serves (seq a rq oo t) (rq t) then seq a rq oo t
      else repair (seq a rq oo t) (rq t) (idx rq oo t)

section
variable [NeZero k] (a : Config M) (rq oo : ℕ → Config M)

theorem seq_succ_of_serves (t : ℕ) (h : Serves (seq a rq oo t) (rq t)) :
    seq a rq oo (t+1) = seq a rq oo t := by
  rw [seq, if_pos h]

theorem seq_succ_of_not (t : ℕ) (h : ¬ Serves (seq a rq oo t) (rq t)) :
    seq a rq oo (t+1) = repair (seq a rq oo t) (rq t) (idx rq oo t) := by
  rw [seq, if_neg h]

theorem seq_succ_serves (t : ℕ) : Serves (seq a rq oo (t+1)) (rq t) := by
  by_cases h : Serves (seq a rq oo t) (rq t)
  · rw [seq_succ_of_serves a rq oo t h]; exact h
  · rw [seq_succ_of_not a rq oo t h]; exact ⟨idx rq oo t, by simp [repair]⟩

theorem step (t : ℕ) (hy : ∃ i, oo (t+1) i = rq t i) :
    (by classical exact if seq a rq oo (t+1) ≠ seq a rq oo t then 1 else 0 : ℕ) +
        UnitWeights.dist (seq a rq oo (t+1)) (oo (t+1)) ≤
      UnitWeights.dist (oo t) (oo (t+1)) + UnitWeights.dist (seq a rq oo t) (oo t) := by
  classical
  by_cases hs : Serves (seq a rq oo t) (rq t)
  · rw [seq_succ_of_serves a rq oo t hs]
    have := dist_triangle (seq a rq oo t) (oo t) (oo (t+1))
    simp only [ne_eq, not_true_eq_false, if_false]
    omega
  · rw [seq_succ_of_not a rq oo t hs]
    have hi : oo (t+1) (idx rq oo t) = rq t (idx rq oo t) := by
      unfold idx; rw [dif_pos hy]; exact Classical.choose_spec hy
    have hne : repair (seq a rq oo t) (rq t) (idx rq oo t) ≠ seq a rq oo t := by
      intro h; apply hs; rw [← h]; exact ⟨idx rq oo t, by simp [repair]⟩
    have hxi : seq a rq oo t (idx rq oo t) ≠ oo (t+1) (idx rq oo t) := by
      rw [hi]; intro h; exact hs ⟨_, h⟩
    have h1 := dist_repair_lt (seq a rq oo t) (oo (t+1)) (rq t) (idx rq oo t) hxi hi
    have h2 := dist_triangle (seq a rq oo t) (oo t) (oo (t+1))
    simp only [ne_eq, hne, not_false_eq_true, if_true]
    omega

theorem sum_bound (n : ℕ) (hy : ∀ t < n, ∃ i, oo (t+1) i = rq t i) :
    ∀ m ≤ n,
      (by classical exact ∑ s ∈ Finset.range m,
        (if seq a rq oo (s+1) ≠ seq a rq oo s then 1 else 0) : ℕ) +
        UnitWeights.dist (seq a rq oo m) (oo m) ≤
      ∑ s ∈ Finset.range m, UnitWeights.dist (oo s) (oo (s+1)) +
        UnitWeights.dist a (oo 0) := by
  intro m
  induction m with
  | zero => intro _; simp [seq]
  | succ m ih =>
    intro hm
    have := ih (by omega)
    have h2 := step a rq oo m (hy m (by omega))
    classical
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    omega
end

end GeneralizedUniformServer.Dev.LazyConversion

namespace GeneralizedUniformServer

open GeneralizedUniformServer.UnitWeights

theorem chk_lazy_conversion {k : ℕ} [NeZero k] {M : Fin k → Type*}
    (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M)
    (ho : IsOfflineSolution ρ o) (a : Config M) :
    ∃ o' : Fin (ρ.length + 1) → Config M,
      IsOfflineSolution ρ o' ∧ IsLazy ρ o' ∧ o' 0 = a ∧
        numMoves ρ o' ≤ offlineCost ρ o + dist a (o 0) := by
  classical
  open Dev.LazyConversion in
  have hreq : ∀ s : Fin ρ.length, req ρ a s.val = ρ[s] := by
    intro s; unfold req; rw [dif_pos s.2]; simp
  open Dev.LazyConversion in
  refine ⟨fun s => seq a (req ρ a) (ext ρ o) s.val, ?_, ?_, ?_, ?_⟩
  · intro s
    have := seq_succ_serves a (req ρ a) (ext ρ o) s.val
    rw [hreq] at this
    exact this
  · intro s
    have e : (fun s : Fin (ρ.length + 1) => seq a (req ρ a) (ext ρ o) s.val) s.succ =
      seq a (req ρ a) (ext ρ o) (s.val + 1) := rfl
    have e' : (fun s : Fin (ρ.length + 1) => seq a (req ρ a) (ext ρ o) s.val) s.castSucc =
      seq a (req ρ a) (ext ρ o) s.val := rfl
    simp only [e, e']
    rw [← hreq s]
    constructor
    · intro h; exact seq_succ_of_serves _ _ _ _ h
    · intro h; exact ⟨_, seq_succ_of_not _ _ _ _ h⟩
  · simp [seq]
  · have hy : ∀ t < ρ.length, ∃ i, ext ρ o (t+1) i = req ρ a t i := by
      intro t ht
      have := ho ⟨t, ht⟩
      rw [← ext_succ ρ o ⟨t, ht⟩] at this
      rw [show req ρ a t = ρ[t] from hreq ⟨t, ht⟩]
      exact this
    have key := sum_bound a (req ρ a) (ext ρ o) ρ.length hy ρ.length le_rfl
    have h0 : ext ρ o 0 = o 0 := by unfold ext; rw [dif_pos (by omega)]; rfl
    have hm : numMoves ρ (fun s : Fin (ρ.length + 1) => seq a (req ρ a) (ext ρ o) s.val) =
        ∑ s ∈ Finset.range ρ.length,
          (if seq a (req ρ a) (ext ρ o) (s+1) ≠ seq a (req ρ a) (ext ρ o) s then 1 else 0) := by
      unfold numMoves
      rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range
        (fun s => if seq a (req ρ a) (ext ρ o) (s+1) ≠ seq a (req ρ a) (ext ρ o) s
          then 1 else 0) ρ.length]
      rfl
    have hc : offlineCost ρ o = ∑ s ∈ Finset.range ρ.length,
        UnitWeights.dist (ext ρ o s) (ext ρ o (s+1)) := by
      unfold offlineCost
      rw [← Fin.sum_univ_eq_sum_range
        (fun s => UnitWeights.dist (ext ρ o s) (ext ρ o (s+1))) ρ.length]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ext_castSucc, ext_succ]
    rw [hm, hc, ← h0]
    omega

end GeneralizedUniformServer
end
end

theorem solution : type_of% @GeneralizedUniformServer.chk_lazy_conversion := @GeneralizedUniformServer.chk_lazy_conversion
