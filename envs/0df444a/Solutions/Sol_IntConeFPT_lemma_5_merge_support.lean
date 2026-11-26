-- Prove2me | solution 1 for IntConeFPT.lemma_5_merge_support
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-26T14:04:59.517361+00:00
-- url     : https://prove2.me/submissions/e4fa819b-5ff3-4b3d-8df0-47ba16cd89bf

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation
import Definitions.Def_IntConeFPT_fracMerge

open OnlineCRS.Combine IntConeFPT

/-- The finitely supported function of a weighted generator list. -/
private noncomputable def listRep {d k : ℕ} (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    Gen d k →₀ ℝ :=
  (L.map fun e => Finsupp.single (ratGen e.1 e.2.1) (e.2.2 : ℝ)).sum

private lemma listRep_cons {d k : ℕ} (e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ)
    (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    listRep (e :: L) = Finsupp.single (ratGen e.1 e.2.1) (e.2.2 : ℝ) + listRep L := by
  simp [listRep]

private lemma listRep_append {d k : ℕ} (A B : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    listRep (A ++ B) = listRep A + listRep B := by
  simp [listRep]

private lemma listRep_sum {d k : ℕ} {M : Type*} [AddCommMonoid M]
    (F : Gen d k → ℝ → M) (h0 : ∀ g, F g 0 = 0) (hadd : ∀ g a b, F g (a + b) = F g a + F g b)
    (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    (listRep L).sum F = (L.map fun e => F (ratGen e.1 e.2.1) (e.2.2 : ℝ)).sum := by
  induction L with
  | nil => simp [listRep]
  | cons e L ih =>
    rw [listRep_cons, Finsupp.sum_add_index' h0 hadd, Finsupp.sum_single_index (h0 _), ih]
    simp

private lemma listRep_support {d k : ℕ} (S : Set (Gen d k))
    (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) (hL : ∀ e ∈ L, ratGen e.1 e.2.1 ∈ S) :
    (↑(listRep L).support : Set (Gen d k)) ⊆ S := by
  classical
  induction L with
  | nil => simp [listRep]
  | cons e L ih =>
    rw [listRep_cons]
    intro g hg
    have hg' := Finsupp.support_add hg
    rcases Finset.mem_union.1 hg' with h | h
    · have := Finsupp.support_single_subset h
      rw [Finset.mem_singleton] at this
      rw [this]; exact hL e (by simp)
    · exact ih (fun e' he' => hL e' (by simp [he'])) h

private lemma listRep_nonneg {d k : ℕ} (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ))
    (hL : ∀ e ∈ L, 0 < e.2.2) (g : Gen d k) : 0 ≤ listRep L g := by
  induction L with
  | nil => simp [listRep]
  | cons e L ih =>
    rw [listRep_cons, Finsupp.add_apply]
    have h1 : 0 ≤ Finsupp.single (ratGen e.1 e.2.1) (e.2.2 : ℝ) g := by
      rw [Finsupp.single_apply]
      split_ifs
      · exact_mod_cast (hL e (by simp)).le
      · exact le_refl _
    exact add_nonneg h1 (ih (fun e' he' => hL e' (by simp [he'])))

private lemma listRep_ge {d k : ℕ} (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ))
    (hL : ∀ e ∈ L, 0 < e.2.2) (e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ) (he : e ∈ L) :
    (e.2.2 : ℝ) ≤ listRep L (ratGen e.1 e.2.1) := by
  induction L with
  | nil => simp at he
  | cons h L ih =>
    rw [listRep_cons, Finsupp.add_apply]
    have hL' : ∀ e' ∈ L, 0 < e'.2.2 := fun e' he' => hL e' (by simp [he'])
    rcases List.mem_cons.1 he with rfl | he'
    · rw [Finsupp.single_apply, if_pos rfl]
      linarith [listRep_nonneg L hL' (ratGen e.1 e.2.1)]
    · have h1 : 0 ≤ Finsupp.single (ratGen h.1 h.2.1) (h.2.2 : ℝ) (ratGen e.1 e.2.1) := by
        rw [Finsupp.single_apply]
        split_ifs
        · exact_mod_cast (hL h (by simp)).le
        · exact le_refl _
      linarith [ih hL' he']

@[simp] private lemma ratGen_fst {d k : ℕ} (x : Fin d → ℤ) (u : Fin k → ℚ) :
    (ratGen x u).1 = x := rfl

private lemma P_convex (I : Instance) (t : Fin I.τ) : Convex ℝ (I.P t) := by
  intro p hp q hq a b ha hb hab i
  have h1 := hp i
  have h2 := hq i
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  calc (∑ j, (I.Aloc t i j : ℝ) * (a * p.1 j + b * q.1 j)) +
        (∑ j, (I.Bloc t i j : ℝ) * (a * p.2 j + b * q.2 j))
      = a * ((∑ j, (I.Aloc t i j : ℝ) * p.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p.2 j)) +
        b * ((∑ j, (I.Aloc t i j : ℝ) * q.1 j) + (∑ j, (I.Bloc t i j : ℝ) * q.2 j)) := by
        have e1 : ∀ (c : Fin I.d → ℝ) (v w : Fin I.d → ℝ), (∑ j, c j * (a * v j + b * w j)) =
            a * (∑ j, c j * v j) + b * (∑ j, c j * w j) := fun c v w => by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        have e2 : ∀ (c : Fin I.k → ℝ) (v w : Fin I.k → ℝ), (∑ j, c j * (a * v j + b * w j)) =
            a * (∑ j, c j * v j) + b * (∑ j, c j * w j) := fun c v w => by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [e1 (fun j => (I.Aloc t i j : ℝ)), e2 (fun j => (I.Bloc t i j : ℝ))]
        ring
    _ ≤ a * (I.bloc t i : ℝ) + b * (I.bloc t i) := by gcongr
    _ = _ := by rw [← add_mul, hab, one_mul]

private lemma memP (I : Instance) (t : Fin I.τ) (r : Residue I.d) (g : Gen I.d I.k)
    (h : g ∈ I.Sr t r) : g.toReal ∈ I.P t := h.1

private lemma avg_mem (I : Instance) (t : Fin I.τ) (r : Residue I.d) (x : Fin I.d → ℤ)
    (u1 u2 : Fin I.k → ℚ) (a b : ℚ) (ha : 0 < a) (hb : 0 < b)
    (h1 : ratGen x u1 ∈ I.Sr t r) (h2 : ratGen x u2 ∈ I.Sr t r) :
    ratGen x (fun j => (a * u1 j + b * u2 j) / (a + b)) ∈ I.Sr t r := by
  refine ⟨?_, h1.2⟩
  have hab : (0:ℝ) < a + b := by exact_mod_cast add_pos ha hb
  have key := P_convex I t (memP I t r _ h1) (memP I t r _ h2) (a := (a:ℝ) / (a + b))
    (b := (b:ℝ) / (a + b)) (by positivity) (by positivity) (by field_simp)
  show (ratGen x _).toReal ∈ I.P t
  convert key using 1
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · simp [Gen.toReal, ratGen]; field_simp
  · simp [Gen.toReal, ratGen]; field_simp

private lemma merge_cons {d k : ℕ} (e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ)
    (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    fracMerge (e :: L) = fracMergeInsert e (fracMerge L) := rfl

private lemma insert_keys {d k : ℕ} (e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ)
    (l : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    (fracMergeInsert e l).map Prod.fst =
      if e.1 ∈ l.map Prod.fst then l.map Prod.fst else l.map Prod.fst ++ [e.1] := by
  induction l with
  | nil => simp [fracMergeInsert]
  | cons h l ih =>
    by_cases hh : h.1 = e.1
    · simp only [fracMergeInsert, if_pos hh, List.map_cons]
      rw [if_pos (by simp only [List.mem_cons]; exact Or.inl hh.symm)]
    · simp only [fracMergeInsert, if_neg hh, List.map_cons, ih]
      have hiff : (e.1 ∈ h.1 :: l.map Prod.fst) ↔ e.1 ∈ l.map Prod.fst := by
        rw [List.mem_cons]; constructor
        · rintro (h' | h')
          · exact absurd h'.symm hh
          · exact h'
        · exact Or.inr
      by_cases hm : e.1 ∈ l.map Prod.fst
      · rw [if_pos hm, if_pos (hiff.2 hm)]
      · rw [if_neg hm, if_neg (fun h' => hm (hiff.1 h')), List.cons_append]

private lemma merge_keys_nodup {d k : ℕ} (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    ((fracMerge L).map Prod.fst).Nodup := by
  induction L with
  | nil => simp [fracMerge]
  | cons e L ih =>
    rw [merge_cons, insert_keys]
    split_ifs with hm
    · exact ih
    · rw [List.nodup_append]
      refine ⟨ih, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact fun h => hm (h ▸ ha)

private lemma merge_length {d k : ℕ} (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    (fracMerge L).length ≤ L.length := by
  induction L with
  | nil => simp [fracMerge]
  | cons e L ih =>
    have := congrArg List.length (insert_keys e (fracMerge L))
    rw [List.length_map] at this
    rw [merge_cons, this]
    split_ifs <;> simp <;> omega

private lemma insert_wsum {d k : ℕ} (g : (Fin d → ℤ) → ℝ) (e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ)
    (l : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    ((fracMergeInsert e l).map fun e => (e.2.2 : ℝ) * g e.1).sum =
      (l.map fun e => (e.2.2 : ℝ) * g e.1).sum + (e.2.2 : ℝ) * g e.1 := by
  induction l with
  | nil => simp [fracMergeInsert]
  | cons h l ih =>
    by_cases hh : h.1 = e.1
    · simp only [fracMergeInsert, if_pos hh, List.map_cons, List.sum_cons]
      rw [hh]; push_cast; ring
    · simp only [fracMergeInsert, if_neg hh, List.map_cons, List.sum_cons, ih]; ring

private lemma merge_wsum {d k : ℕ} (g : (Fin d → ℤ) → ℝ)
    (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    ((fracMerge L).map fun e => (e.2.2 : ℝ) * g e.1).sum =
      (L.map fun e => (e.2.2 : ℝ) * g e.1).sum := by
  induction L with
  | nil => simp [fracMerge]
  | cons e L ih =>
    rw [merge_cons, insert_wsum, ih, List.map_cons, List.sum_cons]; ring

private lemma insert_agg {d k : ℕ} (e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ)
    (l : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) (he : 0 < e.2.2)
    (hl : ∀ e' ∈ l, 0 < e'.2.2) :
    ((fracMergeInsert e l).map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum =
      (l.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum +
        (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal := by
  induction l with
  | nil => simp [fracMergeInsert]
  | cons h l ih =>
    have hh0 := hl h (by simp)
    by_cases hh : h.1 = e.1
    · simp only [fracMergeInsert, if_pos hh, List.map_cons, List.sum_cons]
      have hs : (h.2.2 : ℝ) + e.2.2 ≠ 0 := by
        have : (0:ℝ) < h.2.2 + e.2.2 := by exact_mod_cast add_pos hh0 he
        exact this.ne'
      have key : ((h.2.2 + e.2.2 : ℚ) : ℝ) • (ratGen h.1 (fun j => (h.2.2 * h.2.1 j +
          e.2.2 * e.2.1 j) / (h.2.2 + e.2.2))).toReal =
          (h.2.2:ℝ) • (ratGen h.1 h.2.1).toReal + (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal := by
        rw [← hh]
        refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
        · simp [Gen.toReal, ratGen]; ring
        · simp [Gen.toReal, ratGen]; field_simp
      rw [key]; abel
    · simp only [fracMergeInsert, if_neg hh, List.map_cons, List.sum_cons]
      rw [ih (fun e' he' => hl e' (by simp [he']))]; abel

private lemma insert_pos {d k : ℕ} (e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ)
    (l : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) (he : 0 < e.2.2)
    (hl : ∀ e' ∈ l, 0 < e'.2.2) : ∀ e' ∈ fracMergeInsert e l, 0 < e'.2.2 := by
  induction l with
  | nil => simpa [fracMergeInsert] using he
  | cons h l ih =>
    have hh0 := hl h (by simp)
    have hl' : ∀ e' ∈ l, 0 < e'.2.2 := fun e' he' => hl e' (by simp [he'])
    by_cases hh : h.1 = e.1
    · simp only [fracMergeInsert, if_pos hh]
      intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact add_pos hh0 he
      · exact hl' e' he'
    · simp only [fracMergeInsert, if_neg hh]
      intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact hh0
      · exact ih hl' e' he'

private lemma merge_pos {d k : ℕ} (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ))
    (hL : ∀ e ∈ L, 0 < e.2.2) : ∀ e ∈ fracMerge L, 0 < e.2.2 := by
  induction L with
  | nil => simp [fracMerge]
  | cons e L ih =>
    rw [merge_cons]
    exact insert_pos e _ (hL e (by simp)) (ih (fun e' he' => hL e' (by simp [he'])))

private lemma merge_agg {d k : ℕ} (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ))
    (hL : ∀ e ∈ L, 0 < e.2.2) :
    ((fracMerge L).map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum =
      (L.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum := by
  induction L with
  | nil => simp [fracMerge]
  | cons e L ih =>
    have hL' : ∀ e' ∈ L, 0 < e'.2.2 := fun e' he' => hL e' (by simp [he'])
    rw [merge_cons, insert_agg e _ (hL e (by simp)) (merge_pos L hL'), ih hL', List.map_cons,
      List.sum_cons]
    abel

private lemma insert_mem (I : Instance) (t : Fin I.τ) (r : Residue I.d)
    (e : (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ) (l : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ))
    (he : ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2)
    (hl : ∀ e' ∈ l, ratGen e'.1 e'.2.1 ∈ I.Sr t r ∧ 0 < e'.2.2) :
    ∀ e' ∈ fracMergeInsert e l, ratGen e'.1 e'.2.1 ∈ I.Sr t r ∧ 0 < e'.2.2 := by
  induction l with
  | nil => simpa [fracMergeInsert] using he
  | cons h l ih =>
    have hh0 := hl h (by simp)
    have hl' : ∀ e' ∈ l, ratGen e'.1 e'.2.1 ∈ I.Sr t r ∧ 0 < e'.2.2 :=
      fun e' he' => hl e' (by simp [he'])
    by_cases hh : h.1 = e.1
    · simp only [fracMergeInsert, if_pos hh]
      intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · refine ⟨?_, add_pos hh0.2 he.2⟩
        exact avg_mem I t r h.1 h.2.1 e.2.1 _ _ hh0.2 he.2 hh0.1 (by rw [hh]; exact he.1)
      · exact hl' e' he'
    · simp only [fracMergeInsert, if_neg hh]
      intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact hh0
      · exact ih hl' e' he'

private lemma merge_mem (I : Instance) (t : Fin I.τ) (r : Residue I.d)
    (L : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ))
    (hL : ∀ e ∈ L, ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2) :
    ∀ e ∈ fracMerge L, ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2 := by
  induction L with
  | nil => simp [fracMerge]
  | cons e L ih =>
    rw [merge_cons]
    exact insert_mem I t r e _ (hL e (by simp)) (ih (fun e' he' => hL e' (by simp [he'])))

theorem solution (I : Instance) (hI : I.Valid) (t : Fin I.τ) (r : Residue I.d)
    (z : Fin I.d → ℚ) (w : Fin I.k → ℚ) (n φ : ℚ)
    (L : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ))
    (hS : ∀ e ∈ L, ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2)
    (hagg : (L.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum = ratPair z w)
    (hcnt : (L.map fun e => (e.2.2 : ℝ)).sum = n)
    (hcost : (L.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum = φ)
    (hlex : ∀ θ : Gen I.d I.k →₀ ℝ,
      IsFracRep (I.Sr t r) θ ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) →
      fracCost (I.f t) θ ≤ φ →
      (L.map fun e => (e.2.2 : ℝ) *
          ∑ i, (((e.1 i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2).sum ≤
        fracCost (fun x => ∑ i, ((x i - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2) θ) :
    (fracMerge L).length ≤ 2 ^ I.d ∧ (fracMerge L).length ≤ L.length ∧
      ((fracMerge L).map fun e => (e.1, e.2.1)).Nodup ∧
      (∀ e ∈ fracMerge L, ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2) ∧
      ((fracMerge L).map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum = ratPair z w ∧
      ((fracMerge L).map fun e => (e.2.2 : ℝ)).sum = n ∧
      ((fracMerge L).map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum = φ := by
  classical
  have hMmem := merge_mem I t r L hS
  have hMpos : ∀ e ∈ fracMerge L, 0 < e.2.2 := fun e he => (hMmem e he).2
  have hkeys := merge_keys_nodup L
  have hMagg : ((fracMerge L).map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum =
      ratPair z w := (merge_agg L (fun e he => (hS e he).2)).trans hagg
  have hMcnt : ((fracMerge L).map fun e => (e.2.2 : ℝ)).sum = n := by
    have := merge_wsum (fun _ => (1 : ℝ)) L
    simp only [mul_one] at this
    rw [this, hcnt]
  have hMcost : ((fracMerge L).map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum
      = φ := (merge_wsum (fun x => I.f t (fun i => (x i : ℝ))) L).trans hcost
  have hMsec : ((fracMerge L).map fun e => (e.2.2 : ℝ) *
      ∑ i, (((e.1 i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2).sum =
      (L.map fun e => (e.2.2 : ℝ) *
          ∑ i, (((e.1 i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2).sum :=
    merge_wsum (fun x => ∑ i, (((x i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2) L
  refine ⟨?_, merge_length L, ?_, hMmem, hMagg, hMcnt, hMcost⟩
  swap
  · apply List.Nodup.of_map Prod.fst
    rw [List.map_map]
    exact hkeys
  set M := fracMerge L with hMdef
  by_contra hlt
  push Not at hlt
  set K := (M.map Prod.fst).toFinset with hKdef
  have hK : K.card = M.length := by rw [List.toFinset_card_of_nodup hkeys, List.length_map]
  let par : (Fin I.d → ℤ) → (Fin I.d → Bool) :=
    fun x l => decide (Even ((x l - ((r l : ℕ) : ℤ)) / 2 ^ I.d))
  obtain ⟨x, hx, y, hy, hxy, hpar⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := K) (t := (Finset.univ : Finset (Fin I.d → Bool))) (f := par)
    (by simp [hK]; exact hlt) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  obtain ⟨ei, hei, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
  obtain ⟨ej, hej, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
  have hSi := hMmem ei hei
  have hSj := hMmem ej hej
  have hdec : ∀ e ∈ M, ∀ l, e.1 l = ((r l : ℕ) : ℤ) + 2 ^ I.d * ((e.1 l - ((r l : ℕ) : ℤ)) / 2 ^ I.d) :=
    fun e he l => by
      have hd : (2 : ℤ) ^ I.d ∣ e.1 l - ((r l : ℕ) : ℤ) := ((hMmem e he).1.2 l).symm.dvd
      rw [Int.mul_ediv_cancel' hd]; ring
  have hc : ∀ l, ∃ c : ℤ, (ei.1 l - ((r l : ℕ) : ℤ)) / 2 ^ I.d +
      (ej.1 l - ((r l : ℕ) : ℤ)) / 2 ^ I.d = c + c := fun l => by
    have h := congrFun hpar l
    simp only [par, decide_eq_decide] at h
    exact Int.even_add.2 h
  choose c hc using hc
  obtain ⟨x0, hx0def⟩ : ∃ x0 : Fin I.d → ℤ, ∀ l, x0 l = ((r l : ℕ) : ℤ) + 2 ^ I.d * c l :=
    ⟨_, fun l => rfl⟩
  have hx0 : ∀ l, 2 * x0 l = ei.1 l + ej.1 l := fun l => by
    rw [hx0def]
    linear_combination (-1 : ℤ) * hdec ei hei l - hdec ej hej l - 2 ^ I.d * hc l
  have hx0r : ∀ l, (x0 l : ℝ) = ((ei.1 l : ℝ) + ej.1 l) / 2 := fun l => by
    have := congrArg (Int.cast : ℤ → ℝ) (hx0 l)
    push_cast at this
    linarith
  obtain ⟨u0, hu0⟩ : ∃ u0 : Fin I.k → ℚ, ∀ j, u0 j = (ei.2.1 j + ej.2.1 j) / 2 :=
    ⟨_, fun j => rfl⟩
  have hg0 : ratGen x0 u0 ∈ I.Sr t r := by
    refine ⟨?_, fun l => ?_⟩
    · have key := P_convex I t (memP I t r _ hSi.1) (memP I t r _ hSj.1) (a := (1/2:ℝ))
        (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
      show (ratGen x0 u0).toReal ∈ I.P t
      convert key using 1
      refine Prod.ext (funext fun l => ?_) (funext fun j => ?_)
      · simp [Gen.toReal, ratGen, hx0r]; ring
      · simp [Gen.toReal, ratGen, hu0]; ring
    · show x0 l ≡ _ [ZMOD 2 ^ I.d]
      exact Int.modEq_iff_dvd.2 ⟨-c l, by rw [hx0def]; ring⟩
  have hPx : ∀ e ∈ M, (fun l => (e.1 l : ℝ)) ∈ I.Px t :=
    fun e he => ⟨(ratGen e.1 e.2.1).toReal, memP I t r _ (hMmem e he).1, rfl⟩
  have hconv := (hI.convex t).2 (hPx ei hei) (hPx ej hej) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have hx0f : (fun l => (x0 l : ℝ)) =
      (1/2:ℝ) • (fun l => (ei.1 l : ℝ)) + (1/2:ℝ) • (fun l => (ej.1 l : ℝ)) := by
    funext l; simp [hx0r]; ring
  rw [← hx0f] at hconv
  simp only [smul_eq_mul] at hconv
  obtain ⟨l0, hl0⟩ : ∃ l, ei.1 l ≠ ej.1 l := by
    by_contra h; push Not at h; exact hxy (funext h)
  have hsec : 2 * (∑ i, (((x0 i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2) <
      (∑ i, (((ei.1 i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2) +
      (∑ i, (((ej.1 i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2) := by
    have h1 : (∑ i, (((ei.1 i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2) +
        (∑ i, (((ej.1 i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2) -
        2 * (∑ i, (((x0 i : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2) =
        ∑ l, ((ei.1 l - ej.1 l : ℝ) / 2 ^ I.d) ^ 2 / 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by rw [hx0r]; ring
    have hpos : 0 < ∑ l, ((ei.1 l - ej.1 l : ℝ) / 2 ^ I.d) ^ 2 / 2 := by
      have hne : (ei.1 l0 : ℝ) - ej.1 l0 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hl0)
      have hlt0 : 0 < ((ei.1 l0 - ej.1 l0 : ℝ) / 2 ^ I.d) ^ 2 / 2 := by positivity
      exact lt_of_lt_of_le hlt0 (Finset.single_le_sum
        (f := fun l => ((ei.1 l - ej.1 l : ℝ) / 2 ^ I.d) ^ 2 / 2)
        (fun l _ => by positivity) (Finset.mem_univ l0))
    linarith
  -- the improved representation
  set α : ℚ := min ei.2.2 ej.2.2 with hαdef
  have hα : (0:ℝ) < α := by exact_mod_cast lt_min hSi.2 hSj.2
  have hαi : (α:ℝ) ≤ ei.2.2 := by exact_mod_cast min_le_left _ _
  have hαj : (α:ℝ) ≤ ej.2.2 := by exact_mod_cast min_le_right _ _
  set L' := M ++ [(ei.1, ei.2.1, -α), (ej.1, ej.2.1, -α), (x0, u0, 2 * α)] with hL'
  have hneq : ratGen ei.1 ei.2.1 ≠ ratGen ej.1 ej.2.1 := fun h => hxy (by simpa using congrArg Prod.fst h)
  have hnn : ∀ g, 0 ≤ listRep L' g := by
    intro g
    rw [hL', listRep_append, Finsupp.add_apply]
    simp only [listRep, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Finsupp.add_apply, Finsupp.single_apply]
    have hM0 : 0 ≤ listRep M g := listRep_nonneg M hMpos g
    have hA : ratGen ei.1 ei.2.1 = g → (ei.2.2 : ℝ) ≤ listRep M g :=
      fun h => h ▸ listRep_ge M hMpos ei hei
    have hB : ratGen ej.1 ej.2.1 = g → (ej.2.2 : ℝ) ≤ listRep M g :=
      fun h => h ▸ listRep_ge M hMpos ej hej
    change 0 ≤ listRep M g + _
    split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> push_cast <;>
      first
      | (exfalso; exact hneq (h1.trans h2.symm))
      | (have := hA h1; linarith)
      | (have := hB h2; linarith)
      | linarith
  have hsupp : ∀ e ∈ L', ratGen e.1 e.2.1 ∈ I.Sr t r := by
    intro e he
    rw [hL', List.mem_append] at he
    rcases he with he | he
    · exact (hMmem e he).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hSi.1
      · exact hSj.1
      · exact hg0
  have hzero : ((-α : ℚ) : ℝ) • (ratGen ei.1 ei.2.1).toReal +
      (((-α : ℚ) : ℝ) • (ratGen ej.1 ej.2.1).toReal +
        ((2 * α : ℚ) : ℝ) • (ratGen x0 u0).toReal) = 0 := by
    refine Prod.ext (funext fun l => ?_) (funext fun j => ?_)
    · simp [Gen.toReal, ratGen, hx0r]; ring
    · simp [Gen.toReal, ratGen, hu0]; ring
  have hrep : IsFracRep (I.Sr t r) (listRep L') ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) := by
    refine ⟨listRep_support _ L' hsupp, hnn, ?_, ?_⟩
    · rw [listRep_sum (fun g c => c • g.toReal) (fun g => zero_smul _ _)
        (fun g a b => add_smul a b _), hL', List.map_append, List.sum_append, hMagg]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [hzero, add_zero]
    · rw [listRep_sum (fun _ c => c) (fun _ => rfl) (fun _ _ _ => rfl), hL', List.map_append,
        List.sum_append, hMcnt]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      push_cast; ring
  have hcost' : fracCost (I.f t) (listRep L') ≤ φ := by
    unfold fracCost
    rw [listRep_sum (fun g c => c * I.f t (fun i => (g.1 i : ℝ))) (fun _ => zero_mul _)
        (fun _ _ _ => add_mul _ _ _), hL', List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ratGen_fst]
    rw [hMcost]
    push_cast
    nlinarith [hconv, hα]
  have hle := hlex _ hrep hcost'
  unfold fracCost at hle
  rw [listRep_sum (fun g c => c * ∑ i, ((((g.1 i : ℤ) : ℝ) - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2)
      (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), hL', List.map_append,
      List.sum_append] at hle
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    ratGen_fst] at hle
  rw [hMsec] at hle
  push_cast at hle
  nlinarith [hsec, hα]
