-- Prove2me | solution 1 for LearnDoFrontier.TwoAction.thm6_inductive_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:56:04.648333+00:00
-- url     : https://prove2.me/submissions/cbcb0f2f-6d5f-461d-8ea0-41f0bc81f805

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra

open Polynomial Matrix

namespace LDFDet

noncomputable def colA (z : ℂ) (τ : ℕ) : ℕ → ℂ := fun k => (k.choose τ : ℂ) * z ^ (k - τ)
noncomputable def colB (N : ℕ) (w : ℂ) (τ : ℕ) : ℕ → ℂ :=
  fun k => ((N - 1 - k).choose τ : ℂ) * w ^ (N - 1 - k - τ)

noncomputable def colsA (L : List (ℂ × ℕ)) : List (ℕ → ℂ) :=
  L.flatMap (fun e => (List.range e.2).map (colA e.1))
noncomputable def colsB (N : ℕ) (L : List (ℂ × ℕ)) : List (ℕ → ℂ) :=
  L.flatMap (fun e => (List.range e.2).reverse.map (colB N e.1))

noncomputable def matOf (N : ℕ) (cs : List (ℕ → ℂ)) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun k c => (cs.getD c 0) k

def msum (L : List (ℂ × ℕ)) : ℕ := (L.map Prod.snd).sum

def PP {α : Type} (g : α → α → ℂ) : List α → ℂ
  | [] => 1
  | e :: L => (L.map (g e)).prod * PP g L

def gA (x y : ℂ × ℕ) : ℂ := (y.1 - x.1) ^ (x.2 * y.2)
def gB (x y : ℂ × ℕ) : ℂ := (x.1 - y.1) ^ (x.2 * y.2)
def Cr (LA LB : List (ℂ × ℕ)) : ℂ :=
  (LA.map (fun e => (LB.map (fun f => (1 - e.1 * f.1) ^ (e.2 * f.2))).prod)).prod

lemma length_colsA (L : List (ℂ × ℕ)) : (colsA L).length = msum L := by
  induction L with
  | nil => simp [colsA, msum]
  | cons e L ih => simp_all [colsA, msum]

lemma length_colsB (N : ℕ) (L : List (ℂ × ℕ)) : (colsB N L).length = msum L := by
  induction L with
  | nil => simp [colsB, msum]
  | cons e L ih => simp_all [colsB, msum]

lemma PP_insert {α : Type} (g : α → α → ℂ) (L1 L2 : List α) (e : α) :
    PP g (L1 ++ e :: L2) = PP g (L1 ++ L2) * (L1.map (fun x => g x e)).prod *
      (L2.map (g e)).prod := by
  induction L1 with
  | nil => simp [PP]; ring
  | cons x L1 ih =>
    simp only [List.cons_append, PP, ih, List.map_append, List.map_cons, List.prod_append,
      List.prod_cons]
    ring

lemma matOf_set (N : ℕ) (P Q : List (ℕ → ℂ)) (v v' : ℕ → ℂ) (h : P.length < N) :
    matOf N (P ++ v :: Q) = (matOf N (P ++ v' :: Q)).updateCol ⟨P.length, h⟩ (fun k => v k) := by
  ext k c
  simp only [matOf, updateCol_apply, of_apply]
  by_cases hc : (c : ℕ) = P.length
  · have : c = ⟨P.length, h⟩ := Fin.ext hc
    subst this
    simp
  · have hc' : c ≠ ⟨P.length, h⟩ := fun h' => hc (by rw [h'])
    rw [if_neg hc']
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hgt.le]
      obtain ⟨j, hj⟩ : ∃ j, (c : ℕ) - P.length = j + 1 := ⟨(c : ℕ) - P.length - 1, by omega⟩
      rw [hj]
      simp

lemma hasse_taylor (a : ℂ) (m : ℕ) (G : ℂ[X]) :
    (hasseDeriv m ((X - C a) ^ m * G)).eval a = G.eval a := by
  rw [← taylor_coeff, taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C]
  simp only [add_sub_cancel_right]
  rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, taylor_coeff_zero]

/-- linearity of det in one column -/
lemma det_updateCol_lin {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) (v : Fin N → ℂ) :
    (A.updateCol j v).det = ∑ k, v k * (A.updateCol j (Pi.single k 1)).det := by
  have hv : v = ∑ k, v k • (Pi.single k (1 : ℂ) : Fin N → ℂ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  have : ∀ s : Finset (Fin N), (A.updateCol j (∑ k ∈ s, v k • (Pi.single k (1:ℂ) : Fin N → ℂ))).det
      = ∑ k ∈ s, v k * (A.updateCol j (Pi.single k 1)).det := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      have : A.updateCol j (0 : Fin N → ℂ) = A.updateCol j ((0:ℂ) • (0 : Fin N → ℂ)) := by simp
      rw [this, det_updateCol_smul]; simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, det_updateCol_add, det_updateCol_smul, ih]
  exact this _

lemma key (N : ℕ) (P Q : List (ℕ → ℂ)) (hlen : P.length < N) (φ : ℕ → ℂ[X]) (a : ℂ) (m : ℕ)
    (G : ℂ[X])
    (h : ∀ t : ℂ, (matOf N (P ++ (fun k => (φ k).eval t) :: Q)).det = ((X - C a) ^ m * G).eval t) :
    (matOf N (P ++ (fun k => (hasseDeriv m (φ k)).eval a) :: Q)).det = G.eval a := by
  set A := matOf N (P ++ (0 : ℕ → ℂ) :: Q)
  set j : Fin N := ⟨P.length, hlen⟩
  have hgen : ∀ v : ℕ → ℂ, (matOf N (P ++ v :: Q)).det =
      ∑ k : Fin N, v k * (A.updateCol j (Pi.single k 1)).det := by
    intro v
    rw [matOf_set N P Q v 0 hlen, det_updateCol_lin]
  set Qp : ℂ[X] := ∑ k : Fin N, C ((A.updateCol j (Pi.single k 1)).det) * φ k
  have hQ : Qp = (X - C a) ^ m * G := by
    apply Polynomial.funext
    intro t
    rw [← h t, hgen]
    simp only [Qp, eval_finsetSum, eval_mul, eval_C]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [hgen, ← hasse_taylor a m G, ← hQ]
  simp only [Qp, map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl; intro k _
  rw [← smul_eq_C_mul, map_smul, eval_smul, smul_eq_mul]; ring


lemma PP_append {α : Type} (g : α → α → ℂ) (L1 L2 : List α) :
    PP g (L1 ++ L2) = PP g L1 * PP g L2 * (L1.map (fun x => (L2.map (g x)).prod)).prod := by
  induction L1 with
  | nil => simp [PP]
  | cons x L1 ih =>
    simp only [List.cons_append, PP, ih, List.map_append, List.prod_append, List.map_cons,
      List.prod_cons]
    ring

lemma PP_map {α β : Type} (g : β → β → ℂ) (f : α → β) (L : List α) :
    PP g (L.map f) = PP (fun x y => g (f x) (f y)) L := by
  induction L with
  | nil => simp [PP]
  | cons x L ih => simp [PP, ih, List.map_map, Function.comp_def]

lemma PP_congr {α : Type} (g g' : α → α → ℂ) (L : List α) (h : ∀ x y, g x y = g' x y) :
    PP g L = PP g' L := by
  have : g = g' := funext fun x => funext fun y => h x y
  rw [this]

lemma PP_eq_fin {α : Type} (g : α → α → ℂ) (L : List α) :
    PP g L = ∏ i : Fin L.length, ∏ j ∈ Finset.Ioi i, g L[i.1] L[j.1] := by
  induction L with
  | nil => simp [PP]
  | cons x L ih =>
    show PP g (x :: L) = ∏ i : Fin (L.length + 1), ∏ j ∈ Finset.Ioi i, g (x :: L)[i.1] (x :: L)[j.1]
    rw [Fin.prod_univ_succ]
    simp only [Fin.Ioi_zero_eq_map, Finset.prod_map, Fin.coe_succEmb,
      Fin.prod_Ioi_succ, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
      List.getElem_cons_succ, Fin.prod_univ_fun_getElem]
    rw [PP, ih]


lemma PP_eq_fin' {α : Type} (g : α → α → ℂ) (d : α) (L : List α) (n : ℕ) (hn : L.length = n) :
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, g (L.getD i d) (L.getD j d) = PP g L := by
  subst hn
  rw [PP_eq_fin]
  simp [List.getD_eq_getElem]

lemma colsA_one (A : List ℂ) : colsA (A.map (·, 1)) = A.map (fun z k => z ^ k * (1:ℂ) ^ 0) := by
  induction A with
  | nil => simp [colsA]
  | cons z A ih =>
    simp only [colsA, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    simp only [List.range_one, List.map_cons, List.map_nil, List.singleton_append]
    congr 1
    funext k; simp [colA]

lemma colsB_one (N : ℕ) (B : List ℂ) :
    colsB N (B.map (·, 1)) = B.map (fun w k => (1:ℂ) ^ k * w ^ (N - 1 - k)) := by
  induction B with
  | nil => simp [colsB]
  | cons w B ih =>
    simp only [colsB, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    simp only [List.range_one, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.map_cons, List.map_nil, List.singleton_append]
    congr 1
    funext k; simp [colB]

lemma base (A B : List ℂ) (N : ℕ) (hN : N = A.length + B.length) :
    (matOf N (colsA (A.map (·, 1)) ++ colsB N (B.map (·, 1)))).det =
      PP gA (A.map (·, 1)) * Cr (A.map (·, 1)) (B.map (·, 1)) * PP gB (B.map (·, 1)) := by
  set pts : List (ℂ × ℂ) := A.map (fun z => (z, 1)) ++ B.map (fun w => (1, w)) with hpts
  have hlen : pts.length = N := by simp [pts, hN]
  set F : ℂ × ℂ → ℕ → ℂ := fun p k => p.1 ^ k * p.2 ^ (N - 1 - k)
  have h1 : colsA (A.map (·, 1)) ++ colsB N (B.map (·, 1)) = pts.map F := by
    rw [colsA_one, colsB_one]
    simp [pts, F, Function.comp_def]
  set v : Fin N → ℂ := fun i => (pts.getD i (0, 0)).1
  set w : Fin N → ℂ := fun i => (pts.getD i (0, 0)).2
  have h2 : matOf N (pts.map F) = (projVandermonde v w).transpose := by
    ext k c
    have hc : (c : ℕ) < pts.length := by rw [hlen]; exact c.2
    simp only [matOf, of_apply, transpose_apply, projVandermonde, rectVandermonde, v, w, F,
      List.getD_eq_getElem _ _ hc, Fin.val_rev]
    rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map]
    congr 2
    omega
  rw [h1, h2, det_transpose, det_projVandermonde]
  have h3 := PP_eq_fin' (fun p q : ℂ × ℂ => q.1 * p.2 - p.1 * q.2) (0, 0) pts N hlen
  rw [h3, hpts, PP_append, PP_map, PP_map, PP_map, PP_map, mul_right_comm]
  congr 1
  · congr 1
    · apply PP_congr; intro x y; simp [gA]
    · simp [Cr, Function.comp_def]
  · apply PP_congr; intro x y; simp [gB]


def wt (m : ℕ) : ℕ := if m = 0 then 1 else m - 1
def mu (L : List (ℂ × ℕ)) : ℕ := (L.map (fun e => wt e.2)).sum
def RHS (LA LB : List (ℂ × ℕ)) : ℂ := PP gA LA * Cr LA LB * PP gB LB
def Stmt (N : ℕ) (LA LB : List (ℂ × ℕ)) : Prop :=
  (matOf N (colsA LA ++ colsB N LB)).det = RHS LA LB

lemma Cr_insertL (L1 L2 LB : List (ℂ × ℕ)) (e : ℂ × ℕ) :
    Cr (L1 ++ e :: L2) LB = Cr (L1 ++ L2) LB *
      (LB.map (fun f => (1 - e.1 * f.1) ^ (e.2 * f.2))).prod := by
  simp only [Cr, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  ring

lemma Cr_insertR (LA L1 L2 : List (ℂ × ℕ)) (e : ℂ × ℕ) :
    Cr LA (L1 ++ e :: L2) = Cr LA (L1 ++ L2) *
      (LA.map (fun x => (1 - x.1 * e.1) ^ (x.2 * e.2))).prod := by
  simp only [Cr, ← List.prod_map_mul]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  ring

lemma colsA_append (L1 L2 : List (ℂ × ℕ)) : colsA (L1 ++ L2) = colsA L1 ++ colsA L2 := by
  simp [colsA]

lemma colsA_cons (e : ℂ × ℕ) (L : List (ℂ × ℕ)) :
    colsA (e :: L) = (List.range e.2).map (colA e.1) ++ colsA L := by
  simp [colsA]

lemma colsB_append (N : ℕ) (L1 L2 : List (ℂ × ℕ)) :
    colsB N (L1 ++ L2) = colsB N L1 ++ colsB N L2 := by
  simp [colsB]

lemma colsB_cons (N : ℕ) (e : ℂ × ℕ) (L : List (ℂ × ℕ)) :
    colsB N (e :: L) = (List.range e.2).reverse.map (colB N e.1) ++ colsB N L := by
  simp [colsB]

lemma colA_hasse (z : ℂ) (m : ℕ) :
    colA z m = fun k => (hasseDeriv m ((X : ℂ[X]) ^ k)).eval z := by
  funext k
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial]
  simp [colA]

lemma colB_hasse (N : ℕ) (z : ℂ) (m : ℕ) :
    colB N z m = fun k => (hasseDeriv m ((X : ℂ[X]) ^ (N - 1 - k))).eval z := by
  funext k
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial]
  simp [colB]

lemma colA_zero (t : ℂ) : colA t 0 = fun k => ((X : ℂ[X]) ^ k).eval t := by
  funext k; simp [colA]

lemma colB_zero (N : ℕ) (t : ℂ) : colB N t 0 = fun k => ((X : ℂ[X]) ^ (N - 1 - k)).eval t := by
  funext k; simp [colB]

lemma prod_map_pow_add {α : Type} (L : List α) (f : α → ℂ) (a b c : α → ℕ)
    (h : ∀ x, a x = b x + c x) :
    (L.map (fun x => f x ^ a x)).prod =
      (L.map (fun x => f x ^ b x)).prod * (L.map (fun x => f x ^ c x)).prod := by
  rw [← List.prod_map_mul]
  congr 1
  apply List.map_congr_left
  intro x _
  rw [h, pow_add]

lemma zeroA (N : ℕ) (L1 L2 LB : List (ℂ × ℕ)) (z : ℂ) (h : Stmt N (L1 ++ L2) LB) :
    Stmt N (L1 ++ (z, 0) :: L2) LB := by
  unfold Stmt RHS at *
  rw [colsA_append, colsA_cons] at *
  simp only [List.range_zero, List.map_nil, List.nil_append]
  rw [h, PP_insert, Cr_insertL]
  have : gA (z, 0) = fun _ => 1 := by funext y; simp [gA]
  simp [this, gA]

lemma zeroB (N : ℕ) (LA L1 L2 : List (ℂ × ℕ)) (z : ℂ) (h : Stmt N LA (L1 ++ L2)) :
    Stmt N LA (L1 ++ (z, 0) :: L2) := by
  unfold Stmt RHS at *
  rw [colsB_append, colsB_cons] at *
  simp only [List.range_zero, List.reverse_nil, List.map_nil, List.nil_append]
  rw [h, PP_insert, Cr_insertR]
  have : gB (z, 0) = fun _ => 1 := by funext y; simp [gB]
  simp [this, gB]

lemma splitA (N : ℕ) (L1 L2 LB : List (ℂ × ℕ)) (z : ℂ) (m : ℕ)
    (hN : N = msum (L1 ++ (z, m + 2) :: L2) + msum LB)
    (h : ∀ t : ℂ, Stmt N (L1 ++ (z, m + 1) :: (t, 1) :: L2) LB) :
    Stmt N (L1 ++ (z, m + 2) :: L2) LB := by
  set P := colsA L1 ++ (List.range (m + 1)).map (colA z)
  set Q := colsA L2 ++ colsB N LB
  have hP : P.length < N := by
    simp [P, hN, length_colsA, msum]
    omega
  have hc : colsA (L1 ++ (z, m + 2) :: L2) ++ colsB N LB = P ++ colA z (m + 1) :: Q := by
    simp only [P, Q, colsA_append, colsA_cons, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  have hc' : ∀ t, colsA (L1 ++ (z, m + 1) :: (t, 1) :: L2) ++ colsB N LB = P ++ colA t 0 :: Q := by
    intro t
    simp only [P, Q, colsA_append, colsA_cons, List.range_one, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  set G : ℂ[X] := C (RHS (L1 ++ (z, m + 1) :: L2) LB) *
    (L1.map (fun x => (X - C x.1) ^ x.2)).prod * (L2.map (fun y => (C y.1 - X) ^ y.2)).prod *
    (LB.map (fun f => (1 - X * C f.1) ^ f.2)).prod
  unfold Stmt
  rw [hc, colA_hasse]
  rw [key N P Q hP (fun k => X ^ k) z (m + 1) G]
  · simp only [G, RHS, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_list_prod, List.map_map,
      Function.comp_def, eval_one, PP_insert, Cr_insertL]
    have hg1 : gA (z, m + 2) = fun y => (y.1 - z) ^ ((m + 1) * y.2 + y.2) := by
      funext y; simp only [gA]; ring_nf
    have hg2 : gA (z, m + 1) = fun y => (y.1 - z) ^ ((m + 1) * y.2) := by
      funext y; simp only [gA]
    rw [hg1, hg2]
    simp only [gA]
    rw [prod_map_pow_add L1 (fun x => z - x.1) (fun x => x.2 * (m + 2)) (fun x => x.2 * (m + 1))
      (fun x => x.2) (by intro x; ring)]
    rw [prod_map_pow_add L2 (fun x => x.1 - z) (fun x => (m + 1) * x.2 + x.2)
      (fun x => (m + 1) * x.2) (fun x => x.2) (by intro x; ring)]
    rw [prod_map_pow_add LB (fun x => 1 - z * x.1) (fun x => (m + 2) * x.2)
      (fun x => (m + 1) * x.2) (fun x => x.2) (by intro x; ring)]
    ring
  · intro t
    have := h t
    unfold Stmt at this
    rw [hc', colA_zero] at this
    rw [this]
    have e1 : L1 ++ (z, m + 1) :: (t, 1) :: L2 = (L1 ++ [(z, m + 1)]) ++ (t, 1) :: L2 := by simp
    have e2 : (L1 ++ [(z, m + 1)]) ++ L2 = L1 ++ (z, m + 1) :: L2 := by simp
    unfold RHS
    rw [e1, PP_insert, Cr_insertL, e2]
    have hg : gA (t, 1) = fun y => (y.1 - t) ^ y.2 := by funext y; simp [gA]
    rw [hg]
    simp only [G, RHS, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_list_prod, List.map_map,
      Function.comp_def, eval_one, List.map_append, List.prod_append, gA, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul]
    ring


lemma splitB (N : ℕ) (LA L1 L2 : List (ℂ × ℕ)) (w : ℂ) (m : ℕ)
    (hN : N = msum LA + msum (L1 ++ (w, m + 2) :: L2))
    (h : ∀ t : ℂ, Stmt N LA (L1 ++ (t, 1) :: (w, m + 1) :: L2)) :
    Stmt N LA (L1 ++ (w, m + 2) :: L2) := by
  set P := colsA LA ++ colsB N L1
  set Q := (List.range (m + 1)).reverse.map (colB N w) ++ colsB N L2
  have hP : P.length < N := by
    simp [P, hN, length_colsA, length_colsB, msum]
  have hc : colsA LA ++ colsB N (L1 ++ (w, m + 2) :: L2) = P ++ colB N w (m + 1) :: Q := by
    simp only [P, Q, colsB_append, colsB_cons, List.range_succ (n := m + 1), List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append, List.cons_append]
  have hc' : ∀ t, colsA LA ++ colsB N (L1 ++ (t, 1) :: (w, m + 1) :: L2) =
      P ++ colB N t 0 :: Q := by
    intro t
    simp only [P, Q, colsB_append, colsB_cons, List.range_one, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append, List.cons_append]
  set G : ℂ[X] := C (RHS LA (L1 ++ (w, m + 1) :: L2)) *
    (L1.map (fun x => (C x.1 - X) ^ x.2)).prod * (L2.map (fun y => (X - C y.1) ^ y.2)).prod *
    (LA.map (fun f => (1 - C f.1 * X) ^ f.2)).prod
  unfold Stmt
  rw [hc, colB_hasse]
  rw [key N P Q hP (fun k => X ^ (N - 1 - k)) w (m + 1) G]
  · simp only [G, RHS, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_list_prod, List.map_map,
      Function.comp_def, eval_one, PP_insert, Cr_insertR]
    have hg1 : gB (w, m + 2) = fun y => (w - y.1) ^ ((m + 1) * y.2 + y.2) := by
      funext y; simp only [gB]; ring_nf
    have hg2 : gB (w, m + 1) = fun y => (w - y.1) ^ ((m + 1) * y.2) := by
      funext y; simp only [gB]
    rw [hg1, hg2]
    simp only [gB]
    rw [prod_map_pow_add L1 (fun x => x.1 - w) (fun x => x.2 * (m + 2)) (fun x => x.2 * (m + 1))
      (fun x => x.2) (by intro x; ring)]
    rw [prod_map_pow_add L2 (fun x => w - x.1) (fun x => (m + 1) * x.2 + x.2)
      (fun x => (m + 1) * x.2) (fun x => x.2) (by intro x; ring)]
    rw [prod_map_pow_add LA (fun x => 1 - x.1 * w) (fun x => x.2 * (m + 2))
      (fun x => x.2 * (m + 1)) (fun x => x.2) (by intro x; ring)]
    ring
  · intro t
    have := h t
    unfold Stmt at this
    rw [hc', colB_zero] at this
    rw [this]
    unfold RHS
    rw [PP_insert, Cr_insertR]
    have hg : gB (t, 1) = fun y => (t - y.1) ^ y.2 := by funext y; simp [gB]
    rw [hg]
    simp only [G, RHS, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_list_prod, List.map_map,
      Function.comp_def, eval_one, List.map_append, List.prod_append, gB, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul]
    ring


lemma mu_ins (L1 L2 : List (ℂ × ℕ)) (e : ℂ × ℕ) : mu (L1 ++ e :: L2) = mu L1 + wt e.2 + mu L2 := by
  simp [mu]; ring
lemma mu_app (L1 L2 : List (ℂ × ℕ)) : mu (L1 ++ L2) = mu L1 + mu L2 := by
  simp [mu]
lemma msum_ins (L1 L2 : List (ℂ × ℕ)) (e : ℂ × ℕ) :
    msum (L1 ++ e :: L2) = msum L1 + e.2 + msum L2 := by
  simp [msum]; ring
lemma msum_app (L1 L2 : List (ℂ × ℕ)) : msum (L1 ++ L2) = msum L1 + msum L2 := by
  simp [msum]

lemma all_one (L : List (ℂ × ℕ)) (h : ∀ e ∈ L, e.2 = 1) :
    L = (L.map Prod.fst).map (·, 1) := by
  rw [List.map_map]
  conv_lhs => rw [← List.map_id L]
  apply List.map_congr_left
  intro e he
  ext <;> simp [h e he]

lemma msum_one (A : List ℂ) : msum (A.map (·, 1)) = A.length := by
  induction A with
  | nil => simp [msum]
  | cons a A ih => simp_all [msum]; ring

theorem main_list : ∀ (n : ℕ) (LA LB : List (ℂ × ℕ)), mu LA + mu LB = n →
    ∀ N, N = msum LA + msum LB → Stmt N LA LB := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro LA LB hmu N hN
  by_cases hA : ∃ e ∈ LA, e.2 ≠ 1
  · obtain ⟨e, he, hne⟩ := hA
    obtain ⟨L1, L2, rfl⟩ := List.append_of_mem he
    rcases e with ⟨z, m⟩
    rcases m with _ | _ | m
    · apply zeroA
      rw [mu_ins] at hmu
      refine ih (mu (L1 ++ L2) + mu LB) ?_ _ _ rfl N ?_
      · rw [mu_app]; simp [wt] at hmu; omega
      · rw [hN, msum_ins, msum_app]; simp
    · exact absurd rfl hne
    · apply splitA N L1 L2 LB z m hN
      intro t
      rw [mu_ins] at hmu
      refine ih (mu (L1 ++ (z, m + 1) :: (t, 1) :: L2) + mu LB) ?_ _ _ rfl N ?_
      · have : mu (L1 ++ (z, m + 1) :: (t, 1) :: L2) = mu L1 + m + mu L2 := by
          rw [mu_ins]; simp [mu, wt] <;> ring
        rw [this]; simp [wt] at hmu; omega
      · rw [hN, msum_ins, msum_ins]; simp [msum]; ring
  by_cases hB : ∃ e ∈ LB, e.2 ≠ 1
  · obtain ⟨e, he, hne⟩ := hB
    obtain ⟨L1, L2, rfl⟩ := List.append_of_mem he
    rcases e with ⟨z, m⟩
    rcases m with _ | _ | m
    · apply zeroB
      rw [mu_ins] at hmu
      refine ih (mu LA + mu (L1 ++ L2)) ?_ _ _ rfl N ?_
      · rw [mu_app]; simp [wt] at hmu; omega
      · rw [hN, msum_ins, msum_app]; simp
    · exact absurd rfl hne
    · apply splitB N LA L1 L2 z m hN
      intro t
      rw [mu_ins] at hmu
      refine ih (mu LA + mu (L1 ++ (t, 1) :: (z, m + 1) :: L2)) ?_ _ _ rfl N ?_
      · have : mu (L1 ++ (t, 1) :: (z, m + 1) :: L2) = mu L1 + m + mu L2 := by
          rw [mu_ins]; simp [mu, wt] <;> ring
        rw [this]; simp [wt] at hmu; omega
      · rw [hN, msum_ins, msum_ins]; simp [msum]; ring
  simp only [not_exists, not_and, not_not] at hA hB
  rw [all_one LA hA, all_one LB hB] at hN ⊢
  unfold Stmt RHS
  apply base
  rw [hN, msum_one, msum_one]


lemma flat_getD {β : Type} (d : β) : ∀ (n : ℕ) (F : Fin n → List β) (i : Fin n) (τ : ℕ),
    τ < (F i).length →
    (List.ofFn F).flatten.getD (∑ j : Fin i, (F (Fin.castLE i.2.le j)).length + τ) d =
      (F i).getD τ d := by
  intro n
  induction n with
  | zero => intro F i; exact i.elim0
  | succ n ih =>
    intro F i τ hτ
    rw [List.ofFn_succ, List.flatten_cons]
    rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨i', rfl⟩
    · subst h0
      rw [Finset.sum_eq_zero (fun j _ => absurd j.2 (by simp)), zero_add,
        List.getD_append _ _ _ _ hτ]
    · have hs : ∑ j : Fin (i'.succ : ℕ), (F (Fin.castLE i'.succ.2.le j)).length =
          (F 0).length + ∑ j : Fin i', (F (Fin.castLE i'.2.le j).succ).length := by
        simp only [Fin.val_succ]
        rw [Fin.sum_univ_succ]
        congr 1
      rw [hs, add_assoc, List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.add_sub_cancel_left]
      exact ih (fun j => F j.succ) i' τ hτ


open LearnDoFrontier.TwoAction in
lemma Ymat_eq {dA dB : ℕ} (zA : Fin dA → ℂ) (mA : Fin dA → ℕ) (zB : Fin dB → ℂ)
    (mB : Fin dB → ℕ) :
    Ymat zA mA zB mB = matOf (∑ i, mA i + ∑ j, mB j)
      (colsA (List.ofFn fun i => (zA i, mA i)) ++
        colsB (∑ i, mA i + ∑ j, mB j) (List.ofFn fun j => (zB j, mB j))) := by
  set N := ∑ i, mA i + ∑ j, mB j with hN
  have hA : colsA (List.ofFn fun i => (zA i, mA i)) =
      (List.ofFn (fun i => (List.range (mA i)).map (colA (zA i)))).flatten := by
    simp [colsA, List.flatMap_def, List.map_ofFn, Function.comp_def]
  have hB : colsB N (List.ofFn fun j => (zB j, mB j)) =
      (List.ofFn (fun j => (List.range (mB j)).reverse.map (colB N (zB j)))).flatten := by
    simp [colsB, List.flatMap_def, List.map_ofFn, Function.comp_def]
  have hlenA : (colsA (List.ofFn fun i => (zA i, mA i))).length = ∑ i, mA i := by
    rw [length_colsA]; simp [msum, List.sum_ofFn, Function.comp_def]
  ext k c
  obtain ⟨x, rfl⟩ := (colEquiv mA mB).surjective c
  simp only [Ymat, of_apply, Equiv.symm_apply_apply, matOf]
  rcases x with p | p
  · have hv : ((colEquiv mA mB (Sum.inl p) : Fin N) : ℕ) = (finSigmaFinEquiv p : ℕ) := by
      simp [colEquiv]
    have hlt : (finSigmaFinEquiv p : ℕ) < (colsA (List.ofFn fun i => (zA i, mA i))).length := by
      rw [hlenA]; exact (finSigmaFinEquiv p).2
    have hf := flat_getD 0 dA (fun i => (List.range (mA i)).map (colA (zA i))) p.1 p.2 (by simp)
    simp only [List.length_map, List.length_range] at hf
    rw [hv, List.getD_append _ _ _ _ hlt, hA, finSigmaFinEquiv_apply, hf]
    simp [YBlocks, colA]
  · have hv : ((colEquiv mA mB (Sum.inr p) : Fin N) : ℕ) =
        ∑ i, mA i + (finSigmaFinEquiv p : ℕ) := by
      simp [colEquiv]
    have hf := flat_getD 0 dB (fun j => (List.range (mB j)).reverse.map (colB N (zB j))) p.1 p.2
      (by simp)
    simp only [List.length_map, List.length_reverse, List.length_range] at hf
    rw [hv, List.getD_append_right _ _ _ _ (by omega), hlenA, Nat.add_sub_cancel_left, hB,
      finSigmaFinEquiv_apply, hf]
    have hp := p.2.2
    simp [YBlocks, colB, Fin.val_rev, N]
    have e : mB p.fst - (↑p.snd + 1) = mB p.fst - 1 - ↑p.snd := by omega
    rw [e]


open LearnDoFrontier.TwoAction in
theorem Ymat_det {dA dB : ℕ} (zA : Fin dA → ℂ) (mA : Fin dA → ℕ) (zB : Fin dB → ℂ)
    (mB : Fin dB → ℕ) : (Ymat zA mA zB mB).det = detFormula zA mA zB mB := by
  rw [Ymat_eq]
  have := main_list _ (List.ofFn fun i => (zA i, mA i)) (List.ofFn fun j => (zB j, mB j)) rfl
    (∑ i, mA i + ∑ j, mB j) (by simp [msum, List.sum_ofFn, Function.comp_def])
  unfold Stmt RHS at this
  rw [this, detFormula]
  congr 1
  · congr 1
    · rw [← PP_eq_fin' gA (0, 0) _ dA (by simp)]
      apply Finset.prod_congr rfl; intro i _; apply Finset.prod_congr rfl; intro l _
      simp [gA, List.getD_eq_getElem]
    · simp [Cr, List.map_ofFn, List.prod_ofFn, Function.comp_def]
  · rw [← PP_eq_fin' gB (0, 0) _ dB (by simp)]
    apply Finset.prod_congr rfl; intro i _; apply Finset.prod_congr rfl; intro l _
    simp [gB, List.getD_eq_getElem]

end LDFDet

namespace LDFDet
lemma iteratedDeriv_poly (n : ℕ) : ∀ (p : ℂ[X]),
    iteratedDeriv n (fun x => p.eval x) = fun x => ((derivative)^[n] p).eval x := by
  induction n with
  | zero => intro p; simp
  | succ n ih =>
    intro p
    rw [iteratedDeriv_succ']
    have : deriv (fun x => p.eval x) = fun x => (derivative p).eval x := by
      funext x; exact Polynomial.deriv p
    rw [this, ih, Function.iterate_succ_apply]
end LDFDet

open LearnDoFrontier.TwoAction in
theorem solution {dA dB : ℕ} (zA : Fin dA → ℂ) (mA : Fin dA → ℕ)
    (zB : Fin dB → ℂ) (mB : Fin dB → ℕ)
    (hzA : Function.Injective zA) (hmA : ∀ i, 1 ≤ mA i)
    (hzB : Function.Injective zB) (hmB : ∀ j, 1 ≤ mB j) (j : Fin dB) (hj : 2 ≤ mB j) :
    (Ymat zA mA zB mB).det =
      iteratedDeriv (mB j - 1) (fun t : ℂ => (Yhat zA mA zB mB j (by omega) t).det) (zB j)
        / ((mB j - 1).factorial : ℂ) := by
  set N := ∑ i, mA i + ∑ j, mB j
  set Y := Ymat zA mA zB mB
  set c := firstBCol mA mB j (by omega)
  set n := mB j - 1
  set d : Fin N → ℂ := fun k => (Y.updateCol c (Pi.single k 1)).det
  set Qp : ℂ[X] := ∑ k : Fin N, C (d k) * X ^ (N - 1 - (k : ℕ))
  have hf : (fun t : ℂ => (Yhat zA mA zB mB j (by omega) t).det) = fun t => Qp.eval t := by
    funext t
    unfold Yhat
    rw [LDFDet.det_updateCol_lin]
    simp only [Qp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    apply Finset.sum_congr rfl; intro k _; ring
  have hit : (derivative)^[n] Qp = n.factorial • hasseDeriv n Qp := by
    rw [← factorial_smul_hasseDeriv]; rfl
  rw [hf, LDFDet.iteratedDeriv_poly]
  rw [hit]
  simp only []
  rw [eval_smul, nsmul_eq_mul]
  have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [mul_div_cancel_left₀ _ hfac]
  have hcol : ∀ k : Fin N, Y k c = (hasseDeriv n ((X : ℂ[X]) ^ (N - 1 - (k : ℕ)))).eval (zB j) := by
    intro k
    rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial]
    simp only [Y, c, Ymat, firstBCol, of_apply, Equiv.symm_apply_apply, YBlocks, eval_monomial,
      mul_one, Fin.val_rev]
    simp [n, N]
  have hY : Y = Y.updateCol c (fun k => Y k c) := by
    ext k l
    by_cases hl : l = c
    · subst hl; simp
    · simp [hl]
  conv_lhs => rw [hY]
  rw [LDFDet.det_updateCol_lin]
  simp only [Qp, map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl; intro k _
  rw [hcol, ← smul_eq_C_mul, map_smul, eval_smul, smul_eq_mul]
  ring
