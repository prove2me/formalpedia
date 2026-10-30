-- Prove2me | solution 1 for LearnDoFrontier.TwoAction.thm3_decay_selects_unit_roots
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:18:16.094656+00:00
-- url     : https://prove2.me/submissions/0070e8d3-c2df-4b96-8802-48d506a56662

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra
import Definitions.Def_LearnDoFrontier_TwoAction_Model

section Part0

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
open LearnDoFrontier.TwoAction in
lemma GVM_eq {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ) :
    GVM z m = matOf (∑ i, m i) (colsA (List.ofFn fun i => (z i, m i)) ++
      colsB (∑ i, m i) []) := by
  have hA : colsA (List.ofFn fun i => (z i, m i)) =
      (List.ofFn (fun i => (List.range (m i)).map (colA (z i)))).flatten := by
    simp [colsA, List.flatMap_def, List.map_ofFn, Function.comp_def]
  ext k c
  set p := (finSigmaFinEquiv (n := m)).symm c with hp
  have hc : (c : ℕ) = (finSigmaFinEquiv p : ℕ) := by simp [p]
  simp only [GVM, of_apply, matOf, colsB, List.flatMap_nil, List.append_nil]
  rw [← hp]
  have hf := flat_getD 0 r (fun i => (List.range (m i)).map (colA (z i))) p.1 p.2 (by simp)
  simp only [List.length_map, List.length_range] at hf
  rw [hc, hA, finSigmaFinEquiv_apply, hf]
  simp [colA]
end LDFDet


open LearnDoFrontier.TwoAction in
theorem LDFDet.GVM_det {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ) :
    (GVM z m).det = ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (z j - z i) ^ (m j * m i) := by
  rw [LDFDet.GVM_eq]
  have := LDFDet.main_list _ (List.ofFn fun i => (z i, m i)) [] rfl (∑ i, m i)
    (by simp [LDFDet.msum, List.sum_ofFn, Function.comp_def])
  unfold LDFDet.Stmt LDFDet.RHS at this
  rw [this]
  simp only [LDFDet.Cr, LDFDet.PP, List.map_nil, List.prod_nil, List.map_const',
    List.prod_replicate, one_pow, mul_one]
  rw [← LDFDet.PP_eq_fin' LDFDet.gA (0, 0) _ r (by simp)]
  apply Finset.prod_congr rfl; intro i _; apply Finset.prod_congr rfl; intro l _
  simp [LDFDet.gA, mul_comm]

open LearnDoFrontier.TwoAction in
theorem LDFDet.GVM_det_ne {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ) (hz : Function.Injective z) :
    (GVM z m).det ≠ 0 := by
  rw [LDFDet.GVM_det]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun l hl => ?_
  refine pow_ne_zero _ (sub_ne_zero.mpr fun h => ?_)
  have := hz h
  simp only [Finset.mem_Ioi] at hl
  exact absurd this (ne_of_gt hl)

end Part0

section Part1

open Polynomial Filter Topology

namespace LDFBVP

noncomputable def S : Module.End ℂ (ℕ → ℂ) := LinearMap.funLeft ℂ ℂ (fun k : ℕ => k + 1)

lemma S_pow_apply (i : ℕ) (x : ℕ → ℂ) (k : ℕ) : ((S ^ i) x) k = x (k + i) := by
  induction i generalizing k with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply]
    have : (S ((S ^ i) x)) k = ((S ^ i) x) (k + 1) := rfl
    rw [this, ih]
    ring_nf

lemma app_eq (p : ℂ[X]) (x : ℕ → ℂ) (k : ℕ) :
    (aeval S p x) k = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x (k + i) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.smul_apply, Pi.smul_apply, S_pow_apply, smul_eq_mul]

lemma app_trinom (N nb : ℕ) (c d : ℂ) (x : ℕ → ℂ) (k : ℕ) :
    (aeval S (X ^ N - C c * X ^ nb + C d) x) k = x (k + N) - c * x (k + nb) + d * x k := by
  simp only [map_add, map_sub, map_mul, aeval_X_pow, aeval_C, LinearMap.add_apply,
    LinearMap.sub_apply, Module.End.mul_apply, Pi.add_apply, Pi.sub_apply, S_pow_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply,
    smul_eq_mul]

lemma app_tendsto (p : ℂ[X]) (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (aeval S p x) atTop (𝓝 0) := by
  have : aeval S p x = fun k => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x (k + i) := by
    funext k; exact app_eq p x k
  rw [this]
  have := tendsto_finsetSum (Finset.range (p.natDegree + 1)) (fun i _ =>
    (hx.comp (tendsto_add_atTop_nat i)).const_mul (p.coeff i))
  simpa using this

/-- a sequence killed by `S - a` with `‖a‖ ≥ 1` and tending to zero vanishes -/
lemma kill_one (a : ℂ) (ha : 1 ≤ ‖a‖) (w : ℕ → ℂ) (hw : Tendsto w atTop (𝓝 0))
    (h : aeval S (X - C a) w = 0) : w = 0 := by
  have hrec : ∀ k, w (k + 1) = a * w k := by
    intro k
    have := congrFun h k
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Pi.sub_apply,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [S, LinearMap.funLeft_apply] at this
    linear_combination this
  have hform : ∀ k, w k = a ^ k * w 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [hrec, ih]; ring
  have h0 : w 0 = 0 := by
    have hn : Tendsto (fun k => ‖w k‖) atTop (𝓝 0) := by simpa using hw.norm
    have hge : ∀ k, ‖w 0‖ ≤ ‖w k‖ := by
      intro k
      rw [hform k, norm_mul, norm_pow]
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ ha)
    have : ‖w 0‖ ≤ 0 := ge_of_tendsto' hn hge
    exact norm_le_zero_iff.mp this
  funext k
  rw [hform k, h0, mul_zero]
  rfl

lemma kill (s : Multiset ℂ) (hs : ∀ a ∈ s, 1 ≤ ‖a‖) (u : ℕ → ℂ)
    (hu : Tendsto u atTop (𝓝 0)) (h : aeval S (s.map (fun a => X - C a)).prod u = 0) :
    u = 0 := by
  induction s using Multiset.induction_on generalizing u with
  | empty => simpa using h
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_apply] at h
    have hw := kill_one a (hs a (Multiset.mem_cons_self a t)) _ (app_tendsto _ u hu) h
    exact ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb)) u hu hw

/-- uniqueness from initial values for a monic polynomial -/
lemma init_zero (g : ℂ[X]) (hg : g.Monic) (u : ℕ → ℂ) (hu : aeval S g u = 0)
    (h0 : ∀ k < g.natDegree, u k = 0) : u = 0 := by
  funext k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  by_cases hk : k < g.natDegree
  · exact h0 k hk
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + g.natDegree := ⟨k - g.natDegree, by omega⟩
    have := app_eq g u j
    rw [hu, Finset.sum_range_succ, hg.coeff_natDegree, one_mul] at this
    have hs : ∑ i ∈ Finset.range g.natDegree, g.coeff i * u (j + i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rw [ih (j + i) (by omega)]; simp
    simp only [Pi.zero_apply] at this ⊢
    rw [hs, zero_add] at this
    exact this.symm


noncomputable def bas (z : ℂ) (τ : ℕ) : ℕ → ℂ := fun k => (k.choose τ : ℂ) * z ^ (k - τ)

lemma hasse_eval_pow (m τ : ℕ) (z : ℂ) :
    (hasseDeriv τ ((X : ℂ[X]) ^ m)).eval z = (m.choose τ : ℂ) * z ^ (m - τ) := by
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial]
  simp

lemma hasse_dvd_eval (q : ℂ[X]) (z : ℂ) (τ : ℕ) (h : (X - C z) ^ (τ + 1) ∣ q) :
    (hasseDeriv τ q).eval z = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [← taylor_coeff, taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C]
  simp only [add_sub_cancel_right]
  rw [coeff_X_pow_mul', if_neg (by omega)]

lemma bas_kill (p : ℂ[X]) (z : ℂ) (τ : ℕ) (hdvd : (X - C z) ^ (τ + 1) ∣ p) :
    aeval S p (bas z τ) = 0 := by
  funext k
  rw [app_eq]
  have hexp : (X : ℂ[X]) ^ k * p =
      ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ (k + i) := by
    conv_lhs => rw [as_sum_range_C_mul_X_pow p]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  have h0 := hasse_dvd_eval (X ^ k * p) z τ (dvd_mul_of_dvd_right hdvd _)
  rw [hexp, map_sum, eval_finsetSum] at h0
  simp only [Pi.zero_apply]
  rw [← h0]
  apply Finset.sum_congr rfl; intro i _
  rw [← smul_eq_C_mul, map_smul, eval_smul, smul_eq_mul, hasse_eval_pow, bas]

lemma bas_tendsto (z : ℂ) (hz : ‖z‖ < 1) (τ : ℕ) : Tendsto (bas z τ) atTop (𝓝 0) := by
  by_cases h0 : z = 0
  · apply tendsto_nhds_of_eventually_eq
    rw [eventually_atTop]
    refine ⟨τ + 1, fun k hk => ?_⟩
    simp [bas, h0, zero_pow (show k - τ ≠ 0 by omega)]
  · have hr : 0 < ‖z‖ := norm_pos_iff.mpr h0
    have hlim := (tendsto_pow_const_mul_const_pow_of_abs_lt_one τ
      (show |‖z‖| < 1 by rwa [abs_of_pos hr])).mul_const ((‖z‖ ^ τ)⁻¹)
    rw [zero_mul] at hlim
    apply squeeze_zero_norm' _ hlim
    rw [eventually_atTop]
    refine ⟨τ, fun k hk => ?_⟩
    simp only [bas, norm_mul, norm_pow, Complex.norm_natCast]
    have hpow : ‖z‖ ^ (k - τ) = ‖z‖ ^ k * (‖z‖ ^ τ)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hr.ne'), ← pow_add, Nat.sub_add_cancel hk]
    rw [hpow, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (pow_nonneg hr.le _))
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr.le _)
    exact_mod_cast Nat.choose_le_pow k τ


open LearnDoFrontier.TwoAction Matrix

lemma rootExp_fun {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ) (a : (Σ i : Fin r, Fin (m i)) → ℂ) :
    (fun k => rootExp z m a k) = ∑ p, a p • bas (z p.1) p.2 := by
  funext k
  simp only [rootExp, Finset.sum_apply, Pi.smul_apply, bas, smul_eq_mul]
  apply Finset.sum_congr rfl; intro p _; ring

lemma rootExp_kill (q : ℂ[X]) {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (a : (Σ i : Fin r, Fin (m i)) → ℂ) (h : ∀ i, (X - C (z i)) ^ (m i) ∣ q) :
    aeval S q (fun k => rootExp z m a k) = 0 := by
  rw [rootExp_fun, map_sum]
  apply Finset.sum_eq_zero
  intro p _
  rw [map_smul, bas_kill q (z p.1) p.2 ((pow_dvd_pow _ (by omega)).trans (h p.1)), smul_zero]

lemma rootExp_tendsto {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (a : (Σ i : Fin r, Fin (m i)) → ℂ) (h : ∀ i, ‖z i‖ < 1) :
    Tendsto (fun k => rootExp z m a k) atTop (𝓝 0) := by
  rw [rootExp_fun]
  have := tendsto_finsetSum (Finset.univ : Finset (Σ i : Fin r, Fin (m i)))
    (fun p _ => (bas_tendsto (z p.1) (h p.1) p.2).const_smul (a p))
  simp only [smul_zero, Finset.sum_const_zero] at this
  convert this using 1
  funext k
  simp [Finset.sum_apply]

def revE {dB : ℕ} (mB : Fin dB → ℕ) : (Σ j : Fin dB, Fin (mB j)) ≃ (Σ j : Fin dB, Fin (mB j)) :=
  ⟨fun p => ⟨p.1, Fin.rev p.2⟩, fun p => ⟨p.1, Fin.rev p.2⟩, fun p => by simp, fun p => by simp⟩

lemma Ymat_mulVec {dA dB : ℕ} (zA : Fin dA → ℂ) (mA : Fin dA → ℕ) (zB : Fin dB → ℂ)
    (mB : Fin dB → ℕ) (v : Fin (∑ i, mA i + ∑ j, mB j) → ℂ) (k : Fin (∑ i, mA i + ∑ j, mB j)) :
    (Ymat zA mA zB mB *ᵥ v) k =
      rootExp zA mA (fun p => v (colEquiv mA mB (Sum.inl p))) k -
      rootExp zB mB (fun p => -v (colEquiv mA mB (Sum.inr ⟨p.1, Fin.rev p.2⟩)))
        (∑ i, mA i + ∑ j, mB j - 1 - k) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← (colEquiv mA mB).sum_comp, Fintype.sum_sum_type]
  simp only [Ymat, Matrix.of_apply, Equiv.symm_apply_apply, YBlocks]
  rw [sub_eq_add_neg]
  congr 1
  · simp only [rootExp]
    apply Finset.sum_congr rfl; intro p _; ring
  · simp only [rootExp, ← Finset.sum_neg_distrib]
    rw [← (revE mB).sum_comp]
    apply Finset.sum_congr rfl; intro p _
    have hp := p.2.2
    have h2 : mB p.fst - (mB p.fst - ((p.snd : ℕ) + 1) + 1) = p.snd := by omega
    simp only [revE, Equiv.coe_fn_mk, Fin.rev_rev, Fin.val_rev, h2]
    ring

lemma GVM_mulVec {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ) (a : Fin (∑ i, m i) → ℂ)
    (k : Fin (∑ i, m i)) :
    (GVM z m *ᵥ a) k = rootExp z m (fun p => a (finSigmaFinEquiv p)) k := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← (finSigmaFinEquiv (n := m)).sum_comp]
  simp only [GVM, Matrix.of_apply, rootExp]
  apply Finset.sum_congr rfl; intro p _
  erw [Equiv.symm_apply_apply]
  ring


lemma factor (f : ℂ[X]) (hf : f.Monic) :
    f = ((f.roots.filter (fun a => ¬ ‖a‖ < 1)).map (fun a => X - C a)).prod *
      ((f.roots.filter (fun a => ‖a‖ < 1)).map (fun a => X - C a)).prod := by
  conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf
    IsAlgClosed.card_roots_eq_natDegree]
  conv_lhs => rw [← Multiset.filter_add_not (fun a : ℂ => ‖a‖ < 1) f.roots]
  rw [Multiset.map_add, Multiset.prod_add, mul_comm]

lemma gIn_eq (f : ℂ[X]) {dA : ℕ} (eA : Fin dA ≃ Zunit f) :
    ((f.roots.filter (fun a => ‖a‖ < 1)).map (fun a => X - C a)).prod =
      ∏ i : Fin dA, (X - C ((eA i : ℂ))) ^ (mult f (eA i)) := by
  classical
  rw [Finset.prod_multiset_map_count, Multiset.toFinset_filter]
  have h1 : ∀ z ∈ f.roots.toFinset.filter (fun a => ‖a‖ < 1),
      (X - C z) ^ (Multiset.count z (f.roots.filter (fun a => ‖a‖ < 1))) =
        (X - C z) ^ (mult f z) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Multiset.count_filter_of_pos (p := fun a : ℂ => ‖a‖ < 1) hz.2, count_roots, mult]
  rw [Finset.prod_congr rfl h1]
  have h2 := Finset.prod_coe_sort (Zunit f) (fun z => (X - C z) ^ (mult f z))
  unfold Zunit at h2 eA
  rw [← h2]
  exact (Equiv.prod_comp eA (fun x => (X - C (x : ℂ)) ^ (mult f x))).symm

lemma homog (f : ℂ[X]) (hf : f.Monic) {dA : ℕ} (eA : Fin dA ≃ Zunit f) (u : ℕ → ℂ)
    (hu : aeval S f u = 0) (hut : Tendsto u atTop (𝓝 0)) :
    ∃ a : (Σ i : Fin dA, Fin (mult f (eA i))) → ℂ,
      ∀ k, u k = rootExp (fun i => (eA i : ℂ)) (fun i => mult f (eA i)) a k := by
  set zA : Fin dA → ℂ := fun i => (eA i : ℂ)
  set mA : Fin dA → ℕ := fun i => mult f (eA i)
  set g : ℂ[X] := ∏ i : Fin dA, (X - C (zA i)) ^ (mA i)
  have hg : aeval S g u = 0 := by
    have hfac := factor f hf
    rw [gIn_eq f eA] at hfac
    rw [hfac, map_mul, Module.End.mul_apply] at hu
    have := kill _ (fun a ha => by
      rw [Multiset.mem_filter] at ha; exact not_lt.mp ha.2) _ (app_tendsto _ u hut) hu
    exact this
  have hgm : g.Monic := monic_prod_of_monic _ _ (fun i _ => (monic_X_sub_C _).pow _)
  have hgd : g.natDegree = ∑ i, mA i := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C _).pow _)]
    simp [natDegree_pow, natDegree_X_sub_C]
  have hinj : Function.Injective zA := fun i j h => eA.injective (Subtype.val_injective h)
  set W := GVM zA mA
  have hW : W.det ≠ 0 := LDFDet.GVM_det_ne zA mA hinj
  set a0 := W⁻¹ *ᵥ (fun c : Fin (∑ i, mA i) => u c)
  have ha0 : W *ᵥ a0 = fun c : Fin (∑ i, mA i) => u c := by
    simp only [a0, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hW), one_mulVec]
  refine ⟨fun p => a0 (finSigmaFinEquiv p), ?_⟩
  have hdiff : (fun k => u k - rootExp zA mA (fun p => a0 (finSigmaFinEquiv p)) k) = 0 := by
    apply init_zero g hgm
    · rw [show (fun k => u k - rootExp zA mA (fun p => a0 (finSigmaFinEquiv p)) k) =
          u - (fun k => rootExp zA mA (fun p => a0 (finSigmaFinEquiv p)) k) from rfl, map_sub, hg,
        rootExp_kill g zA mA _ (fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)), sub_zero]
    · intro k hk
      rw [hgd] at hk
      have := congrFun ha0 (⟨k, hk⟩ : Fin (∑ i, mA i))
      rw [GVM_mulVec] at this
      simp only at this
      rw [this, sub_self]
  intro k
  have := congrFun hdiff k
  simp only [Pi.zero_apply] at this
  exact sub_eq_zero.mp this


def CB (fA fB : ℂ[X]) (NN : ℕ) (K : ℂ) (xA xB : ℕ → ℂ) : Prop :=
  aeval S fA xA = 0 ∧ aeval S fB xB = 0 ∧ (∀ k < NN, xA k - xB (NN - 1 - k) = K) ∧
    Tendsto xA atTop (𝓝 0) ∧ Tendsto xB atTop (𝓝 0)

lemma rootExp_zero {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ) (k : ℕ) :
    rootExp z m (fun _ => 0) k = 0 := by
  simp [rootExp]

lemma zunit_norm (f : ℂ[X]) (z : Zunit f) : ‖(z : ℂ)‖ < 1 := by
  have := z.2
  unfold Zunit at this
  exact (Finset.mem_filter.mp this).2

lemma cb_unique (fA fB : ℂ[X]) (hfA : fA.Monic) (hfB : fB.Monic) (NN : ℕ) (K : ℂ)
    {dA dB : ℕ} (eA : Fin dA ≃ Zunit fA) (eB : Fin dB ≃ Zunit fB)
    (hN : ∑ i, mult fA (eA i) + ∑ j, mult fB (eB j) = NN)
    (hY : (Ymat (fun i => (eA i : ℂ)) (fun i => mult fA (eA i)) (fun j => (eB j : ℂ))
      (fun j => mult fB (eB j))).det ≠ 0)
    (xA xB yA yB : ℕ → ℂ) (hx : CB fA fB NN K xA xB) (hy : CB fA fB NN K yA yB) :
    xA = yA ∧ xB = yB := by
  set zA : Fin dA → ℂ := fun i => (eA i : ℂ)
  set mA : Fin dA → ℕ := fun i => mult fA (eA i)
  set zB : Fin dB → ℂ := fun j => (eB j : ℂ)
  set mB : Fin dB → ℕ := fun j => mult fB (eB j)
  obtain ⟨hxA, hxB, hxb, hxtA, hxtB⟩ := hx
  obtain ⟨hyA, hyB, hyb, hytA, hytB⟩ := hy
  obtain ⟨a, ha⟩ := homog fA hfA eA (xA - yA) (by rw [map_sub, hxA, hyA, sub_zero])
    (by have := hxtA.sub hytA; rw [sub_zero] at this; exact this)
  obtain ⟨b, hb⟩ := homog fB hfB eB (xB - yB) (by rw [map_sub, hxB, hyB, sub_zero])
    (by have := hxtB.sub hytB; rw [sub_zero] at this; exact this)
  set N := ∑ i, mA i + ∑ j, mB j
  set v : Fin N → ℂ := fun c => Sum.elim a (fun q => -b (revE mB q)) ((colEquiv mA mB).symm c)
  have hv : Ymat zA mA zB mB *ᵥ v = 0 := by
    funext k
    rw [Ymat_mulVec]
    simp only [v, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, neg_neg]
    have hrr : ∀ p : (Σ j : Fin dB, Fin (mB j)), revE mB ⟨p.1, Fin.rev p.2⟩ = p := by
      intro p; simp [revE]
    simp only [hrr]
    rw [← ha, ← hb]
    have hk : (k : ℕ) < NN := by rw [← hN]; exact k.2
    have := hxb k hk
    have := hyb k hk
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [show N - 1 - (k : ℕ) = NN - 1 - k by rw [← hN]]
    linear_combination hxb k hk - hyb k hk
  have hv0 := eq_zero_of_mulVec_eq_zero hY hv
  have ha0 : a = fun _ => 0 := by
    funext p
    have := congrFun hv0 (colEquiv mA mB (Sum.inl p))
    simpa [v] using this
  have hb0 : b = fun _ => 0 := by
    funext p
    have := congrFun hv0 (colEquiv mA mB (Sum.inr (revE mB p)))
    have hrr : revE mB (revE mB p) = p := by simp [revE]
    simpa [v, hrr] using this
  constructor
  · funext k
    have := ha k
    rw [ha0, rootExp_zero, Pi.sub_apply, sub_eq_zero] at this
    exact this
  · funext k
    have := hb k
    rw [hb0, rootExp_zero, Pi.sub_apply, sub_eq_zero] at this
    exact this


lemma cb_exists (fA fB : ℂ[X]) (NN : ℕ) (K : ℂ)
    {dA dB : ℕ} (eA : Fin dA ≃ Zunit fA) (eB : Fin dB ≃ Zunit fB)
    (hN : ∑ i, mult fA (eA i) + ∑ j, mult fB (eB j) = NN)
    (hY : (Ymat (fun i => (eA i : ℂ)) (fun i => mult fA (eA i)) (fun j => (eB j : ℂ))
      (fun j => mult fB (eB j))).det ≠ 0) :
    CB fA fB NN K
      (fun k => rootExp (fun i => (eA i : ℂ)) (fun i => mult fA (eA i))
        (fun p => ((Ymat (fun i => (eA i : ℂ)) (fun i => mult fA (eA i)) (fun j => (eB j : ℂ))
          (fun j => mult fB (eB j)))⁻¹ *ᵥ (fun _ => K))
          (colEquiv (fun i => mult fA (eA i)) (fun j => mult fB (eB j)) (Sum.inl p))) k)
      (fun k => rootExp (fun j => (eB j : ℂ)) (fun j => mult fB (eB j))
        (fun p => -((Ymat (fun i => (eA i : ℂ)) (fun i => mult fA (eA i)) (fun j => (eB j : ℂ))
          (fun j => mult fB (eB j)))⁻¹ *ᵥ (fun _ => K))
          (colEquiv (fun i => mult fA (eA i)) (fun j => mult fB (eB j))
            (Sum.inr ⟨p.1, Fin.rev p.2⟩))) k) := by
  set zA : Fin dA → ℂ := fun i => (eA i : ℂ)
  set mA : Fin dA → ℕ := fun i => mult fA (eA i)
  set zB : Fin dB → ℂ := fun j => (eB j : ℂ)
  set mB : Fin dB → ℕ := fun j => mult fB (eB j)
  set Y := Ymat zA mA zB mB
  set α := Y⁻¹ *ᵥ (fun _ => K)
  have hYα : Y *ᵥ α = fun _ => K := by
    simp only [α, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hY), one_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact rootExp_kill fA zA mA _ (fun i => pow_rootMultiplicity_dvd fA (zA i))
  · exact rootExp_kill fB zB mB _ (fun i => pow_rootMultiplicity_dvd fB (zB i))
  · intro k hk
    have hk' : k < ∑ i, mA i + ∑ j, mB j := by rw [hN]; exact hk
    have := congrFun hYα ⟨k, hk'⟩
    rw [Ymat_mulVec] at this
    simp only at this
    rw [show NN - 1 - k = ∑ i, mA i + ∑ j, mB j - 1 - k by rw [hN]]
    exact this
  · exact rootExp_tendsto zA mA _ (fun i => zunit_norm fA (eA i))
  · exact rootExp_tendsto zB mB _ (fun i => zunit_norm fB (eB i))

end LDFBVP

end Part1

section Part2

open Polynomial Filter Topology Matrix

namespace LDFT3
open LDFBVP LearnDoFrontier.TwoAction

lemma k_mul_choose (k s : ℕ) : (k : ℂ) * (k.choose s : ℂ) =
    ((s : ℂ) + 1) * (k.choose (s + 1) : ℂ) + (s : ℂ) * (k.choose s : ℂ) := by
  have h1 := Nat.choose_succ_right_eq k s
  by_cases hks : s ≤ k
  · have : ((k.choose (s + 1) * (s + 1) : ℕ) : ℂ) = ((k.choose s * (k - s) : ℕ) : ℂ) := by
      rw [h1]
    push_cast [Nat.cast_sub hks] at this
    linear_combination -this
  · push Not at hks
    rw [Nat.choose_eq_zero_of_lt hks, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `k^τ = ∑_{s ≤ τ} a_s (k choose s)` with `a_τ = τ!`. -/
lemma pow_choose (τ : ℕ) : ∃ a : ℕ → ℂ, a τ = τ.factorial ∧ (∀ s, τ < s → a s = 0) ∧
    ∀ k : ℕ, (k : ℂ) ^ τ = ∑ s ∈ Finset.range (τ + 1), a s * (k.choose s : ℂ) := by
  induction τ with
  | zero => exact ⟨fun s => if s = 0 then 1 else 0, by simp, fun s hs => by simp; omega,
      fun k => by simp⟩
  | succ τ ih =>
    obtain ⟨a, haτ, hz, ha⟩ := ih
    refine ⟨fun s => (s : ℂ) * a s + (if s = 0 then 0 else (s : ℂ) * a (s - 1)), ?_, ?_, ?_⟩
    · simp only [Nat.add_sub_cancel, haτ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        if_false, hz (τ + 1) (by omega), mul_zero, zero_add, Nat.factorial_succ]
      push_cast; ring
    · intro s hs
      simp only
      rw [hz s (by omega), if_neg (by omega), hz (s - 1) (by omega)]
      simp
    · intro k
      rw [pow_succ, ha k, Finset.sum_mul]
      have e1 : ∀ s ∈ Finset.range (τ + 1), a s * (k.choose s : ℂ) * (k : ℂ) =
          ((s : ℂ) + 1) * a s * (k.choose (s + 1) : ℂ) + (s : ℂ) * a s * (k.choose s : ℂ) := by
        intro s _
        rw [mul_assoc, mul_comm (k.choose s : ℂ), k_mul_choose]; ring
      rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
      have h2 : ∑ s ∈ Finset.range (τ + 1 + 1),
          ((s : ℂ) * a s + (if s = 0 then 0 else (s : ℂ) * a (s - 1))) * (k.choose s : ℂ) =
          ∑ s ∈ Finset.range (τ + 1 + 1), (s : ℂ) * a s * (k.choose s : ℂ) +
          ∑ s ∈ Finset.range (τ + 1 + 1),
            (if s = 0 then 0 else (s : ℂ) * a (s - 1)) * (k.choose s : ℂ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro s _; ring
      have h3 : ∑ s ∈ Finset.range (τ + 1 + 1), (s : ℂ) * a s * (k.choose s : ℂ) =
          ∑ s ∈ Finset.range (τ + 1), (s : ℂ) * a s * (k.choose s : ℂ) := by
        rw [Finset.sum_range_succ, hz (τ + 1) (by omega)]; simp
      have h4 : ∑ s ∈ Finset.range (τ + 1 + 1),
            (if s = 0 then 0 else (s : ℂ) * a (s - 1)) * (k.choose s : ℂ) =
          ∑ s ∈ Finset.range (τ + 1), ((s : ℂ) + 1) * a s * (k.choose (s + 1) : ℂ) := by
        rw [Finset.sum_range_succ']
        simp only [if_true, zero_mul, add_zero, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        apply Finset.sum_congr rfl; intro s _; push_cast; ring
      rw [h2, h3, h4]
      ring


noncomputable def tseq (z : ℂ) (τ : ℕ) : ℕ → ℂ := fun k => (k : ℂ) ^ τ * z ^ k

lemma tseq_eq (z : ℂ) (τ : ℕ) : ∃ a : ℕ → ℂ, a τ = τ.factorial ∧
    tseq z τ = ∑ s ∈ Finset.range (τ + 1), (a s * z ^ s) • bas z s := by
  obtain ⟨a, haτ, _, ha⟩ := pow_choose τ
  refine ⟨a, haτ, ?_⟩
  funext k
  simp only [tseq, ha k, Finset.sum_mul, Finset.sum_apply, Pi.smul_apply, bas, smul_eq_mul]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s ≤ k
  · have : z ^ k = z ^ s * z ^ (k - s) := by rw [← pow_add, Nat.add_sub_cancel' hs]
    rw [this]; ring
  · push Not at hs
    rw [Nat.choose_eq_zero_of_lt hs]; simp

lemma bas_zero (z : ℂ) : bas z 0 = fun k => z ^ k := by
  funext k; simp [bas]

lemma pascal0 (z : ℂ) : aeval S (X - C z) (bas z 0) = 0 := by
  funext k
  simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Pi.sub_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  simp only [S, LinearMap.funLeft_apply, bas_zero]
  ring

lemma pascal (z : ℂ) (s : ℕ) : aeval S (X - C z) (bas z (s + 1)) = bas z s := by
  funext k
  simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Pi.sub_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [S, LinearMap.funLeft_apply, bas, Function.comp_apply]
  rw [Nat.choose_succ_succ]
  by_cases hk : s + 1 ≤ k
  · have e1 : k + 1 - (s + 1) = k - s := by omega
    have e2 : z * z ^ (k - (s + 1)) = z ^ (k - s) := by
      rw [← pow_succ']; congr 1; omega
    rw [e1]; push_cast
    linear_combination -(↑(k.choose (s + 1)) : ℂ) * e2
  · push Not at hk
    rw [Nat.choose_eq_zero_of_lt (show k < s + 1 by omega)]
    have e1 : k + 1 - (s + 1) = k - s := by omega
    rw [e1]; simp

lemma pascal_iter (z : ℂ) (j : ℕ) : ∀ s, aeval S ((X - C z) ^ j) (bas z s) =
    if j ≤ s then bas z (s - j) else 0 := by
  induction j with
  | zero => intro s; simp
  | succ j ih =>
    intro s
    rw [pow_succ', map_mul, Module.End.mul_apply, ih]
    by_cases hjs : j ≤ s
    · rw [if_pos hjs]
      by_cases hjs' : j + 1 ≤ s
      · rw [if_pos hjs', show s - j = (s - (j + 1)) + 1 by omega, pascal]
      · rw [if_neg hjs', show s - j = 0 by omega, pascal0]
    · rw [if_neg hjs, if_neg (by omega), map_zero]

lemma tseq_kill (p : ℂ[X]) (z : ℂ) (τ : ℕ) (h : (X - C z) ^ (τ + 1) ∣ p) :
    aeval S p (tseq z τ) = 0 := by
  obtain ⟨a, _, ha⟩ := tseq_eq z τ
  rw [ha, map_sum]
  apply Finset.sum_eq_zero
  intro s hs
  rw [Finset.mem_range] at hs
  rw [map_smul, bas_kill p z s ((pow_dvd_pow _ (by omega)).trans h), smul_zero]

lemma tseq_top (z : ℂ) (τ : ℕ) :
    aeval S ((X - C z) ^ τ) (tseq z τ) = ((τ.factorial : ℂ) * z ^ τ) • bas z 0 := by
  obtain ⟨a, haτ, ha⟩ := tseq_eq z τ
  rw [ha, map_sum, Finset.sum_eq_single τ]
  · rw [map_smul, pascal_iter, if_pos le_rfl, Nat.sub_self, haτ]
  · intro s hs hne
    rw [Finset.mem_range] at hs
    rw [map_smul, pascal_iter, if_neg (by omega), smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self τ)) h

lemma geom_app (p : ℂ[X]) (z : ℂ) : aeval S p (bas z 0) = p.eval z • bas z 0 := by
  funext k
  rw [app_eq, bas_zero, eval_eq_sum_range]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [pow_add]; ring

lemma tseq_tendsto (z : ℂ) (hz : ‖z‖ < 1) (τ : ℕ) : Tendsto (tseq z τ) atTop (𝓝 0) := by
  obtain ⟨a, _, ha⟩ := tseq_eq z τ
  rw [ha]
  have := tendsto_finsetSum (Finset.range (τ + 1))
    (fun s _ => (bas_tendsto z hz s).const_smul (a s * z ^ s))
  simp only [smul_zero, Finset.sum_const_zero] at this
  convert this using 1
  funext k
  simp [Finset.sum_apply]


theorem decay {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (hz : Function.Injective z) (b : (Σ i : Fin r, Fin (m i)) → ℂ)
    (hdecay : Tendsto (fun k : ℕ => exp3 z m b k) atTop (𝓝 0)) :
    ∀ p : (Σ i : Fin r, Fin (m i)), 1 ≤ ‖z p.1‖ → b p = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨i0, τ1⟩, hz1, hb1⟩ := hcon
  set T := Finset.univ.filter (fun τ : Fin (m i0) => b ⟨i0, τ⟩ ≠ 0)
  have hT : T.Nonempty := ⟨τ1, by simp [T, hb1]⟩
  set τ0 := T.max' hT
  have hb0 : b ⟨i0, τ0⟩ ≠ 0 := by
    have := T.max'_mem hT
    simpa [T] using this
  have hmax : ∀ τ : Fin (m i0), b ⟨i0, τ⟩ ≠ 0 → τ ≤ τ0 := by
    intro τ hτ
    exact T.le_max' τ (by simp [T, hτ])
  set z0 := z i0
  have hz0 : z0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; linarith
  set Q : ℂ[X] := ∏ i ∈ Finset.univ.erase i0, (X - C (z i)) ^ (m i)
  set R : ℂ[X] := (X - C z0) ^ (τ0 : ℕ)
  have hexp : (fun k => exp3 z m b k) = ∑ p, b p • tseq (z p.1) p.2 := by
    funext k
    simp only [exp3, tseq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl; intro p _; ring
  set u := aeval S (Q * R) (fun k => exp3 z m b k)
  have hu : u = (b ⟨i0, τ0⟩ * ((τ0 : ℕ).factorial * z0 ^ (τ0 : ℕ)) * Q.eval z0) • bas z0 0 := by
    simp only [u, hexp, map_sum, map_smul]
    rw [Finset.sum_eq_single ⟨i0, τ0⟩]
    · rw [map_mul, Module.End.mul_apply, tseq_top, map_smul, geom_app, smul_smul, smul_smul]
    · rintro ⟨i, τ⟩ _ hne
      by_cases hi : i = i0
      · subst hi
        by_cases hbz : b ⟨i, τ⟩ = 0
        · rw [hbz, zero_smul]
        · have hle := hmax τ hbz
          have hne' : τ ≠ τ0 := fun h => hne (by rw [h])
          have hlt : (τ : ℕ) < τ0 := lt_of_le_of_ne hle (fun h => hne' (Fin.ext h))
          have hdvd : (X - C (z i)) ^ ((τ : ℕ) + 1) ∣ Q * R :=
            dvd_mul_of_dvd_right (pow_dvd_pow _ (Nat.succ_le_of_lt hlt)) Q
          show b ⟨i, τ⟩ • aeval S (Q * R) (tseq (z i) τ) = 0
          rw [tseq_kill _ _ _ hdvd, smul_zero]
      · have hdvd : (X - C (z i)) ^ ((τ : ℕ) + 1) ∣ Q * R :=
          dvd_mul_of_dvd_left ((pow_dvd_pow _ (Nat.succ_le_of_lt τ.2)).trans
            (Finset.dvd_prod_of_mem (fun i => (X - C (z i)) ^ (m i))
              (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩))) R
        show b ⟨i, τ⟩ • aeval S (Q * R) (tseq (z i) τ) = 0
        rw [tseq_kill _ _ _ hdvd, smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQ : Q.eval z0 ≠ 0 := by
    simp only [Q, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    apply pow_ne_zero
    rw [sub_ne_zero]
    intro h
    exact (Finset.mem_erase.mp hi).1 (hz h.symm)
  set c := b ⟨i0, τ0⟩ * ((τ0 : ℕ).factorial * z0 ^ (τ0 : ℕ)) * Q.eval z0
  have hc : c ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hb0 (mul_ne_zero ?_ (pow_ne_zero _ hz0))) hQ
    exact_mod_cast Nat.factorial_ne_zero _
  have hut : Tendsto u atTop (𝓝 0) := app_tendsto _ _ hdecay
  have hn : Tendsto (fun k => ‖u k‖) atTop (𝓝 0) := by simpa using hut.norm
  have hge : ∀ k, ‖c‖ ≤ ‖u k‖ := by
    intro k
    rw [hu, bas_zero]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hz1)
  have : ‖c‖ ≤ 0 := ge_of_tendsto' hn hge
  exact hc (norm_le_zero_iff.mp this)

end LDFT3

end Part2

open LearnDoFrontier.TwoAction Filter Topology in
theorem solution {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (hz : Function.Injective z) (b : (Σ i : Fin r, Fin (m i)) → ℂ)
    (hdecay : Tendsto (fun k : ℕ => exp3 z m b k) atTop (𝓝 0)) :
    ∀ p : (Σ i : Fin r, Fin (m i)), 1 ≤ ‖z p.1‖ → b p = 0 :=
  LDFT3.decay z m hz b hdecay
