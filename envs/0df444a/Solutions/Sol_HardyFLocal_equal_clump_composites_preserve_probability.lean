-- Prove2me | solution 1 for HardyFLocal.equal_clump_composites_preserve_probability
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T01:16:02.70228+00:00
-- url     : https://prove2.me/submissions/68820f3d-b2a9-473b-af42-99f210674c83

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_product_lattice_trace
open HardyCausaloid
namespace HardyFLocal
private theorem wire_vertex_filter {m n : ℕ} (q : Q m n) :
    (vertexList m n).filter (fun x => match q with
      | .inl u => decide (x.1 = u) | .inr v => decide (x.2 = v)) = qubitVertices q := by
  cases q with
  | inl u =>
    have aux (us : List (Fin m)) :
        (us.product (List.finRange n)).filter (fun x => decide (x.1 = u)) =
          (us.filter (fun i => decide (i = u))).flatMap (fun i => (List.finRange n).map fun j => (i,j)) := by
      induction us with
      | nil => rfl
      | cons i us ih => by_cases h : i = u <;> simp [List.product] at ih <;> simp [List.product,List.filter_append,List.filter_map,Function.comp_def,h,ih]
    simpa [vertexList,qubitVertices,List.filter_eq] using aux (List.finRange m)
  | inr v =>
    have aux (us : List (Fin m)) :
        (us.product (List.finRange n)).filter (fun x => decide (x.2 = v)) = us.map fun i => (i,v) := by
      induction us with
      | nil => rfl
      | cons i us ih => simp [List.product] at ih; simp [List.product,List.filter_append,List.filter_map,Function.comp_def,List.filter_eq,ih]
    exact aux _

private theorem active_fold {A B : Type} (V : List B) (p : B → Bool) (f : A → B → A) (a : A) :
    V.foldl (fun s x => if p x then f s x else s) a = (V.filter p).foldl f a := by
  induction V generalizing a with
  | nil => rfl
  | cons x xs ih => by_cases h : p x <;> simp [h,ih]

private theorem fold_only_wire {m n : ℕ} {A : Type} (q : Q m n) (F G : A → X m n → A) (a : A) :
    (vertexList m n).foldl (fun b x => if q = .inl x.1 then F b x else if q = .inr x.2 then G b x else b) a =
      (qubitVertices q).foldl (match q with | .inl _ => F | .inr _ => G) a := by
  cases q with
  | inl i =>
    simpa [eq_comm] using (active_fold (vertexList m n) (fun z => decide (z.1 = i)) F a).trans
      (congrArg (fun l => l.foldl F a) (wire_vertex_filter (m := m) (n := n) (.inl i)))
  | inr j =>
    simpa [eq_comm] using (active_fold (vertexList m n) (fun z => decide (z.2 = j)) G a).trans
      (congrArg (fun l => l.foldl G a) (wire_vertex_filter (m := m) (n := n) (.inr j)))
end HardyFLocal
namespace HardyFLocal

private theorem split_fold_congr {A X : Type} (l : List X) (p : X → Bool)
    (f g : A → X → A)
    (gap : ∀ x ∈ l, p x = true → ∀ a, f a x = g a x)
    (run : ∀ c ∈ l.splitOnP p, ∀ a, c.foldl f a = c.foldl g a) :
    ∀ a, l.foldl f a = l.foldl g a := by
  have aux (cs ds : List (List X))
      (hc : ∀ c ∈ cs, ∀ a, c.foldl f a = c.foldl g a)
      (hd : ∀ c ∈ ds, ∀ a, c.foldl f a = c.foldl g a) :
      ∀ a, ((cs.zipWith (· ++ ·) ds).flatten).foldl f a = ((cs.zipWith (· ++ ·) ds).flatten).foldl g a := by
    induction cs generalizing ds with
    | nil => simp
    | cons x xs ih =>
      cases ds with
      | nil => simp
      | cons y ys =>
        intro a
        simp only [List.zipWith_cons_cons,List.flatten_cons,List.foldl_append]
        rw [hc x List.mem_cons_self, hd y List.mem_cons_self]
        apply ih ys (fun c h => hc c (List.mem_cons_of_mem _ h)) (fun c h => hd c (List.mem_cons_of_mem _ h))
  have separators : ∀ c ∈ ((l.filter p).map fun x => [x]) ++ [[]], ∀ a, c.foldl f a = c.foldl g a := by
    intro c h a
    rcases List.mem_append.mp h with h | h
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
      exact gap x (List.mem_filter.mp hx).1 (List.mem_filter.mp hx).2 a
    · obtain rfl := List.mem_singleton.mp h
      rfl
  simpa only [List.splitOnP_spec] using aux _ _ run separators

private theorem clump_fold_congruence {m n : ℕ} {A : Type} (O : Finset (X m n)) (q : Q m n)
    (f g : A → X m n → A)
    (gap : ∀ x ∈ qubitVertices q, x ∉ O → ∀ a, f a x = g a x)
    (run : ∀ c ∈ clumps O q, ∀ a, c.foldl f a = c.foldl g a) :
    ∀ a, (qubitVertices q).foldl f a = (qubitVertices q).foldl g a := by
  apply split_fold_congr (qubitVertices q) (fun x => decide (x ∉ O)) f g
  · simpa using gap
  · intro c hc
    cases c with
    | nil => exact fun _ => rfl
    | cons x xs => exact run _ (List.mem_filter.mpr ⟨hc,rfl⟩)

end HardyFLocal
namespace HardyFLocal
open HardyCausaloid

end HardyFLocal

open HardyFLocal

open Classical in
theorem solution {m n : ℕ} (O : Finset (X m n))
    (ρ : GlobalMat m n) (t t' : ∀ x, Label (Setting m n) (Outcome m n) x)
    (U U' : Q m n → X m n → Op (Fin 2))
    (h : ∀ x, labelOp (t x) = prodOp (U (.inl x.1) x) (U (.inr x.2) x))
    (h' : ∀ x, labelOp (t' x) = prodOp (U' (.inl x.1) x) (U' (.inr x.2) x))
    (hg : ∀ q x, x ∈ qubitVertices q → x ∉ O → U q x = U' q x)
    (hc : ∀ q c, c ∈ clumps O q → ∀ a, c.foldl (fun b x => U q x b) a = c.foldl (fun b x => U' q x b) a) :
    latticeProb ρ t = latticeProb ρ t' := by
  classical
  rw [product_lattice_trace ρ t _ _ h,product_lattice_trace ρ t' _ _ h']
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.prod_congr rfl
  intro q _
  congr 1
  let start := Matrix.single (i q) (j q) (1 : ℂ)
  have wire (S : Q m n → X m n → Op (Fin 2)) :
      (vertexList m n).foldl (fun b x => (if q = .inl x.1 then S (.inl x.1) x else
        if q = .inr x.2 then S (.inr x.2) x else LinearMap.id) b) start =
          (qubitVertices q).foldl (fun b x => S q x b) start := by
    have same (b : Matrix (Fin 2) (Fin 2) ℂ) (x : X m n) :
        (if q = .inl x.1 then S (.inl x.1) x else if q = .inr x.2 then S (.inr x.2) x else LinearMap.id) b =
          if q = .inl x.1 then S q x b else if q = .inr x.2 then S q x b else b := by
      by_cases h₁ : q = .inl x.1
      · rw [if_pos h₁,if_pos h₁,h₁]
      · rw [if_neg h₁,if_neg h₁]
        by_cases h₂ : q = .inr x.2
        · rw [if_pos h₂,if_pos h₂,h₂]
        · rw [if_neg h₂,if_neg h₂]; rfl
    simp_rw [same]
    have hh := fold_only_wire q (fun b x => S q x b) (fun b x => S q x b) start
    cases q <;> exact hh
  exact (wire U).trans ((clump_fold_congruence O q _ _ (fun x hx hO a => by rw [hg q x hx hO])
    (hc q) start).trans (wire U').symm)

