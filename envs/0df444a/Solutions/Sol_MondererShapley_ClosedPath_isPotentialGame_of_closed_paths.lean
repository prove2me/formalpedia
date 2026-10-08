-- Prove2me | solution 1 for MondererShapley.ClosedPath.isPotentialGame_of_closed_paths
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:19:23.20428+00:00
-- url     : https://prove2.me/submissions/f28727d1-f9b4-43a6-8065-9c89dd00cca4

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_FinPath
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame

namespace MondererShapley.ClosedPath
variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

inductive Walk : (∀ i, Y i) → (∀ i, Y i) → Type _
  | nil (a) : Walk a a
  | cons {a b c} (i : ι) (h : IsStep a b i) (w : Walk b c) : Walk a c

def Walk.cost (u : ι → (∀ i, Y i) → ℝ) {a b : ∀ i, Y i} : Walk a b → ℝ
  | .nil _ => 0
  | @Walk.cons _ _ a b _ i _ w => (u i b - u i a) + w.cost u

def Walk.append {a b c : ∀ i, Y i} : Walk a b → Walk b c → Walk a c
  | .nil _, v => v
  | .cons i h w, v => .cons i h (w.append v)

theorem Walk.cost_append (u : ι → (∀ i, Y i) → ℝ) {a b c : ∀ i, Y i}
    (w : Walk a b) (v : Walk b c) : (w.append v).cost u = w.cost u + v.cost u := by
  induction w with
  | nil => simp [Walk.append, Walk.cost]
  | cons i h w ih => simp [Walk.append, Walk.cost, ih, add_assoc]

theorem step_symm {a b : ∀ i, Y i} {i} (h : IsStep a b i) : IsStep b a i :=
  ⟨h.1.symm, fun j hj => (h.2 j hj).symm⟩

def Walk.reverse {a b : ∀ i, Y i} : Walk a b → Walk b a
  | .nil a => .nil a
  | .cons i h w => w.reverse.append (.cons i (step_symm h) (.nil _))

theorem Walk.cost_reverse (u : ι → (∀ i, Y i) → ℝ) {a b : ∀ i, Y i} (w : Walk a b) :
    w.reverse.cost u = -w.cost u := by
  induction w with
  | nil => simp [Walk.reverse, Walk.cost]
  | cons i h w ih => simp [Walk.reverse, Walk.cost_append, Walk.cost, ih]

def Walk.toPathData {a b : ∀ i, Y i} : Walk a b →
    {p : FinPath Y // p.pt 0 = a ∧ p.pt (Fin.last p.len) = b}
  | .nil a => ⟨⟨0, fun _ => a, Fin.elim0, fun k => Fin.elim0 k⟩, rfl, rfl⟩
  | @Walk.cons _ _ a b c i h w =>
    let d := w.toPathData
    let p := d.val
    ⟨{ len := p.len + 1
       pt := Fin.cases a p.pt
       dev := Fin.cases i p.dev
       step := fun k => Fin.cases (by
           change IsStep a (p.pt 0) i
           rw [d.property.1]; exact h)
         (fun j => by simpa using p.step j) k }, rfl, by
           change Fin.cases a p.pt ((Fin.last p.len).succ) = c
           rw [Fin.cases_succ]; exact d.property.2⟩

def Walk.toPath {a b : ∀ i, Y i} (w : Walk a b) : FinPath Y := w.toPathData.val

theorem Walk.toPath_start {a b : ∀ i, Y i} (w : Walk a b) : w.toPath.pt 0 = a :=
  w.toPathData.property.1

theorem Walk.toPath_end {a b : ∀ i, Y i} (w : Walk a b) :
    w.toPath.pt (Fin.last w.toPath.len) = b := w.toPathData.property.2

theorem Walk.toPath_cost (u : ι → (∀ i, Y i) → ℝ) {a b : ∀ i, Y i} (w : Walk a b) :
    w.toPath.I u = w.cost u := by
  induction w with
  | nil => simp [Walk.toPath, Walk.toPathData, FinPath.I, Walk.cost]
  | @cons a b c i h w ih =>
    change (∑ k : Fin (w.toPath.len + 1),
      (u (Fin.cases i w.toPath.dev k) (Fin.cases a w.toPath.pt k.succ) -
       u (Fin.cases i w.toPath.dev k) (Fin.cases a w.toPath.pt k.castSucc))) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.succ_castSucc, Fin.cases_succ, Fin.castSucc_zero, Fin.cases_zero]
    change (u i (w.toPath.pt 0) - u i a) + w.toPath.I u = _
    rw [ih, Walk.toPath_start]; rfl

theorem walk_independent (u : ι → (∀ i, Y i) → ℝ)
    (hc : ∀ γ : FinPath Y, γ.IsClosed → γ.I u = 0) {a b : ∀ i, Y i} (w v : Walk a b) :
    w.cost u = v.cost u := by
  have hz := hc (w.append v.reverse).toPath (by
    simp [FinPath.IsClosed, Walk.toPath_start, Walk.toPath_end])
  rw [Walk.toPath_cost, Walk.cost_append, Walk.cost_reverse] at hz
  linarith

def pathWalk (n : ℕ) (pt : Fin (n+1) → ∀ i, Y i) (dev : Fin n → ι)
    (hs : ∀ k, IsStep (pt k.castSucc) (pt k.succ) (dev k)) :
    Walk (pt 0) (pt (Fin.last n)) :=
  match n with
  | 0 => .nil _
  | n+1 => .cons (dev 0) (hs 0)
      (pathWalk n (fun k => pt k.succ) (fun k => dev k.succ) (fun k => hs k.succ))

theorem pathWalk_cost (u : ι → (∀ i, Y i) → ℝ) (n : ℕ)
    (pt : Fin (n+1) → ∀ i, Y i) (dev : Fin n → ι)
    (hs : ∀ k, IsStep (pt k.castSucc) (pt k.succ) (dev k)) :
    (pathWalk n pt dev hs).cost u = ∑ k, (u (dev k) (pt k.succ) - u (dev k) (pt k.castSucc)) := by
  induction n with
  | zero => simp [pathWalk, Walk.cost]
  | succ n ih => simp only [pathWalk, Walk.cost, Fin.sum_univ_succ, ih]; rfl

theorem walk_exists [Fintype ι] (a b : ∀ i, Y i) : Nonempty (Walk a b) := by
  classical
  have aux (s : Finset ι) : ∀ a b : ∀ i, Y i,
      (∀ j, j ∉ s → b j = a j) → Nonempty (Walk a b) := by
    induction s using Finset.induction_on with
    | empty =>
      intro a b h
      have he : b = a := funext (fun j => h j (by simp))
      subst b; exact ⟨.nil a⟩
    | @insert i s hi ih =>
      intro a b h
      let c := Function.update a i (b i)
      obtain ⟨w⟩ := ih c b (by
        intro j hj
        by_cases hji : j = i
        · subst j; simp [c]
        · simpa [c, hji] using h j (by simp [hj, hji]))
      by_cases he : b i = a i
      · have hc : c = a := by simp [c, he]
        exact hc ▸ ⟨w⟩
      · exact ⟨.cons i ⟨by simpa [c], fun j hj => by simp [c, hj]⟩ w⟩
  exact aux Finset.univ a b (by simp)

theorem potential_from_closed [Fintype ι] (u : ι → (∀ i, Y i) → ℝ)
    (hc : ∀ γ : FinPath Y, γ.IsClosed → γ.I u = 0) : IsPotentialGame u := by
  classical
  by_cases hn : Nonempty (∀ i, Y i)
  · let a := Classical.choice hn
    let w (b : ∀ i, Y i) : Walk a b := Classical.choice (walk_exists a b)
    refine ⟨fun b => (w b).cost u, ?_⟩
    intro i y x z
    let b := Function.update y i z
    let c := Function.update y i x
    by_cases hxz : x = z
    · subst x; simp
    · have hs : IsStep b c i := by
        exact ⟨by simpa [b, c] using hxz, fun j hj => by simp [b, c, hj]⟩
      let v : Walk b c := .cons i hs (.nil c)
      have he := walk_independent u hc (w c) ((w b).append v)
      rw [Walk.cost_append] at he
      simp only [v, Walk.cost, add_zero] at he
      dsimp [b, c] at he ⊢
      linarith
  · refine ⟨fun _ => 0, ?_⟩
    intro i y x z
    exact (hn ⟨y⟩).elim

end MondererShapley.ClosedPath

open MondererShapley.ClosedPath
theorem solution {ι : Type*} [DecidableEq ι] {Y : ι → Type*} [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ)
    (hclosed : ∀ γ : FinPath Y, γ.IsClosed → γ.I u = 0) :
    IsPotentialGame u := potential_from_closed u hclosed
#print axioms solution
