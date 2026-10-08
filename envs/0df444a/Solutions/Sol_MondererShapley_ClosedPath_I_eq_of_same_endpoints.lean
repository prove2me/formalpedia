-- Prove2me | solution 1 for MondererShapley.ClosedPath.I_eq_of_same_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:17:39.952058+00:00
-- url     : https://prove2.me/submissions/64c4265a-ae13-4f13-9f04-dd35e57f5b86

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

end MondererShapley.ClosedPath

open MondererShapley.ClosedPath
theorem cost_transport {ι : Type*} {Y : ι → Type*}
    (u : ι → (∀ i, Y i) → ℝ) {a a' b b' : ∀ i, Y i}
    (ha : a = a') (hb : b = b') (w : Walk a' b') :
    (ha ▸ hb ▸ w).cost u = w.cost u := by
  cases ha; cases hb; rfl
theorem solution {ι : Type*} [DecidableEq ι] {Y : ι → Type*} [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ)
    (hclosed : ∀ γ : FinPath Y, γ.IsClosed → γ.I u = 0)
    (γ₁ γ₂ : FinPath Y)
    (hstart : γ₁.pt 0 = γ₂.pt 0)
    (hend : γ₁.pt (Fin.last γ₁.len) = γ₂.pt (Fin.last γ₂.len)) :
    γ₁.I u = γ₂.I u := by
  let w := pathWalk γ₁.len γ₁.pt γ₁.dev γ₁.step
  let v := pathWalk γ₂.len γ₂.pt γ₂.dev γ₂.step
  have hc := walk_independent u hclosed w (hstart ▸ hend ▸ v)
  rw [cost_transport u hstart hend] at hc
  simpa [w, v, pathWalk_cost, FinPath.I] using hc
#print axioms solution
