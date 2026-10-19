-- Prove2me | solution 1 for HunterPDE.Shared.iteratedPartial_boundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T19:41:04.542738+00:00
-- url     : https://prove2.me/submissions/7dc119cf-c7e8-4bf3-8049-4e7d09994cd4

import Theorems.Thm_HunterPDE_Shared_iteratedPartial_eq_of_perm
import Theorems.Thm_HunterPDE_Shared_contDiffOn_iteratedPartial
import Definitions.Def_HunterPDE_Shared_WeakDeriv

open HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} (i : Fin n) (k : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ r : ℕ, r < k → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial f (List.replicate r i) x = 0)
    (l : List (Fin n)) (hl : l.count i < k) :
    ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 → iteratedPartial f l x = 0 := by
  classical
  have smooth (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ ∞ g) (t : List (Fin n)) :
      ContDiff ℝ ∞ (iteratedPartial g t) :=
    contDiffOn_univ.mp (contDiffOn_iteratedPartial isOpen_univ hg.contDiffOn t)
  have tangent (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ ∞ g)
      (hz : ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 → g x = 0)
      (t : List (Fin n)) (ht : i ∉ t) :
      ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 → iteratedPartial g t x = 0 := by
    induction t with
    | nil => exact hz
    | cons j t ih =>
      have ht' : i ≠ j ∧ i ∉ t := by simpa using ht
      have hj : j ≠ i := ht'.1.symm
      have hh := ih ht'.2
      intro x hx
      let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
      have heq : (fun a : ℝ => iteratedPartial g t (x + a • e)) = fun _ => 0 := by
        funext a
        apply hh
        simp [e, hx, hj]
      have hline : HasDerivAt (fun a : ℝ => x + a • e) e 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
      have hd := ((smooth g hg t).differentiable (by simp) (x + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt 0 hline
      simp only [zero_smul, add_zero] at hd
      simp only [Function.comp_def] at hd
      rw [heq] at hd
      have hd' : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (partialDeriv (iteratedPartial g t) j x) 0 := by
        simpa only [heq, partialDeriv, e] using hd
      exact hd'.unique (hasDerivAt_const 0 0)
  have app (a b : List (Fin n)) :
      iteratedPartial f (a ++ b) = iteratedPartial (iteratedPartial f b) a := by
    induction a with
    | nil => rfl
    | cons j a ih => simp only [List.cons_append, iteratedPartial, ih]
  have hp : l.Perm (l.filter (fun j => j != i) ++ List.replicate (l.count i) i) := by
    simpa only [bne, Bool.not_not, List.filter_beq] using
      (List.filter_append_perm (fun j => j != i) l).symm
  intro x hx
  rw [iteratedPartial_eq_of_perm isOpen_univ hf.contDiffOn hp (Set.mem_univ x), app]
  apply tangent _ (smooth f hf _) (hb _ hl) _ _ x hx
  simp

