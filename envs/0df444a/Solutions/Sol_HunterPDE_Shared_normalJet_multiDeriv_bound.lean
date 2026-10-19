-- Prove2me | solution 1 for HunterPDE.Shared.normalJet_multiDeriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T19:42:08.486504+00:00
-- url     : https://prove2.me/submissions/02979404-7c0f-49af-9a16-dbe4233652d0

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Theorems.Thm_HunterPDE_Shared_normalJet_bound
import Theorems.Thm_HunterPDE_Shared_iteratedPartial_boundary_zero
import Theorems.Thm_HunterPDE_Shared_contDiffOn_iteratedPartial
open HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} (i : Fin n) (k : ℕ)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hb : ∀ r : ℕ, r < k → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial ψ (List.replicate r i) x = 0)
    (β : Fin n → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      ‖multiDeriv ψ β x‖ ≤ C * ‖x i‖ ^ (k - β i) := by
  classical
  have hs : ContDiff ℝ ∞ (multiDeriv ψ β) :=
    contDiffOn_univ.mp (contDiffOn_iteratedPartial isOpen_univ hψ.contDiffOn _)
  have hcompact (l : List (Fin n)) : HasCompactSupport (iteratedPartial ψ l) := by
    induction l with
    | nil => exact hc
    | cons j l ih => exact ih.fderiv_apply ℝ _
  have hcount : (multiIndexList β).count i = β i := by
    simp only [multiIndexList, List.count_flatMap, Function.comp_def, List.count_replicate,
      beq_iff_eq]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    simp
  apply normalJet_bound i (k - β i) (multiDeriv ψ β) hs (hcompact _)
  intro r hr x hx
  have happ (a b : List (Fin n)) :
      iteratedPartial ψ (a ++ b) = iteratedPartial (iteratedPartial ψ b) a := by
    induction a with
    | nil => rfl
    | cons j a ih => simp only [List.cons_append, iteratedPartial, ih]
  change iteratedPartial (iteratedPartial ψ (multiIndexList β)) (List.replicate r i) x = 0
  rw [← happ]
  apply iteratedPartial_boundary_zero i k ψ hψ hb _ _ x hx
  simp only [List.count_append, List.count_replicate_self, hcount]
  omega
