-- Prove2me | solution 1 for HunterPDE.Sobolev.iteratedPartial_add
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:29:07.248407+00:00
-- url     : https://prove2.me/submissions/0d5cfcee-d181-414e-aecf-8bbf40c163a5

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Theorems.Thm_HunterPDE_Shared_iteratedPartial_eq_of_perm

open scoped ContDiff
open HunterPDE.Sobolev
set_option autoImplicit false

theorem sobolev_word_bridge {n : ℕ} (α : Fin n → ℕ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    iteratedPartial α u = HunterPDE.Shared.multiDeriv u α := by
  unfold iteratedPartial HunterPDE.Shared.multiDeriv HunterPDE.Shared.multiIndexList
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, List.flatMap_cons]
    rw [ih]
    generalize List.flatMap (fun i => List.replicate (α i) i) l = t
    induction α i with
    | zero => rfl
    | succ k ihk =>
      simp only [Function.iterate_succ_apply', List.replicate_succ, List.cons_append,
        HunterPDE.Shared.iteratedPartial]
      rw [ihk]
      rfl

theorem shared_word_append {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (l t : List (Fin n)) :
    HunterPDE.Shared.iteratedPartial (HunterPDE.Shared.iteratedPartial u t) l =
      HunterPDE.Shared.iteratedPartial u (l ++ t) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [HunterPDE.Shared.iteratedPartial, List.cons_append, ih]

theorem multiIndexList_count {n : ℕ} (α : Fin n → ℕ) (i : Fin n) :
    (HunterPDE.Shared.multiIndexList α).count i = α i := by
  classical
  rw [HunterPDE.Shared.multiIndexList, List.count_flatMap]
  simp only [Function.comp_def, List.count_replicate, beq_iff_eq]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp

theorem solution {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (α β : Fin n → ℕ) :
    iteratedPartial α (iteratedPartial β u) = iteratedPartial (fun i => β i + α i) u := by
  classical
  simp only [sobolev_word_bridge, HunterPDE.Shared.multiDeriv, shared_word_append]
  have hp : (HunterPDE.Shared.multiIndexList α ++ HunterPDE.Shared.multiIndexList β).Perm
      (HunterPDE.Shared.multiIndexList (fun i => β i + α i)) := by
    apply List.perm_iff_count.mpr
    intro i
    simp [List.count_append, multiIndexList_count, Nat.add_comm]
  funext x
  exact HunterPDE.Shared.iteratedPartial_eq_of_perm isOpen_univ hu.contDiffOn hp (Set.mem_univ x)
