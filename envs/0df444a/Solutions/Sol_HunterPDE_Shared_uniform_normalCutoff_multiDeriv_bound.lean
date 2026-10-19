-- Prove2me | solution 1 for HunterPDE.Shared.uniform_normalCutoff_multiDeriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T15:51:40.947004+00:00
-- url     : https://prove2.me/submissions/1f91f39b-4c9e-450d-957c-d0343b115f67

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Theorems.Thm_ContDiff_ordered_directional_mul
import Theorems.Thm_HunterPDE_Shared_normalJet_multiDeriv_bound
import Theorems.Thm_ContDiff_exists_weighted_cutoff_deriv_bound
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open HunterPDE.Shared Filter
open scoped ContDiff Topology
set_option autoImplicit false

theorem solution {n : ℕ} (i : Fin n) (α : Fin n → ℕ)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hb : ∀ r : ℕ, r < α i → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial ψ (List.replicate r i) x = 0)
    (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q)
    (hlo : ∀ s : ℝ, s ≤ 1 → q s = 0)
    (hhi : ∀ s : ℝ, 2 ≤ s → q s = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 1 ≤ a →
      ∀ x : EuclideanSpace ℝ (Fin n),
        ‖multiDeriv (fun y => q (a * y i) * ψ y) α x‖ ≤ C := by
  classical
  have wordcount {n : ℕ} (i : Fin n) (β : Fin n → ℕ) :
      (multiIndexList β).count i = β i := by
    classical
    simp only [multiIndexList, List.count_flatMap, Function.comp_def, List.count_replicate,
      beq_iff_eq]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    simp
  have wordfold {n : ℕ} (β : Fin n → ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
      multiDeriv u β = (List.finRange n).foldr
        (fun i h => (fun u y => fderiv ℝ u y (EuclideanSpace.single i 1))^[β i] h) u := by
    have app (l : List (Fin n)) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
        iteratedPartial u l = l.foldr (fun i h => partialDeriv h i) u := by
      induction l with
      | nil => rfl
      | cons i l ih => simp [iteratedPartial, ih]
    have rep (j : Fin n) (k : ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
        (List.replicate k j).foldr (fun i h => partialDeriv h i) u =
        (fun h => partialDeriv h j)^[k] u := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ, ih, Function.iterate_succ_apply']
    simp only [multiDeriv, app, multiIndexList, List.foldr_flatMap, rep]
    rfl
  have wordcut {n : ℕ} (i : Fin n) (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) (a : ℝ)
      (l : List (Fin n)) :
      iteratedPartial (fun x : EuclideanSpace ℝ (Fin n) => q (a * x i)) l =
        fun x => if l.count i = l.length then
          a ^ l.length * iteratedDeriv l.length q (a * x i) else 0 := by
    classical
    induction l with
    | nil => simp [iteratedPartial, iteratedDeriv_zero]
    | cons j l ih =>
      simp only [iteratedPartial, ih]
      by_cases hl : l.count i = l.length
      · simp only [hl, if_true]
        funext x
        have hd (s : ℝ) := (hq.differentiable_iteratedDeriv l.length (by exact_mod_cast (WithTop.coe_lt_top l.length)) s).hasDerivAt
        have he := ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt (x := x) |>.const_mul a)
        have hcomp := ((hd (a * x i)).comp_hasFDerivAt x he).const_mul (a ^ l.length)
        simp only [Function.comp_def, PiLp.proj_apply] at hcomp
        unfold partialDeriv
        rw [hcomp.fderiv]
        by_cases hj : j = i
        · subst j
          simp [hl, iteratedDeriv_succ, pow_succ,
            mul_assoc, mul_comm, mul_left_comm]
        · simp [hj, hl]
      · have hn : (j :: l).count i ≠ (j :: l).length := by
          simp only [List.count_cons, List.length_cons]
          have hh := List.count_le_length (a := i) (l := l)
          split <;> omega
        simp only [if_neg hl]
        funext x
        change partialDeriv (fun _ => (0 : ℝ)) j x = _
        rw [if_neg hn]
        simp [partialDeriv]
  choose B hBpos hB using fun β => normalJet_multiDeriv_bound i (α i) ψ hψ hc hb β
  choose D hDpos hD using fun r => ContDiff.exists_weighted_cutoff_deriv_bound q hq hlo hhi r
  let coeff (β : Fin n → ℕ) : ℝ := ∏ j, (Nat.choose (α j) (β j) : ℝ)
  refine ⟨∑ β ∈ Finset.Iic α, ‖coeff β‖ * (B β * D (α i - β i)), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun β _ => mul_nonneg (norm_nonneg _) (mul_nonneg (hBpos β) (hDpos _)))
  intro a _ha x
  have hprod : multiDeriv (fun y => q (a * y i) * ψ y) α x =
      ∑ β ∈ Finset.Iic α, coeff β *
        (multiDeriv (fun y => q (a * y i)) (fun j => α j - β j) x * multiDeriv ψ β x) := by
    simp only [wordfold]
    exact ContDiff.ordered_directional_mul (fun j => EuclideanSpace.single j 1) α
      (fun y => q (a * y i)) ψ
      (by simpa only [Function.comp_def, PiLp.proj_apply] using
        hq.comp (contDiff_const.mul (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).contDiff)) hψ x
  rw [hprod]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro β hβ
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  let δ : Fin n → ℕ := fun j => α j - β j
  let r := α i - β i
  have hcut := congrFun (wordcut i q hq a (multiIndexList δ)) x
  change multiDeriv (fun y => q (a * y i)) δ x = _ at hcut
  by_cases hall : (multiIndexList δ).count i = (multiIndexList δ).length
  · have hlen : (multiIndexList δ).length = r := hall.symm.trans (wordcount i δ)
    rw [if_pos hall, hlen] at hcut
    rw [hcut, norm_mul, norm_mul, norm_pow]
    calc
      ‖a‖ ^ r * ‖iteratedDeriv r q (a * x i)‖ * ‖multiDeriv ψ β x‖ ≤
          (‖a‖ ^ r * ‖iteratedDeriv r q (a * x i)‖) * (B β * ‖x i‖ ^ r) :=
        mul_le_mul_of_nonneg_left (hB β x) (by positivity)
      _ = B β * (‖iteratedDeriv r q (a * x i)‖ * ‖a * x i‖ ^ r) := by
        rw [norm_mul, mul_pow]
        ring
      _ ≤ B β * D r := mul_le_mul_of_nonneg_left (hD r (a * x i)) (hBpos β)
  · rw [if_neg hall] at hcut
    rw [hcut, zero_mul, norm_zero]
    exact mul_nonneg (hBpos β) (hDpos _)
