-- Prove2me | solution 1 for Komlos.banaszczyk_convex_body
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:44:09.392184+00:00
-- url     : https://prove2.me/submissions/140d981e-a6fd-4c18-b0f0-f21cae10d335
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Komlos_gaussian_closed_convex_contains_zero
import Theorems.Thm_Komlos_banaszczyk_convex_fold

open MeasureTheory ProbabilityTheory Set Komlos
open scoped BigOperators

private theorem balancing
    (hfold : ∀ (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m))),
      Convex ℝ K → IsCompact K →
      (1/2:ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real K →
      ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ ≤ (1/5:ℝ) →
      ∃ L : Set (EuclideanSpace ℝ (Fin m)), Convex ℝ L ∧ IsCompact L ∧
        (stdGaussian (EuclideanSpace ℝ (Fin m))).real K ≤
          (stdGaussian (EuclideanSpace ℝ (Fin m))).real L ∧
        ∀ x ∈ L, x+u ∈ K ∨ x-u ∈ K) :
    ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ (1/5:ℝ)) →
      ∀ K : Set (EuclideanSpace ℝ (Fin m)), Convex ℝ K → IsCompact K →
      (1/2:ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real K →
      ∃ eps : Fin n → ℝ, IsSignVector eps ∧ ∑ i, eps i • v i ∈ K := by
  intro n
  induction n with
  | zero =>
    intro m v hv K hc hk hmass
    refine ⟨fun _ => 1, (fun _ => Or.inl rfl), ?_⟩
    simpa using gaussian_closed_convex_contains_zero m K hc hk.isClosed hmass
  | succ n ih =>
    intro m v hv K hc hk hmass
    obtain ⟨L,hLc,hLk,hLmass,hLK⟩ := hfold m K hc hk hmass (v (Fin.last n)) (hv _)
    obtain ⟨eps,heps,hsum⟩ := ih m (fun i => v i.castSucc) (fun i => hv i.castSucc)
      L hLc hLk (hmass.trans hLmass)
    rcases hLK _ hsum with hp | hn
    · refine ⟨Fin.snoc eps 1, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simpa using heps j
      · simpa [Fin.sum_univ_castSucc] using hp
    · refine ⟨Fin.snoc eps (-1), ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simpa using heps j
      · simpa [Fin.sum_univ_castSucc, sub_eq_add_neg] using hn


theorem solution
    (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m))
    (hv : ∀ i, ‖v i‖ ≤ (1/5 : ℝ))
    (K : Set (EuclideanSpace ℝ (Fin m))) (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hGauss : (1/2 : ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real K) :
    ∃ ε : Fin n → ℝ, IsSignVector ε ∧ ∑ i, ε i • v i ∈ K := by
  exact balancing banaszczyk_convex_fold n m v hv K hconv hcomp hGauss
