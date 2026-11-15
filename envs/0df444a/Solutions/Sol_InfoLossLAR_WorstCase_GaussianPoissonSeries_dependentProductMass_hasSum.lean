-- Prove2me | solution 1 for InfoLossLAR.WorstCase.GaussianPoissonSeries.dependentProductMass_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:49:25.414319+00:00
-- url     : https://prove2.me/submissions/b93b1f98-9ff7-4585-a6fa-5974939aab22

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem solution {Index : Type*} (dimension : ℕ)
    (mass : Fin dimension → Index → ℝ)
    (hnonnegative : ∀ index value,0 ≤ mass index value) (hsummable : ∀ index,Summable (mass index)) :
    HasSum (fun word : Fin dimension → Index => ∏ index,mass index (word index))
      (∏ index,∑' value,mass index value):= by
  classical
  induction dimension with
  | zero =>
    have heq : (fun word : Fin 0 → Index => ∏ index,mass index (word index))=(fun _ => (1 : ℝ)) := by
      funext word
      simp
    rw [heq]
    simpa only [Finset.univ_eq_empty,Finset.prod_empty,Fintype.sum_unique] using
      (hasSum_fintype (fun _ : Fin 0 → Index => (1 : ℝ)))
  | succ dimension ih =>
    have htail := ih (fun index => mass index.succ) (fun index => hnonnegative index.succ)
      (fun index => hsummable index.succ)
    have htailNonnegative (word : Fin dimension → Index) : 0 ≤ ∏ index,mass index.succ (word index) :=
      Finset.prod_nonneg (fun _ _ => hnonnegative _ _)
    have hs := (hsummable 0).mul_of_nonneg htail.summable (hnonnegative 0) htailNonnegative
    have hp := (hsummable 0).hasSum.mul htail hs
    have hcompose : (fun pair : Index×(Fin dimension → Index) => mass 0 pair.1*(∏ index,mass index.succ (pair.2 index)))=
        (fun word : Fin (dimension+1) → Index => ∏ index,mass index (word index)) ∘
          (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)) := by
      funext pair
      simp only [Function.comp_apply,Fin.consEquiv,Equiv.coe_fn_mk,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [hcompose] at hp
    have h := (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)).hasSum_iff.mp hp
    simpa only [Fin.prod_univ_succ] using h
