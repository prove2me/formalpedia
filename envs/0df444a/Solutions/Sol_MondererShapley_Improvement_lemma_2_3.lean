-- Prove2me | solution 1 for MondererShapley.Improvement.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:22:50.573508+00:00
-- url     : https://prove2.me/submissions/dc33ad5e-dd53-4561-9ae7-db7ffdd3d700

import Mathlib
import Definitions.Def_MondererShapley_Improvement_IsOrdinalPotential
import Definitions.Def_MondererShapley_Improvement_HasFIP

open MondererShapley.Improvement

theorem solution {ι : Type*} [DecidableEq ι] {Y : ι → Type*}
    [Fintype ι] [∀ i, Fintype (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) (h : ∃ P, IsOrdinalPotential u P) :
    HasFIP u := by
  classical
  obtain ⟨P, hP⟩ := h
  rintro ⟨y, d, hd⟩
  have hup (k : ℕ) : Function.update (y k) (d k) (y (k+1) (d k)) = y (k+1) := by
    funext j
    by_cases hj : j = d k
    · subst j; simp
    · simpa [Function.update_of_ne hj] using (hd k).1.2 j hj |>.symm
  have hmono : StrictMono (fun k => P (y k)) := by
    apply strictMono_nat_of_lt_succ
    intro k
    have ht := (hP (d k) (y k) (y (k+1) (d k)) (y k (d k))).mp
      (by simpa only [hup k, Function.update_eq_self, sub_pos] using (hd k).2)
    simpa only [hup k, Function.update_eq_self, sub_pos] using ht
  have hinj : Function.Injective y := fun a b hab => hmono.injective (congrArg P hab)
  letI := Finite.of_injective y hinj
  exact not_finite ℕ

#print axioms solution
