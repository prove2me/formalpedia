-- Prove2me | solution 1 for KernelRank.totalCost_le_of_tendsto_radial_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:54:12.945795+00:00
-- url     : https://prove2.me/submissions/d70e9e65-7355-4fe6-901f-744397e3a651

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
import Theorems.Thm_KernelRank_separableRank_padTwo_le_of_tendsto
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_separableRank_radial_two_profile
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same


section
open Complex Polynomial
open scoped Topology
namespace KernelRank
section LowerSemicontinuity
private lemma sum_padTwo_sq {d : ℕ} (hd : 2 ≤ d) (y : Fin 2 → ℝ) :
    (∑ j : Fin d, (padTwo y j) ^ 2) = ∑ j : Fin 2, y j ^ 2 := by
  have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin d => (j : ℕ) < 2) (fun j => (padTwo y j) ^ 2)).symm
  have hrest : ∑ j ∈ Finset.univ.filter (fun j : Fin d => ¬ (j : ℕ) < 2),
      (padTwo y j) ^ 2 = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have hj' : ¬ (j : ℕ) < 2 := (Finset.mem_filter.mp hj).2
      simp [padTwo, hj']
  have htwo : ∑ j ∈ Finset.univ.filter (fun j : Fin d => (j : ℕ) < 2),
      (padTwo y j) ^ 2 = ∑ j : Fin 2, y j ^ 2 := by
    have hset : Finset.univ.filter (fun j : Fin d => (j : ℕ) < 2) =
        {Fin.castLE hd 0, Fin.castLE hd 1} := by
      ext ⟨j, hj⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff, Fin.val_castLE, Fin.val_zero, Fin.val_one]
      omega
    have hne : Fin.castLE hd 0 ≠ Fin.castLE hd 1 := by simp [Fin.ext_iff]
    rw [hset, Finset.sum_pair hne, Fin.sum_univ_two]
    simp [padTwo, Fin.castLE]
  rw [hsplit, hrest, htwo, add_zero]
end LowerSemicontinuity
section AdjugateBorderRank
end AdjugateBorderRank
section UniversalApproximation
end UniversalApproximation
end KernelRank
end

set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d)
    {cs : List Component} (hcs : IsRepresentation cs)
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → (Fin d → ℝ) → ℝ} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (profile cs (∑ j, x j ^ 2)))) :
    totalCost cs ≤ r := by
  have hle := separableRank_padTwo_le_of_tendsto hd hrank htend
  have hpad : (fun y : Fin 2 → ℝ => profile cs (∑ j : Fin d, (padTwo y j) ^ 2)) =
      fun y : Fin 2 → ℝ => profile cs (∑ j : Fin 2, y j ^ 2) :=
    funext fun y => by rw [sum_padTwo_sq hd y]
  rw [hpad, separableRank_radial_two_profile hcs] at hle
  exact_mod_cast hle
end KernelRank
