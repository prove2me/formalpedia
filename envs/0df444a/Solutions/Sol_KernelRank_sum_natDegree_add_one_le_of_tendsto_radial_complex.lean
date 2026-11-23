-- Prove2me | solution 1 for KernelRank.sum_natDegree_add_one_le_of_tendsto_radial_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:50:39.091815+00:00
-- url     : https://prove2.me/submissions/37d481d1-13c0-45e9-8666-fc38c0a3afb6

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
import Theorems.Thm_KernelRank_separableRank_padTwo_le_of_tendsto
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_separableRank_radial_complex_eq_iff
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
    {S : Finset ℂ} {P : ℂ → ℂ[X]} (hP : ∀ μ ∈ S, P μ ≠ 0)
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → (Fin d → ℝ) → ℂ} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l
      (𝓝 (∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)))) :
    (∑ μ ∈ S, ((P μ).natDegree + 1)) ≤ r := by
  have hle := separableRank_padTwo_le_of_tendsto hd hrank htend
  have hpad : (fun y : Fin 2 → ℝ => ∑ μ ∈ S, expPoly (P μ) μ (∑ j : Fin d, (padTwo y j) ^ 2)) =
      fun y : Fin 2 → ℝ => ∑ μ ∈ S, expPoly (P μ) μ (∑ j : Fin 2, y j ^ 2) :=
    funext fun y => by rw [sum_padTwo_sq hd y]
  have hcont : ContinuousOn (fun s : ℝ => ∑ μ ∈ S, expPoly (P μ) μ s) (Set.Ici 0) := by
    refine Continuous.continuousOn ?_
    have hterm (μ : ℂ) : Continuous (fun s : ℝ => expPoly (P μ) μ s) := by
      unfold expPoly
      exact ((P μ).continuous_aeval.comp Complex.continuous_ofReal).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    fun_prop
  have h2d : separableRank (fun y : Fin 2 → ℝ =>
      ∑ μ ∈ S, expPoly (P μ) μ (∑ j : Fin 2, y j ^ 2)) =
      ((∑ μ ∈ S, ((P μ).natDegree + 1) : ℕ) : ℕ∞) := by
    rw [separableRank_radial_complex_eq_iff (le_refl 2) _ hcont]
    exact ⟨S, P, hP, fun _ _ => rfl, by simp⟩
  rw [hpad, h2d] at hle
  exact_mod_cast hle
end KernelRank
