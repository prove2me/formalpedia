-- Prove2me | solution 1 for KernelRank.separableRank_radial_complex_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:48:19.366617+00:00
-- url     : https://prove2.me/submissions/0ffaba0d-bb18-4637-8600-6fae9c7ab716

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
import Theorems.Thm_KernelRank_radial_congr
import Theorems.Thm_KernelRank_exists_sum_expPoly_of_finiteDimensional
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_separableRank_radial_sum_expPoly
import Theorems.Thm_KernelRank_separableRank_radial_two_le
import Theorems.Thm_KernelRank_separableRank_radial_two_lt_top_iff
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
open scoped Classical
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d)
    (ψ : ℝ → ℂ) (hψ : ContinuousOn ψ (Set.Ici 0)) (N : ℕ) :
    separableRank (fun x : Fin d → ℝ => ψ (∑ j, x j ^ 2)) = N ↔
      ∃ (S : Finset ℂ) (P : ℂ → ℂ[X]),
        (∀ μ ∈ S, P μ ≠ 0) ∧
        (∀ s, 0 ≤ s → ψ s = ∑ μ ∈ S, expPoly (P μ) μ s) ∧
        ∑ μ ∈ S, ((d - 1) * (P μ).natDegree + 1) = N := by
  constructor
  · intro h
    have h2 : separableRank (fun x : Fin 2 → ℝ => ψ (∑ j, x j ^ 2)) < ⊤ :=
      lt_of_le_of_lt (separableRank_radial_two_le hd ψ) (by rw [h]; simp)
    have : FiniteDimensional ℂ (translateSpan ψ) :=
      (separableRank_radial_two_lt_top_iff ψ).mp h2
    obtain ⟨S₀, P, hP₀⟩ := exists_sum_expPoly_of_finiteDimensional ψ hψ
    let S := S₀.filter fun μ => P μ ≠ 0
    have hPS : ∀ μ ∈ S, P μ ≠ 0 := fun μ hμ => (Finset.mem_filter.mp hμ).2
    have hψS : ∀ s, 0 ≤ s → ψ s = ∑ μ ∈ S, expPoly (P μ) μ s := by
      intro s hs
      rw [hP₀ s hs]
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun μ hμ₀ hμ => ?_
      have h0 : P μ = 0 := by simpa [S, hμ₀] using hμ
      simp [h0]
    refine ⟨S, P, hPS, hψS, ?_⟩
    rw [radial_congr hψS] at h
    have hcoe : (fun x : Fin d → ℝ => ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)) =
        fun x => ∑ μ : S, expPoly (P μ.1) μ.1 (∑ j, x j ^ 2) := by
      funext x
      exact (Finset.sum_coe_sort S (fun μ => expPoly (P μ) μ (∑ j, x j ^ 2))).symm
    rw [hcoe, separableRank_radial_sum_expPoly hd Subtype.val_injective
      (fun μ : S => P μ.1) (fun μ => hPS μ.1 μ.2)] at h
    have hsum : (∑ μ : S, ((d - 1) * (P μ.1).natDegree + 1)) =
        ∑ μ ∈ S, ((d - 1) * (P μ).natDegree + 1) :=
      Finset.sum_coe_sort S (fun μ => (d - 1) * (P μ).natDegree + 1)
    rw [← hsum]
    exact_mod_cast h
  · rintro ⟨S, P, hPS, hψS, rfl⟩
    rw [radial_congr hψS]
    have hcoe : (fun x : Fin d → ℝ => ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2)) =
        fun x => ∑ μ : S, expPoly (P μ.1) μ.1 (∑ j, x j ^ 2) := by
      funext x
      exact (Finset.sum_coe_sort S (fun μ => expPoly (P μ) μ (∑ j, x j ^ 2))).symm
    have hsum : (∑ μ ∈ S, ((d - 1) * (P μ).natDegree + 1)) =
        ∑ μ : S, ((d - 1) * (P μ.1).natDegree + 1) :=
      (Finset.sum_coe_sort S (fun μ => (d - 1) * (P μ).natDegree + 1)).symm
    rw [hcoe, hsum]
    exact separableRank_radial_sum_expPoly hd Subtype.val_injective
      (fun μ : S => P μ.1) (fun μ => hPS μ.1 μ.2)
end KernelRank
