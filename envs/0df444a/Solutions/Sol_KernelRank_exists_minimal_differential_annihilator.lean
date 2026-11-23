-- Prove2me | solution 1 for KernelRank.exists_minimal_differential_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:46:33.891388+00:00
-- url     : https://prove2.me/submissions/a824c838-d02d-4f52-b0f9-2ffec5872e51

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_Annihilator
import Theorems.Thm_KernelRank_differentialOperator_congr
import Theorems.Thm_KernelRank_differentialOperator_sum_expPoly_eq_zero_iff
import Theorems.Thm_KernelRank_exists_sum_expPoly_of_finiteDimensional
import Theorems.Thm_KernelRank_expPolyAnnihilator_monic
import Theorems.Thm_KernelRank_expPolyAnnihilator_natDegree
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_finiteDimensional_translateSpan_ofReal
import Theorems.Thm_KernelRank_finrank_translateSpan_ofReal
import Theorems.Thm_KernelRank_finrank_translateSpan_sum_expPoly
import Theorems.Thm_KernelRank_separableRank_radial_two_eq_finrank
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)] (hφ : ContinuousOn φ (Set.Ici 0)) :
    ∃ p : ℂ[X], p.Monic ∧
      separableRank (fun x : Fin 2 → ℝ => φ (∑ i, x i ^ 2)) = p.natDegree ∧
      ∀ q : ℂ[X],
        (∀ t, 0 ≤ t → differentialOperator q (fun s => (φ s : ℂ)) t = 0) ↔ p ∣ q := by
  classical
  let ψ : ℝ → ℂ := fun t => (φ t : ℂ)
  let : FiniteDimensional ℂ (translateSpan ψ) := finiteDimensional_translateSpan_ofReal φ
  obtain ⟨S, Q, hψ⟩ := exists_sum_expPoly_of_finiteDimensional ψ
    (Complex.continuous_ofReal.comp_continuousOn hφ)
  let T := S.filter (fun μ => Q μ ≠ 0)
  let P (i : T) := Q i.1
  let rate (i : T) := i.1
  have hP (i : T) : P i ≠ 0 := (Finset.mem_filter.mp i.2).2
  have heq : Set.EqOn ψ (fun t => ∑ i, expPoly (P i) (rate i) t) (Set.Ici 0) := by
    intro t ht
    rw [hψ t ht]
    change (∑ μ ∈ S, expPoly (Q μ) μ t) = ∑ i : T, expPoly (Q i.1) i.1 t
    rw [Finset.sum_coe_sort T (fun μ => expPoly (Q μ) μ t)]
    symm
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro μ hμ hn
    have hQ : Q μ = 0 := by simpa [T, hμ] using hn
    simp [hQ]
  have hspan : translateSpan ψ = translateSpan (fun t => ∑ i, expPoly (P i) (rate i) t) := by
    unfold translateSpan
    congr 2
    ext t u
    exact heq (add_nonneg u.2 t.2)
  obtain ⟨_, hrank⟩ := finrank_translateSpan_sum_expPoly Subtype.coe_injective P hP
  refine ⟨expPolyAnnihilator P rate, expPolyAnnihilator_monic P rate, ?_, fun q => ?_⟩
  · rw [separableRank_radial_two_eq_finrank, ← finrank_translateSpan_ofReal φ,
      hspan, hrank, expPolyAnnihilator_natDegree]
  · have h := differentialOperator_sum_expPoly_eq_zero_iff P rate Subtype.coe_injective hP q
    constructor
    · intro hq
      apply h.mp
      exact fun t ht => (differentialOperator_congr q heq ht).symm.trans (hq t ht)
    · intro hq t ht
      exact (differentialOperator_congr q heq ht).trans (h.mpr hq t ht)
end KernelRank
