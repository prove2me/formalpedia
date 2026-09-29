-- Prove2me | solution 1 for MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c58b94b1-bc6f-5f1c-be60-a05ceee608a9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

theorem solution
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (H : Subgroup K) (hH : IsOpen (H : Set K)) :
    ∃ (n : ℕ) (r : Fin n → K), H.index = n ∧ 0 < n ∧
      (∀ v : K, ∃ i, (r i)⁻¹ * v ∈ H) ∧
      (∀ i j, (r i)⁻¹ * r j ∈ H → i = j) ∧
      ∀ h : K → ℂ, (∀ v : K, ∀ w ∈ H, h (v * w) = h v) →
        ∫ v, h v ∂μ = (n : ℂ)⁻¹ * ∑ i, h (r i) := by
  classical
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  haveI : DiscreteTopology (K ⧸ H) := QuotientGroup.discreteTopology hH
  set n := Fintype.card (K ⧸ H) with hn
  let e : Fin n ≃ K ⧸ H := (Fintype.equivFin _).symm
  let r : Fin n → K := fun i => (e i).out
  have hr : ∀ i, (QuotientGroup.mk (r i) : K ⧸ H) = e i := fun i => QuotientGroup.out_eq' (e i)

  let σ : K → Fin n := fun v => e.symm (QuotientGroup.mk v)
  have hσ : ∀ v, (r (σ v))⁻¹ * v ∈ H := fun v => by
    rw [← QuotientGroup.eq, hr, Equiv.apply_symm_apply]
  have hn0 : 0 < n := Fintype.card_pos
  have hidx : H.index = n := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  refine ⟨n, r, hidx, hn0, fun v => ⟨σ v, hσ v⟩, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    rw [← hr, ← hr]
    exact QuotientGroup.eq.mpr hij

  let A : Fin n → Set K := fun i => σ ⁻¹' {i}
  have hσc : Continuous σ :=
    continuous_of_discreteTopology.comp (QuotientGroup.continuous_mk (N := H))
  have hAm : ∀ i, MeasurableSet (A i) := fun i =>
    ((isOpen_discrete ({i} : Set (Fin n))).preimage hσc).measurableSet

  have hA : ∀ i, A i = (fun v => (r i)⁻¹ * v) ⁻¹' (H : Set K) := fun i => by
    ext v
    simp only [A, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro rfl; exact hσ v
    · intro hv
      apply e.injective
      rw [Equiv.apply_symm_apply, ← hr]
      exact (QuotientGroup.eq.mpr hv).symm
  have hμA : ∀ i, μ (A i) = μ H := fun i => by
    rw [hA]; exact measure_preimage_mul μ (r i)⁻¹ _

  have hsum : ∑ i, μ (A i) = 1 := by
    have hdisj : Pairwise (Function.onFun Disjoint A) := fun i j hij =>
      Set.disjoint_iff.mpr fun v ⟨hi, hj⟩ => hij (hi.symm.trans hj)
    have h1 : μ (⋃ i, A i) = ∑' i, μ (A i) := measure_iUnion hdisj hAm
    rw [tsum_fintype] at h1
    rw [← h1, ← measure_univ (μ := μ)]
    congr 1; ext v; simp [A]
  have hμH : μ (H : Set K) = 1 / (n : ENNReal) := by
    simp only [hμA, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    exact (ENNReal.eq_div_iff (by exact_mod_cast hn0.ne') (ENNReal.natCast_ne_top n)).mpr hsum
  have hμrA : ∀ i, μ.real (A i) = (n : ℝ)⁻¹ := fun i => by
    rw [measureReal_def, hμA, hμH, one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  intro h hh

  have hconst : ∀ v, h v = ∑ i, (A i).indicator (fun _ => h (r i)) v := fun v => by
    rw [Finset.sum_eq_single (σ v)]
    · rw [Set.indicator_of_mem (by simp [A])]
      conv_lhs => rw [show v = r (σ v) * ((r (σ v))⁻¹ * v) by group]
      exact hh _ _ (hσ v)
    · intro i _ hi
      exact Set.indicator_of_notMem (by simpa [A] using fun h' => hi h'.symm) _
    · simp
  calc ∫ v, h v ∂μ = ∫ v, ∑ i, (A i).indicator (fun _ => h (r i)) v ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hconst)
    _ = ∑ i, ∫ v, (A i).indicator (fun _ => h (r i)) v ∂μ :=
        integral_finsetSum _ fun i _ => (integrable_const _).indicator (hAm i)
    _ = ∑ i, (μ.real (A i)) • h (r i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact integral_indicator_const _ (hAm i)
    _ = (n : ℂ)⁻¹ * ∑ i, h (r i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hμrA, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

end S_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup
end P2MW
export P2MW.S_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup (solution)
