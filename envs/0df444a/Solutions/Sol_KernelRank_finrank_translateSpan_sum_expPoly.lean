-- Prove2me | solution 1 for KernelRank.finrank_translateSpan_sum_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:43:28.215939+00:00
-- url     : https://prove2.me/submissions/644ebfbf-694d-4f0f-96f8-8eee412888e6

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
import Theorems.Thm_KernelRank_expPoly_translate
import Theorems.Thm_KernelRank_expPolyAnnihilator_natDegree
import Theorems.Thm_KernelRank_differentialOperator_sum_expPoly_eq_zero_iff
import Theorems.Thm_KernelRank_exists_charpoly_differential_annihilator
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Fintype ι] {rate : ι → ℂ}
    (hinj : Function.Injective rate) (P : ι → ℂ[X]) (hP : ∀ i, P i ≠ 0) :
    FiniteDimensional ℂ (translateSpan (fun t => ∑ i, expPoly (P i) (rate i) t)) ∧
      Module.finrank ℂ (translateSpan (fun t => ∑ i, expPoly (P i) (rate i) t)) =
        ∑ i, ((P i).natDegree + 1) := by
  classical
  let ψ := fun t => ∑ i, expPoly (P i) (rate i) t
  let f (j : Σ i, Fin ((P i).natDegree + 1)) (u : ℝ≥0) :=
    expPoly (X ^ (j.2 : ℕ)) (rate j.1) u
  have hG (t : ℝ≥0) :
      (fun u : ℝ≥0 => ψ (u + t)) =
        ∑ j, expPoly (hasseDeriv j.2 (P j.1)) (rate j.1) t • f j := by
    ext u
    simp only [f, ψ, Finset.sum_apply, smul_eq_mul, Pi.smul_apply, Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun i _ => by
      rw [expPoly_translate (Nat.lt_succ_self _)]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hspan : translateSpan ψ ≤ Submodule.span ℂ (Set.range f) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, rfl⟩
    change (fun u : ℝ≥0 => ψ (u + t)) ∈ Submodule.span ℂ (Set.range f)
    rw [hG t]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  have hfin := Submodule.finiteDimensional_of_le hspan
  let : FiniteDimensional ℂ (translateSpan ψ) := hfin
  have hcont : Continuous ψ := by
    dsimp [ψ, expPoly]
    fun_prop
  obtain ⟨q, hq, hdeg, hann⟩ := exists_charpoly_differential_annihilator ψ hcont.continuousOn
  refine ⟨hfin, le_antisymm ?_ ?_⟩
  · calc
      Module.finrank ℂ (translateSpan ψ) ≤
          Module.finrank ℂ (Submodule.span ℂ (Set.range f)) := Submodule.finrank_mono hspan
      _ ≤ Fintype.card (Σ i, Fin ((P i).natDegree + 1)) := finrank_range_le_card f
      _ = _ := by simp
  · rw [← hdeg, ← expPolyAnnihilator_natDegree P rate]
    exact natDegree_le_of_dvd
      ((differentialOperator_sum_expPoly_eq_zero_iff P rate hinj hP q).mp hann) hq.ne_zero
end KernelRank
