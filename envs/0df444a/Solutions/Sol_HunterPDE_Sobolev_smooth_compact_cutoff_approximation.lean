-- Prove2me | solution 1 for HunterPDE.Sobolev.smooth_compact_cutoff_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:36:01.529311+00:00
-- url     : https://prove2.me/submissions/d5257394-e9b1-4d96-8957-99ea8b140d99

import Theorems.Thm_HunterPDE_Sobolev_memW_of_isTestFunction
import Theorems.Thm_HunterPDE_Sobolev_tendsto_weakDeriv_cutoff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.ConstMulAction

open MeasureTheory Filter HunterPDE.Sobolev
open scoped Topology

theorem solution {n k : ℕ}
    {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgW : MemW k p Set.univ g)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsTestFunction Set.univ φ ∧ MemW k p Set.univ φ ∧
        sobolevNorm k p Set.univ (g - φ) < ε := by
  classical
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hχ : IsTestFunction Set.univ χ :=
    ⟨χ.contDiff, χ.hasCompactSupport, Set.subset_univ _⟩
  let φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun j x => χ (((j : ℝ) + 1)⁻¹ • x) * g x
  have hφ (j : ℕ) : IsTestFunction Set.univ (φ j) := by
    have hj : (j : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    refine ⟨(χ.contDiff.comp (contDiff_id.const_smul _)).mul hg, ?_, Set.subset_univ _⟩
    exact (χ.hasCompactSupport.comp_smul (inv_ne_zero hj)).mul_right
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hsum : Tendsto (fun j => ∑ α ∈ multiIndices n k,
      eLpNorm (weakDeriv Set.univ α (g - φ j)) p volume ^ p.toReal)
      atTop (𝓝 0) := by
    have hterm (α : Fin n → ℕ) (hα : α ∈ multiIndices n k) :=
      (tendsto_weakDeriv_cutoff hp hptop g χ hgW hχ χ.eventuallyEq_one α
        (Finset.mem_filter.mp hα).2).ennrpow_const p.toReal
    simpa [ENNReal.zero_rpow_of_pos hpr, φ] using
      (tendsto_finsetSum (multiIndices n k) hterm)
  have hnorm : Tendsto (fun j => sobolevNorm k p Set.univ (g - φ j))
      atTop (𝓝 0) := by
    simpa [sobolevNorm, hptop, ENNReal.zero_rpow_of_pos (inv_pos.mpr hpr)] using
      hsum.ennrpow_const (1 / p.toReal)
  obtain ⟨j, hj⟩ := (hnorm.eventually (gt_mem_nhds hε)).exists
  exact ⟨φ j, hφ j, memW_of_isTestFunction hp (φ j) (hφ j), hj⟩
