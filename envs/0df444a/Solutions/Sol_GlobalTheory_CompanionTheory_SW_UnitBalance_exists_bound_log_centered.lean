-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitBalance.exists_bound_log_centered
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:35:12.264641+00:00
-- url     : https://prove2.me/submissions/47c8ddb3-dc46-41ad-930c-ae64e5dd5ebf

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitBalancingImaginaryParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitBalance
open NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace GlobalTheory.CompanionTheory.SW.UnitBalance
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (s : ℝ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (u : E)) - s| ≤ R := by
  classical
  let B := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)
  obtain ⟨C, hC⟩ := (ZSpan.fundamentalDomain_isBounded B).exists_norm_le
  refine ⟨Fintype.card (InfinitePlace E) * |C|, fun t => ?_⟩
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  let s : ℝ := (∑ w : InfinitePlace E, (w.mult : ℝ) * t w) / Module.finrank ℚ E
  let l : logSpace E := fun w => (w.1.mult : ℝ) * (t w.1 - s)
  obtain ⟨⟨e, he⟩, h2, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B l
  rw [Module.Basis.ofZLatticeBasis_span ℝ (unitLattice E)] at he
  obtain ⟨u, -, rfl⟩ := he
  let a : InfinitePlace E → ℝ := fun w => (w.mult : ℝ) * (t w - s + Real.log (w (u.toMul : E)))
  have hsum : ∑ w, a w = 0 := by
    have h1 := sum_mult_mul_log (K := E) u.toMul
    have h3 : ∑ w : InfinitePlace E, (w.mult : ℝ) = Module.finrank ℚ E := by
      exact_mod_cast InfinitePlace.sum_mult_eq (K := E)
    simp only [a, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, h3, s]
    field_simp
    ring
  have ha : ∀ w, w ≠ w₀ → |a w| ≤ |C| := fun w hw => by
    have h4 := (norm_le_pi_norm _ (⟨w, hw⟩ : {w : InfinitePlace E // w ≠ w₀})).trans (hC _ h2)
    refine le_trans (le_of_eq ?_) (h4.trans (le_abs_self C))
    rw [Real.norm_eq_abs]
    congr 1
    change _ = (w.mult : ℝ) * Real.log (w (u.toMul : E)) + (w.mult : ℝ) * (t w - s)
    simp only [a]
    ring
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
  have ha' : ∀ w, |a w| ≤ Fintype.card (InfinitePlace E) * |C| := fun w => by
    by_cases hw : w = w₀
    · subst hw
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀), add_eq_zero_iff_eq_neg] at hsum
      rw [hsum, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ _ fun w hw => ha w (Finset.ne_of_mem_erase hw)).trans ?_
      rw [nsmul_eq_mul]
      gcongr
      exact Finset.card_le_univ _
    · exact (ha w hw).trans (le_mul_of_one_le_left (abs_nonneg C) hcard)
  refine ⟨u.toMul, s, fun w => ?_⟩
  have h5 : |t w - s + Real.log (w (u.toMul : E))| ≤ |a w| := by
    simp only [a]
    rw [abs_mul]
    refine le_mul_of_one_le_left (abs_nonneg _) ?_
    rw [Nat.abs_cast]
    exact_mod_cast w.mult_pos
  have h6 := h5.trans (ha' w)
  have h7 : t w + Real.log (w (u.toMul : E)) - s = t w - s + Real.log (w (u.toMul : E)) := by ring
  rw [h7]
  exact h6
end GlobalTheory.CompanionTheory.SW.UnitBalance
