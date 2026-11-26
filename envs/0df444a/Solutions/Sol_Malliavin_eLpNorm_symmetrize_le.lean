-- Prove2me | solution 1 for Malliavin.eLpNorm_symmetrize_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:18.119973+00:00
-- url     : https://prove2.me/submissions/34ab4bd8-4fa0-4748-b702-d75a788a1542

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrize_eq_smul_sum
import Theorems.Thm_Malliavin_aestronglyMeasurable_comp_perm

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ}
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → T) → E}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin n => μ)) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (symmetrize n f) p (Measure.pi fun _ : Fin n => μ) ≤
      eLpNorm f p (Measure.pi fun _ : Fin n => μ) := by
  set ν : Measure (Fin n → T) := Measure.pi fun _ : Fin n => μ with hν
  have hfac : (n.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [symmetrize_eq_smul_sum, eLpNorm_const_smul]
  calc ‖(n.factorial : ℝ)⁻¹‖ₑ *
        eLpNorm (∑ σ : Equiv.Perm (Fin n), f ∘ fun t : Fin n → T => t ∘ σ) p ν
      ≤ ‖(n.factorial : ℝ)⁻¹‖ₑ *
        ∑ σ : Equiv.Perm (Fin n), eLpNorm (f ∘ fun t : Fin n → T => t ∘ σ) p ν := by
        gcongr
        exact eLpNorm_sum_le (fun σ _ => aestronglyMeasurable_comp_perm hf σ) hp
    _ = ‖(n.factorial : ℝ)⁻¹‖ₑ * ∑ _σ : Equiv.Perm (Fin n), eLpNorm f p ν := by
        congr 1
        exact Finset.sum_congr rfl fun σ _ =>
          eLpNorm_comp_measurePreserving hf (measurePreserving_comp_perm μ n σ)
    _ = ‖(n.factorial : ℝ)⁻¹‖ₑ * ((n.factorial : ℝ≥0∞) * eLpNorm f p ν) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    _ = eLpNorm f p ν := by
        rw [enorm_inv (by exact_mod_cast n.factorial_ne_zero), Real.enorm_natCast, ← mul_assoc,
          ENNReal.inv_mul_cancel hfac (ENNReal.natCast_ne_top _), one_mul]
end Malliavin
