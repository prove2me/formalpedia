-- Prove2me | solution 1 for GlobalTheory.exists_eq_sum_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:50.979096+00:00
-- url     : https://prove2.me/submissions/72195110-07a0-4889-b4e3-0d8665fcee20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_GlobalTheory_constDerivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pderivEval_X
attribute [local simp] GlobalTheory.constDerivEval_X

set_option autoImplicit false
open GlobalTheory
open Finsupp
open MvPowerSeries
variable {R σ Λ M : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [Fintype σ] {n : ℕ} {g : MvPowerSeries σ R}
    (hg : ∀ d : σ →₀ ℕ, degree d < n + 1 → coeff d g = 0) :
    ∃ h : σ → MvPowerSeries σ R, (∀ i (d : σ →₀ ℕ), degree d < n → coeff d (h i) = 0) ∧
      g = ∑ i, X i * h i := by
  classical
  have hidx : ∀ d : σ →₀ ℕ, d ≠ 0 → ∃ i, d i ≠ 0 := fun d hd => by
    by_contra hc
    push Not at hc
    exact hd (Finsupp.ext hc)
  choose idx hidx using hidx
  let part : σ → MvPowerSeries σ R := fun i d =>
    if hd : d ≠ 0 then (if idx d hd = i then coeff d g else 0) else 0
  have hpart : ∀ i d, coeff d (part i) =
      if hd : d ≠ 0 then (if idx d hd = i then coeff d g else 0) else 0 := fun _ _ => rfl
  have hdvd : ∀ i, (X i : MvPowerSeries σ R) ∣ part i := fun i => by
    rw [X_dvd_iff]
    intro d hd
    rw [hpart]
    split_ifs with h₁ h₂
    · exact absurd hd (h₂ ▸ hidx d h₁)
    · rfl
    · rfl
  choose h hh using hdvd
  refine ⟨h, fun i d hd => ?_, ?_⟩
  · have h₁ : coeff (single i 1 + d) (part i) = coeff d (h i) := by
      rw [hh, X_def, coeff_add_monomial_mul, one_mul]
    rw [← h₁, hpart]
    have h₂ : coeff (single i 1 + d) g = 0 := hg _ (by simp; omega)
    simp [h₂]
  · ext d
    simp only [← hh, map_sum, hpart]
    by_cases hd : d = 0
    · subst hd
      simpa using hg 0 (by simp)
    · simp [hd]
end GlobalTheory
