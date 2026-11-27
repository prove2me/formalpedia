-- Prove2me | solution 1 for GlobalTheory.exists_section_jet_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:16.97831+00:00
-- url     : https://prove2.me/submissions/b45f7dc7-6467-4c4b-89af-8f2badd49304

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Theorems.Thm_GlobalTheory_ThetaJet_jets_span
import Theorems.Thm_GlobalTheory_dirPolyDeriv_eq_sum_coeff_taylorDir
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
open ThetaJet
open Classical
namespace GlobalTheory
theorem _root_.solution {ι : Type} [Fintype ι] (Y : GT ι) (θ : EuclideanSpace ℂ ι → ℂ) (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    (D q : ℕ) (hq : 3 * D + 2 ≤ q) (P : MvPolynomial ι ℂ) (hP : P ≠ 0) (hD : P.totalDegree ≤ D) :
    ∃ F : EuclideanSpace ℂ ι → ℂ, Differentiable ℂ F ∧
      (∀ γ ∈ lat Y.b, ∀ v, F (v + γ) = Y.ka γ ^ q * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * F v) ∧
      polyDeriv P (fun i => EuclideanSpace.single i 1) F 0 ≠ 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 * D := ⟨q - 3 * D, by omega⟩
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hP
  obtain ⟨_, ⟨F, hF, rfl⟩, hs⟩ :=
    jets_span hθ h0 (r := r) (by omega) D (MvPowerSeries.monomial m 1)
  refine ⟨F, hF.1, hF.2, ?_⟩
  rw [dirPolyDeriv_eq_sum_coeff_taylorDir, Finset.sum_congr rfl (g := fun d => P.coeff d *
    ((∏ i, (d i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff d (MvPowerSeries.monomial m (1 : ℂ))),
    Finset.sum_eq_single m]
  · rw [MvPowerSeries.coeff_monomial_same, mul_one]
    exact mul_ne_zero hm (cast_prod_factorial_ne_zero m)
  · intro d _ hd
    rw [MvPowerSeries.coeff_monomial_ne hd, mul_zero]
  · intro h
    exact absurd (MvPolynomial.mem_support_iff.2 hm) h
  · intro d hd
    have h1 : d.degree ≤ D := (MvPolynomial.le_totalDegree hd).trans hD
    have h2 := mem_germIdeal_pow_iff.1 hs d (by omega)
    rw [map_sub, sub_eq_zero] at h2
    rw [h2]
end GlobalTheory
