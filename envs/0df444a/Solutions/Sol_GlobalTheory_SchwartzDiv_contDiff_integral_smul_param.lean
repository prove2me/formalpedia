-- Prove2me | solution 1 for GlobalTheory.SchwartzDiv.contDiff_integral_smul_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:35:51.34119+00:00
-- url     : https://prove2.me/submissions/358b5dec-e9e5-4dd9-be37-b913f5c5520e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
import Theorems.Thm_GlobalTheory_SchwartzDiv_hasFDerivAt_integral_smul_param

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric
noncomputable section
open GlobalTheory GlobalTheory.SchwartzDiv
variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}
namespace GlobalTheory.SchwartzDiv
theorem _root_.solution (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ fun t => ∫ y, φ y • Θ (t, c y) ∂ν := by
  rw [contDiff_infty]
  intro n
  induction n generalizing W with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t).continuousAt)
  | succ n ih =>
    have hΘ' : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
      ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
        (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨fun t => ∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t ∂ν,
      ih hΘ', fun t => hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t⟩
end GlobalTheory.SchwartzDiv
