-- Prove2me | solution 1 for GlobalTheory.NearZeroDeriv.power_sum_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:45.168394+00:00
-- url     : https://prove2.me/submissions/6934ba96-8f2e-4fcb-881e-c9cc3ddd3eee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.NearZeroDeriv
namespace GlobalTheory.NearZeroDeriv
theorem _root_.solution {C : ℝ} (hC : 1 ≤ C)
    (hT : ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖)
    (Z : Finset ℂ) (m : ℂ → ℕ) (f : ℂ → ℂ) (K : ℕ) (hK : ∑ w ∈ Z, m w ≤ K) (ρ : ℂ) (hρ : ρ ∈ Z)
    (hm : 1 ≤ m ρ) : ∃ j : ℕ, K + 1 ≤ j ∧ j ≤ 2 * K ∧
      (‖f ρ‖ / (2 * C)) ^ j ≤ ‖∑ w ∈ Z, (m w : ℂ) * f w ^ j‖ := by
  have hK1 : 1 ≤ K := hm.trans ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hρ).trans hK)
  let ι := (Σ w : Z, Fin (m w)) ⊕ Fin (K - ∑ w ∈ Z, m w)
  have hc : Fintype.card ι = K := by
    simp only [ι, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    rw [Finset.sum_coe_sort Z m]; omega
  let e : ι ≃ Fin K := Fintype.equivFinOfCardEq hc
  let g : ι → ℂ := Sum.elim (fun p => f p.1) (fun _ => 0)
  obtain ⟨j, h1, h2, h3⟩ := hT K K (fun i => g (e.symm i)) (e (Sum.inl ⟨⟨ρ, hρ⟩, ⟨0, hm⟩⟩))
  refine ⟨j, h1, by omega, ?_⟩
  have hj : j ≠ 0 := by omega
  have es : ∑ i, g (e.symm i) ^ j = ∑ w ∈ Z, (m w : ℂ) * f w ^ j := by
    rw [Equiv.sum_comp e.symm (fun x => g x ^ j), Fintype.sum_sum_type, Fintype.sum_sigma]
    simp [g, hj, Finset.sum_attach Z (fun w => (m w : ℂ) * f w ^ j)]
  rw [es, Equiv.symm_apply_apply] at h3
  refine le_trans ?_ h3
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK1
  have e1 : (K : ℝ) / (C * (K + K)) = 1 / (2 * C) := by field_simp; ring
  rw [e1, div_eq_mul_one_div, mul_pow, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_of_le_one (by positivity) (by rw [div_le_one (by positivity)]; linarith)
    (by omega)
end GlobalTheory.NearZeroDeriv
