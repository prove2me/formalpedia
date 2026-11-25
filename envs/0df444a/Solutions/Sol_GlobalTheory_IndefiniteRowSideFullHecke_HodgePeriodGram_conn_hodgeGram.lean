-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.conn_hodgeGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:26.886743+00:00
-- url     : https://prove2.me/submissions/bb6e4e96-250d-4aad-a11b-9768d4634923

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Theorems.Thm_GlobalTheory_HermFrame_conn_eq_of_isSymm
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
open GlobalTheory.HermFrame
variable {n a g : ℕ}
open Matrix Complex Filter Topology
open scoped ComplexOrder
variable {n a g : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
theorem _root_.solution {rk : ℕ} (ha : a ≤ n) {τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {B : Fin a → Matrix (Fin g) (Fin g) ℤ} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B) {z : Fin n → ℂ}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) (ξ : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.conn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ =
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z)⁻¹ * _root_.GlobalTheory.HermFrame.mdel (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ := by
  apply _root_.GlobalTheory.HermFrame.conn_eq_of_isSymm
  have hnear : ∀ᶠ x in 𝓝 z, x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1 :=
    Filter.eventually_all.2 fun k =>
      (continuous_apply k).norm.continuousAt.eventually_lt continuousAt_const (hz k)
  filter_upwards [hnear] with x hx
  have hB : ∀ i, ((B i).map (Int.cast : ℤ → ℝ))ᵀ = (B i).map (Int.cast : ℤ → ℝ) := fun i => by
    have := (h.psd i).isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hτ : ((τ₀ x).map Complex.im)ᵀ = (τ₀ x).map Complex.im := by
    rw [← Matrix.transpose_map, (h.symm x hx).eq]
  have hI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B x).IsSymm := by
    unfold Matrix.IsSymm _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod
    rw [Matrix.transpose_add, Matrix.transpose_sum, hτ]
    simp only [Matrix.transpose_smul, hB]
  exact hI.map _
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
end GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
