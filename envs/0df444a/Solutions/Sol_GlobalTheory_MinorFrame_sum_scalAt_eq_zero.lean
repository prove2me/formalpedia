-- Prove2me | solution 1 for GlobalTheory.MinorFrame.sum_scalAt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:28:11.33325+00:00
-- url     : https://prove2.me/submissions/b8d9f344-af6f-4f1c-b641-22295c35c861

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
import Theorems.Thm_GlobalTheory_MinorFrame_colSub_scalAt_monomial
import Theorems.Thm_GlobalTheory_MinorFrame_degAt_le
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame
theorem _root_.solution {d a : ℕ} (τ₀ : ι) (N : ℕ) (hN : 0 < N) (P : Pol ι d a) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (N + P.totalDegree + 1)) :
    ∑ k ∈ Finset.range (N + P.totalDegree + 1), (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P = 0 := by
  generalize hM : N + P.totalDegree + 1 = M at hω ⊢
  conv_lhs => rw [as_sum P]
  simp only [map_sum, colSub_scalAt_monomial, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t ht => ?_
  have hsum : ∑ k ∈ Finset.range M, (ω ^ (N + degAt τ₀ t)) ^ k = 0 := by
    have hne : ω ^ (N + degAt τ₀ t) ≠ 1 := by
      rw [Ne, hω.pow_eq_one_iff_dvd]
      intro hdvd
      have h1 := degAt_le τ₀ t
      have h2 := le_totalDegree ht
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]
  have : ∀ k ∈ Finset.range M,
      (ω ^ k) ^ N • (monomial t (coeff t P * (ω ^ k) ^ degAt τ₀ t) : Pol ι d a) =
        monomial t (coeff t P * (ω ^ (N + degAt τ₀ t)) ^ k) := by
    intro k _
    rw [smul_monomial, smul_eq_mul]
    congr 1
    rw [← pow_mul, ← pow_mul, ← pow_mul, show (N + degAt τ₀ t) * k = k * N + k * degAt τ₀ t by ring, pow_add]
    ring
  rw [Finset.sum_congr rfl this, ← map_sum, ← Finset.mul_sum, hsum, mul_zero, map_zero]
end GlobalTheory.MinorFrame
