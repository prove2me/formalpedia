-- Prove2me | solution 1 for GlobalTheory.Chow.algebraicIndependent_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:39.889523+00:00
-- url     : https://prove2.me/submissions/4c36a25a-5817-4705-afdf-351dbd3026e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.Chow
theorem _root_.solution {K F β : Type*} [Field K] [Field F] [Algebra K F] {z : β → F}
    (hz : AlgebraicIndependent K z) (i₀ : β) :
    AlgebraicIndependent K fun i : {i // i ≠ i₀} => z i / z i₀ := by
  classical
  have h0 : z i₀ ≠ 0 := hz.ne_zero i₀
  let π : MvPolynomial β K →ₐ[K] MvPolynomial {i // i ≠ i₀} K :=
    aeval fun i => if h : i = i₀ then 1 else X ⟨i, h⟩
  have hπ0 : π (X i₀) = 1 := by simp [π]
  have key (P : MvPolynomial {i // i ≠ i₀} K) : ∃ (m : ℕ) (Q : MvPolynomial β K),
      aeval z Q = z i₀ ^ m * aeval (fun i : {i // i ≠ i₀} => z i / z i₀) P ∧ π Q = P := by
    induction P using MvPolynomial.induction_on with
    | C a => exact ⟨0, C a, by simp, by simp⟩
    | add p q hp hq =>
      obtain ⟨m, p', hp, hp'⟩ := hp
      obtain ⟨n, q', hq, hq'⟩ := hq
      refine ⟨m + n, p' * X i₀ ^ n + q' * X i₀ ^ m, ?_, by simp [hπ0, hp', hq']⟩
      simp only [map_add, map_mul, map_pow, aeval_X, hp, hq]
      ring
    | mul_X p i hp =>
      obtain ⟨m, p', hp, hp'⟩ := hp
      refine ⟨m + 1, p' * X i.1, ?_, by rw [map_mul, hp']; simp [π, i.2]⟩
      simp only [map_mul, aeval_X, hp]
      field_simp
      ring
  rw [algebraicIndependent_iff] at hz ⊢
  intro P hP
  obtain ⟨m, Q, hQ, rfl⟩ := key P
  rw [hz Q (by rw [hQ, hP, mul_zero]), map_zero]
end GlobalTheory.Chow
