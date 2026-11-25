-- Prove2me | solution 1 for GlobalTheory.FiniteQuotOmega.det_smul_kaehler_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:21:39.987878+00:00
-- url     : https://prove2.me/submissions/8fd8f1d8-d9fe-424c-80b3-81b3e9a2985d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JacobianSmulKaehlerEqZero
import Theorems.Thm_GlobalTheory_FiniteQuotOmega_derivation_apply_eq_sum
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.FiniteQuotOmega
open MvPowerSeries IsLocalRing
open scoped TensorProduct
variable {T Q σ : Type*} [CommRing T] [CommRing Q] [Algebra T Q] [Fintype σ]
namespace GlobalTheory.FiniteQuotOmega
theorem _root_.solution [DecidableEq σ] [IsNoetherianRing T] [Module.Finite T Q]
    (φ : MvPowerSeries σ T →ₐ[T] Q) (hφ : Function.Surjective φ) (f : σ → MvPowerSeries σ T)
    (hf : ∀ i, φ (f i) = 0) (ω : KaehlerDifferential T Q) :
    φ (Matrix.det (Matrix.of fun i j => pderiv T j (f i))) • ω = 0 := by
  haveI : IsNoetherianRing Q := IsNoetherianRing.of_finite T Q
  set D := KaehlerDifferential.D T Q with hD
  set A : Matrix σ σ Q := Matrix.of fun i j => φ (pderiv T j (f i)) with hA
  have hdet : φ (Matrix.det (Matrix.of fun i j => pderiv T j (f i))) = A.det := by
    rw [AlgHom.map_det]; rfl
  have hrel : ∀ i, ∑ j, A i j • D (φ (X j)) = 0 := fun i => by
    have := derivation_apply_eq_sum φ hφ D (f i)
    rw [hf, map_zero] at this
    exact this.symm
  have hx : ∀ l, A.det • D (φ (X l)) = 0 := fun l => by
    have h : ∑ j, (A.adjugate * A) l j • D (φ (X j)) = 0 := by
      simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hrel, smul_zero, Finset.sum_const_zero]
    rw [Matrix.adjugate_mul] at h
    simpa [Matrix.one_apply] using h
  rw [hdet]
  have hω : ω ∈ Submodule.span Q (Set.range D) := by
    rw [hD, KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x h =>
    obtain ⟨y, rfl⟩ := h
    obtain ⟨g, rfl⟩ := hφ y
    rw [derivation_apply_eq_sum φ hφ D g, Finset.smul_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [smul_comm, hx, smul_zero]
  | zero => simp
  | add x y _ _ h1 h2 => rw [smul_add, h1, h2, add_zero]
  | smul a x _ h => rw [smul_comm, h, smul_zero]
end GlobalTheory.FiniteQuotOmega
