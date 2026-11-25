-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.coeff_extract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:46.503339+00:00
-- url     : https://prove2.me/submissions/5719f938-b4b4-4fff-b09f-041d6c6c0fb1

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeNonScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
namespace GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] (T : Module.End ℂ W) (k : ℕ) (hk : 2 ≤ k)
    (w : ℕ → W) (P : ℂ[X]) (u : W) (hP : (X : ℂ[X]) ^ 2 ∣ P)
    (h : ∀ t : ℂ, T (∑ i ∈ range k, t ^ i • w i) + t • ∑ i ∈ range k, t ^ i • w i = P.eval t • u) :
    T (w 0) = 0 ∧ T (w 1) + w 0 = 0 := by
  have hP' := (X_pow_dvd_iff (f := P) (n := 2)).1 hP
  have hP0 := hP' 0 (by norm_num)
  have hP1 := hP' 1 (by norm_num)
  have key : ∀ φ : Module.Dual ℂ W, φ (T (w 0)) = 0 ∧ φ (T (w 1) + w 0) = 0 := by
    intro φ
    have hQ : (∑ i ∈ range k, C (φ (T (w i))) * X ^ i) + X * (∑ i ∈ range k, C (φ (w i)) * X ^ i)
        - C (φ u) * P = 0 := by
      refine Polynomial.funext fun t => ?_
      have := congrArg φ (h t)
      simp only [map_add, map_sum, map_smul, smul_eq_mul] at this
      simp only [eval_sub, eval_add, eval_mul, eval_finset_sum, eval_C, eval_X, eval_pow, eval_zero]
      rw [sub_eq_zero, mul_comm (φ u)]
      simp only [mul_comm (φ _) (t ^ _)]
      exact this
    have c0 := congrArg (fun q : ℂ[X] => q.coeff 0) hQ
    have c1 := congrArg (fun q : ℂ[X] => q.coeff 1) hQ
    have k0 : 0 ∈ range k := mem_range.2 (by omega)
    have k1 : 1 ∈ range k := mem_range.2 (by omega)
    simp only [coeff_sub, coeff_add, finset_sum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero,
      mul_ite, mul_one, mul_zero, coeff_X_mul, coeff_X_mul_zero, hP0, hP1] at c0 c1
    simp [k0, k1] at c0 c1
    exact ⟨c0, by rw [map_add]; exact c1⟩
  exact ⟨(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => (key φ).1,
    (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => (key φ).2⟩
end GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
