-- Prove2me | solution 1 for HamLocality237.Testing.theorem_3_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T05:22:16.730223+00:00
-- url     : https://prove2.me/submissions/cc595136-a50b-4b27-8f59-19a11c441dc1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HamLocality237_Testing_Adversary
import Theorems.Thm_HamLocality237_Testing_lemma_3_6
import Theorems.Thm_HamLocality237_Testing_lemma_3_9

open MeasureTheory
open scoped BigOperators TensorProduct

namespace HamLocality237.Testing

lemma dyson_zero' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : ℝ → E →L[ℂ] E) : dysonEvolution F 0 = 1 := by
  unfold dysonEvolution
  rw [tsum_eq_single 0]
  · rfl
  · intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simp [dysonTerm]

lemma algebraicLift_product {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    ∀ (m : ℕ) (j : Fin m) (a : E →L[ℂ] E) (u : Fin m → E),
    algebraicLift m j a (algebraicProduct m u) =
      algebraicProduct m (Function.update u j (a (u j)))
  | 0, j, _, _ => Fin.elim0 j
  | m + 1, j, a, u => by
    refine Fin.cases ?_ (fun i => ?_) j
    · have e : algebraicLift (m + 1) 0 a = TensorProduct.mapL a (ContinuousLinearMap.id ℂ (AlgebraicPower E m)) := by
        simp [algebraicLift]
      rw [e]
      show (a (u 0)) ⊗ₜ[ℂ] algebraicProduct m (fun j => u j.succ) = _
      show _ = (Function.update u 0 (a (u 0)) 0) ⊗ₜ[ℂ] algebraicProduct m (fun j => Function.update u 0 (a (u 0)) j.succ)
      rw [Function.update_self]
      congr 2
    · have e : algebraicLift (m + 1) i.succ a = TensorProduct.mapL (ContinuousLinearMap.id ℂ E) (algebraicLift m i a) := by
        simp [algebraicLift]
      rw [e]
      show (u 0) ⊗ₜ[ℂ] (algebraicLift m i a (algebraicProduct m (fun j => u j.succ))) = _
      rw [algebraicLift_product m i a]
      show _ = (Function.update u i.succ (a (u i.succ)) 0) ⊗ₜ[ℂ] algebraicProduct m (fun j => Function.update u i.succ (a (u i.succ)) j.succ)
      rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 2
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · rw [Function.update_of_ne hk, Function.update_of_ne]
        exact fun h => hk (Fin.succ_injective _ h)

lemma hilbertLift_product {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {m : ℕ} (j : Fin m) (a : E →L[ℂ] E) (u : Fin m → E) :
    hilbertLift j a (hilbertProduct u) = hilbertProduct (Function.update u j (a (u j))) := by
  unfold hilbertLift hilbertProduct
  rw [ContinuousLinearMap.completion_apply_coe, algebraicLift_product]

lemma singleCorrection_bottom : singleCorrection bottomVector = 0 := by
  unfold singleCorrection pairRegister
  have : bandPart bottomVector = 0 := by
    simp [bandPart, bottomVector]
  simp [this]

lemma algebraicProduct_zero {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    ∀ (m : ℕ) (j : Fin m) (u : Fin m → E), u j = 0 → algebraicProduct m u = 0
  | 0, j, _, _ => Fin.elim0 j
  | m + 1, j, u, h => by
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
    · simp [algebraicProduct, h]
    · simp only [algebraicProduct]
      rw [algebraicProduct_zero m i _ h, TensorProduct.tmul_zero]

lemma fullCorrection_vacuum (n : ℕ) : fullCorrection n (inputVacuum n) = 0 := by
  unfold fullCorrection
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro x _
  unfold inputLift inputVacuum
  rw [hilbertLift_product, singleCorrection_bottom]
  unfold hilbertProduct
  rw [algebraicProduct_zero _ (siteEnumeration n x) _ (by simp)]
  rfl

lemma jointLift_product {n : ℕ} (A : ContinuousAlgorithm n) (a : A.Space →L[ℂ] A.Space)
    (b : InputRegister n →L[ℂ] InputRegister n) (v : A.Space) (r : InputRegister n) :
    jointLift A a b (jointProduct A v r) = jointProduct A (a v) (b r) := by
  unfold jointLift jointProduct
  rw [ContinuousLinearMap.completion_apply_coe]
  rfl

lemma bottom_norm : ‖bottomVector‖ = 1 := by
  simp [bottomVector, WithLp.prod_norm_eq_of_L2]

lemma progress_zero {n : ℕ} (A : ContinuousAlgorithm n) (ε : ℝ) : progress A ε 0 = 0 := by
  have hv : inner ℂ (jointProduct A A.initial (inputVacuum n))
      (jointProduct A A.initial (inputVacuum n)) = 1 := by
    unfold jointProduct
    rw [UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]
    have h1 : inner ℂ A.initial A.initial = (1:ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, A.initial_unit]; simp
    have h2 : inner ℂ (inputVacuum n) (inputVacuum n) = (1:ℂ) := by
      unfold inputVacuum
      rw [hilbertProduct_inner]
      simp [inner_self_eq_norm_sq_to_K, bottom_norm]
    rw [h1, h2]; simp
  unfold progress purifiedFar purifiedZero
  rw [dyson_zero', dyson_zero']
  simp only [ContinuousLinearMap.one_apply]
  rw [jointLift_product, fullCorrection_vacuum]
  simp only [jointProduct] at hv ⊢
  rw [hv, TensorProduct.tmul_zero, UniformSpace.Completion.coe_zero, inner_zero_right]
  simp

end HamLocality237.Testing

open HamLocality237.Testing MeasureTheory in
theorem solution (n : ℕ) (A : ContinuousAlgorithm n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ‖purifiedFar A ε A.finalTime - purifiedZero A A.finalTime‖ ^ 2 ≤
      2 * progressConstant * ε ^ 2 * A.time := by
  have h6 := lemma_3_6 n A ε hε hε'
  obtain ⟨hac, hae⟩ := lemma_3_9 n A ε hε hε'
  have hft := A.finalTime_nonneg
  have hI : IntervalIntegrable A.intensity volume 0 A.finalTime :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hft).2 A.intensity_integrable
  have hd := hac.intervalIntegrable_deriv
  have hftc := hac.integral_deriv_eq_sub
  rw [progress_zero] at hftc
  have hmono : ∫ x in (0:ℝ)..A.finalTime, deriv (progress A ε) x ≤
      ∫ x in (0:ℝ)..A.finalTime, progressConstant * ε ^ 2 * A.intensity x := by
    apply intervalIntegral.integral_mono_ae_restrict hft hd (hI.const_mul _)
    filter_upwards [hae] with t ht using ht.2
  rw [intervalIntegral.integral_const_mul] at hmono
  have : A.time = ∫ x in (0:ℝ)..A.finalTime, A.intensity x := rfl
  rw [← this] at hmono
  nlinarith
