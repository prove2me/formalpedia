-- Prove2me | solution 1 for KLTNuclear.Oracle.eq_2_9
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T13:08:33.981338+00:00
-- url     : https://prove2.me/submissions/15511e8d-6bc5-4fee-a0a8-28fd0bb10733

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

/-! KLT, arXiv:1011.6256v4, Eq.(2.9), p.8.
Formalization: Alexander Richard Towell / queelius, with substantial OpenAI Codex assistance.
No predecessor proof body is used in this polarization proof. -/
open MeasureTheory MatrixCompletion
open scoped BigOperators
namespace KLTWork

lemma inner_comm {m k : ℕ} (A B : RealMatrix m k) : matrixInner A B = matrixInner B A := by
  simp [matrixInner, mul_comm]
lemma inner_sub_left {m k : ℕ} (A B D : RealMatrix m k) :
    matrixInner (A - B) D = matrixInner A D - matrixInner B D := by
  simp [matrixInner, sub_mul, Finset.sum_sub_distrib]
lemma inner_sub_right {m k : ℕ} (A B D : RealMatrix m k) :
    matrixInner A (B - D) = matrixInner A B - matrixInner A D := by
  simp [matrixInner, mul_sub, Finset.sum_sub_distrib]
lemma inner_smul_left {m k : ℕ} (c : ℝ) (A B : RealMatrix m k) :
    matrixInner (c • A) B = c * matrixInner A B := by
  simp [matrixInner, Finset.mul_sum, mul_assoc]
lemma inner_sum_left {m k : ℕ} {ι : Type*} [Fintype ι] (A : ι → RealMatrix m k) (B : RealMatrix m k) :
    matrixInner (∑ i, A i) B = ∑ i, matrixInner (A i) B := by
  simp only [matrixInner, Matrix.sum_apply, Finset.sum_mul]
  calc
    (∑ a, ∑ b, ∑ i, A i a b * B a b) = ∑ a, ∑ i, ∑ b, A i a b * B a b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

open KLTNuclear.Oracle
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n m k : ℕ}
  {X : Fin n → Ω → RealMatrix m k} {Y : Fin n → Ω → ℝ}
lemma inner_memLp (hreg : SampleRegularity P X Y) (A : RealMatrix m k) (i : Fin n) :
    MemLp (fun ω => matrixInner A (X i ω)) 2 P := by
  exact memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun l _ =>
    (hreg.2.2.1 i j l).const_mul (A j l)
lemma inner_product_integrable (hreg : SampleRegularity P X Y) (A B : RealMatrix m k) (i : Fin n) :
    Integrable (fun ω => matrixInner A (X i ω) * matrixInner B (X i ω)) P :=
  (inner_memLp hreg A i).integrable_mul (inner_memLp hreg B i)

lemma centered_entry [IsProbabilityMeasure P] (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m k) (hmodel : TraceRegressionModel P X Y A₀)
    (i : Fin n) (j : Fin m) (l : Fin k) :
    expectYX P X Y i j l = ∫ ω, matrixInner A₀ (X i ω) * X i ω j l ∂P := by
  let g : Ω → Fin m → Fin k → ℝ := fun ω j l => X i ω j l
  have hx : Measurable g := measurable_pi_lambda _ fun a =>
    measurable_pi_lambda _ fun b => hreg.1 i a b
  have hs : MeasurableSpace.comap g inferInstance ≤ ‹MeasurableSpace Ω› := hx.comap_le
  have hx_s : @Measurable Ω (Fin m → Fin k → ℝ)
      (MeasurableSpace.comap g inferInstance) _ g := measurable_iff_comap_le.mpr le_rfl
  have he : @Measurable Ω ℝ (MeasurableSpace.comap g inferInstance) _ (fun ω => X i ω j l) :=
    (measurable_pi_apply l).comp ((measurable_pi_apply j).comp hx_s)
  have hc := condExp_mul_of_stronglyMeasurable_right (μ := P)
    he.stronglyMeasurable (hreg.2.2.2.2 i j l) (hreg.2.2.2.1 i)
  unfold expectYX
  calc
    _ = ∫ ω, P[(fun ω => Y i ω * X i ω j l) | MeasurableSpace.comap g inferInstance] ω ∂P :=
      (integral_condExp hs).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hc, hmodel i] with ω h1 h2
      change P[Y i | MeasurableSpace.comap g inferInstance] ω = matrixInner A₀ (X i ω) at h2
      change P[(fun ω => Y i ω * X i ω j l) | MeasurableSpace.comap g inferInstance] ω =
        P[Y i | MeasurableSpace.comap g inferInstance] ω * X i ω j l at h1
      rw [h2] at h1
      exact h1

lemma l2_square_sub (hreg : SampleRegularity P X Y) (A B : RealMatrix m k) :
    l2NormSq P X (A - B) = l2NormSq P X A - 2 * l2Inner P X A B + l2NormSq P X B := by
  unfold l2NormSq l2Inner
  have hi (i : Fin n) :
      (∫ ω, matrixInner (A-B) (X i ω) * matrixInner (A-B) (X i ω) ∂P) =
      (∫ ω, matrixInner A (X i ω) * matrixInner A (X i ω) ∂P) -
        2 * (∫ ω, matrixInner A (X i ω) * matrixInner B (X i ω) ∂P) +
        (∫ ω, matrixInner B (X i ω) * matrixInner B (X i ω) ∂P) := by
    simp_rw [inner_sub_left]
    have he (ω : Ω) : (matrixInner A (X i ω) - matrixInner B (X i ω)) *
        (matrixInner A (X i ω) - matrixInner B (X i ω)) =
        matrixInner A (X i ω) * matrixInner A (X i ω) -
          2 * (matrixInner A (X i ω) * matrixInner B (X i ω)) +
          matrixInner B (X i ω) * matrixInner B (X i ω) := by ring
    simp_rw [he]
    have hAA := inner_product_integrable hreg A A i
    have hAB := (inner_product_integrable hreg A B i).const_mul 2
    have hBB := inner_product_integrable hreg B B i
    have hsum := integral_add (hAA.sub hAB) hBB
    have hsub := integral_sub hAA hAB
    simp only [Pi.sub_apply] at hsum
    rw [hsum, hsub, integral_const_mul]

  simp_rw [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
lemma integral_inner (F : Ω → RealMatrix m k)
    (hF : ∀ j l, Integrable (fun ω => F ω j l) P) (B : RealMatrix m k) :
    matrixInner (fun j l => ∫ ω, F ω j l ∂P) B = ∫ ω, matrixInner (F ω) B ∂P := by
  unfold matrixInner
  simp_rw [← integral_mul_const]
  symm
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun l _ =>
    (hF j l).mul_const (B j l))]
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_finsetSum _ (fun l _ => (hF j l).mul_const (B j l))

lemma centered_inner [IsProbabilityMeasure P] (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m k) (hmodel : TraceRegressionModel P X Y A₀)
    (i : Fin n) (B : RealMatrix m k) :
    matrixInner (expectYX P X Y i) B =
      ∫ ω, matrixInner A₀ (X i ω) * matrixInner B (X i ω) ∂P := by
  have he : expectYX P X Y i = fun j l =>
      ∫ ω, matrixInner A₀ (X i ω) * X i ω j l ∂P := by
    funext j l
    exact centered_entry hreg A₀ hmodel i j l
  rw [he]
  have hi (j : Fin m) (l : Fin k) :
      Integrable (fun ω => matrixInner A₀ (X i ω) * X i ω j l) P :=
    (inner_memLp hreg A₀ i).integrable_mul (hreg.2.2.1 i j l)
  calc
    _ = ∫ ω, matrixInner (matrixInner A₀ (X i ω) • X i ω) B ∂P := by
      simpa only [Matrix.smul_apply, smul_eq_mul] using
        integral_inner (fun ω => matrixInner A₀ (X i ω) • X i ω) hi B
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [inner_smul_left, inner_comm (X i ω) B]

lemma empirical_pairing [IsProbabilityMeasure P] (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m k) (hmodel : TraceRegressionModel P X Y A₀)
    (ω : Ω) (B : RealMatrix m k) :
    matrixInner (empiricalYX X Y ω) B =
      2 * matrixInner (noiseMatrix P X Y ω) B + 2 * l2Inner P X A₀ B := by
  simp only [empiricalYX, noiseMatrix, inner_smul_left, inner_sum_left,
    inner_sub_left, centered_inner hreg A₀ hmodel, l2Inner, Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv, one_mul]
  ring

lemma l2_comm (A B : RealMatrix m k) : l2Inner P X A B = l2Inner P X B A := by
  unfold l2Inner
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext ω
  exact mul_comm _ _
end KLTWork

open KLTNuclear.Oracle

/-- (2.9) (p. 8): polarization identity for the L₂(Π) inner product, stated for arbitrary
matrices B (in the paper B = Â^λ), A and A₀. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (B A A₀ : RealMatrix m₁ m₂) :
    2 * l2Inner P X (B - A₀) (B - A) =
      l2NormSq P X (B - A₀) + l2NormSq P X (B - A) - l2NormSq P X (A - A₀)  := by
  have h := KLTWork.l2_square_sub hreg (B - A₀) (B - A)
  have he : (B - A₀) - (B - A) = A - A₀ := by abel
  rw [he] at h
  linarith

#print axioms solution
