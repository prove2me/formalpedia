-- Prove2me | solution 1 for MultimodalPricing.Regret.lemma_10
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:02:42.294727+00:00
-- url     : https://prove2.me/submissions/4af37d59-6563-4ad0-b54c-cffa7e064b77

import Mathlib

open MeasureTheory Matrix
open scoped BigOperators ENNReal



namespace DM10

local instance mΩ : MeasurableSpace (ULift.{0} Bool) := ⊤

def F : Filtration ℕ (mΩ : MeasurableSpace (ULift.{0} Bool)) where
  seq n := if n = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · subst hi; simp only [if_true]; split_ifs <;> simp
    · have : j ≠ 0 := by omega
      simp [hi, this]
  le' := by
    intro n
    split_ifs <;> simp [mΩ]

noncomputable def μ0 : Measure (ULift.{0} Bool) :=
  (PMF.uniformOfFintype (ULift.{0} Bool)).toMeasure

instance : IsProbabilityMeasure (μ0) := by unfold μ0; infer_instance

def ξ0 (ω : ULift.{0} Bool) : ℝ := if ω.down then 1 else -1

lemma μ_single (x : ULift.{0} Bool) : μ0 {x} = 2⁻¹ := by
  unfold μ0
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton x)]
  simp [PMF.uniformOfFintype_apply]

lemma ξ0_int : ∫ ω, ξ0 ω ∂(μ0) = 0 := by
  rw [integral_fintype]
  · simp only [Measure.real, μ_single, ξ0, smul_eq_mul]
    have := Fintype.sum_equiv Equiv.ulift (fun x : ULift.{0} Bool => (ENNReal.toReal 2⁻¹) * (if x.down = true then (1:ℝ) else -1))
      (fun b : Bool => (ENNReal.toReal 2⁻¹) * (if b = true then (1:ℝ) else -1)) (fun x => rfl)
    rw [this]
    simp [Fintype.sum_bool]
  · exact Integrable.of_finite

lemma ξ0_set (A : Set (ULift.{0} Bool)) (hA : A = ∅ ∨ A = Set.univ) :
    ∫ ω in A, ξ0 ω ∂(μ0) = 0 := by
  rcases hA with rfl | rfl
  · simp
  · simp [ξ0_int]

lemma pd (c : ℝ) (hc : 0 < c) : (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef :=
  Matrix.PosDef.smul (Matrix.PosDef.one) hc

end DM10

theorem solution : ¬ (∀ (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (info : Filtration ℕ mΩ) (X : ℕ → Ω → Fin k → ℝ) (ξ : ℕ → Ω → ℝ)
    (hX : ∀ n < t, Measurable[info n] (X n))
    (hξ : ∀ n < t, Measurable[info (n + 1)] (ξ n))
    (hbound : ∀ᵐ ω ∂μ, ∀ n < t,
      Real.sqrt (X n ω ⬝ᵥ X n ω) ≤ Real.sqrt k ∧ |ξ n ω| ≤ 1)
    (hint : ∀ n < t, Integrable (ξ n) μ)
    (hcenter : ∀ n < t, ∀ A : Set Ω, MeasurableSet[info n] A →
      (∫ ω in A, ξ n ω ∂μ) = 0),
    μ {ω | ∃ Λ : Matrix (Fin k) (Fin k) ℝ, Λ.PosDef ∧
      ∃ z : Fin k → ℝ, z ⬝ᵥ (Λ *ᵥ z) ≤ 1 ∧
        Real.sqrt (2 * k * Real.log (4 * k * t / δ)) + 2 <
          |∑ n ∈ Finset.range t, ξ n ω * (X n ω ⬝ᵥ z)|} ≤ ENNReal.ofReal δ) := by
  intro H
  have hδ : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have key := @H 1 1 le_rfl le_rfl (1 / 2) hδ (ULift.{0} Bool) DM10.mΩ DM10.μ0 _ DM10.F
    (fun _ _ _ => 1) (fun _ => DM10.ξ0)
    (fun n hn => measurable_const) ?_ ?_ ?_ ?_
  · set c : ℝ := Real.sqrt (2 * ((1 : ℕ) : ℝ) * Real.log (4 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (1 / 2))) + 2 with hc
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hset : {ω : ULift.{0} Bool | ∃ Λ : Matrix (Fin 1) (Fin 1) ℝ, Λ.PosDef ∧
        ∃ z : Fin 1 → ℝ, z ⬝ᵥ (Λ *ᵥ z) ≤ 1 ∧ c <
          |∑ n ∈ Finset.range 1, DM10.ξ0 ω * ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ z)|} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      refine ⟨(1 / (c + 1) ^ 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ), DM10.pd _ (by positivity),
        fun _ => c + 1, ?_, ?_⟩
      · simp [Matrix.smul_mulVec, dotProduct]
        field_simp
        rfl
      · simp [DM10.ξ0, dotProduct]
        split_ifs
        · rw [abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith)]; linarith
    have key' : DM10.μ0 Set.univ ≤ ENNReal.ofReal (1 / 2) := by
      convert key using 2
      exact hset.symm
    rw [measure_univ] at key'
    have : ENNReal.ofReal (1 / 2) < 1 := by
      rw [ENNReal.ofReal_lt_one]; norm_num
    exact absurd key' (not_le.mpr this)
  · intro n hn
    have h : (DM10.F : Filtration ℕ _) (n + 1) = ⊤ := by simp [DM10.F]
    show @Measurable _ _ ((DM10.F : Filtration ℕ _) (n + 1)) _ _
    rw [h]
    exact measurable_from_top
  · exact Filter.Eventually.of_forall fun ω n hn =>
      ⟨by simp [dotProduct], by simp [DM10.ξ0]; split_ifs <;> simp⟩
  · intro n hn; exact Integrable.of_finite
  · intro n hn A hA
    have hn0 : n = 0 := by omega
    subst hn0
    have h : (DM10.F : Filtration ℕ _) 0 = ⊥ := by simp [DM10.F]
    have hA' : MeasurableSet[(⊥ : MeasurableSpace (ULift.{0} Bool))] A := by
      rw [← h]; exact hA
    exact DM10.ξ0_set A (MeasurableSpace.measurableSet_bot_iff.mp hA')
