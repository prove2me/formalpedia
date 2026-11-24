-- Prove2me | solution 1 for Kyprianou.Ch02.threeSigmaIndepOfJoinAndPairCh02V1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:45:24.855799+00:00
-- url     : https://prove2.me/submissions/fd4b37ba-8016-44fa-8aa8-bfad0fe3818f

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m₀ m₁ m₂ : MeasurableSpace Ω)
    (h₀ : Indep m₀ (m₁ ⊔ m₂) P) (h₁ : Indep m₁ m₂ P) :
    iIndep (fun i : Fin 3 => if i = 0 then m₀ else if i = 1 then m₁ else m₂) P := by
  classical
  let m : Fin 3 → MeasurableSpace Ω := fun i =>
    if i = 0 then m₀ else if i = 1 then m₁ else m₂
  change iIndep m P
  rw [iIndep_iff]
  intro s f hf
  let g : Fin 3 → Set Ω := fun i => if i ∈ s then f i else Set.univ
  have hg (i : Fin 3) : MeasurableSet[m i] (g i) := by
    by_cases hi : i ∈ s
    · simpa [g, hi] using hf i hi
    · simp [g, hi]
  have hg₀ : MeasurableSet[m₀] (g 0) := by simpa [m] using hg 0
  have hg₁ : MeasurableSet[m₁] (g 1) := by simpa [m] using hg 1
  have hg₂ : MeasurableSet[m₂] (g 2) := by simpa [m] using hg 2
  have hjoin : MeasurableSet[m₁ ⊔ m₂] (g 1 ∩ g 2) :=
    ((show m₁ ≤ m₁ ⊔ m₂ from le_sup_left) _ hg₁).inter
      ((show m₂ ≤ m₁ ⊔ m₂ from le_sup_right) _ hg₂)
  have hprod : P (g 0 ∩ (g 1 ∩ g 2)) = P (g 0) * P (g 1) * P (g 2) := by
    rw [(Indep_iff _ _ _).mp h₀ _ _ hg₀ hjoin,
      (Indep_iff _ _ _).mp h₁ _ _ hg₁ hg₂, mul_assoc]
  have hset : (⋂ i ∈ s, f i) = ⋂ i, g i := by
    ext ω
    simp [g, apply_ite]
  have hthree : (⋂ i, g i) = g 0 ∩ (g 1 ∩ g 2) := by
    ext ω
    simp [Fin.forall_fin_succ]
  have hprod' : (∏ i ∈ s, P (f i)) = ∏ i, P (g i) := by
    simpa only [g, apply_ite P, measure_univ] using
      (Finset.prod_ite_mem_eq s (fun i => P (f i))).symm
  rw [hset, hthree, hprod', Fin.prod_univ_three]
  exact hprod
