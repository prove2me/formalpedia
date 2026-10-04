-- Prove2me | solution 1 for MongeKantorovichYao.discrete_exists_cyclicallyMonotone_plan
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T10:35:19.540814+00:00
-- url     : https://prove2.me/submissions/7026026f-31bb-4292-b842-7f49a7d213e4

/-
Released under Apache 2.0 license.
Written by Codex.
-/
import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs



open Finset Set Matrix
namespace MongeKantorovichYao

variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixCost (A M : Matrix I I ℝ) : ℝ := ∑ i, ∑ j, M i j * A i j

lemma exists_min_transport_matrix (A : Matrix I I ℝ) :
    ∃ M ∈ doublyStochastic ℝ I, ∀ N ∈ doublyStochastic ℝ I, matrixCost A M ≤ matrixCost A N := by
  have hc : IsCompact (doublyStochastic ℝ I : Set (Matrix I I ℝ)) := by
    rw [doublyStochastic_eq_convexHull_permMatrix]
    exact (Set.finite_range (fun σ : Equiv.Perm I => σ.permMatrix ℝ)).isCompact_convexHull ℝ
  have hn : (doublyStochastic ℝ I : Set (Matrix I I ℝ)).Nonempty :=
    ⟨1, (doublyStochastic ℝ I).one_mem⟩
  have hcont : Continuous (matrixCost A) := by
    unfold matrixCost
    exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
      (by fun_prop)))
  exact hc.exists_isMinOn hn hcont.continuousOn

noncomputable def cycleMatrix {K : Type*} [Fintype K] (r s : K → I) : Matrix I I ℝ :=
  fun i j => ∑ k, if r k = i ∧ s k = j then 1 else 0

lemma cycleMatrix_nonneg {K : Type*} [Fintype K] (r s : K → I) (i j : I) :
    0 ≤ cycleMatrix r s i j := by
  unfold cycleMatrix
  exact sum_nonneg (fun k _ => by split <;> norm_num)

lemma cycleMatrix_row {K : Type*} [Fintype K] (r s : K → I) (i : I) :
    ∑ j, cycleMatrix r s i j = ∑ k, if r k = i then (1 : ℝ) else 0 := by
  classical
  unfold cycleMatrix
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases h : r k = i
  · simp [h]
  · simp [h]

lemma cycleMatrix_col {K : Type*} [Fintype K] (r s : K → I) (j : I) :
    ∑ i, cycleMatrix r s i j = ∑ k, if s k = j then (1 : ℝ) else 0 := by
  classical
  unfold cycleMatrix
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases h : s k = j
  · simp [h]
  · simp [h]

lemma cycleMatrix_cost {K : Type*} [Fintype K] (A : Matrix I I ℝ) (r s : K → I) :
    matrixCost A (cycleMatrix r s) = ∑ k, A (r k) (s k) := by
  classical
  unfold matrixCost cycleMatrix
  simp_rw [sum_mul]
  calc
    (∑ i, ∑ j, ∑ k, (if r k = i ∧ s k = j then (1 : ℝ) else 0) * A i j) =
        ∑ i, ∑ k, ∑ j, (if r k = i ∧ s k = j then (1 : ℝ) else 0) * A i j := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ k, ∑ i, ∑ j, (if r k = i ∧ s k = j then (1 : ℝ) else 0) * A i j := by
      rw [sum_comm]
    _ = ∑ k, A (r k) (s k) := by
      apply sum_congr rfl
      intro k _
      simp [ite_and]

end MongeKantorovichYao


open Finset Set Matrix
namespace MongeKantorovichYao

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma matrixCost_perturb (A M D B : Matrix I I ℝ) (ε : ℝ) :
    matrixCost A (fun i j => M i j - ε * D i j + ε * B i j) =
      matrixCost A M - ε * matrixCost A D + ε * matrixCost A B := by
  simp only [matrixCost, add_mul, sub_mul, mul_assoc]
  simp_rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]

lemma positive_support_cycle_inequality (A M : Matrix I I ℝ)
    (hM : M ∈ doublyStochastic ℝ I)
    (hmin : ∀ N ∈ doublyStochastic ℝ I, matrixCost A M ≤ matrixCost A N)
    {K : Type*} [Fintype K] [Nonempty K] (r s : K → I) (σ : Equiv.Perm K)
    (hpos : ∀ k, 0 < M (r k) (s k)) :
    ∑ k, A (r k) (s k) ≤ ∑ k, A (r k) (s (σ k)) := by
  classical
  obtain ⟨k0, _, hk0⟩ := Finset.exists_min_image Finset.univ
    (fun k => M (r k) (s k)) Finset.univ_nonempty
  let δ := M (r k0) (s k0)
  let L : ℝ := Fintype.card K
  have hL : 0 < L := by dsimp [L]; exact_mod_cast Fintype.card_pos
  have hδ : 0 < δ := hpos k0
  let ε := δ / L
  have hε : 0 < ε := div_pos hδ hL
  let D := cycleMatrix r s
  let B := cycleMatrix r (s ∘ σ)
  have hD (i j : I) : ε * D i j ≤ M i j := by
    have hterm (k : K) : δ * (if r k = i ∧ s k = j then (1 : ℝ) else 0) ≤ M i j := by
      by_cases h : r k = i ∧ s k = j
      · rw [if_pos h, mul_one]
        dsimp only [δ]
        simpa only [h.1, h.2] using hk0 k (Finset.mem_univ k)
      · simp only [h, ↓reduceIte, mul_zero]
        exact nonneg_of_mem_doublyStochastic hM
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
    have hs : δ * D i j ≤ L * M i j := by
      simpa only [← mul_sum, D, cycleMatrix, sum_const, card_univ, nsmul_eq_mul, L] using hsum
    dsimp only [ε]
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    simpa only [mul_comm] using hs
  have hrow (i : I) : ∑ j, D i j = ∑ j, B i j := by
    simp only [D, B, cycleMatrix_row]
  have hcol (j : I) : ∑ i, D i j = ∑ i, B i j := by
    simp only [D, B, cycleMatrix_col, Function.comp_apply]
    exact (Equiv.sum_comp σ (fun k => if s k = j then (1 : ℝ) else 0)).symm
  let N : Matrix I I ℝ := fun i j => M i j - ε * D i j + ε * B i j
  have hN : N ∈ doublyStochastic ℝ I := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have hd := hD i j
      have hb := mul_nonneg hε.le (cycleMatrix_nonneg r (s ∘ σ) i j)
      dsimp [N]
      linarith
    · intro i
      dsimp only [N]
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, hrow i,
        sum_row_of_mem_doublyStochastic hM]
      ring
    · intro j
      dsimp only [N]
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, hcol j,
        sum_col_of_mem_doublyStochastic hM]
      ring
  have h := hmin N hN
  rw [matrixCost_perturb] at h
  have heD : matrixCost A D = ∑ k, A (r k) (s k) := cycleMatrix_cost A r s
  have heB : matrixCost A B = ∑ k, A (r k) (s (σ k)) := cycleMatrix_cost A r (s ∘ σ)
  rw [heD, heB] at h
  nlinarith

end MongeKantorovichYao


open MeasureTheory Finset Set Matrix
namespace MongeKantorovichYao

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    [Fintype I] [DecidableEq I]

lemma stochastic_row_ennreal (M : Matrix I I ℝ) (hM : M ∈ doublyStochastic ℝ I) (i : I) :
    ∑ j, ENNReal.ofReal (M i j) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => nonneg_of_mem_doublyStochastic hM)]
  rw [sum_row_of_mem_doublyStochastic hM]
  norm_num

lemma stochastic_col_ennreal (M : Matrix I I ℝ) (hM : M ∈ doublyStochastic ℝ I) (j : I) :
    ∑ i, ENNReal.ofReal (M i j) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => nonneg_of_mem_doublyStochastic hM)]
  rw [sum_col_of_mem_doublyStochastic hM]
  norm_num

noncomputable def atomicTransport (x : I → X) (y : I → Y) (M : Matrix I I ℝ) : Measure (X × Y) :=
  ∑ i, ∑ j, ENNReal.ofReal (M i j) • Measure.dirac (x i, y j)

lemma atomicTransport_fst (x : I → X) (y : I → Y) (M : Matrix I I ℝ)
    (hM : M ∈ doublyStochastic ℝ I) :
    (atomicTransport x y M).map Prod.fst = ∑ i, Measure.dirac (x i) := by
  unfold atomicTransport
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  apply sum_congr rfl
  intro i _
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac, Prod.fst]
  rw [← Finset.sum_smul, stochastic_row_ennreal M hM]
  simp

lemma atomicTransport_snd (x : I → X) (y : I → Y) (M : Matrix I I ℝ)
    (hM : M ∈ doublyStochastic ℝ I) :
    (atomicTransport x y M).map Prod.snd = ∑ j, Measure.dirac (y j) := by
  have he : atomicTransport x y M =
      ∑ j, ∑ i, ENNReal.ofReal (M i j) • Measure.dirac (x i,y j) := by
    unfold atomicTransport
    rw [sum_comm]
  rw [he, Measure.map_finset_sum measurable_snd.aemeasurable]
  apply sum_congr rfl
  intro j _
  rw [Measure.map_finset_sum measurable_snd.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac]
  rw [← Finset.sum_smul, stochastic_col_ennreal M hM]
  simp

lemma atomicTransport_mass (x : I → X) (y : I → Y) (M : Matrix I I ℝ)
    (hM : M ∈ doublyStochastic ℝ I) :
    atomicTransport x y M Set.univ = Fintype.card I := by
  simp only [atomicTransport, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  simp only [stochastic_row_ennreal M hM, sum_const, card_univ, nsmul_one]

lemma atomicTransport_concentrated (x : I → X) (y : I → Y) (M : Matrix I I ℝ)
    (hM : M ∈ doublyStochastic ℝ I) :
    atomicTransport x y M {p | ∃ i j, 0 < M i j ∧ p = (x i,y j)}ᶜ = 0 := by
  unfold atomicTransport
  simp only [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : 0 < M i j
  · have hp : (x i,y j) ∈ {p | ∃ i j, 0 < M i j ∧ p = (x i,y j)} := ⟨i,j,hij,rfl⟩
    simp [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem,
      Set.notMem_compl_iff.mpr hp]
  · have hz : M i j = 0 := le_antisymm (le_of_not_gt hij) (nonneg_of_mem_doublyStochastic hM)
    simp [hz]

end MongeKantorovichYao


open MeasureTheory Finset Set Matrix
namespace MongeKantorovichYao

theorem finite_plan {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (n : ℕ) (hn : 0 < n) (x : Fin n → X) (y : Fin n → Y) (c : X × Y → ℝ) :
    ∃ π ∈ transferencePlans ((n : ENNReal)⁻¹ • ∑ i, Measure.dirac (x i))
        ((n : ENNReal)⁻¹ • ∑ i, Measure.dirac (y i)),
      IsCCyclicallyMonotonePlan c π := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => c (x i,y j)
  obtain ⟨M,hM,hmin⟩ := exists_min_transport_matrix A
  let π : Measure (X × Y) := (n : ENNReal)⁻¹ • atomicTransport x y M
  have hmass : π Set.univ = 1 := by
    dsimp only [π]
    rw [Measure.smul_apply, atomicTransport_mass x y M hM]
    simp only [smul_eq_mul, Fintype.card_fin]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)
  have hprob : IsProbabilityMeasure π := ⟨hmass⟩
  have hfst : π.map Prod.fst = (n : ENNReal)⁻¹ • ∑ i, Measure.dirac (x i) := by
    dsimp only [π]
    rw [Measure.map_smul, atomicTransport_fst x y M hM]
  have hsnd : π.map Prod.snd = (n : ENNReal)⁻¹ • ∑ j, Measure.dirac (y j) := by
    dsimp only [π]
    rw [Measure.map_smul, atomicTransport_snd x y M hM]
  let Γ : Set (X × Y) := {p | ∃ i j, 0 < M i j ∧ p = (x i,y j)}
  have hΓ : IsCCyclicallyMonotone c Γ := by
    intro N p hp
    choose r s hpos he using hp
    have h := positive_support_cycle_inequality A M hM hmin r s
      (Equiv.addRight (1 : Fin (N+1))) hpos
    have hpEq : p = fun k => (x (r k),y (s k)) := funext he
    rw [hpEq]
    convert h using 1 <;> rfl
  have hnull : π Γᶜ = 0 := by
    dsimp only [π]
    rw [Measure.smul_apply, atomicTransport_concentrated x y M hM]
    simp
  exact ⟨π, ⟨hprob,hfst,hsnd⟩, Γ,hΓ,hnull⟩

end MongeKantorovichYao

open MongeKantorovichYao MeasureTheory
theorem solution {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (n : ℕ) (hn : 0 < n) (x : Fin n → X) (y : Fin n → Y) (c : X × Y → ℝ) :
    ∃ π ∈ transferencePlans ((n : ENNReal)⁻¹ • ∑ i, Measure.dirac (x i))
        ((n : ENNReal)⁻¹ • ∑ i, Measure.dirac (y i)),
      IsCCyclicallyMonotonePlan c π := by
  exact finite_plan n hn x y c

#print axioms solution
