-- Prove2me | solution 1 for MongeKantorovichYao.exists_cyclicallyMonotone_plan
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T10:52:47.234571+00:00
-- url     : https://prove2.me/submissions/98ae5f1e-d5d8-4ea0-8545-d4200f7e0eed

/-
Released under Apache 2.0 license.
Written by Codex.
-/
import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs



open MeasureTheory Set Topology
namespace MongeKantorovichYao

lemma cyclic_closure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    (c : X × Y → ℝ) (hc : Continuous c) (Γ : Set (X × Y))
    (hΓ : IsCCyclicallyMonotone c Γ) : IsCCyclicallyMonotone c (closure Γ) := by
  intro n p hp
  let A : Set (Fin (n+1) → X × Y) := Set.pi Set.univ (fun _ => Γ)
  let B : Set (Fin (n+1) → X × Y) :=
    {q | ∑ i, c (q i) ≤ ∑ i, c ((q i).1, (q (i+1)).2)}
  have hB : IsClosed B := by
    apply isClosed_le
    · exact continuous_finsetSum _ (fun i _ => hc.comp (continuous_apply i))
    · exact continuous_finsetSum _ (fun i _ =>
        hc.comp ((continuous_fst.comp (continuous_apply i)).prodMk
          (continuous_snd.comp (continuous_apply (i+1)))))
  have hAB : A ⊆ B := by
    intro q hq
    exact hΓ n q (fun i => hq i (Set.mem_univ i))
  exact (closure_minimal hAB hB) (mem_closure_pi.mpr (fun i _ => hp i))

lemma support_cyclic {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y]
    (c : X × Y → ℝ) (hc : Continuous c) (π : Measure (X × Y))
    (hπ : IsCCyclicallyMonotonePlan c π) : IsCCyclicallyMonotone c π.support := by
  obtain ⟨Γ, hΓ, hnull⟩ := hπ
  have hs : π.support ⊆ closure Γ := by
    apply π.support_subset_of_isClosed isClosed_closure
    show π (closure Γ)ᶜ = 0
    exact measure_mono_null (Set.compl_subset_compl.mpr subset_closure) hnull
  intro n p hp
  exact cyclic_closure c hc Γ hΓ n p (fun i => hs (hp i))

end MongeKantorovichYao


open Set Finset Matrix
namespace MongeKantorovichYao
namespace Weighted

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def Couplings (a : I → ℝ) (b : J → ℝ) : Set (Matrix I J ℝ) :=
  {M | (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = a i) ∧ ∀ j, ∑ i, M i j = b j}

def cost (A M : Matrix I J ℝ) : ℝ := ∑ i, ∑ j, M i j * A i j

lemma coupling_nonempty (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (has : ∑ i, a i = 1) (hbs : ∑ j, b j = 1) : (Couplings a b).Nonempty := by
  refine ⟨fun i j => a i * b j, ?_⟩
  refine ⟨fun i j => mul_nonneg (ha i) (hb j), ?_, ?_⟩
  · intro i; simp only [← mul_sum, hbs, mul_one]
  · intro j; simp only [← sum_mul, has, one_mul]

lemma coupling_closed (a : I → ℝ) (b : J → ℝ) : IsClosed (Couplings a b) := by
  have h0 : IsClosed {M : Matrix I J ℝ | ∀ i j, 0 ≤ M i j} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_le continuous_const (by fun_prop)
  have hr : IsClosed {M : Matrix I J ℝ | ∀ i, ∑ j, M i j = a i} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq (continuous_finsetSum _ (fun j _ => by fun_prop)) continuous_const
  have hc : IsClosed {M : Matrix I J ℝ | ∀ j, ∑ i, M i j = b j} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro j
    exact isClosed_eq (continuous_finsetSum _ (fun i _ => by fun_prop)) continuous_const
  exact h0.inter (hr.inter hc)

lemma coupling_compact (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1) : IsCompact (Couplings a b) := by
  have hcomp : IsCompact (Set.pi Set.univ (fun _ : I =>
      Set.pi Set.univ (fun _ : J => Set.Icc (0 : ℝ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  apply hcomp.of_isClosed_subset (coupling_closed a b)
  intro M hM i _ j _
  refine ⟨hM.1 i j, ?_⟩
  have hij : M i j ≤ a i := by
    rw [← hM.2.1 i]
    exact single_le_sum (fun k _ => hM.1 i k) (mem_univ j)
  have hi : a i ≤ 1 := by
    rw [← has]
    exact single_le_sum (fun k _ => ha k) (mem_univ i)
  exact hij.trans hi

lemma exists_min (A : Matrix I J ℝ) (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (has : ∑ i, a i = 1) (hbs : ∑ j, b j = 1) :
    ∃ M ∈ Couplings a b, ∀ N ∈ Couplings a b, cost A M ≤ cost A N := by
  have hcont : Continuous (cost A) := by
    unfold cost
    exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => by fun_prop))
  exact (coupling_compact a b ha has).exists_isMinOn
    (coupling_nonempty a b ha hb has hbs) hcont.continuousOn

end Weighted
end MongeKantorovichYao


open Finset Set Matrix
namespace MongeKantorovichYao.Weighted

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def cycleMatrix {K : Type*} [Fintype K] (r : K → I) (s : K → J) : Matrix I J ℝ :=
  fun i j => ∑ k, if r k = i ∧ s k = j then 1 else 0

lemma cycleMatrix_nonneg {K : Type*} [Fintype K] (r : K → I) (s : K → J) (i : I) (j : J) :
    0 ≤ cycleMatrix r s i j := by
  unfold cycleMatrix
  exact sum_nonneg (fun k _ => by split <;> norm_num)

lemma cycleMatrix_row {K : Type*} [Fintype K] (r : K → I) (s : K → J) (i : I) :
    ∑ j, cycleMatrix r s i j = ∑ k, if r k = i then (1 : ℝ) else 0 := by
  classical
  unfold cycleMatrix
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases h : r k = i
  · simp [h]
  · simp [h]

lemma cycleMatrix_col {K : Type*} [Fintype K] (r : K → I) (s : K → J) (j : J) :
    ∑ i, cycleMatrix r s i j = ∑ k, if s k = j then (1 : ℝ) else 0 := by
  classical
  unfold cycleMatrix
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases h : s k = j
  · simp [h]
  · simp [h]

lemma cycleMatrix_cost {K : Type*} [Fintype K] (A : Matrix I J ℝ) (r : K → I) (s : K → J) :
    cost A (cycleMatrix r s) = ∑ k, A (r k) (s k) := by
  classical
  unfold cost cycleMatrix
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


lemma cost_perturb (A M D B : Matrix I J ℝ) (ε : ℝ) :
    cost A (fun i j => M i j - ε * D i j + ε * B i j) =
      cost A M - ε * cost A D + ε * cost A B := by
  simp only [cost, add_mul, sub_mul, mul_assoc]
  simp_rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]

lemma positive_support_cycle_inequality (A M : Matrix I J ℝ) (a : I → ℝ) (b : J → ℝ)
    (hM : M ∈ Couplings a b)
    (hmin : ∀ N ∈ Couplings a b, cost A M ≤ cost A N)
    {K : Type*} [Fintype K] [Nonempty K] (r : K → I) (s : K → J) (σ : Equiv.Perm K)
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
  have hD (i : I) (j : J) : ε * D i j ≤ M i j := by
    have hterm (k : K) : δ * (if r k = i ∧ s k = j then (1 : ℝ) else 0) ≤ M i j := by
      by_cases h : r k = i ∧ s k = j
      · rw [if_pos h, mul_one]
        dsimp only [δ]
        simpa only [h.1, h.2] using hk0 k (Finset.mem_univ k)
      · simp only [h, ↓reduceIte, mul_zero]
        exact hM.1 i j
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
    have hs : δ * D i j ≤ L * M i j := by
      simpa only [← mul_sum, D, cycleMatrix, sum_const, card_univ, nsmul_eq_mul, L] using hsum
    dsimp only [ε]
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    simpa only [mul_comm] using hs
  have hrow (i : I) : ∑ j, D i j = ∑ j, B i j := by
    simp only [D, B, cycleMatrix_row]
  have hcol (j : J) : ∑ i, D i j = ∑ i, B i j := by
    simp only [D, B, cycleMatrix_col, Function.comp_apply]
    exact (Equiv.sum_comp σ (fun k => if s k = j then (1 : ℝ) else 0)).symm
  let N : Matrix I J ℝ := fun i j => M i j - ε * D i j + ε * B i j
  have hN : N ∈ Couplings a b := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have hd := hD i j
      have hb := mul_nonneg hε.le (cycleMatrix_nonneg r (s ∘ σ) i j)
      dsimp [N]
      linarith
    · intro i
      dsimp only [N]
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, hrow i,
        hM.2.1]
      ring
    · intro j
      dsimp only [N]
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, hcol j,
        hM.2.2]
      ring
  have h := hmin N hN
  rw [cost_perturb] at h
  have heD : cost A D = ∑ k, A (r k) (s k) := cycleMatrix_cost A r s
  have heB : cost A B = ∑ k, A (r k) (s (σ k)) := cycleMatrix_cost A r (s ∘ σ)
  rw [heD, heB] at h
  nlinarith


end MongeKantorovichYao.Weighted


open MeasureTheory Finset Set Matrix
namespace MongeKantorovichYao.Weighted

variable {X Y I J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

lemma row_ennreal (M : Matrix I J ℝ) (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b) (i : I) :
    ∑ j, ENNReal.ofReal (M i j) = ENNReal.ofReal (a i) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hM.1 _ _)]
  rw [hM.2.1]

lemma col_ennreal (M : Matrix I J ℝ) (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b) (j : J) :
    ∑ i, ENNReal.ofReal (M i j) = ENNReal.ofReal (b j) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hM.1 _ _)]
  rw [hM.2.2]

noncomputable def atomicTransport (x : I → X) (y : J → Y) (M : Matrix I J ℝ) : Measure (X × Y) :=
  ∑ i, ∑ j, ENNReal.ofReal (M i j) • Measure.dirac (x i, y j)

lemma atomicTransport_fst (x : I → X) (y : J → Y) (M : Matrix I J ℝ)
    (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b) :
    (atomicTransport x y M).map Prod.fst = ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i) := by
  unfold atomicTransport
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  apply sum_congr rfl
  intro i _
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac, Prod.fst]
  rw [← Finset.sum_smul, row_ennreal M a b hM]

lemma atomicTransport_snd (x : I → X) (y : J → Y) (M : Matrix I J ℝ)
    (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b) :
    (atomicTransport x y M).map Prod.snd = ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j) := by
  have he : atomicTransport x y M =
      ∑ j, ∑ i, ENNReal.ofReal (M i j) • Measure.dirac (x i,y j) := by
    unfold atomicTransport
    rw [sum_comm]
  rw [he, Measure.map_finset_sum measurable_snd.aemeasurable]
  apply sum_congr rfl
  intro j _
  rw [Measure.map_finset_sum measurable_snd.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac]
  rw [← Finset.sum_smul, col_ennreal M a b hM]

lemma atomicTransport_mass (x : I → X) (y : J → Y) (M : Matrix I J ℝ)
    (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b)
    (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1) :
    atomicTransport x y M Set.univ = 1 := by
  simp only [atomicTransport, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one,
    row_ennreal M a b hM]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i), has]
  norm_num

lemma atomicTransport_concentrated (x : I → X) (y : J → Y) (M : Matrix I J ℝ)
    (a : I → ℝ) (b : J → ℝ) (hM : M ∈ Couplings a b) :
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
  · have hz : M i j = 0 := le_antisymm (le_of_not_gt hij) (hM.1 _ _)
    simp [hz]


lemma finite_weighted_plan (x : I → X) (y : J → Y) (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (has : ∑ i, a i = 1) (hbs : ∑ j, b j = 1) (c : X × Y → ℝ) :
    ∃ π ∈ transferencePlans (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))
      (∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j)),
      IsCCyclicallyMonotonePlan c π := by
  classical
  let A : Matrix I J ℝ := fun i j => c (x i,y j)
  obtain ⟨M,hM,hmin⟩ := exists_min A a b ha hb has hbs
  let π := atomicTransport x y M
  have hprob : IsProbabilityMeasure π := ⟨atomicTransport_mass x y M a b hM ha has⟩
  have hfst := atomicTransport_fst x y M a b hM
  have hsnd := atomicTransport_snd x y M a b hM
  let Γ : Set (X × Y) := {p | ∃ i j, 0 < M i j ∧ p = (x i,y j)}
  have hΓ : IsCCyclicallyMonotone c Γ := by
    intro N p hp
    choose r s hpos he using hp
    have h := positive_support_cycle_inequality A M a b hM hmin r s
      (Equiv.addRight (1 : Fin (N+1))) hpos
    have hpEq : p = fun k => (x (r k),y (s k)) := funext he
    rw [hpEq]
    convert h using 1 <;> rfl
  have hnull := atomicTransport_concentrated x y M a b hM
  exact ⟨π, ⟨hprob,hfst,hsnd⟩, Γ,hΓ,hnull⟩

end MongeKantorovichYao.Weighted


open MeasureTheory Filter Set Topology Finset
namespace MongeKantorovichYao

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

noncomputable def simpleWeights (μ : ProbabilityMeasure X) (f : SimpleFunc X X)
    (i : f.range) : ℝ := ((μ : Measure X) (f ⁻¹' {i.1})).toReal

lemma simpleWeights_nonneg (μ : ProbabilityMeasure X) (f : SimpleFunc X X) (i : f.range) :
    0 ≤ simpleWeights μ f i := ENNReal.toReal_nonneg

lemma simpleWeights_sum (μ : ProbabilityMeasure X) (f : SimpleFunc X X) :
    ∑ i : f.range, simpleWeights μ f i = 1 := by
  classical
  have hsum : (∑ i ∈ f.range, (μ : Measure X) (f ⁻¹' {i})) = 1 := by
    rw [sum_measure_preimage_singleton]
    · have hpre : f ⁻¹' (↑f.range : Set X) = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Finset.mem_coe, Set.mem_univ, iff_true]
        exact f.mem_range_self x
      rw [hpre, measure_univ]
    · intro i _
      exact f.measurable (measurableSet_singleton i)
  simp only [simpleWeights]
  rw [Finset.sum_coe_sort f.range (fun i => ((μ : Measure X) (f ⁻¹' {i})).toReal),
    ← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _), hsum]
  norm_num

lemma simple_map_eq_atoms (μ : ProbabilityMeasure X) (f : SimpleFunc X X) :
    (μ.map f.measurable.aemeasurable : Measure X) =
      ∑ i : f.range, ENNReal.ofReal (simpleWeights μ f i) • Measure.dirac (i.1) := by
  classical
  change (μ : Measure X).map f = _
  have he := (Measure.ae_mem_finset_iff_map_eq_sum_dirac (s := f.range) (μ := (μ : Measure X))
    f.measurable.aemeasurable).mp (Filter.Eventually.of_forall (fun x => f.mem_range_self x))
  rw [he]
  simp only [simpleWeights]
  rw [Finset.sum_coe_sort f.range (fun i =>
    ENNReal.ofReal ((μ : Measure X) (f ⁻¹' {i})).toReal • Measure.dirac i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

end MongeKantorovichYao


open MeasureTheory Filter Set Topology TopologicalSpace
namespace MongeKantorovichYao

lemma simple_map_tendsto {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure X) (f : ℕ → SimpleFunc X X)
    (hf : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 x)) :
    Tendsto (fun n => μ.map (f n).measurable.aemeasurable) atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => g (f n x)) (μ : Measure X) :=
    (g.continuous.measurable.comp (f n).measurable).aestronglyMeasurable
  have hd := tendsto_integral_of_dominated_convergence (μ := (μ : Measure X))
    (fun _ => ‖g‖) hm (integrable_const ‖g‖)
    (fun n => Filter.Eventually.of_forall (fun x => g.norm_coe_le_norm (f n x)))
    (Filter.Eventually.of_forall (fun x => g.continuous.continuousAt.tendsto.comp (hf x)))
  convert hd using 1
  funext n
  exact integral_map_of_stronglyMeasurable (f n).measurable g.continuous.stronglyMeasurable

lemma exists_simple_map_tendsto {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SeparableSpace X] (μ : ProbabilityMeasure X) :
    ∃ f : ℕ → SimpleFunc X X,
      Tendsto (fun n => μ.map (f n).measurable.aemeasurable) atTop (𝓝 μ) := by
  classical
  letI : Nonempty X := nonempty_of_isProbabilityMeasure (μ : Measure X)
  let x0 : X := Classical.arbitrary X
  let f : ℕ → SimpleFunc X X := SimpleFunc.approxOn id measurable_id Set.univ x0 (Set.mem_univ x0)
  refine ⟨f, simple_map_tendsto μ f ?_⟩
  intro x
  exact SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ x0) (by simp)

end MongeKantorovichYao


open MeasureTheory Filter Set Topology TopologicalSpace
namespace MongeKantorovichYao

lemma cyclic_plan_tendsto {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (c : X × Y → ℝ) (hc : Continuous c)
    (πs : ℕ → ProbabilityMeasure (X × Y)) (π : ProbabilityMeasure (X × Y))
    (hlim : Tendsto πs atTop (𝓝 π))
    (hcyc : ∀ n, IsCCyclicallyMonotonePlan c (πs n : Measure (X × Y))) :
    IsCCyclicallyMonotonePlan c (π : Measure (X × Y)) := by
  classical
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  have hs (n : ℕ) : IsCCyclicallyMonotone c (πs n : Measure (X × Y)).support :=
    support_cyclic c hc (πs n : Measure (X × Y)) (hcyc n)
  refine ⟨(π : Measure (X × Y)).support, ?_, Measure.measure_compl_support⟩
  intro N p hp
  by_contra! hbad
  let V : Set (Fin (N+1) → X × Y) :=
    {q | ∑ i, c ((q i).1,(q (i+1)).2) < ∑ i, c (q i)}
  have hV : IsOpen V := by
    apply isOpen_lt
    · exact continuous_finsetSum _ (fun i _ =>
        hc.comp ((continuous_fst.comp (continuous_apply i)).prodMk
          (continuous_snd.comp (continuous_apply (i+1)))))
    · exact continuous_finsetSum _ (fun i _ => hc.comp (continuous_apply i))
  obtain ⟨F,U,hU,hsub⟩ := isOpen_pi_iff.mp hV p hbad
  let W : Fin (N+1) → Set (X × Y) := fun i => if i ∈ F then U i else Set.univ
  have hw (i : Fin (N+1)) : IsOpen (W i) ∧ p i ∈ W i := by
    by_cases hi : i ∈ F
    · simpa only [W, hi, ↓reduceIte] using hU i hi
    · simp [W,hi]
  have he (i : Fin (N+1)) : ∀ᶠ n in atTop, 0 < (πs n : Measure (X × Y)) (W i) := by
    have hpos : 0 < (π : Measure (X × Y)) (W i) :=
      (Measure.mem_support_iff_forall (p i)).mp (hp i) (W i) ((hw i).1.mem_nhds (hw i).2)
    have hli := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (hw i).1
    exact eventually_lt_of_lt_liminf (hpos.trans_le hli)
  obtain ⟨n,hn⟩ := (Filter.eventually_all.mpr he).exists
  have hq (i : Fin (N+1)) : ∃ q ∈ W i, q ∈ (πs n : Measure (X × Y)).support :=
    (πs n : Measure (X × Y)).nonempty_inter_support_of_pos (hn i)
  choose q hqW hqS using hq
  have hqV : q ∈ V := hsub (fun i hi => by
    have hi' : i ∈ F := hi
    simpa only [W, hi', ↓reduceIte] using hqW i)
  have hqC := hs n N q hqS
  exact (not_lt_of_ge hqC) hqV

end MongeKantorovichYao


open MeasureTheory Filter Set Topology TopologicalSpace
namespace MongeKantorovichYao

lemma tight_range_of_tendsto {X : Type*} [MetricSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto μs atTop (𝓝 μ)) :
    IsTightMeasureSet (Set.range (fun n => (μs n : Measure X))) := by
  have hK : IsCompact (closure (Set.range μs)) :=
    hlim.isCompact_insert_range.closure_of_subset (Set.subset_insert μ (Set.range μs))
  apply (isTightMeasureSet_of_isCompact_closure hK).subset
  rintro ρ ⟨n,rfl⟩
  exact ⟨μs n, Set.mem_range_self n, rfl⟩

lemma limit_cyclic_couplings {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (c : X × Y → ℝ) (hc : Continuous c)
    (μs : ℕ → ProbabilityMeasure X) (νs : ℕ → ProbabilityMeasure Y)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (πs : ℕ → ProbabilityMeasure (X × Y))
    (hfst : ∀ n, (πs n : Measure (X × Y)).map Prod.fst = (μs n : Measure X))
    (hsnd : ∀ n, (πs n : Measure (X × Y)).map Prod.snd = (νs n : Measure Y))
    (hcyc : ∀ n, IsCCyclicallyMonotonePlan c (πs n : Measure (X × Y))) :
    ∃ π ∈ transferencePlans (μ : Measure X) (ν : Measure Y), IsCCyclicallyMonotonePlan c π := by
  classical
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  have hμt := tight_range_of_tendsto μs μ hμ
  have hνt := tight_range_of_tendsto νs ν hν
  have hπt : IsTightMeasureSet (Set.range (fun n => (πs n : Measure (X × Y)))) := by
    apply IsTightMeasureSet.prodMk
    · apply hμt.subset
      rintro ρ ⟨π',⟨n,rfl⟩,rfl⟩
      exact ⟨n, (hfst n).symm⟩
    · apply hνt.subset
      rintro ρ ⟨π',⟨n,rfl⟩,rfl⟩
      exact ⟨n, (hsnd n).symm⟩
  have hπt' : IsTightMeasureSet {((ρ : ProbabilityMeasure (X × Y)) : Measure (X × Y)) |
      ρ ∈ Set.range πs} := by
    apply hπt.subset
    rintro ρ ⟨ρ',⟨n,rfl⟩,rfl⟩
    exact Set.mem_range_self n
  have hK := isCompact_closure_of_isTightMeasureSet hπt'
  obtain ⟨π,_,φ,hφ,hlim⟩ := hK.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have heF (n : ℕ) : (πs n).map measurable_fst.aemeasurable = μs n :=
    Subtype.ext (hfst n)
  have heS (n : ℕ) : (πs n).map measurable_snd.aemeasurable = νs n :=
    Subtype.ext (hsnd n)
  have hpF : π.map measurable_fst.aemeasurable = μ := by
    apply tendsto_nhds_unique ?_ (hμ.comp hφ.tendsto_atTop)
    have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (πs ∘ φ) π hlim continuous_fst
    simpa only [Function.comp_def, heF] using h
  have hpS : π.map measurable_snd.aemeasurable = ν := by
    apply tendsto_nhds_unique ?_ (hν.comp hφ.tendsto_atTop)
    have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (πs ∘ φ) π hlim continuous_snd
    simpa only [Function.comp_def, heS] using h
  have hpC := cyclic_plan_tendsto c hc (πs ∘ φ) π hlim (fun n => hcyc (φ n))
  exact ⟨(π : Measure (X × Y)), ⟨inferInstance, congrArg Subtype.val hpF,
    congrArg Subtype.val hpS⟩, hpC⟩

end MongeKantorovichYao


open MeasureTheory Filter Set Topology TopologicalSpace
namespace MongeKantorovichYao

lemma simple_coupling_exists {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (f : SimpleFunc X X) (g : SimpleFunc Y Y) (c : X × Y → ℝ) :
    ∃ π ∈ transferencePlans (μ.map f.measurable.aemeasurable : Measure X)
      (ν.map g.measurable.aemeasurable : Measure Y), IsCCyclicallyMonotonePlan c π := by
  classical
  rw [simple_map_eq_atoms μ f, simple_map_eq_atoms ν g]
  exact Weighted.finite_weighted_plan (fun i : f.range => (i : X)) (fun j : g.range => (j : Y))
    (simpleWeights μ f) (simpleWeights ν g) (simpleWeights_nonneg μ f)
    (simpleWeights_nonneg ν g) (simpleWeights_sum μ f) (simpleWeights_sum ν g) c

lemma general_cyclic_plan {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc_cont : Continuous c) (hc_nonneg : ∀ p, 0 ≤ c p) :
    ∃ π ∈ transferencePlans μ ν, IsCCyclicallyMonotonePlan c π := by
  classical
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  let μp : ProbabilityMeasure X := ⟨μ, inferInstance⟩
  let νp : ProbabilityMeasure Y := ⟨ν, inferInstance⟩
  obtain ⟨f,hf⟩ := exists_simple_map_tendsto μp
  obtain ⟨g,hg⟩ := exists_simple_map_tendsto νp
  let μs : ℕ → ProbabilityMeasure X := fun n => μp.map (f n).measurable.aemeasurable
  let νs : ℕ → ProbabilityMeasure Y := fun n => νp.map (g n).measurable.aemeasurable
  have hx (n : ℕ) : ∃ π ∈ transferencePlans (μs n : Measure X) (νs n : Measure Y),
      IsCCyclicallyMonotonePlan c π := simple_coupling_exists μp νp (f n) (g n) c
  choose ρ hρ hρC using hx
  let πs : ℕ → ProbabilityMeasure (X × Y) := fun n => ⟨ρ n, (hρ n).1⟩
  exact limit_cyclic_couplings c hc_cont μs νs μp νp hf hg πs
    (fun n => (hρ n).2.1) (fun n => (hρ n).2.2) hρC

end MongeKantorovichYao

open MongeKantorovichYao MeasureTheory
theorem solution {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc_cont : Continuous c) (hc_nonneg : ∀ p, 0 ≤ c p) :
    ∃ π ∈ transferencePlans μ ν, IsCCyclicallyMonotonePlan c π := by
  exact general_cyclic_plan μ ν c hc_cont hc_nonneg

#print axioms solution
