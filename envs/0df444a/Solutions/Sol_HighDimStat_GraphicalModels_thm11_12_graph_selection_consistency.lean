-- Prove2me | solution 1 for HighDimStat.GraphicalModels.thm11_12_graph_selection_consistency
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:35:01.614718+00:00
-- url     : https://prove2.me/submissions/7147c122-fdb8-4eb7-9e95-d50e09f92d89

import Mathlib
import Definitions.Def_HighDimStat_GraphicalModels_NeighborhoodLasso

open HighDimStat.GraphicalModels MeasureTheory ProbabilityTheory

open Classical

theorem exists_n_exp_lt (c2 c3 : ℝ) (hc2 : 0 < c2) (hc3 : 0 < c3) :
    ∃ n : ℕ, 0 < n ∧ c2 * Real.exp (-c3 * (n : ℝ) * min (1 ^ 2) (1 / (1 : ℝ))) < 1 := by
  have hmin : min (1 ^ 2 : ℝ) (1 / (1 : ℝ)) = 1 := by norm_num
  have h_bound : ∃ m : ℕ, Real.log c2 / c3 < (m : ℝ) := exists_nat_gt (Real.log c2 / c3)
  obtain ⟨m, hm⟩ := h_bound
  use m + 1
  constructor
  · omega
  · rw [hmin, mul_one]
    have hpos : (m : ℝ) < (m + 1 : ℝ) := lt_add_one (m : ℝ)
    have hmn : Real.log c2 / c3 < (m + 1 : ℝ) := hm.trans hpos
    rw [div_lt_iff₀ hc3] at hmn
    have h1 : Real.log c2 < c3 * (m + 1 : ℝ) := by linarith
    have h2 : - (c3 * (m + 1 : ℝ)) < - Real.log c2 := by linarith
    have h3 : - Real.log c2 = Real.log (c2⁻¹) := (Real.log_inv c2).symm
    have h4 : - (c3 * (m + 1 : ℝ)) < Real.log (c2⁻¹) := by rwa [← h3]
    have h5 : Real.exp (- (c3 * (m + 1 : ℝ))) < c2⁻¹ := by
      rw [← Real.exp_log (inv_pos.mpr hc2)]
      exact Real.exp_lt_exp.mpr h4
    have h6 : c2 * Real.exp (- (c3 * (m + 1 : ℝ))) < c2 * c2⁻¹ :=
      mul_lt_mul_of_pos_left h5 hc2
    rw [mul_inv_cancel₀ (ne_of_gt hc2)] at h6
    have heq : -c3 * ((m + 1 : ℕ) : ℝ) = - (c3 * (m + 1 : ℝ)) := by
      push_cast
      ring
    rwa [heq]

lemma indep_const (n : ℕ) :
    iIndepFun (fun (_ : Fin n) (_ : Unit) => (0 : Fin 2 → ℝ)) (Measure.dirac ()) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  by_cases h : ∀ i ∈ S, (0 : Fin 2 → ℝ) ∈ sets i
  · have h1 : (⋂ i ∈ S, (fun (_ : Unit) => (0 : Fin 2 → ℝ)) ⁻¹' sets i) = Set.univ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
      exact h
    rw [h1, Measure.dirac_apply_of_mem (by trivial)]
    have h2 : ∀ i ∈ S, (Measure.dirac ()) ((fun (_ : Unit) => (0 : Fin 2 → ℝ)) ⁻¹' sets i) = 1 := by
      intro i hi
      rw [Measure.dirac_apply_of_mem]
      simp [h i hi]
    rw [Finset.prod_congr rfl h2, Finset.prod_const_one]
  · simp only [not_forall] at h
    rcases h with ⟨i, hiS, hi⟩
    have h1 : (⋂ j ∈ S, (fun (_ : Unit) => (0 : Fin 2 → ℝ)) ⁻¹' sets j) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hall
      exact hi (hall i hiS)
    rw [h1, measure_empty]
    have hpre : (fun (_ : Unit) => (0 : Fin 2 → ℝ)) ⁻¹' sets i = ∅ := by
      ext ⟨⟩
      simp [hi]
    have hzero : (Measure.dirac ()) ((fun (_ : Unit) => (0 : Fin 2 → ℝ)) ⁻¹' sets i) = 0 := by
      rw [hpre, measure_empty]
    exact (Finset.prod_eq_zero hiS hzero).symm

lemma gauss_const (w : Fin 2 → ℝ) :
    Measure.map (fun (_ : Unit) => ∑ j : Fin 2, w j * (0 : ℝ)) (Measure.dirac ()) =
      gaussianReal 0 (Real.toNNReal (∑ j : Fin 2, ∑ k : Fin 2, w j * w k * (-1 : Matrix (Fin 2) (Fin 2) ℝ) j k)) := by
  have hl : (fun (_ : Unit) => ∑ j : Fin 2, w j * (0 : ℝ)) = (fun _ => (0 : ℝ)) := by
    ext x
    simp
  rw [hl, Measure.map_dirac (f := fun _ => (0 : ℝ)) ()]
  have hr : (∑ j : Fin 2, ∑ k : Fin 2, w j * w k * (-1 : Matrix (Fin 2) (Fin 2) ℝ) j k) ≤ 0 := by
    simp [Fin.sum_univ_two]
    nlinarith
  rw [Real.toNNReal_of_nonpos hr, gaussianReal_zero_var]

lemma iid_const (n : ℕ) :
    IsIIDGaussianDesign (fun (_ : Fin n) (_ : Unit) (_ : Fin 2) => (0 : ℝ))
      (Measure.dirac ()) (-1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨fun _ => measurable_const, indep_const n, fun _ => gauss_const⟩

lemma empty_iSup (ι : Type) [IsEmpty ι] (f : ι → ℝ) : (⨆ i, f i) = 0 := by
  change sSup (Set.range f) = 0
  have : Set.range f = ∅ := Set.range_eq_empty f
  rw [this, Real.sSup_empty]

lemma opnorm_empty (_j : Fin 2) :
    opNormInfty (submatrixOn (-1 : Matrix (Fin 2) (Fin 2) ℝ) (∅ : Finset (Fin 2)))⁻¹ ≤ 1 := by
  dsimp [opNormInfty]
  rw [empty_iSup {i // i ∈ (∅ : Finset (Fin 2))}]
  linarith

lemma incoherent_empty (_j : Fin 2) :
    IsAlphaIncoherent (-1 : Matrix (Fin 2) (Fin 2) ℝ)
      (Finset.univ.filter (· ≠ _j)) (∅ : Finset (Fin 2)) 0 := by
  intro k hk hnot
  simp

lemma lasso_sol (n : ℕ) (j : Fin 2) (ω : Unit) :
    IsNeighborhoodLassoSolution
      (fun (_ : Fin n) (_ : Unit) (_ : Fin 2) => (0 : ℝ))
      j ω 0
      (fun (_ : {k : Fin 2 // k ≠ j}) => (1 : ℝ)) := by
  intro β
  dsimp [IsNeighborhoodLassoSolution]
  simp

lemma edges_not_sub :
    ¬ (orRuleEdges (fun (j : Fin 2) => estimatedNeighborhood (fun (_ : {k : Fin 2 // k ≠ j}) => (1 : ℝ))) ⊆
        {p : Fin 2 × Fin 2 | p.1 ≠ p.2 ∧ (-1 : Matrix (Fin 2) (Fin 2) ℝ) p.1 p.2 ≠ 0}) := by
  intro hsub
  have hmem : ((0 : Fin 2), (1 : Fin 2)) ∈ orRuleEdges (fun (j : Fin 2) => estimatedNeighborhood (fun (_ : {k : Fin 2 // k ≠ j}) => (1 : ℝ))) := by
    dsimp [orRuleEdges, estimatedNeighborhood]
    constructor
    · decide
    · left
      refine ⟨by decide, by norm_num⟩
  have htarget := hsub hmem
  dsimp at htarget
  have hdiag : (-1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
    simp
  exact htarget.2 hdiag

open HighDimStat.GraphicalModels MeasureTheory in
theorem solution :
    ¬ (∃ c0 c2 c3 : ℝ, 0 < c0 ∧ 0 < c2 ∧ 0 < c3 ∧
    ∀ {V Ω : Type} [Fintype V] [DecidableEq V]
      [Nonempty V] [MeasurableSpace Ω] {n : ℕ}, 0 < n →
    ∀ (Θstar Sigstar : Matrix V V ℝ), Sigstar * Θstar = 1 →
    ∀ (trueNbhd : V → Finset V), (∀ j k, k ∈ trueNbhd j ↔ k ≠ j ∧ Θstar j k ≠ 0) →
    ∀ (α b : ℝ), 1 ≤ b →
      (∀ j, IsAlphaIncoherent Sigstar (Finset.univ.filter (· ≠ j)) (trueNbhd j) α) →
      (∀ j, opNormInfty (submatrixOn Sigstar (trueNbhd j))⁻¹ ≤ b) →
    ∀ (m : ℕ), 0 < m → (∀ j, (trueNbhd j).card ≤ m) →
    ∀ (P : Measure Ω) [IsProbabilityMeasure P] (Xdes : Fin n → Ω → V → ℝ),
      IsIIDGaussianDesign Xdes P Sigstar →
    ∀ (δ : ℝ), δ ∈ Set.Ioc (0 : ℝ) 1 →
    ∀ (lam : ℝ), lam = c0 * (1 / α) * (Real.sqrt (Real.log (Fintype.card V) / n) + δ) →
    ∀ (θhat : ∀ j : V, Ω → {k : V // k ≠ j} → ℝ),
      (∀ j ω, IsNeighborhoodLassoSolution Xdes j ω lam (θhat j ω)) →
      1 - c2 * Real.exp (-c3 * n * min (δ ^ 2) (1 / (m : ℝ))) ≤
        P.real {ω |
          (orRuleEdges (fun j => estimatedNeighborhood (θhat j ω)) ⊆
              {p : V × V | p.1 ≠ p.2 ∧ Θstar p.1 p.2 ≠ 0} ∧
            ∀ j k, j ≠ k → 7 * b * lam ≤ |Θstar j k| →
              (j, k) ∈ orRuleEdges (fun j => estimatedNeighborhood (θhat j ω))) ∧
          (andRuleEdges (fun j => estimatedNeighborhood (θhat j ω)) ⊆
              {p : V × V | p.1 ≠ p.2 ∧ Θstar p.1 p.2 ≠ 0} ∧
            ∀ j k, j ≠ k → 7 * b * lam ≤ |Θstar j k| →
              (j, k) ∈ andRuleEdges (fun j => estimatedNeighborhood (θhat j ω)))}) := by
  intro ⟨c0, c2, c3, hc0, hc2, hc3, hthm⟩
  obtain ⟨n, hnpos, hbound⟩ := exists_n_exp_lt c2 c3 hc2 hc3
  have hspec := hthm (V := Fin 2) (Ω := Unit) (n := n) hnpos
    (-1) (-1) (by simp)
    (fun _ => ∅) (by
      intro j k
      simp [Matrix.one_apply]
      aesop)
    0 1 le_rfl
    incoherent_empty
    opnorm_empty
    1 zero_lt_one (by intro j; simp)
    (Measure.dirac ()) (fun _ _ _ => 0)
    (iid_const n)
    1 (by simp)
    0 (by simp)
    (fun _ _ _ => 1)
    (lasso_sol n)
  have hevent : {ω : Unit |
      (orRuleEdges (fun j => estimatedNeighborhood (fun (_ : {k : Fin 2 // k ≠ j}) => (1 : ℝ))) ⊆
          {p : Fin 2 × Fin 2 | p.1 ≠ p.2 ∧ (-1 : Matrix (Fin 2) (Fin 2) ℝ) p.1 p.2 ≠ 0} ∧
        ∀ j k, j ≠ k → 7 * 1 * 0 ≤ |(-1 : Matrix (Fin 2) (Fin 2) ℝ) j k| →
          (j, k) ∈ orRuleEdges (fun j => estimatedNeighborhood (fun (_ : {k : Fin 2 // k ≠ j}) => (1 : ℝ)))) ∧
      (andRuleEdges (fun j => estimatedNeighborhood (fun (_ : {k : Fin 2 // k ≠ j}) => (1 : ℝ))) ⊆
          {p : Fin 2 × Fin 2 | p.1 ≠ p.2 ∧ (-1 : Matrix (Fin 2) (Fin 2) ℝ) p.1 p.2 ≠ 0} ∧
        ∀ j k, j ≠ k → 7 * 1 * 0 ≤ |(-1 : Matrix (Fin 2) (Fin 2) ℝ) j k| →
          (j, k) ∈ andRuleEdges (fun j => estimatedNeighborhood (fun (_ : {k : Fin 2 // k ≠ j}) => (1 : ℝ))))} = ∅ := by
    ext ⟨⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    intro ⟨⟨h_or, _⟩, _⟩
    exact edges_not_sub h_or
  rw [hevent, measureReal_empty] at hspec
  linarith
