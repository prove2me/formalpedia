-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiForwardFiniteDimensionalLawWithoutMoment
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T10:15:40.883797+00:00
-- url     : https://prove2.me/submissions/872d3e88-f34c-4ece-bd87-e0f95bab0fbe

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardTimeChangeMarkov
import Theorems.Thm_Kyprianou_Ch01_stoppedCompoundPoissonMarkov
import Theorems.Thm_Kyprianou_Ch01_lampertiLatticeGeneratorSemigroupUnique
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace LampertiFDDAux

def cyl {Ω : Type*} (X : ℝ≥0 → Ω → ℕ) (S : Finset (ℝ≥0 × ℕ)) : Set Ω :=
  {ω | ∀ p ∈ S, X p.1 ω = p.2}

lemma markov_finset {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℝ≥0 → Ω → ℕ) (K : ℕ → ℝ≥0 → PMF ℕ)
    (hM : ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
      (∀ i, u i ≤ s) →
      μ ({ω | ∀ i, X (u i) ω = v i} ∩ {ω | X (s + t) ω = k}) =
        ∑' z : ℕ, μ ({ω | ∀ i, X (u i) ω = v i} ∩ {ω | X s ω = z}) * K z t k)
    (S : Finset (ℝ≥0 × ℕ)) (s t : ℝ≥0) (k : ℕ) (hS : ∀ p ∈ S, p.1 ≤ s) :
    μ (cyl X S ∩ {ω | X (s + t) ω = k}) =
      ∑' z : ℕ, μ (cyl X S ∩ {ω | X s ω = z}) * K z t k := by
  have hset : cyl X S = {ω | ∀ i : Fin S.card,
      X ((S.equivFin.symm i).1.1) ω = (S.equivFin.symm i).1.2} := by
    ext ω
    simp only [cyl, Set.mem_ofPred_eq]
    constructor
    · intro h i
      exact h _ (S.equivFin.symm i).2
    · intro h p hp
      have := h (S.equivFin ⟨p, hp⟩)
      simpa using this
  rw [hset]
  exact hM S.card _ _ s t k (fun i => hS _ (S.equivFin.symm i).2)

lemma start_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℝ≥0 → Ω → ℕ) (y : ℕ) (hX : AEMeasurable (X 0) μ)
    (h : μ {ω | X 0 ω = y} = 1) (z : ℕ) :
    μ {ω | X 0 ω = z} = if z = y then 1 else 0 := by
  split_ifs with hz
  · subst hz; exact h
  · have hnm : NullMeasurableSet {ω | X 0 ω = y} μ :=
      hX.nullMeasurable (measurableSet_singleton y)
    have hc : μ {ω | X 0 ω = y}ᶜ = 0 := by
      rw [measure_compl₀ hnm (measure_ne_top _ _), h]; simp
    refine le_antisymm ?_ bot_le
    rw [← hc]
    apply measure_mono
    intro ω hω hω'
    exact hz (hω.symm.trans hω' : z = y) |>.elim
    

lemma cyl_inter_max {Ω : Type*} (X : ℝ≥0 → Ω → ℕ) (S : Finset (ℝ≥0 × ℕ))
    (q : ℝ≥0 × ℕ) (hq : q ∈ S) (z : ℕ) :
    cyl X S ∩ {ω | X q.1 ω = z} = if z = q.2 then cyl X S else ∅ := by
  ext ω
  split_ifs with hz
  · subst hz
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_iff_left_iff_imp]
    intro h; exact h q hq
  · simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro h h'
    exact hz (h'.symm.trans (h q hq))

lemma cyl_split {Ω : Type*} (X : ℝ≥0 → Ω → ℕ) (S : Finset (ℝ≥0 × ℕ))
    (p : ℝ≥0 × ℕ) (hp : p ∈ S) :
    cyl X S = cyl X (S.erase p) ∩ {ω | X p.1 ω = p.2} := by
  ext ω
  simp only [cyl, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_erase]
  constructor
  · intro h; exact ⟨fun q hq => h q hq.2, h p hp⟩
  · intro ⟨h, h'⟩ q hq
    by_cases hqp : q = p
    · subst hqp; exact h'
    · exact h q ⟨hqp, hq⟩

theorem cyl_eq {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (X₁ : ℝ≥0 → Ω₁ → ℕ) (X₂ : ℝ≥0 → Ω₂ → ℕ)
    (K : ℕ → ℝ≥0 → PMF ℕ) (y : ℕ)
    (hMeas₁ : ∀ t : ℝ≥0, AEMeasurable (X₁ t) μ₁)
    (hMeas₂ : ∀ t : ℝ≥0, AEMeasurable (X₂ t) μ₂)
    (hStart₁ : μ₁ {ω | X₁ 0 ω = y} = 1)
    (hStart₂ : μ₂ {ω | X₂ 0 ω = y} = 1)
    (hMarkov₁ : ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
      (∀ i, u i ≤ s) →
      μ₁ ({ω | ∀ i, X₁ (u i) ω = v i} ∩ {ω | X₁ (s + t) ω = k}) =
        ∑' z : ℕ, μ₁ ({ω | ∀ i, X₁ (u i) ω = v i} ∩ {ω | X₁ s ω = z}) * K z t k)
    (hMarkov₂ : ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
      (∀ i, u i ≤ s) →
      μ₂ ({ω | ∀ i, X₂ (u i) ω = v i} ∩ {ω | X₂ (s + t) ω = k}) =
        ∑' z : ℕ, μ₂ ({ω | ∀ i, X₂ (u i) ω = v i} ∩ {ω | X₂ s ω = z}) * K z t k)
    (S : Finset (ℝ≥0 × ℕ)) :
    μ₁ (cyl X₁ S) = μ₂ (cyl X₂ S) := by
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    have h1 : cyl X₁ ∅ = Set.univ := by ext; simp [cyl]
    have h2 : cyl X₂ ∅ = Set.univ := by ext; simp [cyl]
    rw [h1, h2]; simp
  obtain ⟨p, hp, hpmax⟩ := S.exists_max_image Prod.fst hS
  set S' := S.erase p with hS'
  have hsub : S' ⊂ S := Finset.erase_ssubset hp
  rw [cyl_split X₁ S p hp, cyl_split X₂ S p hp]
  rcases S'.eq_empty_or_nonempty with hE | hE
  · -- only p: use start time 0
    have hS0 : ∀ q ∈ S', q.1 ≤ 0 := by simp [hE]
    have e1 := markov_finset μ₁ X₁ K hMarkov₁ S' 0 p.1 p.2 hS0
    have e2 := markov_finset μ₂ X₂ K hMarkov₂ S' 0 p.1 p.2 hS0
    rw [zero_add] at e1 e2
    rw [e1, e2]
    congr 1; funext z; congr 1
    have h1 : cyl X₁ S' = Set.univ := by ext; simp [cyl, hE]
    have h2 : cyl X₂ S' = Set.univ := by ext; simp [cyl, hE]
    rw [h1, h2, Set.univ_inter, Set.univ_inter,
      start_prob μ₁ X₁ y (hMeas₁ 0) hStart₁, start_prob μ₂ X₂ y (hMeas₂ 0) hStart₂]
  · obtain ⟨q, hq, hqmax⟩ := S'.exists_max_image Prod.fst hE
    have hqS : q ∈ S := Finset.mem_of_mem_erase hq
    have hle : q.1 ≤ p.1 := hpmax q hqS
    have hS0 : ∀ r ∈ S', r.1 ≤ q.1 := hqmax
    have e1 := markov_finset μ₁ X₁ K hMarkov₁ S' q.1 (p.1 - q.1) p.2 hS0
    have e2 := markov_finset μ₂ X₂ K hMarkov₂ S' q.1 (p.1 - q.1) p.2 hS0
    rw [add_tsub_cancel_of_le hle] at e1 e2
    rw [e1, e2]
    congr 1; funext z; congr 1
    rw [cyl_inter_max X₁ S' q hq z, cyl_inter_max X₂ S' q hq z]
    split_ifs
    · exact ih S' hsub
    · simp


lemma preimage_eq {Ω : Type*} (X : ℝ≥0 → Ω → ℕ) {n : ℕ} (times : Fin n → ℝ≥0)
    (w : Fin n → ℤ) :
    (fun ω => fun i : Fin n => (X (times i) ω : ℤ)) ⁻¹' {w} =
      if ∀ i, 0 ≤ w i then
        cyl X (Finset.univ.image (fun i => (times i, (w i).toNat)))
      else ∅ := by
  ext ω
  split_ifs with h
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, cyl, Set.mem_ofPred_eq,
      Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff]
    constructor
    · intro hω i
      have := congrFun hω i
      omega
    · intro hω
      funext i
      have := hω i
      have := h i
      omega
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hω
    apply h
    intro i
    rw [← congrFun hω i]
    exact Int.natCast_nonneg _

lemma aemeas_vec {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ≥0 → Ω → ℕ)
    {n : ℕ} (times : Fin n → ℝ≥0) (hX : ∀ t, AEMeasurable (X t) μ) :
    AEMeasurable (fun ω => fun i : Fin n => (X (times i) ω : ℤ)) μ :=
  aemeasurable_pi_lambda _ (fun i => (measurable_from_top).comp_aemeasurable (hX _))

end LampertiFDDAux

open LampertiFDDAux in
theorem LampertiFDDAux.markovFiniteDimensionalLawsUnique
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (X₁ : ℝ≥0 → Ω₁ → ℕ) (X₂ : ℝ≥0 → Ω₂ → ℕ)
    (K : ℕ → ℝ≥0 → PMF ℕ) (y : ℕ)
    (hMeas₁ : ∀ t : ℝ≥0, AEMeasurable (X₁ t) μ₁)
    (hMeas₂ : ∀ t : ℝ≥0, AEMeasurable (X₂ t) μ₂)
    (hStart₁ : μ₁ {ω | X₁ 0 ω = y} = 1)
    (hStart₂ : μ₂ {ω | X₂ 0 ω = y} = 1)
    (hMarkov₁ : ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
      (∀ i, u i ≤ s) →
      μ₁ ({ω | ∀ i, X₁ (u i) ω = v i} ∩ {ω | X₁ (s + t) ω = k}) =
        ∑' z : ℕ, μ₁ ({ω | ∀ i, X₁ (u i) ω = v i} ∩ {ω | X₁ s ω = z}) * K z t k)
    (hMarkov₂ : ∀ (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
      (∀ i, u i ≤ s) →
      μ₂ ({ω | ∀ i, X₂ (u i) ω = v i} ∩ {ω | X₂ (s + t) ω = k}) =
        ∑' z : ℕ, μ₂ ({ω | ∀ i, X₂ (u i) ω = v i} ∩ {ω | X₂ s ω = z}) * K z t k) :
    ∀ (n : ℕ) (times : Fin n → ℝ≥0),
      μ₁.map (fun ω => fun i : Fin n => (X₁ (times i) ω : ℤ)) =
        μ₂.map (fun ω => fun i : Fin n => (X₂ (times i) ω : ℤ)) := by
  intro n times
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_apply_of_aemeasurable (aemeas_vec μ₁ X₁ times hMeas₁) (measurableSet_singleton w),
    Measure.map_apply_of_aemeasurable (aemeas_vec μ₂ X₂ times hMeas₂) (measurableSet_singleton w),
    preimage_eq X₁ times w, preimage_eq X₂ times w]
  split_ifs
  · exact cyl_eq μ₁ μ₂ X₁ X₂ K y hMeas₁ hMeas₂ hStart₁ hStart₂ hMarkov₁ hMarkov₂ _
  · simp


theorem solution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω))
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ y : ℕ, ∀ n : ℕ, ∀ times : Fin n → ℝ≥0,
      (P y).map
        (fun ω => fun i : Fin n =>
          (branchingToPoisson Y (times i) ω : ℤ)) =
      Q.map
        (fun ω => fun i : Fin n =>
          stoppedIntegerCompoundPoisson y arrival marks (times i) ω) := by
  intro y n times
  obtain ⟨lawX, hsX, hiX, hgX, hX⟩ :=
    lampertiForwardTimeChangeMarkov Y P law rate hRate offspring hNoNullJumps
      hBranching hMarkov hSemigroup hGenerator hInitial hMeas hCadlag
  obtain ⟨lawC, hsC, hiC, hgC, hC⟩ :=
    stoppedCompoundPoissonMarkov Q rate hRate offspring hNoNullJumps
      arrival marks jumpLaw hDriver hSupport hJumpMass
  have heq : lawX = lawC :=
    lampertiLatticeGeneratorSemigroupUnique rate offspring hNoNullJumps
      lawX lawC hsX hsC hiX hiC hgX hgC
  subst heq
  obtain ⟨hmeasX, h0X, hmX⟩ := hX y
  obtain ⟨hnn, hmeasC, h0C, hmC⟩ := hC y
  have : IsProbabilityMeasure (P y) := hMarkov.1 y
  have key := LampertiFDDAux.markovFiniteDimensionalLawsUnique (P y) Q
    (fun t ω => branchingToPoisson Y t ω)
    (fun t ω => (stoppedIntegerCompoundPoisson y arrival marks t ω).toNat)
    lawX y hmeasX hmeasC h0X h0C hmX hmC n times
  rw [key]
  apply Measure.map_congr
  filter_upwards [ae_all_iff.2 (fun i : Fin n => hnn (times i))] with ω hω
  funext i
  exact Int.toNat_of_nonneg (hω i)
