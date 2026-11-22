-- Prove2me | solution 1 for Kyprianou.Ch01.stoppedCompoundPoissonGenerator
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T11:35:54.324822+00:00
-- url     : https://prove2.me/submissions/f9540442-090d-4653-b9e6-eac0885bee24

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false


namespace StoppedCPGen

variable {Ω : Type*}

lemma arrival_zero (τ : ℕ → Ω → ℝ) (ω : Ω) : arrival τ 0 ω = τ 0 ω := by
  simp [arrival]

lemma arrival_one (τ : ℕ → Ω → ℝ) (ω : Ω) : arrival τ 1 ω = τ 0 ω + τ 1 ω := by
  simp [arrival, Finset.sum_range_succ]

lemma jumpCount_before (τ : ℕ → Ω → ℝ) (ω : Ω) {s : ℝ} (hs : s < τ 0 ω) :
    jumpCount (fun n => arrival τ n ω) s = 0 := by
  unfold jumpCount
  exact Nat.sInf_eq_zero.2 (Or.inl (by simpa [arrival_zero] using hs))

lemma jumpCount_one (τ : ℕ → Ω → ℝ) (ω : Ω) {s : ℝ} (h0 : τ 0 ω ≤ s)
    (h1 : s < τ 0 ω + τ 1 ω) :
    jumpCount (fun n => arrival τ n ω) s = 1 := by
  unfold jumpCount
  have hmem : (1 : ℕ) ∈ {n | s < arrival τ n ω} := by
    simp only [Set.mem_ofPred_eq, arrival_one]; exact h1
  apply le_antisymm (Nat.sInf_le hmem)
  rw [Nat.one_le_iff_ne_zero]
  intro h
  rcases Nat.sInf_eq_zero.1 h with h' | h'
  · simp only [Set.mem_ofPred_eq, arrival_zero] at h'; linarith
  · rw [h'] at hmem; exact hmem

lemma cp_before (τ ξ : ℕ → Ω → ℝ) (ω : Ω) {s : ℝ} (hs : s < τ 0 ω) :
    compoundPoisson 0 τ ξ s ω = 0 := by
  simp [compoundPoisson, piecewisePath, jumpCount_before τ ω hs]

lemma cp_one (τ ξ : ℕ → Ω → ℝ) (ω : Ω) {s : ℝ} (h0 : τ 0 ω ≤ s)
    (h1 : s < τ 0 ω + τ 1 ω) :
    compoundPoisson 0 τ ξ s ω = ξ 0 ω := by
  simp [compoundPoisson, piecewisePath, jumpCount_one τ ω h0 h1]

lemma icp_before (z : ℕ) (τ ξ : ℕ → Ω → ℝ) (ω : Ω) {s : ℝ≥0} (hs : (s : ℝ) < τ 0 ω) :
    integerCompoundPoisson z τ ξ s ω = z := by
  simp [integerCompoundPoisson, cp_before τ ξ ω hs]

lemma icp_one (z j : ℕ) (τ ξ : ℕ → Ω → ℝ) (ω : Ω) {s : ℝ≥0} (h0 : τ 0 ω ≤ s)
    (h1 : (s : ℝ) < τ 0 ω + τ 1 ω) (hj : ξ 0 ω = (j : ℝ) - 1) :
    integerCompoundPoisson z τ ξ s ω = (z : ℤ) + j - 1 := by
  unfold integerCompoundPoisson
  rw [cp_one τ ξ ω h0 h1, hj]
  have : (z : ℝ) + ((j : ℝ) - 1) = (((z : ℤ) + j - 1 : ℤ) : ℝ) := by push_cast; ring
  rw [this, Int.floor_intCast]

lemma stop_keep (X : ℝ≥0 → Ω → ℤ) (ω : Ω) (b : ℝ) (t : ℝ≥0) (htb : (t : ℝ) < b)
    (hpos : ∀ s : ℝ≥0, (s : ℝ) < b → 0 < X s ω) :
    (if firstNonpositiveLattice X ω ≤ (t : WithTop ℝ≥0) then 0 else X t ω) = X t ω := by
  rw [if_neg]
  unfold firstNonpositiveLattice
  split_ifs with h
  · rw [WithTop.coe_le_coe, not_le]
    have hlb : b.toNNReal ≤ sInf {s : ℝ≥0 | X s ω ≤ 0} := by
      apply le_csInf h
      intro s hs
      by_contra hlt
      rw [not_le, Real.lt_toNNReal_iff_coe_lt] at hlt
      have := hpos s hlt
      exact absurd hs (not_le.2 this)
    exact lt_of_lt_of_le (Real.lt_toNNReal_iff_coe_lt.2 htb) hlb
  · exact not_le.2 (WithTop.coe_lt_top t)

lemma stop_zero (X : ℝ≥0 → Ω → ℤ) (ω : Ω) (t s0 : ℝ≥0) (hs0 : s0 ≤ t) (hX : X s0 ω ≤ 0) :
    (if firstNonpositiveLattice X ω ≤ (t : WithTop ℝ≥0) then 0 else X t ω) = 0 := by
  rw [if_pos]
  unfold firstNonpositiveLattice
  rw [if_pos ⟨s0, hX⟩, WithTop.coe_le_coe]
  exact (csInf_le (OrderBot.bddBelow _) (show s0 ∈ {s : ℝ≥0 | X s ω ≤ 0} from hX)).trans hs0

/-- Before the first arrival the stopped process sits at its start `z ≥ 1`. -/
lemma P0 (z : ℕ) (hz : 1 ≤ z) (τ ξ : ℕ → Ω → ℝ) (ω : Ω) (t : ℝ≥0) (ht : (t : ℝ) < τ 0 ω) :
    (stoppedIntegerCompoundPoisson z τ ξ t ω).toNat = z := by
  unfold stoppedIntegerCompoundPoisson
  simp only
  rw [stop_keep _ ω (τ 0 ω) t ht (fun s hs => by
    rw [icp_before z τ ξ ω hs]; exact_mod_cast hz), icp_before z τ ξ ω ht]
  simp

/-- Between the first and second arrival, with first mark `j - 1`. -/
lemma P1 (z : ℕ) (hz : 1 ≤ z) (τ ξ : ℕ → Ω → ℝ) (ω : Ω) (h0pos : 0 < τ 0 ω) (h1pos : 0 < τ 1 ω)
    (t : ℝ≥0) (j : ℕ) (h0 : τ 0 ω ≤ t) (h1 : (t : ℝ) < τ 0 ω + τ 1 ω)
    (hj : ξ 0 ω = (j : ℝ) - 1) :
    (stoppedIntegerCompoundPoisson z τ ξ t ω).toNat = z + j - 1 := by
  unfold stoppedIntegerCompoundPoisson
  simp only
  by_cases hv : 1 ≤ (z : ℤ) + j - 1
  · rw [stop_keep _ ω (τ 0 ω + τ 1 ω) t h1 (fun s hs => by
      by_cases hs0 : (s : ℝ) < τ 0 ω
      · rw [icp_before z τ ξ ω hs0]; exact_mod_cast hz
      · rw [icp_one z j τ ξ ω (not_lt.1 hs0) hs hj]; omega),
      icp_one z j τ ξ ω h0 h1 hj]
    omega
  · set s0 : ℝ≥0 := (τ 0 ω).toNNReal with hs0
    have hs0v : (s0 : ℝ) = τ 0 ω := Real.coe_toNNReal _ h0pos.le
    rw [stop_zero _ ω t s0 (by rw [← NNReal.coe_le_coe, hs0v]; exact h0) (by
      rw [icp_one z j τ ξ ω (by rw [hs0v]) (by rw [hs0v]; linarith) hj]; omega)]
    omega

/-- For `z = 0` the stopped process is identically `0` once the first clock is positive. -/
lemma Pzero (τ ξ : ℕ → Ω → ℝ) (ω : Ω) (h0pos : 0 < τ 0 ω) (t : ℝ≥0) :
    stoppedIntegerCompoundPoisson 0 τ ξ t ω = 0 := by
  unfold stoppedIntegerCompoundPoisson
  simp only
  exact stop_zero _ ω t 0 (zero_le) (by rw [icp_before 0 τ ξ ω (by simpa using h0pos)]; simp)

section Prob
variable [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  {rate : ℝ≥0} (hRate : 0 < rate) {τ ξ : ℕ → Ω → ℝ}
  {jumpLaw : Measure ℝ} [IsProbabilityMeasure jumpLaw]
  (hD : IsCompoundPoissonDriver τ ξ rate jumpLaw Q)
include hRate hD

lemma prob_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Q.real {ω | τ n ω ≤ t} = 1 - Real.exp (-((rate : ℝ) * t)) := by
  have hr : (0 : ℝ) < rate := hRate
  have := isProbabilityMeasure_expMeasure hr
  rw [(hD.law_interarrival n).measureReal_eq (p := fun x => x ≤ t) measurableSet_Iic,
    show {x : ℝ | x ≤ t} = Set.Iic t from rfl, ← cdf_eq_real, cdf_expMeasure_eq hr, if_pos ht]

lemma prob_gt (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Q.real {ω | t < τ n ω} = Real.exp (-((rate : ℝ) * t)) := by
  have hm : MeasurableSet {ω | τ n ω ≤ t} := hD.measurable_interarrival n measurableSet_Iic
  have : {ω | t < τ n ω} = {ω | τ n ω ≤ t}ᶜ := by ext; simp
  rw [this, measureReal_compl hm, probReal_univ, prob_le Q hRate hD n ht]; ring

lemma prob_pair {t : ℝ} (ht : 0 ≤ t) :
    Q.real ({ω | τ 0 ω ≤ t} ∩ {ω | τ 1 ω ≤ t}) = (1 - Real.exp (-((rate : ℝ) * t))) ^ 2 := by
  have hind : IndepFun (τ 0) (τ 1) Q := by
    have := hD.indep.indepFun (i := Sum.inl 0) (j := Sum.inl 1) (by simp)
    simpa using this
  have := hind.measure_inter_preimage_eq_mul (Set.Iic t) (Set.Iic t) measurableSet_Iic measurableSet_Iic
  rw [Measure.real, show {ω | τ 0 ω ≤ t} ∩ {ω | τ 1 ω ≤ t} = τ 0 ⁻¹' Set.Iic t ∩ τ 1 ⁻¹' Set.Iic t from rfl,
    this, ENNReal.toReal_mul]
  rw [← Measure.real, ← Measure.real]
  rw [show τ 0 ⁻¹' Set.Iic t = {ω | τ 0 ω ≤ t} from rfl, show τ 1 ⁻¹' Set.Iic t = {ω | τ 1 ω ≤ t} from rfl,
    prob_le Q hRate hD 0 ht, prob_le Q hRate hD 1 ht]; ring

lemma prob_mark (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Q.real ({ω | τ 0 ω ≤ t} ∩ {ω | ξ 0 ω = c}) =
      (1 - Real.exp (-((rate : ℝ) * t))) * jumpLaw.real {c} := by
  have hind : IndepFun (τ 0) (ξ 0) Q := by
    have := hD.indep.indepFun (i := Sum.inl 0) (j := Sum.inr 0) (by simp)
    simpa using this
  have := hind.measure_inter_preimage_eq_mul (Set.Iic t) {c} measurableSet_Iic (measurableSet_singleton c)
  rw [Measure.real, show {ω | τ 0 ω ≤ t} ∩ {ω | ξ 0 ω = c} = τ 0 ⁻¹' Set.Iic t ∩ ξ 0 ⁻¹' {c} from rfl,
    this, ENNReal.toReal_mul, ← Measure.real, ← Measure.real]
  rw [show τ 0 ⁻¹' Set.Iic t = {ω | τ 0 ω ≤ t} from rfl, prob_le Q hRate hD 0 ht]
  congr 1
  have := (hD.law_mark 0).measureReal_eq (p := fun x => x = c) (measurableSet_singleton c)
  exact this

lemma ae_pos (n : ℕ) : ∀ᵐ ω ∂Q, 0 < τ n ω := by
  rw [ae_iff]
  have h := prob_le Q hRate hD n le_rfl
  simp only [mul_zero, neg_zero, Real.exp_zero, sub_self] at h
  have : {ω | ¬ 0 < τ n ω} = {ω | τ n ω ≤ 0} := by ext; simp
  rw [this]
  exact (measureReal_eq_zero_iff).1 h

lemma ae_mark (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1) :
    ∀ᵐ ω ∂Q, ∃ j : ℕ, ξ 0 ω = (j : ℝ) - 1 := by
  have hS : MeasurableSet {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} := by
    have : {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = Set.range (fun k : ℕ => (k : ℝ) - 1) := by
      ext x; simp [eq_comm]
    rw [this]; exact (Set.countable_range _).measurableSet
  have h1 : ∀ᵐ x ∂jumpLaw, ∃ k : ℕ, x = (k : ℝ) - 1 := by
    rw [ae_iff]
    have : {a : ℝ | ¬∃ k : ℕ, a = (k : ℝ) - 1} = {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1}ᶜ := rfl
    rw [this, prob_compl_eq_zero_iff hS]; exact hSupport
  exact ((hD.law_mark 0).ae_iff (p := fun x => ∃ k : ℕ, x = (k : ℝ) - 1) (measurable_mem.2 hS)).2 h1

lemma estimate (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (z k : ℕ) (hz : 1 ≤ z) (t : ℝ≥0) :
    |Q.real {ω | (stoppedIntegerCompoundPoisson z τ ξ t ω).toNat = k} -
      ((if k = z then 1 else 0) * Real.exp (-((rate : ℝ) * t)) +
        (if z ≤ k + 1 then jumpLaw.real {((k + 1 - z : ℕ) : ℝ) - 1} else 0) *
          (1 - Real.exp (-((rate : ℝ) * t))))| ≤
      (1 - Real.exp (-((rate : ℝ) * t))) ^ 2 := by
  have ht0 : (0 : ℝ) ≤ t := t.2
  set A := {ω | (stoppedIntegerCompoundPoisson z τ ξ t ω).toNat = k} with hA
  set c : ℝ := ((k + 1 - z : ℕ) : ℝ) - 1 with hc
  set G := {ω | 0 < τ 0 ω ∧ 0 < τ 1 ω ∧ ∃ j : ℕ, ξ 0 ω = (j : ℝ) - 1} with hG_def
  have hGae : ∀ᵐ ω ∂Q, ω ∈ G :=
    (ae_pos Q hRate hD 0).and ((ae_pos Q hRate hD 1).and (ae_mark Q hRate hD hSupport))
  have hGc : Q.real Gᶜ = 0 := by
    have h : Q Gᶜ = 0 := mem_ae_iff.1 hGae
    simp [Measure.real, h]
  set E0 := {ω | (t : ℝ) < τ 0 ω}
  set T := {ω | τ 0 ω ≤ (t : ℝ)}
  set Bm := {ω | ξ 0 ω = c}
  set E2 := {ω | τ 0 ω ≤ (t : ℝ)} ∩ {ω | τ 1 ω ≤ (t : ℝ)} with hE2
  set F1 : Set Ω := if k = z then E0 else ∅ with hF1
  set F2 : Set Ω := if z ≤ k + 1 then T ∩ Bm else ∅ with hF2
  have mT : MeasurableSet T := hD.measurable_interarrival 0 measurableSet_Iic
  have mB : MeasurableSet Bm := hD.measurable_mark 0 (measurableSet_singleton c)
  have mE2 : MeasurableSet E2 :=
    mT.inter (hD.measurable_interarrival 1 measurableSet_Iic)
  have mF2 : MeasurableSet F2 := by rw [hF2]; split_ifs; exacts [mT.inter mB, MeasurableSet.empty]
  have pF1 : Q.real F1 = (if k = z then 1 else 0) * Real.exp (-((rate : ℝ) * t)) := by
    rw [hF1]; split_ifs
    · rw [one_mul]; exact prob_gt Q hRate hD 0 ht0
    · simp
  have pF2 : Q.real F2 = (if z ≤ k + 1 then jumpLaw.real {c} else 0) *
      (1 - Real.exp (-((rate : ℝ) * t))) := by
    rw [hF2]; split_ifs
    · rw [prob_mark Q hRate hD c ht0, mul_comm]
    · simp
  have pE2 : Q.real E2 = (1 - Real.exp (-((rate : ℝ) * t))) ^ 2 := prob_pair Q hRate hD ht0
  -- upper bound
  have hup : A ⊆ F1 ∪ F2 ∪ E2 ∪ Gᶜ := by
    intro ω hω
    by_cases hωG : ω ∈ G
    swap; · exact Or.inr hωG
    obtain ⟨h0, h1, j, hj⟩ := hωG
    have hω' : (stoppedIntegerCompoundPoisson z τ ξ t ω).toNat = k := hω
    rcases lt_or_ge (t : ℝ) (τ 0 ω) with ht | ht
    · rw [P0 z hz τ ξ ω t ht] at hω'
      left; left; left
      rw [hF1, if_pos hω'.symm]; exact ht
    · rcases lt_or_ge (t : ℝ) (τ 0 ω + τ 1 ω) with ht2 | ht2
      · rw [P1 z hz τ ξ ω h0 h1 t j ht ht2 hj] at hω'
        left; left; right
        have hzk : z ≤ k + 1 := by omega
        have hjk : j = k + 1 - z := by omega
        rw [hF2, if_pos hzk]
        refine ⟨ht, ?_⟩
        show ξ 0 ω = c
        rw [hj, hc, hjk]
      · left; right
        exact ⟨ht, by show τ 1 ω ≤ (t : ℝ); linarith⟩
  have hupR : Q.real A ≤ Q.real F1 + Q.real F2 + Q.real E2 := by
    calc Q.real A ≤ Q.real (F1 ∪ F2 ∪ E2 ∪ Gᶜ) := measureReal_mono hup
      _ ≤ Q.real (F1 ∪ F2 ∪ E2) + Q.real Gᶜ := measureReal_union_le _ _
      _ ≤ Q.real (F1 ∪ F2) + Q.real E2 + 0 := by
          rw [hGc]; gcongr; exact measureReal_union_le _ _
      _ ≤ Q.real F1 + Q.real F2 + Q.real E2 := by
          rw [add_zero]; gcongr; exact measureReal_union_le _ _
  -- lower bound
  have hlow : F1 ∪ (F2 \ E2) ⊆ A ∪ Gᶜ := by
    intro ω hω
    by_cases hωG : ω ∈ G
    swap; · exact Or.inr hωG
    obtain ⟨h0, h1, j, hj⟩ := hωG
    left
    show (stoppedIntegerCompoundPoisson z τ ξ t ω).toNat = k
    rcases hω with hω | ⟨hω2, hωE⟩
    · rw [hF1] at hω
      split_ifs at hω with hkz
      · rw [P0 z hz τ ξ ω t hω, hkz]
      · exact absurd hω (Set.notMem_empty ω)
    · rw [hF2] at hω2
      split_ifs at hω2 with hzk
      · obtain ⟨hT, hB⟩ := hω2
        have hT' : τ 0 ω ≤ (t : ℝ) := hT
        have hB' : ξ 0 ω = ((k + 1 - z : ℕ) : ℝ) - 1 := hB
        have h1t : (t : ℝ) < τ 1 ω := by
          by_contra hcon
          exact hωE ⟨hT', not_lt.1 hcon⟩
        rw [P1 z hz τ ξ ω h0 h1 t (k + 1 - z) hT' (by linarith) hB']
        omega
      · exact absurd hω2 (Set.notMem_empty ω)
  have hdisj : Disjoint F1 (F2 \ E2) := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    rw [hF1] at h1; rw [hF2] at h2
    split_ifs at h1 h2
    all_goals first
      | exact (Set.notMem_empty ω) h1
      | exact (Set.notMem_empty ω) h2.1
      | exact absurd (show τ 0 ω ≤ (t : ℝ) from h2.1.1) (not_le.2 (show (t : ℝ) < τ 0 ω from h1))
  have hlowR : Q.real F1 + (Q.real F2 - Q.real E2) ≤ Q.real A := by
    calc Q.real F1 + (Q.real F2 - Q.real E2) ≤ Q.real F1 + Q.real (F2 \ E2) := by
          gcongr; exact le_measureReal_sdiff
      _ = Q.real (F1 ∪ (F2 \ E2)) := (measureReal_union hdisj (mF2.diff mE2)).symm
      _ ≤ Q.real (A ∪ Gᶜ) := measureReal_mono hlow
      _ ≤ Q.real A + Q.real Gᶜ := measureReal_union_le _ _
      _ = Q.real A := by rw [hGc, add_zero]
  rw [pF1, pF2, pE2] at *
  rw [abs_le]
  constructor <;> linarith

end Prob

end StoppedCPGen

theorem solution
    {Ω' : Type*} [MeasurableSpace Ω']
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ z k : ℕ,
      HasDerivWithinAt
        (fun t : ℝ => (Q {ω |
          (stoppedIntegerCompoundPoisson z arrival marks (Real.toNNReal t) ω).toNat = k}).toReal)
        (if k = z then (if z = 0 then 0 else -(rate : ℝ))
         else if 1 ≤ z ∧ z ≤ k + 1 then
           (rate : ℝ) * (offspring (k + 1 - z)).toReal
         else 0)
        (Set.Ici 0) 0  := by
  intro z k
  have hr : (0 : ℝ) ≤ rate := rate.2
  rcases Nat.eq_zero_or_pos z with hz | hz
  · -- z = 0: the stopped process is a.s. identically 0
    subst hz
    have hconst : ∀ t : ℝ, (Q {ω |
        (stoppedIntegerCompoundPoisson 0 arrival marks (Real.toNNReal t) ω).toNat = k}).toReal =
        if k = 0 then 1 else 0 := by
      intro t
      have heq : {ω | (stoppedIntegerCompoundPoisson 0 arrival marks (Real.toNNReal t) ω).toNat = k}
          =ᵐ[Q] {ω : Ω' | 0 = k} := by
        refine Filter.eventuallyEq_set.2 ?_
        filter_upwards [StoppedCPGen.ae_pos Q hRate hDriver 0] with ω hω
        simp [StoppedCPGen.Pzero arrival marks ω hω]
      rw [measure_congr heq]
      by_cases hk : k = 0
      · subst hk; simp
      · simp [Ne.symm hk, hk]
    have : (fun t : ℝ => (Q {ω |
        (stoppedIntegerCompoundPoisson 0 arrival marks (Real.toNNReal t) ω).toNat = k}).toReal) =
        fun _ => if k = 0 then (1 : ℝ) else 0 := funext hconst
    rw [this]
    refine (hasDerivWithinAt_const (0 : ℝ) (Set.Ici (0 : ℝ)) (if k = 0 then (1 : ℝ) else 0)).congr_deriv ?_
    split_ifs <;> simp_all
  · set δ : ℝ := if k = z then 1 else 0 with hδ
    set c : ℝ := ((k + 1 - z : ℕ) : ℝ) - 1 with hc
    set q : ℝ := if z ≤ k + 1 then jumpLaw.real {c} else 0 with hq
    set F : ℝ → ℝ := fun t => (Q {ω |
        (stoppedIntegerCompoundPoisson z arrival marks (Real.toNNReal t) ω).toNat = k}).toReal
      with hF
    set M : ℝ → ℝ := fun t =>
      δ * Real.exp (-((rate : ℝ) * t)) + q * (1 - Real.exp (-((rate : ℝ) * t))) with hM_def
    have he : HasDerivAt (fun t : ℝ => Real.exp (-((rate : ℝ) * t))) (-(rate : ℝ)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (rate : ℝ)).neg).exp
      simpa using this
    have hM : HasDerivAt M (δ * (-(rate : ℝ)) + q * (-(-(rate : ℝ)))) 0 :=
      (he.const_mul δ).add ((he.const_sub 1).const_mul q)
    have hbound : ∀ t : ℝ, 0 ≤ t → |F t - M t| ≤ ((rate : ℝ) * t) ^ 2 := by
      intro t ht
      have h := StoppedCPGen.estimate Q hRate hDriver hSupport z k hz (Real.toNNReal t)
      rw [Real.coe_toNNReal t ht] at h
      refine h.trans ?_
      have hx : 0 ≤ (rate : ℝ) * t := mul_nonneg hr ht
      have h1 : 0 ≤ 1 - Real.exp (-((rate : ℝ) * t)) := by
        rw [sub_nonneg]; exact Real.exp_le_one_iff.2 (neg_nonpos.2 hx)
      have h2 : 1 - Real.exp (-((rate : ℝ) * t)) ≤ (rate : ℝ) * t := by
        have := Real.add_one_le_exp (-((rate : ℝ) * t)); linarith
      exact pow_le_pow_left₀ h1 h2 2
    have herr0 : F 0 - M 0 = 0 := by
      have := hbound 0 le_rfl
      exact abs_nonpos_iff.1 (by simpa using this)
    have herr : HasDerivWithinAt (fun t => F t - M t) 0 (Set.Ici 0) 0 := by
      rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
      have hlim : Tendsto (fun t : ℝ => (rate : ℝ) ^ 2 * t) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun t : ℝ => (rate : ℝ) ^ 2 * t) (𝓝 0) (𝓝 ((rate : ℝ) ^ 2 * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [slope_def_field, herr0, sub_zero, sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos ht,
        div_le_iff₀ ht]
      have := hbound t ht.le
      nlinarith [this]
    have hsum := hM.hasDerivWithinAt.add herr
    have hfun : (M + fun t => F t - M t) = F := by funext t; simp only [Pi.add_apply]; ring
    rw [hfun] at hsum
    refine hsum.congr_deriv ?_
    -- identify the derivative with the generator entry
    have hz0 : z ≠ 0 := by omega
    by_cases hkz : k = z
    · subst hkz
      have hq0 : q = 0 := by
        rw [hq, if_pos (by omega), hc, show k + 1 - k = 1 by omega, Measure.real]
        have := hJumpMass 1
        simp only [Nat.cast_one] at this ⊢
        rw [this, hNoNullJumps]; simp
      rw [hδ, if_pos rfl, hq0]
      simp [hz0]
    · rw [hδ, if_neg hkz, if_neg hkz]
      by_cases hzk : z ≤ k + 1
      · rw [if_pos ⟨hz, hzk⟩, hq, if_pos hzk, hc, Measure.real, hJumpMass (k + 1 - z)]
        ring
      · rw [if_neg (fun h => hzk h.2), hq, if_neg hzk]
        ring
