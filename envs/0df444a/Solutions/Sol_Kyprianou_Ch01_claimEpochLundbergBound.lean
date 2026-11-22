-- Prove2me | solution 1 for Kyprianou.Ch01.claimEpochLundbergBound
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T09:29:01.651553+00:00
-- url     : https://prove2.me/submissions/9af568e5-1e4a-4547-86c6-16b2febc689d

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_finiteGridOptionalStoppingEventwisePublic
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (premium : ℝ) (nu : ℝ) (hnu : 0 ≤ nu)
    (hint : Integrable
      (fun ω => Real.exp (-nu * (premium * arrival 0 ω - claims 0 ω))) P)
    (hroot : (∫ ω, Real.exp
      (-nu * (premium * arrival 0 ω - claims 0 ω)) ∂P) = 1)
    (x : ℝ) :
    P {ω | ∃ n : ℕ, x + ∑ i ∈ Finset.range (n + 1),
        (premium * arrival i ω - claims i ω) < 0} ≤
      ENNReal.ofReal (Real.exp (-nu * x)) := by
  classical
  -- σ-algebras of past and future blocks
  set f : ℕ ⊕ ℕ → Ω → ℝ := Sum.elim arrival claims with hf
  set idx : ℕ ⊕ ℕ → ℕ := Sum.elim id id with hidx
  set m : ℕ ⊕ ℕ → MeasurableSpace Ω := fun i => MeasurableSpace.comap (f i) inferInstance
    with hm
  have hmeas_f : ∀ i, Measurable (f i) := by
    rintro (i | i)
    exacts [hd.measurable_interarrival i, hd.measurable_mark i]
  have hm_le : ∀ i, m i ≤ ‹MeasurableSpace Ω› := fun i => (hmeas_f i).comap_le
  have hiInd : iIndep m P := (iIndepFun_iff_iIndep _ f P).mp hd.indep
  set Fp : ℕ → MeasurableSpace Ω := fun n => ⨆ i ∈ {i | idx i ≤ n}, m i with hFp
  set Gf : ℕ → MeasurableSpace Ω := fun n => ⨆ i ∈ {i | n < idx i}, m i with hGf
  have hInd : ∀ n, Indep (Fp n) (Gf n) P := fun n =>
    indep_iSup_of_disjoint hm_le hiInd (by
      rw [Set.disjoint_left]
      intro i h1 h2
      simp only [Set.mem_ofPred_eq] at h1 h2
      omega)
  have hFp_le : ∀ n, Fp n ≤ ‹MeasurableSpace Ω› := fun n => iSup₂_le (fun i _ => hm_le i)
  have hmF : ∀ n i, idx i ≤ n → Measurable[Fp n] (f i) := fun n i hi =>
    Measurable.of_comap_le (le_iSup₂ (f := fun j (_ : j ∈ {j | idx j ≤ n}) => m j) i hi)
  have hmG : ∀ n i, n < idx i → Measurable[Gf n] (f i) := fun n i hi =>
    Measurable.of_comap_le (le_iSup₂ (f := fun j (_ : j ∈ {j | n < idx j}) => m j) i hi)
  -- the walk
  set Z : ℕ → Ω → ℝ := fun i ω => premium * arrival i ω - claims i ω with hZ
  set W : ℕ → Ω → ℝ := fun n ω => x + ∑ i ∈ Finset.range (n + 1), Z i ω with hW
  set E : ℕ → Ω → ℝ := fun i ω => Real.exp (-nu * Z i ω) with hE
  set L : ℕ → Ω → ℝ := fun n ω => Real.exp (-nu * W n ω) with hL
  have hZF : ∀ n i, i ≤ n → Measurable[Fp n] (Z i) := fun n i hi =>
    (measurable_const.mul (hmF n (Sum.inl i) hi)).sub (hmF n (Sum.inr i) hi)
  have hWF : ∀ n k, k ≤ n → Measurable[Fp n] (W k) := fun n k hk =>
    measurable_const.add (Finset.measurable_sum _ (fun i hi => hZF n i (by
      simp only [Finset.mem_range] at hi; omega)))
  have hLF : ∀ n, Measurable[Fp n] (L n) := fun n =>
    Real.measurable_exp.comp (measurable_const.mul (hWF n n le_rfl))
  have hEG : ∀ n, Measurable[Gf n] (E (n + 1)) := fun n =>
    Real.measurable_exp.comp (measurable_const.mul
      ((measurable_const.mul (hmG n (Sum.inl (n + 1)) (by simp [idx]))).sub
        (hmG n (Sum.inr (n + 1)) (by simp [idx]))))
  have hIndFG : ∀ n (X Y : Ω → ℝ), Measurable[Fp n] X → Measurable[Gf n] Y →
      IndepFun X Y P := fun n X Y hX hY =>
    (IndepFun_iff_Indep X Y P).mpr
      (indep_of_indep_of_le_left (indep_of_indep_of_le_right (hInd n) hY.comap_le) hX.comap_le)
  -- identical distribution of the increments
  have hpair : ∀ k, P.map (fun ω => (arrival k ω, claims k ω)) = (expMeasure (rate : ℝ)).prod F := by
    intro k
    have hind : IndepFun (arrival k) (claims k) P := by
      have := hd.indep.indepFun (i := Sum.inl k) (j := Sum.inr k) (by simp)
      simpa using this
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hd.measurable_interarrival k).aemeasurable
      (hd.measurable_mark k).aemeasurable).mp hind, (hd.law_interarrival k).map_eq,
      (hd.law_mark k).map_eq]
  have hID : ∀ k, IdentDistrib (E k) (E 0) P P := by
    intro k
    have h : IdentDistrib (fun ω => (arrival k ω, claims k ω))
        (fun ω => (arrival 0 ω, claims 0 ω)) P P :=
      ⟨((hd.measurable_interarrival k).prodMk (hd.measurable_mark k)).aemeasurable,
        ((hd.measurable_interarrival 0).prodMk (hd.measurable_mark 0)).aemeasurable,
        by rw [hpair k, hpair 0]⟩
    exact h.comp (u := fun p : ℝ × ℝ => Real.exp (-nu * (premium * p.1 - p.2))) (by fun_prop)
  have hEint : ∀ k, Integrable (E k) P := fun k => (hID k).integrable_iff.mpr hint
  have hEone : ∀ k, ∫ ω, E k ω ∂P = 1 := fun k => (hID k).integral_eq.trans hroot
  -- the exponential martingale
  have hLsucc : ∀ n ω, L (n + 1) ω = L n ω * E (n + 1) ω := by
    intro n ω
    simp only [hL, hE, hW, Finset.sum_range_succ (n := n + 1), ← Real.exp_add]
    ring_nf
  have hL0 : ∀ ω, L 0 ω = Real.exp (-nu * x) * E 0 ω := by
    intro ω
    simp only [hL, hE, hW, zero_add, Finset.sum_range_one, ← Real.exp_add]
    ring_nf
  have hLint : ∀ n, Integrable (L n) P := by
    intro n
    induction n with
    | zero =>
      have := (hEint 0).const_mul (Real.exp (-nu * x))
      exact this.congr (ae_of_all _ (fun ω => (hL0 ω).symm))
    | succ n ih =>
      have := (hIndFG n _ _ (hLF n) (hEG n)).integrable_mul ih (hEint (n + 1))
      exact this.congr (ae_of_all _ (fun ω => (hLsucc n ω).symm))
  have hMart : ∀ (n : ℕ) (A : Set Ω), MeasurableSet[Fp n] A →
      (∫ ω in A, L (n + 1) ω ∂P) = (∫ ω in A, L n ω ∂P) := by
    intro n A hA
    have hA' : MeasurableSet A := hFp_le n A hA
    rw [← integral_indicator hA', ← integral_indicator hA']
    have h1 : A.indicator (L (n + 1)) = A.indicator (L n) * E (n + 1) := by
      funext ω
      by_cases hω : ω ∈ A
      · simp [indicator_of_mem hω, hLsucc]
      · simp [indicator_of_notMem hω]
    have hX : Measurable[Fp n] (A.indicator (L n)) := (hLF n).indicator hA
    rw [h1, (hIndFG n _ _ hX (hEG n)).integral_mul_eq_mul_integral
      ((hX.mono (hFp_le n) le_rfl).aestronglyMeasurable) (hEint (n + 1)).aestronglyMeasurable,
      hEone, mul_one]
  have hL0int : ∫ ω, L 0 ω ∂P = Real.exp (-nu * x) := by
    simp only [hL0]
    rw [integral_const_mul, hEone, mul_one]
  -- finite-horizon bound via optional stopping
  set R : ℕ → Set Ω := fun N => {ω | ∃ n ≤ N, W n ω < 0} with hR
  have hRmeas : ∀ N, MeasurableSet (R N) := by
    intro N
    have : R N = ⋃ n, ⋃ (_ : n ≤ N), {ω | W n ω < 0} := by
      ext ω; simp [hR]
    rw [this]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun hn =>
      measurableSet_lt ((hWF n n le_rfl).mono (hFp_le n) le_rfl) measurable_const
  have hfin : ∀ N, P (R N) ≤ ENNReal.ofReal (Real.exp (-nu * x)) := by
    intro N
    let τ : Ω → ℕ := fun ω =>
      if h : ∃ n, n ≤ N ∧ W n ω < 0 then Nat.find h else N
    have hBound : ∀ ω, τ ω ≤ N := by
      intro ω
      by_cases h : ∃ n, n ≤ N ∧ W n ω < 0
      · simp only [τ, dif_pos h]; exact (Nat.find_spec h).1
      · simp only [τ, dif_neg h]; exact le_rfl
    have hStop : ∀ n, n < N → MeasurableSet[Fp n] {ω | n < τ ω} := by
      intro n hn
      have : {ω | n < τ ω} = ⋂ k ∈ Finset.range (n + 1), {ω | 0 ≤ W k ω} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
        by_cases h : ∃ n, n ≤ N ∧ W n ω < 0
        · simp only [τ, dif_pos h, Nat.lt_find_iff]
          constructor
          · intro H k hk
            have := H k (by omega)
            push Not at this
            exact this (by omega)
          · intro H k hk hk2
            linarith [H k (by omega), hk2.2]
        · simp only [τ, dif_neg h, hn, true_iff]
          intro k hk
          push Not at h
          exact h k (by omega)
      rw [this]
      exact Finset.measurableSet_biInter _ fun k hk =>
        measurableSet_le measurable_const (hWF n k (by simp at hk; omega))
    obtain ⟨hτint, hτeq⟩ := Kyprianou.Ch01.finiteGridOptionalStoppingEventwisePublic P Fp L τ N
      hFp_le hBound hLint hStop hMart
    have hpt : ∀ ω, (R N).indicator (fun _ => (1 : ℝ)) ω ≤ L (τ ω) ω := by
      intro ω
      by_cases h : ∃ n, n ≤ N ∧ W n ω < 0
      · have hmem : ω ∈ R N := by obtain ⟨n, hn, hw⟩ := h; exact ⟨n, hn, hw⟩
        rw [indicator_of_mem hmem]
        have hτω : τ ω = Nat.find h := by simp only [τ, dif_pos h]
        have hw : W (τ ω) ω < 0 := by rw [hτω]; exact (Nat.find_spec h).2
        exact Real.one_le_exp (by nlinarith)
      · have hmem : ω ∉ R N := by
          rintro ⟨n, hn, hw⟩; exact h ⟨n, hn, hw⟩
        rw [indicator_of_notMem hmem]
        exact (Real.exp_pos _).le
    have hle : (P (R N)).toReal ≤ Real.exp (-nu * x) := by
      have := integral_mono ((integrable_const (1 : ℝ)).indicator (hRmeas N)) hτint hpt
      rw [integral_indicator_const _ (hRmeas N), hτeq, hL0int] at this
      simpa [measureReal_def] using this
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr hle
  have hU : {ω | ∃ n : ℕ, x + ∑ i ∈ Finset.range (n + 1),
      (premium * arrival i ω - claims i ω) < 0} = ⋃ N, R N := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hR, hW, hZ]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, n, le_rfl, hn⟩
    · rintro ⟨N, n, -, hn⟩; exact ⟨n, hn⟩
  have hmono : Monotone R := by
    intro a b hab ω ⟨n, hn, hw⟩
    exact ⟨n, hn.trans hab, hw⟩
  rw [hU, hmono.measure_iUnion]
  exact iSup_le hfin
