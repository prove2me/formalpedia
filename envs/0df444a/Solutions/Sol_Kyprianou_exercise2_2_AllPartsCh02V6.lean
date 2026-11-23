-- Prove2me | solution 1 for Kyprianou.exercise2_2_AllPartsCh02V6
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T12:07:37.514512+00:00
-- url     : https://prove2.me/submissions/82e3eeec-d2fe-476a-941a-8ac6ec176fdf

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Complex Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace KyprianouEx22Helpers

private def closedSimplex (n : ℕ) (t : ℝ≥0) : Set (Fin n → ℝ) :=
  {v : Fin n → ℝ | (∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)) ∧ Monotone v}

private def openSimplex (n : ℕ) (t : ℝ≥0) : Set (Fin n → ℝ) :=
  {v : Fin n → ℝ | (∀ i, 0 < v i ∧ v i < (t : ℝ)) ∧ StrictMono v}

private def diagSet (n : ℕ) : Set (Fin n → ℝ) :=
  ⋃ (i : Fin n) (j : Fin n) (_ : i ≠ j), {v : Fin n → ℝ | v i = v j}

private lemma isOpen_openSimplex (n : ℕ) (t : ℝ≥0) : IsOpen (openSimplex n t) := by
  have h1 : IsOpen {v : Fin n → ℝ | ∀ i, 0 < v i ∧ v i < (t : ℝ)} := by
    have : {v : Fin n → ℝ | ∀ i, 0 < v i ∧ v i < (t : ℝ)} =
        ⋂ i : Fin n, ({v : Fin n → ℝ | 0 < v i} ∩ {v : Fin n → ℝ | v i < (t : ℝ)}) := by
      ext v; simp
    rw [this]
    refine isOpen_iInter_of_finite fun i => IsOpen.inter ?_ ?_
    · exact isOpen_lt continuous_const (continuous_apply i)
    · exact isOpen_lt (continuous_apply i) continuous_const
  have h2 : IsOpen {v : Fin n → ℝ | StrictMono v} := by
    have : {v : Fin n → ℝ | StrictMono v} =
        ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), {v : Fin n → ℝ | v i < v j} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_iInter, StrictMono]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j)
  exact h1.inter h2

private lemma measurableSet_closedSimplex (n : ℕ) (t : ℝ≥0) : MeasurableSet (closedSimplex n t) := by
  have h1 : MeasurableSet {v : Fin n → ℝ | ∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)} := by
    have : {v : Fin n → ℝ | ∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)} =
        ⋂ i : Fin n, ({v : Fin n → ℝ | 0 ≤ v i} ∩ {v : Fin n → ℝ | v i ≤ (t : ℝ)}) := by
      ext v; simp
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.inter ?_ ?_
    · exact measurableSet_le measurable_const (measurable_pi_apply i)
    · exact measurableSet_le (measurable_pi_apply i) measurable_const
  have h2 : MeasurableSet {v : Fin n → ℝ | Monotone v} := by
    have : {v : Fin n → ℝ | Monotone v} =
        ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i ≤ j), {v : Fin n → ℝ | v i ≤ v j} := by
      ext v; simp [Monotone]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
  exact h1.inter h2

private lemma volume_coord_eq_const_zero {n : ℕ} (i : Fin n) (c : ℝ) :
    volume {v : Fin n → ℝ | v i = c} = 0 := by
  let S : Submodule ℝ (Fin n → ℝ) :=
    { carrier := {v : Fin n → ℝ | v i = 0}
      zero_mem' := rfl
      add_mem' := fun {a b} ha hb => show a i + b i = 0 by rw [ha, hb, add_zero]
      smul_mem' := fun r {a} ha => show r * a i = 0 by rw [ha, mul_zero] }
  have hSne : S ≠ ⊤ := by
    intro htop
    have hmem : (fun _ : Fin n => (1 : ℝ)) ∈ S := by rw [htop]; trivial
    exact one_ne_zero hmem
  have hS0 : volume (S : Set (Fin n → ℝ)) = 0 := Measure.addHaar_submodule volume S hSne
  have htrans : {v : Fin n → ℝ | v i = c} = (fun v => v + fun _ => -c) ⁻¹' (S : Set (Fin n → ℝ)) := by
    ext v
    simp only [Set.mem_preimage, SetLike.mem_coe]
    show v i = c ↔ v i + -c = 0
    constructor <;> intro h <;> linarith
  rw [htrans, measure_preimage_add_right, hS0]

private lemma volume_eq_coord_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    volume {v : Fin n → ℝ | v i = v j} = 0 := by
  let S : Submodule ℝ (Fin n → ℝ) :=
    { carrier := {v : Fin n → ℝ | v i = v j}
      zero_mem' := rfl
      add_mem' := fun {a b} ha hb => show a i + b i = a j + b j by rw [ha, hb]
      smul_mem' := fun r {a} ha => show r * a i = r * a j by rw [ha] }
  have hSne : S ≠ ⊤ := by
    intro htop
    let e : Fin n → ℝ := fun k => if k = i then 1 else 0
    have hmem : e ∈ S := by rw [htop]; trivial
    have h1 : e i = e j := hmem
    simp [e, hij.symm] at h1
  exact Measure.addHaar_submodule volume S hSne

private lemma volume_diagSet_zero (n : ℕ) : volume (diagSet n) = 0 := by
  unfold diagSet
  refine measure_iUnion_null fun i => measure_iUnion_null fun j =>
    measure_iUnion_null fun hij => volume_eq_coord_zero hij

private lemma volume_closedSimplex_diff_openSimplex_zero (n : ℕ) (t : ℝ≥0) :
    volume (closedSimplex n t \ openSimplex n t) = 0 := by
  have hsub : closedSimplex n t \ openSimplex n t ⊆
      (⋃ i : Fin n, {v : Fin n → ℝ | v i = 0}) ∪
      (⋃ i : Fin n, {v : Fin n → ℝ | v i = (t : ℝ)}) ∪ diagSet n := by
    intro v ⟨⟨hbd, hmono⟩, hnot⟩
    by_contra hmem
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists] at hmem
    obtain ⟨⟨h0, ht⟩, hdiag⟩ := hmem
    apply hnot
    refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
    · exact lt_of_le_of_ne (hbd i).1 (Ne.symm (h0 i))
    · exact lt_of_le_of_ne (hbd i).2 (ht i)
    · refine lt_of_le_of_ne (hmono (le_of_lt hij)) ?_
      intro heq
      apply hdiag
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨ne_of_lt hij, heq⟩⟩⟩
  refine measure_mono_null hsub (measure_union_null (measure_union_null ?_ ?_) (volume_diagSet_zero n))
  · exact measure_iUnion_null fun i => volume_coord_eq_const_zero i 0
  · exact measure_iUnion_null fun i => volume_coord_eq_const_zero i (t : ℝ)

private lemma poissonMeasure_singleton_eq (r : ℝ≥0) (k : ℕ) :
    ProbabilityTheory.poissonMeasure r {k} =
      ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ)) := by
  rw [← poissonMeasure_real_singleton r k, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

private lemma poissonMeasure_ge_two_le (r : ℝ≥0) :
    ProbabilityTheory.poissonMeasure r {k : ℕ | 2 ≤ k} ≤ ENNReal.ofReal ((r : ℝ) ^ 2) := by
  have huniv : ({k : ℕ | 2 ≤ k} : Set ℕ) = ({0, 1} : Set ℕ)ᶜ := by
    ext k; simp; omega
  rw [huniv, prob_compl_eq_one_sub (by measurability)]
  have hdisj : Disjoint ({0} : Set ℕ) {1} := by simp
  have hpair : ({0, 1} : Set ℕ) = {0} ∪ {1} := rfl
  rw [hpair, measure_union hdisj (measurableSet_singleton 1),
    poissonMeasure_singleton_eq r 0, poissonMeasure_singleton_eq r 1]
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
    Nat.factorial_one]
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (mul_nonneg (Real.exp_nonneg _) r.coe_nonneg)]
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ← ENNReal.ofReal_sub _ (add_nonneg (Real.exp_nonneg _) (mul_nonneg (Real.exp_nonneg _) r.coe_nonneg))]
  apply ENNReal.ofReal_le_ofReal
  have hexp : 1 - (r : ℝ) ≤ Real.exp (-(r : ℝ)) := by
    have h := Real.add_one_le_exp (-(r : ℝ))
    linarith
  have hmul : (1 + (r : ℝ)) * (1 - (r : ℝ)) ≤ (1 + (r : ℝ)) * Real.exp (-(r : ℝ)) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  nlinarith

private lemma aemeasurable_N_of_law
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (N : ℝ≥0 → Ω → ℕ)
    (hNlaw : ∀ t, P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (t : ℝ≥0) : AEMeasurable (N t) P := by
  by_contra hnot
  have h0 : P.map (N t) = 0 := Measure.map_of_not_aemeasurable hnot
  have h1 : (ProbabilityTheory.poissonMeasure (rate * t)) Set.univ = 1 := measure_univ
  rw [← hNlaw t, h0] at h1
  simp at h1

private lemma N_zero_eq_zero
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (N : ℝ≥0 → Ω → ℕ)
    (hNlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (N t ω : ℝ)) P)
    (ω : Ω) : N 0 ω = 0 := by
  have h0 : (N 0 ω : ℝ) = 0 := congrFun hNlevy.start_zero ω
  exact Nat.cast_eq_zero.mp h0

private lemma increment_prob_eq_poisson
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (N : ℝ≥0 → Ω → ℕ)
    (hNlaw : ∀ t, P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (hNlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (N t ω : ℝ)) P)
    {u v : ℝ≥0} (huv : u ≤ v) (k : ℕ) :
    P {ω | increment (fun s ω => (N s ω : ℝ)) u v ω = (k : ℝ)} =
      ProbabilityTheory.poissonMeasure (rate * (v - u)) {k} := by
  have hid := hNlevy.stationary_increments u (v - u)
  rw [add_tsub_cancel_of_le huv] at hid
  have hpre : {ω | increment (fun s ω => (N s ω : ℝ)) u v ω = (k : ℝ)} =
      (increment (fun s ω => (N s ω : ℝ)) u v) ⁻¹' {(k : ℝ)} := rfl
  rw [hpre, hid.measure_mem_eq (measurableSet_singleton (k : ℝ))]
  have h0 : (increment (fun s ω => (N s ω : ℝ)) 0 (v - u)) ⁻¹' {(k : ℝ)} =
      (N (v - u)) ⁻¹' {k} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, increment, N_zero_eq_zero P N hNlevy ω,
      Nat.cast_zero, sub_zero, Nat.cast_inj]
  rw [h0, ← Measure.map_apply_of_aemeasurable (aemeasurable_N_of_law P rate N hNlaw (v - u))
    (measurableSet_singleton k), hNlaw (v - u)]

private lemma increment_ge_two_prob_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (N : ℝ≥0 → Ω → ℕ)
    (hNlaw : ∀ t, P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (hNlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (N t ω : ℝ)) P)
    {u v : ℝ≥0} (huv : u ≤ v) :
    P {ω | (2 : ℝ) ≤ increment (fun s ω => (N s ω : ℝ)) u v ω} ≤
      ENNReal.ofReal ((((rate * (v - u) : ℝ≥0) : ℝ)) ^ 2) := by
  have hid := hNlevy.stationary_increments u (v - u)
  rw [add_tsub_cancel_of_le huv] at hid
  have hpre : {ω | (2 : ℝ) ≤ increment (fun s ω => (N s ω : ℝ)) u v ω} =
      (increment (fun s ω => (N s ω : ℝ)) u v) ⁻¹' Set.Ici (2 : ℝ) := rfl
  rw [hpre, hid.measure_mem_eq measurableSet_Ici]
  have h0 : (increment (fun s ω => (N s ω : ℝ)) 0 (v - u)) ⁻¹' Set.Ici (2 : ℝ) =
      (N (v - u)) ⁻¹' {k : ℕ | 2 ≤ k} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_setOf_eq, increment,
      N_zero_eq_zero P N hNlevy ω, Nat.cast_zero, sub_zero]
    exact_mod_cast Iff.rfl
  rw [h0, ← Measure.map_apply_of_aemeasurable (aemeasurable_N_of_law P rate N hNlaw (v - u))
    MeasurableSet.of_discrete, hNlaw (v - u)]
  exact poissonMeasure_ge_two_le (rate * (v - u))

private lemma increment_ne_zero_prob_eq
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (N : ℝ≥0 → Ω → ℕ)
    (hNlaw : ∀ t, P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (hNlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (N t ω : ℝ)) P)
    {u v : ℝ≥0} (huv : u ≤ v) :
    P {ω | increment (fun s ω => (N s ω : ℝ)) u v ω ≠ 0} =
      1 - ENNReal.ofReal (Real.exp (-((rate * (v - u) : ℝ≥0) : ℝ))) := by
  have hid := hNlevy.stationary_increments u (v - u)
  rw [add_tsub_cancel_of_le huv] at hid
  have hpre : {ω | increment (fun s ω => (N s ω : ℝ)) u v ω ≠ 0} =
      (increment (fun s ω => (N s ω : ℝ)) u v) ⁻¹' ({0}ᶜ : Set ℝ) := rfl
  rw [hpre, hid.measure_mem_eq (measurableSet_singleton (0 : ℝ)).compl]
  have h0 : (increment (fun s ω => (N s ω : ℝ)) 0 (v - u)) ⁻¹' ({0}ᶜ : Set ℝ) =
      (N (v - u)) ⁻¹' ({0}ᶜ : Set ℕ) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, increment,
      N_zero_eq_zero P N hNlevy ω, Nat.cast_zero, sub_zero, Nat.cast_eq_zero]
  rw [h0, ← Measure.map_apply_of_aemeasurable (aemeasurable_N_of_law P rate N hNlaw (v - u))
    (measurableSet_singleton 0).compl, hNlaw (v - u),
    prob_compl_eq_one_sub (measurableSet_singleton 0), poissonMeasure_singleton_eq]
  simp

private lemma arrival_monotone_of_ae
    {N : ℝ≥0 → ℕ} {T : ℕ → ℝ≥0}
    (h : ∀ (n : ℕ), 0 < n → ∀ (t : ℝ≥0), (n ≤ N t ↔ T n ≤ t)) :
    (∀ {s u : ℝ≥0}, s ≤ u → N s ≤ N u) ∧
    (∀ {a b : ℕ}, 0 < a → a ≤ b → T a ≤ T b) := by
  constructor
  · intro s u hsu
    by_cases h0 : N s = 0
    · omega
    · have hpos : 0 < N s := Nat.pos_of_ne_zero h0
      have hTs : T (N s) ≤ s := (h (N s) hpos s).mp le_rfl
      exact (h (N s) hpos u).mpr (le_trans hTs hsu)
  · intro a b ha hab
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hbN : b ≤ N (T b) := (h b hb (T b)).mpr le_rfl
    exact (h a ha (T b)).mp (le_trans hab hbN)

private lemma arrival_mem_openSimplex_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0)
    (hNlaw : ∀ t, P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (hNlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (N t ω : ℝ)) P)
    (harrival : ∀ᵐ ω ∂P, ∀ (n : ℕ), 0 < n → ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t))
    (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (hn : 0 < n) :
    P {ω | N t ω = n ∧ (fun i : Fin n => (T (i.val + 1) ω : ℝ)) ∉ openSimplex n t} = 0 := by
  have hbad : {ω | N t ω = n ∧ (fun i : Fin n => (T (i.val + 1) ω : ℝ)) ∉ openSimplex n t} ⊆
      {ω | ¬ ∀ (m : ℕ), 0 < m → ∀ (s : ℝ≥0), (m ≤ N s ω ↔ T m ω ≤ s)} ∪
      {ω | N t ω = n ∧ T n ω = t} ∪
      ⋃ (i : Fin n) (hi : i.val + 1 < n),
        {ω | 0 < T (i.val + 1) ω ∧ T (i.val + 1) ω = T (i.val + 2) ω ∧ T (i.val + 1) ω ≤ t} := by
    intro ω ⟨hNt, hnot⟩
    by_cases ha : ∀ (m : ℕ), 0 < m → ∀ (s : ℝ≥0), (m ≤ N s ω ↔ T m ω ≤ s)
    · have ⟨_, hTmono⟩ := arrival_monotone_of_ae ha
      have hpos : ∀ i : Fin n, 0 < T (i.val + 1) ω := by
        intro i
        by_contra hle
        have hle0 : T (i.val + 1) ω ≤ 0 := le_of_not_gt hle
        have h1 : i.val + 1 ≤ N 0 ω := (ha (i.val + 1) (Nat.succ_pos _) 0).mpr hle0
        rw [N_zero_eq_zero P N hNlevy ω] at h1
        omega
      have hle_t : ∀ i : Fin n, T (i.val + 1) ω ≤ t := by
        intro i
        refine (ha (i.val + 1) (Nat.succ_pos _) t).mp ?_
        rw [hNt]; exact i.isLt
      by_cases hTn : T n ω = t
      · exact Or.inl (Or.inr ⟨hNt, hTn⟩)
      · right
        have hlt_t : ∀ i : Fin n, T (i.val + 1) ω < t := by
          intro i
          have h1 : T (i.val + 1) ω ≤ T n ω := hTmono (Nat.succ_pos _) i.isLt
          have h2 : T n ω < t := lt_of_le_of_ne ((ha n hn t).mp (by rw [hNt])) hTn
          exact lt_of_le_of_lt h1 h2
        have hnotstrict : ¬ StrictMono (fun i : Fin n => (T (i.val + 1) ω : ℝ)) := by
          intro hsm
          apply hnot
          refine ⟨fun i => ⟨by exact_mod_cast hpos i, by exact_mod_cast hlt_t i⟩, hsm⟩
        have hex : ∃ i : Fin n, ∃ hi : i.val + 1 < n, T (i.val + 1) ω = T (i.val + 2) ω := by
          by_contra hno
          push_neg at hno
          apply hnotstrict
          intro i j hij
          have hstep : ∀ k : ℕ, ∀ hk : k + 1 < n, T (k + 1) ω < T (k + 2) ω := by
            intro k hk
            exact lt_of_le_of_ne (hTmono (Nat.succ_pos _) (by omega))
              (hno ⟨k, by omega⟩ hk)
          have hlt : T (i.val + 1) ω < T (j.val + 1) ω := by
            have h1 : T (i.val + 1) ω < T (i.val + 2) ω := hstep i.val (by omega)
            have h2 : T (i.val + 2) ω ≤ T (j.val + 1) ω := hTmono (by omega) (by omega)
            exact lt_of_lt_of_le h1 h2
          exact_mod_cast hlt
        obtain ⟨i, hi, heq⟩ := hex
        exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hpos i, heq, hle_t i⟩⟩
    · exact Or.inl (Or.inl ha)
  refine measure_mono_null hbad (measure_union_null (measure_union_null ?_ ?_) ?_)
  · exact harrival
  · -- P {ω | N t ω = n ∧ T n ω = t} = 0
    have hle_seq : ∀ m : ℕ,
        P {ω | N t ω = n ∧ T n ω = t} ≤
          1 - ENNReal.ofReal (Real.exp (-((rate * (t / (m + 1 : ℝ≥0)) : ℝ≥0) : ℝ))) := by
      intro m
      let s : ℝ≥0 := t * (m : ℝ≥0) / (m + 1 : ℝ≥0)
      have hm1 : (0 : ℝ≥0) < (m + 1 : ℝ≥0) := by positivity
      have hs_lt : s < t := by
        dsimp [s]
        rw [div_lt_iff₀ hm1]
        have : (m : ℝ≥0) < (m + 1 : ℝ≥0) := by exact_mod_cast Nat.lt_succ_self m
        exact mul_lt_mul_of_pos_left this ht
      have hs_le : s ≤ t := le_of_lt hs_lt
      have hts : t - s = t / (m + 1 : ℝ≥0) := by
        apply NNReal.coe_injective
        rw [NNReal.coe_sub hs_le]
        push_cast [s]
        have hm1' : ((m : ℝ) + 1) ≠ 0 := by positivity
        field_simp [hm1']
        ring
      have hsub : {ω | N t ω = n ∧ T n ω = t} ⊆
          {ω | ¬ ∀ (k : ℕ), 0 < k → ∀ (u : ℝ≥0), (k ≤ N u ω ↔ T k ω ≤ u)} ∪
          {ω | increment (fun u ω => (N u ω : ℝ)) s t ω ≠ 0} := by
        intro ω ⟨hNt, hTn⟩
        by_cases ha : ∀ (k : ℕ), 0 < k → ∀ (u : ℝ≥0), (k ≤ N u ω ↔ T k ω ≤ u)
        · right
          intro hinc
          have hNs_eq : N s ω = N t ω := by
            have hinc' : (N t ω : ℝ) - (N s ω : ℝ) = 0 := hinc
            exact Nat.cast_injective (sub_eq_zero.mp hinc').symm
          have hle_s : T n ω ≤ s := (ha n hn s).mp (by rw [hNs_eq, hNt])
          rw [hTn] at hle_s
          exact not_le_of_gt hs_lt hle_s
        · exact Or.inl ha
      calc P {ω | N t ω = n ∧ T n ω = t}
          ≤ P ({ω | ¬ ∀ (k : ℕ), 0 < k → ∀ (u : ℝ≥0), (k ≤ N u ω ↔ T k ω ≤ u)} ∪
              {ω | increment (fun u ω => (N u ω : ℝ)) s t ω ≠ 0}) := measure_mono hsub
        _ ≤ P {ω | ¬ ∀ (k : ℕ), 0 < k → ∀ (u : ℝ≥0), (k ≤ N u ω ↔ T k ω ≤ u)} +
              P {ω | increment (fun u ω => (N u ω : ℝ)) s t ω ≠ 0} := measure_union_le _ _
        _ = 0 + (1 - ENNReal.ofReal (Real.exp (-((rate * (t - s) : ℝ≥0) : ℝ)))) := by
              rw [show P {ω | ¬ ∀ (k : ℕ), 0 < k → ∀ (u : ℝ≥0), (k ≤ N u ω ↔ T k ω ≤ u)} = 0 from harrival,
                increment_ne_zero_prob_eq P rate N hNlaw hNlevy hs_le]
        _ = 1 - ENNReal.ofReal (Real.exp (-((rate * (t / (m + 1 : ℝ≥0)) : ℝ≥0) : ℝ))) := by
              rw [zero_add, hts]
    have htend : Tendsto (fun m : ℕ =>
        1 - ENNReal.ofReal (Real.exp (-((rate * (t / (m + 1 : ℝ≥0)) : ℝ≥0) : ℝ)))) atTop (𝓝 0) := by
      have hdiv : Tendsto (fun m : ℕ => -((rate : ℝ) * ((t : ℝ) / ((m : ℝ) + 1)))) atTop (𝓝 0) := by
        have h1 : Tendsto (fun m : ℕ => ((m : ℝ) + 1)) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        have h2 : Tendsto (fun m : ℕ => (t : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop h1
        simpa using (h2.const_mul (rate : ℝ)).neg
      have hexp : Tendsto (fun m : ℕ =>
          ENNReal.ofReal (Real.exp (-((rate * (t / (m + 1 : ℝ≥0)) : ℝ≥0) : ℝ)))) atTop (𝓝 1) := by
        have hrew : (fun m : ℕ => ENNReal.ofReal (Real.exp (-((rate * (t / (m + 1 : ℝ≥0)) : ℝ≥0) : ℝ)))) =
            (fun m : ℕ => ENNReal.ofReal (Real.exp (-((rate : ℝ) * ((t : ℝ) / ((m : ℝ) + 1)))))) := by
          ext m; push_cast; rfl
        have hone : (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp 0) := by simp
        rw [hrew, hone]
        exact (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto 0).comp hdiv)
      simpa using (ENNReal.Tendsto.sub tendsto_const_nhds hexp (Or.inl ENNReal.one_ne_top))
    exact le_antisymm (ge_of_tendsto htend (Eventually.of_forall hle_seq)) bot_le
  · -- P {ω | 0 < T (i+1) ω ∧ T (i+1) ω = T (i+2) ω ∧ T (i+1) ω ≤ t} = 0
    refine measure_iUnion_null fun i => measure_iUnion_null fun hi => ?_
    have hle_seq : ∀ m : ℕ,
        P {ω | 0 < T (i.val + 1) ω ∧ T (i.val + 1) ω = T (i.val + 2) ω ∧ T (i.val + 1) ω ≤ t} ≤
          ENNReal.ofReal (((rate : ℝ) * (t : ℝ)) ^ 2 / ((m : ℝ) + 1)) := by
      intro m
      let M : ℕ := m + 1
      have hMpos : (0 : ℝ≥0) < (M : ℝ≥0) := by positivity
      let grid : ℕ → ℝ≥0 := fun k => t * (k : ℝ≥0) / (M : ℝ≥0)
      have hsub : {ω | 0 < T (i.val + 1) ω ∧ T (i.val + 1) ω = T (i.val + 2) ω ∧ T (i.val + 1) ω ≤ t} ⊆
          {ω | ¬ ∀ (k : ℕ), 0 < k → ∀ (u : ℝ≥0), (k ≤ N u ω ↔ T k ω ≤ u)} ∪
          ⋃ k : Fin M, {ω | (2 : ℝ) ≤ increment (fun u ω => (N u ω : ℝ)) (grid k.val) (grid (k.val + 1)) ω} := by
        intro ω ⟨hpos, heq, hle⟩
        by_cases ha : ∀ (k : ℕ), 0 < k → ∀ (u : ℝ≥0), (k ≤ N u ω ↔ T k ω ≤ u)
        · right
          -- Find k : Fin M such that grid k < T (i+1) ω ≤ grid (k+1)
          have hexk : ∃ k : Fin M, grid k.val < T (i.val + 1) ω ∧ T (i.val + 1) ω ≤ grid (k.val + 1) := by
            have hceil : ∃ j : ℕ, j < M ∧ grid j < T (i.val + 1) ω ∧ T (i.val + 1) ω ≤ grid (j + 1) := by
              have hgridM : T (i.val + 1) ω ≤ grid M := by
                dsimp [grid]; rwa [mul_div_cancel_right₀ _ (ne_of_gt hMpos)]
              have hgrid0 : grid 0 < T (i.val + 1) ω := by simpa [grid] using hpos
              let S : Set ℕ := {j : ℕ | T (i.val + 1) ω ≤ grid j}
              have hSne : S.Nonempty := ⟨M, hgridM⟩
              let j0 := Nat.find hSne
              have hj0_spec : T (i.val + 1) ω ≤ grid j0 := Nat.find_spec hSne
              have hj0_le : j0 ≤ M := Nat.find_min' hSne hgridM
              have hj0_pos : 0 < j0 := by
                by_contra h0
                have : j0 = 0 := by omega
                rw [this] at hj0_spec
                exact not_lt_of_ge hj0_spec hgrid0
              refine ⟨j0 - 1, by omega, ?_, ?_⟩
              · have hlt := Nat.find_min hSne (show j0 - 1 < j0 by omega)
                exact lt_of_not_ge hlt
              · rwa [show j0 - 1 + 1 = j0 by omega]
            obtain ⟨j, hj, h1, h2⟩ := hceil
            exact ⟨⟨j, hj⟩, h1, h2⟩
          obtain ⟨k, hk1, hk2⟩ := hexk
          refine Set.mem_iUnion.mpr ⟨k, ?_⟩
          have hN1 : N (grid k.val) ω ≤ i.val := by
            by_contra hgt
            have hle' : i.val + 1 ≤ N (grid k.val) ω := by omega
            have := (ha (i.val + 1) (Nat.succ_pos _) (grid k.val)).mp hle'
            exact not_lt_of_ge this hk1
          have hN2 : i.val + 2 ≤ N (grid (k.val + 1)) ω := by
            refine (ha (i.val + 2) (by omega) (grid (k.val + 1))).mpr ?_
            rwa [← heq]
          change (2 : ℝ) ≤ (N (grid (k.val + 1)) ω : ℝ) - (N (grid k.val) ω : ℝ)
          have hnat : i.val + 2 ≤ N (grid (k.val + 1)) ω := hN2
          have : (2 : ℝ) + (N (grid k.val) ω : ℝ) ≤ (N (grid (k.val + 1)) ω : ℝ) := by
            exact_mod_cast (show 2 + N (grid k.val) ω ≤ N (grid (k.val + 1)) ω by omega)
          linarith
        · exact Or.inl ha
      calc P {ω | 0 < T (i.val + 1) ω ∧ T (i.val + 1) ω = T (i.val + 2) ω ∧ T (i.val + 1) ω ≤ t}
          ≤ P {ω | ¬ ∀ (k : ℕ), 0 < k → ∀ (u : ℝ≥0), (k ≤ N u ω ↔ T k ω ≤ u)} +
              P (⋃ k : Fin M, {ω | (2 : ℝ) ≤ increment (fun u ω => (N u ω : ℝ)) (grid k.val) (grid (k.val + 1)) ω}) :=
            le_trans (measure_mono hsub) (measure_union_le _ _)
        _ ≤ 0 + ∑ k : Fin M, P {ω | (2 : ℝ) ≤ increment (fun u ω => (N u ω : ℝ)) (grid k.val) (grid (k.val + 1)) ω} := by
            rw [show P {ω | ¬ ∀ (k : ℕ), 0 < k → ∀ (u : ℝ≥0), (k ≤ N u ω ↔ T k ω ≤ u)} = 0 from harrival]
            exact add_le_add le_rfl (measure_iUnion_fintype_le _ _)
        _ = ∑ k : Fin M, P {ω | (2 : ℝ) ≤ increment (fun u ω => (N u ω : ℝ)) (grid k.val) (grid (k.val + 1)) ω} := zero_add _
        _ ≤ ∑ k : Fin M, ENNReal.ofReal ((((rate * (grid (k.val + 1) - grid k.val) : ℝ≥0) : ℝ)) ^ 2) := by
            refine Finset.sum_le_sum fun k _ => increment_ge_two_prob_le P rate N hNlaw hNlevy ?_
            dsimp [grid]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ k.val) bot_le) bot_le
        _ = ENNReal.ofReal (((rate : ℝ) * (t : ℝ)) ^ 2 / ((m : ℝ) + 1)) := by
            have hstep : ∀ k : Fin M, (((rate * (grid (k.val + 1) - grid k.val) : ℝ≥0) : ℝ)) ^ 2 =
                ((rate : ℝ) * (t : ℝ)) ^ 2 / ((M : ℝ) ^ 2) := by
              intro k
              have hle_g : grid k.val ≤ grid (k.val + 1) := by
                dsimp [grid]
                exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ k.val) bot_le) bot_le
              have hdiff : ((grid (k.val + 1) - grid k.val : ℝ≥0) : ℝ) = (t : ℝ) / (M : ℝ) := by
                rw [NNReal.coe_sub hle_g]
                push_cast [grid]
                have hM0 : (M : ℝ) ≠ 0 := by positivity
                field_simp [hM0]
                ring
              rw [NNReal.coe_mul, hdiff]
              ring
            simp_rw [hstep]
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg M)]
            congr 1
            have hM0 : (M : ℝ) ≠ 0 := by positivity
            have hMeq : (M : ℝ) = (m : ℝ) + 1 := by simp [M]
            rw [hMeq] at hM0 ⊢
            field_simp [hM0]
    have htend : Tendsto (fun m : ℕ =>
        ENNReal.ofReal (((rate : ℝ) * (t : ℝ)) ^ 2 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => ((m : ℝ) + 1)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have h2 : Tendsto (fun m : ℕ => ((rate : ℝ) * (t : ℝ)) ^ 2 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop h1
      have h0 : (0 : ℝ≥0∞) = ENNReal.ofReal 0 := ENNReal.ofReal_zero.symm
      rw [h0]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp h2
    exact le_antisymm (ge_of_tendsto htend (Eventually.of_forall hle_seq)) bot_le

private lemma disjoint_box_prob_eq
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0)
    (hNlaw : ∀ t, P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (hNlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (N t ω : ℝ)) P)
    (harrival : ∀ᵐ ω ∂P, ∀ (n : ℕ), 0 < n → ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t))
    (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (hn : 0 < n)
    (a b : Fin n → ℝ)
    (hab : ∀ i, 0 ≤ a i ∧ a i < b i ∧ b i ≤ (t : ℝ))
    (hord : ∀ i j : Fin n, i < j → b i ≤ a j) :
    P {ω | N t ω = n ∧ (fun i : Fin n => (T (i.val + 1) ω : ℝ)) ∈
        Set.univ.pi (fun i => Set.Ioc (a i) (b i))} =
      P {ω | N t ω = n} *
        ENNReal.ofReal ((Nat.factorial n : ℝ) / ((t : ℝ) ^ n)) *
        volume (Set.univ.pi (fun i => Set.Ioc (a i) (b i)) ∩ closedSimplex n t) := by
  let a' : Fin n → ℝ≥0 := fun i => ⟨a i, (hab i).1⟩
  let b' : Fin n → ℝ≥0 := fun i => ⟨b i, le_trans (hab i).1 (le_of_lt (hab i).2.1)⟩
  let τ : Fin (2 * n + 2) → ℝ≥0 := fun k =>
    if h0 : k.val = 0 then 0
    else if hlast : k.val = 2 * n + 1 then t
    else if k.val % 2 = 1 then a' ⟨(k.val - 1) / 2, by omega⟩
    else b' ⟨(k.val - 2) / 2, by omega⟩
  have hτ_mono : Monotone τ := by
    have hstep : ∀ k : Fin (2 * n + 1), τ k.castSucc ≤ τ k.succ := by
      intro k
      change τ ⟨k.val, by omega⟩ ≤ τ ⟨k.val + 1, by omega⟩
      by_cases hk0 : k.val = 0
      · simp [τ, hk0]
      · by_cases hklast : k.val = 2 * n
        · have hne0 : 2 * n ≠ 0 := by omega
          have hnel : 2 * n ≠ 2 * n + 1 := by omega
          have hmod : (2 * n) % 2 ≠ 1 := by omega
          simp only [τ, hklast, hne0, hnel, hmod, ↓reduceDIte, ↓reduceIte]
          exact_mod_cast (hab ⟨(2 * n - 2) / 2, by omega⟩).2.2
        · by_cases hmod : k.val % 2 = 1
          · have h1 : k.val + 1 ≠ 0 := by omega
            have h2 : k.val + 1 ≠ 2 * n + 1 := by omega
            have h3 : (k.val + 1) % 2 ≠ 1 := by omega
            have hne_l : k.val ≠ 2 * n + 1 := by omega
            simp only [τ, hk0, hne_l, hmod, h1, h2, h3, ↓reduceDIte, ↓reduceIte]
            have hidx : (k.val + 1 - 2) / 2 = (k.val - 1) / 2 := by omega
            simp only [hidx]
            exact_mod_cast le_of_lt (hab ⟨(k.val - 1) / 2, by omega⟩).2.1
          · have h1 : k.val + 1 ≠ 0 := by omega
            have h2 : k.val + 1 ≠ 2 * n + 1 := by omega
            have h3 : (k.val + 1) % 2 = 1 := by omega
            have hne_l : k.val ≠ 2 * n + 1 := by omega
            simp only [τ, hk0, hne_l, hmod, h1, h2, h3, ↓reduceDIte, ↓reduceIte]
            have hlt_idx : (⟨(k.val - 2) / 2, by omega⟩ : Fin n) < ⟨(k.val + 1 - 1) / 2, by omega⟩ := by
              change (k.val - 2) / 2 < (k.val + 1 - 1) / 2; omega
            exact_mod_cast hord _ _ hlt_idx
    intro i j hij
    have hnat : ∀ (a b : ℕ) (ha : a < 2 * n + 2) (hb : b < 2 * n + 2), a ≤ b →
        τ ⟨a, ha⟩ ≤ τ ⟨b, hb⟩ := by
      intro a b ha hb hab
      induction b with
      | zero =>
        have : a = 0 := by omega
        subst this; exact le_rfl
      | succ b ih =>
        by_cases heq : a = b + 1
        · subst heq; exact le_rfl
        · exact le_trans (ih (by omega) (by omega)) (hstep ⟨b, by omega⟩)
    exact hnat i.val j.val i.isLt j.isLt hij
  let c : Fin (2 * n + 1) → ℕ := fun k => if k.val % 2 = 1 then 1 else 0
  let X : ℝ≥0 → Ω → ℝ := fun s ω => (N s ω : ℝ)
  let E_box : Set Ω := {ω | N t ω = n ∧ (fun i : Fin n => (T (i.val + 1) ω : ℝ)) ∈
    Set.univ.pi (fun i => Set.Ioc (a i) (b i))}
  let E_inc : Set Ω := ⋂ k : Fin (2 * n + 1),
    (increment X (τ k.castSucc) (τ k.succ)) ⁻¹' {(c k : ℝ)}
  have hτ_a : ∀ i : Fin n, τ ⟨2 * i.val + 1, by omega⟩ = a' i := by
    intro i
    have h1 : 2 * i.val + 1 ≠ 0 := by omega
    have h2 : 2 * i.val + 1 ≠ 2 * n + 1 := by omega
    have h3 : (2 * i.val + 1) % 2 = 1 := by omega
    simp only [τ, h1, h2, h3, ↓reduceDIte, ↓reduceIte]
    congr 1; ext; dsimp; omega
  have hτ_b : ∀ i : Fin n, τ ⟨2 * i.val + 2, by omega⟩ = b' i := by
    intro i
    have h1 : 2 * i.val + 2 ≠ 0 := by omega
    have h2 : 2 * i.val + 2 ≠ 2 * n + 1 := by omega
    have h3 : (2 * i.val + 2) % 2 ≠ 1 := by omega
    simp only [τ, h1, h2, h3, ↓reduceDIte, ↓reduceIte]
    congr 1; ext; dsimp; omega
  have hτ_0 : τ ⟨0, by omega⟩ = 0 := by simp [τ]
  have hτ_last : τ ⟨2 * n + 1, by omega⟩ = t := by simp [τ]
  have hsymm : E_box =ᵐ[P] E_inc := by
    filter_upwards [harrival] with ω ha
    have ⟨hNmono, _⟩ := arrival_monotone_of_ae ha
    have hN0 : N 0 ω = 0 := N_zero_eq_zero P N hNlevy ω
    apply propext
    change ω ∈ E_box ↔ ω ∈ E_inc
    constructor
    · rintro ⟨hNt, hbox⟩
      simp only [E_inc, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff, increment, X]
      have hNa : ∀ i : Fin n, N (a' i) ω = i.val := by
        intro i
        have hgt : a' i < T (i.val + 1) ω := by
          have := (hbox i (Set.mem_univ i)).1
          exact_mod_cast this
        have hle1 : N (a' i) ω ≤ i.val := by
          by_contra hcon
          have : T (i.val + 1) ω ≤ a' i := (ha (i.val + 1) (Nat.succ_pos _) (a' i)).mp (by omega)
          exact not_lt_of_ge this hgt
        have hge1 : i.val ≤ N (a' i) ω := by
          cases hi0 : i.val with
          | zero => omega
          | succ m =>
            let im : Fin n := ⟨m, by omega⟩
            have hbm : T (m + 1) ω ≤ b' im := by
              have := (hbox im (Set.mem_univ im)).2
              exact_mod_cast this
            have hba : b' im ≤ a' i := by
              exact_mod_cast hord im i (by change m < i.val; omega)
            exact (ha (m + 1) (Nat.succ_pos _) (a' i)).mpr (le_trans hbm hba)
        omega
      have hNb : ∀ i : Fin n, N (b' i) ω = i.val + 1 := by
        intro i
        have hleT : T (i.val + 1) ω ≤ b' i := by
          have := (hbox i (Set.mem_univ i)).2
          exact_mod_cast this
        have hge1 : i.val + 1 ≤ N (b' i) ω := (ha (i.val + 1) (Nat.succ_pos _) (b' i)).mpr hleT
        have hle1 : N (b' i) ω ≤ i.val + 1 := by
          by_cases hlast : i.val + 1 < n
          · let inxt : Fin n := ⟨i.val + 1, hlast⟩
            have hba : b' i ≤ a' inxt := by
              exact_mod_cast hord i inxt (by change i.val < i.val + 1; omega)
            have hNle := hNmono hba
            rw [hNa inxt] at hNle
            exact hNle
          · have heq : i.val + 1 = n := by omega
            have hbt : b' i ≤ t := by exact_mod_cast (hab i).2.2
            have hNle := hNmono hbt
            rw [hNt] at hNle
            omega
        omega
      intro k
      change (N (τ ⟨k.val + 1, by omega⟩) ω : ℝ) - (N (τ ⟨k.val, by omega⟩) ω : ℝ) = (c k : ℝ)
      by_cases hk0 : k.val = 0
      · have h1 : τ ⟨k.val, by omega⟩ = 0 := by
          have : (⟨k.val, by omega⟩ : Fin (2 * n + 2)) = ⟨0, by omega⟩ := by ext; exact hk0
          rw [this, hτ_0]
        have h2 : τ ⟨k.val + 1, by omega⟩ = a' ⟨0, hn⟩ := by
          have : (⟨k.val + 1, by omega⟩ : Fin (2 * n + 2)) = ⟨2 * (⟨0, hn⟩ : Fin n).val + 1, by omega⟩ := by
            ext; simp [hk0]
          rw [this, hτ_a ⟨0, hn⟩]
        rw [h1, h2, hN0, hNa ⟨0, hn⟩]
        simp [c, hk0]
      · by_cases hklast : k.val = 2 * n
        · let ilast : Fin n := ⟨n - 1, by omega⟩
          have h1 : τ ⟨k.val, by omega⟩ = b' ilast := by
            convert hτ_b ilast using 2; ext; dsimp [ilast]; omega
          have h2 : τ ⟨k.val + 1, by omega⟩ = t := by
            convert hτ_last using 2; ext; dsimp; omega
          rw [h1, h2, hNb ilast, hNt]
          have : (ilast.val + 1 : ℕ) = n := by dsimp [ilast]; omega
          rw [this]
          simp [c, hklast]
        · by_cases hmod : k.val % 2 = 1
          · let idx : Fin n := ⟨(k.val - 1) / 2, by omega⟩
            have h1 : τ ⟨k.val, by omega⟩ = a' idx := by
              convert hτ_a idx using 2; ext; dsimp [idx]; omega
            have h2 : τ ⟨k.val + 1, by omega⟩ = b' idx := by
              convert hτ_b idx using 2; ext; dsimp [idx]; omega
            rw [h1, h2, hNa idx, hNb idx]
            simp only [c, hmod, ↓reduceIte, Nat.cast_add, Nat.cast_one]
            ring
          · let idx : Fin n := ⟨(k.val - 2) / 2, by omega⟩
            let idx' : Fin n := ⟨(k.val - 2) / 2 + 1, by omega⟩
            have h1 : τ ⟨k.val, by omega⟩ = b' idx := by
              convert hτ_b idx using 2; ext; dsimp [idx]; omega
            have h2 : τ ⟨k.val + 1, by omega⟩ = a' idx' := by
              convert hτ_a idx' using 2; ext; dsimp [idx']; omega
            rw [h1, h2, hNb idx, hNa idx']
            simp only [c, hmod, ↓reduceIte, Nat.cast_zero, idx, idx']
            simp
    · intro hinc
      simp only [E_inc, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff, increment, X] at hinc
      have hval : ∀ j : Fin (2 * n + 2), N (τ j) ω = j.val / 2 := by
        intro j
        obtain ⟨jv, hjv⟩ := j
        induction jv with
        | zero =>
          rw [hτ_0, hN0]; simp
        | succ m ih =>
          let k : Fin (2 * n + 1) := ⟨m, by omega⟩
          have hk : (N (τ ⟨m + 1, hjv⟩) ω : ℝ) - (N (τ ⟨m, by omega⟩) ω : ℝ) = (c k : ℝ) := hinc k
          have hm := ih (by omega)
          have hstep : (N (τ ⟨m + 1, hjv⟩) ω : ℝ) = (N (τ ⟨m, by omega⟩) ω : ℝ) + (c k : ℝ) := by
            linarith [hk]
          have hnat : N (τ ⟨m + 1, hjv⟩) ω = N (τ ⟨m, by omega⟩) ω + c k := by
            exact_mod_cast hstep
          rw [hnat, hm]
          dsimp [c, k]
          split_ifs <;> omega
      refine ⟨?_, ?_⟩
      · have h2 := hval ⟨2 * n + 1, by omega⟩
        rw [hτ_last] at h2
        dsimp only at h2
        omega
      · intro i _
        have hNa : N (a' i) ω = i.val := by
          have h2 := hval ⟨2 * i.val + 1, by omega⟩
          rw [hτ_a i] at h2
          dsimp only at h2
          omega
        have hNb : N (b' i) ω = i.val + 1 := by
          have h2 := hval ⟨2 * i.val + 2, by omega⟩
          rw [hτ_b i] at h2
          dsimp only at h2
          omega
        constructor
        · have hlt : a' i < T (i.val + 1) ω := by
            by_contra hle
            have h1 := (ha (i.val + 1) (Nat.succ_pos _) (a' i)).mpr (le_of_not_gt hle)
            rw [hNa] at h1
            omega
          exact_mod_cast hlt
        · have hle : T (i.val + 1) ω ≤ b' i := (ha (i.val + 1) (Nat.succ_pos _) (b' i)).mp (by rw [hNb])
          exact_mod_cast hle
  -- Compute P E_box = P E_inc using independent stationary Poisson increments
  have hPE : P E_box = ∏ k : Fin (2 * n + 1),
      ProbabilityTheory.poissonMeasure (rate * (τ k.succ - τ k.castSucc)) {c k} := by
    rw [measure_congr hsymm]
    have hind := hNlevy.indep_increments (2 * n + 1) τ hτ_mono
    have hmul := hind.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun k => {(c k : ℝ)}) (fun k _ => measurableSet_singleton _)
    have hEq : E_inc = ⋂ k ∈ (Finset.univ : Finset (Fin (2 * n + 1))),
        (increment X (τ k.castSucc) (τ k.succ)) ⁻¹' {(c k : ℝ)} := by
      ext ω; simp [E_inc]
    rw [hEq, hmul]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact increment_prob_eq_poisson P rate N hNlaw hNlevy (hτ_mono k.castSucc_le_succ) (c k)
  -- Evaluate the product of Poisson point masses
  have hprod_eval : (∏ k : Fin (2 * n + 1),
      ProbabilityTheory.poissonMeasure (rate * (τ k.succ - τ k.castSucc)) {c k}) =
      ENNReal.ofReal (Real.exp (-((rate : ℝ) * (t : ℝ))) * (rate : ℝ) ^ n *
        ∏ i : Fin n, (b i - a i)) := by
    have hterm : ∀ k : Fin (2 * n + 1),
        ProbabilityTheory.poissonMeasure (rate * (τ k.succ - τ k.castSucc)) {c k} =
          ENNReal.ofReal (Real.exp (-((rate : ℝ) * ((τ k.succ : ℝ) - (τ k.castSucc : ℝ)))) *
            (if k.val % 2 = 1 then (rate : ℝ) * ((τ k.succ : ℝ) - (τ k.castSucc : ℝ)) else 1)) := by
      intro k
      rw [poissonMeasure_singleton_eq]
      have hsub : ((rate * (τ k.succ - τ k.castSucc) : ℝ≥0) : ℝ) =
          (rate : ℝ) * ((τ k.succ : ℝ) - (τ k.castSucc : ℝ)) := by
        rw [NNReal.coe_mul, NNReal.coe_sub (hτ_mono k.castSucc_le_succ)]
      rw [hsub]
      dsimp [c]
      split_ifs <;> simp
    simp_rw [hterm]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => by
      refine mul_nonneg (Real.exp_nonneg _) ?_
      split_ifs
      · exact mul_nonneg rate.coe_nonneg (sub_nonneg.mpr (by exact_mod_cast hτ_mono k.castSucc_le_succ))
      · exact zero_le_one)]
    congr 1
    rw [Finset.prod_mul_distrib]
    have hexp_prod : (∏ k : Fin (2 * n + 1),
        Real.exp (-((rate : ℝ) * ((τ k.succ : ℝ) - (τ k.castSucc : ℝ))))) =
        Real.exp (-((rate : ℝ) * (t : ℝ))) := by
      rw [← Real.exp_sum]
      congr 1
      have htel : ∑ k : Fin (2 * n + 1), ((τ k.succ : ℝ) - (τ k.castSucc : ℝ)) =
          (τ (Fin.last (2 * n + 1)) : ℝ) - (τ 0 : ℝ) := by
        have htele : ∀ (m : ℕ) (g : Fin (m + 1) → ℝ),
            ∑ k : Fin m, (g k.succ - g k.castSucc) = g (Fin.last m) - g 0 := by
          intro m
          induction m with
          | zero => intro g; simp
          | succ m ih =>
            intro g
            rw [Fin.sum_univ_castSucc]
            have hsc : ∀ i : Fin m, i.castSucc.succ = i.succ.castSucc := fun _ => rfl
            simp_rw [hsc]
            rw [ih (fun j => g j.castSucc)]
            have h0 : (0 : Fin (m + 1)).castSucc = (0 : Fin (m + 1 + 1)) := rfl
            rw [h0, Fin.succ_last]
            ring
        exact htele (2 * n + 1) (fun j => (τ j : ℝ))
      have hsum : ∑ k : Fin (2 * n + 1), -((rate : ℝ) * ((τ k.succ : ℝ) - (τ k.castSucc : ℝ))) =
          -((rate : ℝ) * ∑ k : Fin (2 * n + 1), ((τ k.succ : ℝ) - (τ k.castSucc : ℝ))) := by
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      rw [hsum, htel]
      have hlast' : τ (Fin.last (2 * n + 1)) = t := hτ_last
      have h0' : τ 0 = 0 := hτ_0
      rw [hlast', h0']
      simp
    have hlin_prod : (∏ k : Fin (2 * n + 1),
        if k.val % 2 = 1 then (rate : ℝ) * ((τ k.succ : ℝ) - (τ k.castSucc : ℝ)) else 1) =
        (rate : ℝ) ^ n * ∏ i : Fin n, (b i - a i) := by
      let S : Finset (Fin (2 * n + 1)) := Finset.univ.filter (fun k => k.val % 2 = 1)
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k : Fin (2 * n + 1) => k.val % 2 = 1)]
      have hnot : (∏ x ∈ Finset.univ.filter (fun k : Fin (2 * n + 1) => ¬k.val % 2 = 1),
          if x.val % 2 = 1 then (rate : ℝ) * ((τ x.succ : ℝ) - (τ x.castSucc : ℝ)) else 1) = 1 := by
        refine Finset.prod_eq_one fun x hx => ?_
        rw [Finset.mem_filter] at hx
        simp [hx.2]
      rw [hnot, mul_one]
      have hbij : (∏ x ∈ S, if x.val % 2 = 1 then (rate : ℝ) * ((τ x.succ : ℝ) - (τ x.castSucc : ℝ)) else 1) =
          ∏ i : Fin n, ((rate : ℝ) * (b i - a i)) := by
        refine Finset.prod_bij (fun x hx => (⟨(x.val - 1) / 2, by omega⟩ : Fin n)) ?_ ?_ ?_ ?_
        · intro x _; exact Finset.mem_univ _
        · intro x hx y hy hxy
          rw [Finset.mem_filter] at hx hy
          have : (x.val - 1) / 2 = (y.val - 1) / 2 := congrArg Fin.val hxy
          ext; omega
        · intro i _
          refine ⟨⟨2 * i.val + 1, by omega⟩, ?_, ?_⟩
          · simp [S]
          · ext; dsimp; omega
        · intro x hx
          rw [Finset.mem_filter] at hx
          rw [if_pos hx.2]
          let idx : Fin n := ⟨(x.val - 1) / 2, by omega⟩
          have h1 : τ x.castSucc = a' idx := by
            convert hτ_a idx using 2; ext; dsimp [idx]; omega
          have h2 : τ x.succ = b' idx := by
            convert hτ_b idx using 2; ext; dsimp [idx]; omega
          rw [h1, h2]
          rfl
      rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hexp_prod, hlin_prod, mul_assoc]
  -- Evaluate the RHS
  have hsub_simp : Set.univ.pi (fun i => Set.Ioc (a i) (b i)) ⊆ closedSimplex n t := by
    intro v hv
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · have hi := hv i (Set.mem_univ i)
      exact ⟨le_trans (hab i).1 (le_of_lt hi.1), le_trans hi.2 (hab i).2.2⟩
    · by_cases heq : i = j
      · subst heq; exact le_rfl
      · have hlt : i < j := lt_of_le_of_ne hij heq
        exact le_trans (hv i (Set.mem_univ i)).2
          (le_trans (hord i j hlt) (le_of_lt (hv j (Set.mem_univ j)).1))
  have hvol : volume (Set.univ.pi (fun i => Set.Ioc (a i) (b i)) ∩ closedSimplex n t) =
      ENNReal.ofReal (∏ i : Fin n, (b i - a i)) := by
    rw [Set.inter_eq_left.mpr hsub_simp, volume_pi, Measure.pi_pi]
    simp_rw [Real.volume_Ioc]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => sub_nonneg.mpr (le_of_lt (hab i).2.1))]
  have hPNt : P {ω | N t ω = n} =
      ENNReal.ofReal (Real.exp (-((rate : ℝ) * (t : ℝ))) * ((rate : ℝ) * (t : ℝ)) ^ n / (Nat.factorial n : ℝ)) := by
    have hpre : {ω | N t ω = n} = (N t) ⁻¹' {n} := rfl
    rw [hpre, ← Measure.map_apply_of_aemeasurable (aemeasurable_N_of_law P rate N hNlaw t)
      (measurableSet_singleton n), hNlaw t, poissonMeasure_singleton_eq]
    push_cast; rfl
  rw [hPE, hprod_eval, hPNt, hvol]
  have h1_nn : 0 ≤ Real.exp (-((rate : ℝ) * (t : ℝ))) * ((rate : ℝ) * (t : ℝ)) ^ n / (Nat.factorial n : ℝ) := by
    positivity
  have h2_nn : 0 ≤ (Nat.factorial n : ℝ) / ((t : ℝ) ^ n) := by positivity
  rw [← ENNReal.ofReal_mul h1_nn, ← ENNReal.ofReal_mul (mul_nonneg h1_nn h2_nn)]
  congr 1
  have hfact : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
  have htn : (t : ℝ) ^ n ≠ 0 := pow_ne_zero n ht0
  field_simp [hfact, htn]
  ring

private lemma part_i_aux
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
    (hNlaw : ∀ t, P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (hNlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (N t ω : ℝ)) P)
    (harrival : ∀ᵐ ω ∂P, ∀ (n : ℕ), 0 < n → ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t))
    (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (hn : 0 < n) :
    ∀ (A : Set (Fin n → ℝ)), MeasurableSet A →
      P {ω | N t ω = n ∧ (fun i : Fin n => (T (i.val + 1) ω : ℝ)) ∈ A} =
        P {ω | N t ω = n} *
          ENNReal.ofReal ((Nat.factorial n : ℝ) / ((t : ℝ) ^ n)) *
          volume (A ∩ closedSimplex n t) := by
  let Φ : Ω → (Fin n → ℝ) := fun ω i => (T (i.val + 1) ω : ℝ)
  have hΦmeas : Measurable Φ :=
    measurable_pi_lambda _ fun i => NNReal.continuous_coe.measurable.comp (hTmeas (i.val + 1) (Nat.succ_pos _))
  let μ₁ : Measure (Fin n → ℝ) := (P.restrict {ω | N t ω = n}).map Φ
  let c : ℝ≥0∞ := P {ω | N t ω = n} * ENNReal.ofReal ((Nat.factorial n : ℝ) / ((t : ℝ) ^ n))
  let μ₂ : Measure (Fin n → ℝ) := c • (volume.restrict (closedSimplex n t))
  -- Reduce to equality of comap measures on the open simplex U = openSimplex n t
  let U : Set (Fin n → ℝ) := openSimplex n t
  have hUopen : IsOpen U := isOpen_openSimplex n t
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hμ₁_compl : μ₁ Uᶜ = 0 := by
    rw [Measure.map_apply hΦmeas hUmeas.compl, Measure.restrict_apply (hΦmeas hUmeas.compl)]
    have hset : Φ ⁻¹' Uᶜ ∩ {ω | N t ω = n} =
        {ω | N t ω = n ∧ Φ ω ∉ openSimplex n t} := by ext ω; simp [U, and_comm]
    rw [hset]
    exact arrival_mem_openSimplex_ae P rate N T hNlaw hNlevy harrival t ht n hn
  have hμ₂_compl : μ₂ Uᶜ = 0 := by
    simp only [μ₂, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hUmeas.compl]
    have hdiff : Uᶜ ∩ closedSimplex n t = closedSimplex n t \ openSimplex n t := by
      ext v; simp [U, Set.diff_eq, and_comm]
    rw [hdiff, volume_closedSimplex_diff_openSimplex_zero n t, mul_zero]
  let ν₁ : Measure U := μ₁.comap Subtype.val
  let ν₂ : Measure U := μ₂.comap Subtype.val
  have hval_meas_img : ∀ s : Set U, MeasurableSet s → MeasurableSet ((Subtype.val : U → Fin n → ℝ) '' s) :=
    fun _ hs => hUopen.isOpenEmbedding_subtypeVal.measurableEmbedding.measurableSet_image.mpr hs
  -- Define the pi-system S of disjoint ordered Ioc boxes on U, and countable rational cover T_cov
  let isOrderedBox (a b : Fin n → ℝ) : Prop :=
    (∀ i, 0 ≤ a i ∧ a i < b i ∧ b i ≤ (t : ℝ)) ∧ (∀ i j : Fin n, i < j → b i ≤ a j)
  let boxSet (a b : Fin n → ℝ) : Set U :=
    Subtype.val ⁻¹' Set.univ.pi (fun i => Set.Ioc (a i) (b i))
  let S : Set (Set U) := {∅} ∪ {s : Set U | ∃ a b : Fin n → ℝ, isOrderedBox a b ∧ s = boxSet a b}
  let T_cov : Set (Set U) :=
    {s : Set U | ∃ qa qb : Fin n → ℚ,
      isOrderedBox (fun i => (qa i : ℝ)) (fun i => (qb i : ℝ)) ∧
      s = boxSet (fun i => (qa i : ℝ)) (fun i => (qb i : ℝ))}
  have h_sub : T_cov ⊆ S := by
    rintro s ⟨qa, qb, hbox, rfl⟩
    exact Or.inr ⟨fun i => (qa i : ℝ), fun i => (qb i : ℝ), hbox, rfl⟩
  have h_count : T_cov.Countable := by
    have hsub : T_cov ⊆ (fun p : (Fin n → ℚ) × (Fin n → ℚ) =>
        boxSet (fun i => (p.1 i : ℝ)) (fun i => (p.2 i : ℝ))) '' Set.univ := by
      rintro s ⟨qa, qb, _, rfl⟩
      exact ⟨(qa, qb), Set.mem_univ _, rfl⟩
    exact (Set.to_countable _).image _ |>.mono hsub
  -- Helper: around any x : U and any ε > 0, there is a rational box in T_cov containing x within ε
  have hex_rat_box : ∀ (x : U) (ε : ℝ), 0 < ε →
      ∃ s ∈ T_cov, x ∈ s ∧ ∀ y ∈ s, ∀ i : Fin n, |y.1 i - x.1 i| < ε := by
    intro x ε hε
    have hx_bd := x.2.1
    have hx_sm := x.2.2
    -- Construct δ > 0 smaller than ε/2, all x i, all t - x i, and half all gaps x j - x i
    have hpos_list : ∀ i : Fin n, 0 < min (x.1 i) ((t : ℝ) - x.1 i) := fun i =>
      lt_min (hx_bd i).1 (sub_pos.mpr (hx_bd i).2)
    let δ1 : ℝ := (Finset.univ : Finset (Fin n)).inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i => min (x.1 i) ((t : ℝ) - x.1 i))
    have hδ1 : 0 < δ1 := (Finset.lt_inf'_iff _).mpr fun i _ => hpos_list i
    let gap : Fin n × Fin n → ℝ := fun p => if p.1 < p.2 then (x.1 p.2 - x.1 p.1) / 2 else 1
    let δ2 : ℝ := (Finset.univ : Finset (Fin n × Fin n)).inf' ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩ gap
    have hδ2 : 0 < δ2 := (Finset.lt_inf'_iff _).mpr fun p _ => by
      dsimp [gap]; split_ifs with hlt
      · exact half_pos (sub_pos.mpr (hx_sm hlt))
      · exact zero_lt_one
    let δ : ℝ := min (ε / 2) (min δ1 δ2)
    have hδ : 0 < δ := lt_min (half_pos hε) (lt_min hδ1 hδ2)
    have hqa : ∀ i : Fin n, ∃ q : ℚ, x.1 i - δ < (q : ℝ) ∧ (q : ℝ) < x.1 i := fun i =>
      exists_rat_btwn (sub_lt_self (x.1 i) hδ)
    have hqb : ∀ i : Fin n, ∃ q : ℚ, x.1 i < (q : ℝ) ∧ (q : ℝ) < x.1 i + δ := fun i =>
      exists_rat_btwn (lt_add_of_pos_right (x.1 i) hδ)
    choose qa hqa1 hqa2 using hqa
    choose qb hqb1 hqb2 using hqb
    refine ⟨boxSet (fun i => (qa i : ℝ)) (fun i => (qb i : ℝ)), ⟨qa, qb, ⟨?_, ?_⟩, rfl⟩, ?_, ?_⟩
    · intro i
      have hδ_le_i : δ ≤ min (x.1 i) ((t : ℝ) - x.1 i) :=
        le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (Finset.inf'_le _ (Finset.mem_univ i)))
      have hδ_le_x : δ ≤ x.1 i := le_trans hδ_le_i (min_le_left _ _)
      have hδ_le_tx : δ ≤ (t : ℝ) - x.1 i := le_trans hδ_le_i (min_le_right _ _)
      exact ⟨by linarith [hqa1 i], lt_trans (hqa2 i) (hqb1 i), by linarith [hqb2 i]⟩
    · intro i j hij
      have hδ_le_gap : δ ≤ (x.1 j - x.1 i) / 2 := by
        have h1 : δ ≤ δ2 := le_trans (min_le_right _ _) (min_le_right _ _)
        have h2 : δ2 ≤ gap (i, j) := Finset.inf'_le _ (Finset.mem_univ (i, j))
        simpa [gap, hij] using le_trans h1 h2
      linarith [hqb2 i, hqa1 j]
    · intro i _
      exact ⟨hqa2 i, le_of_lt (hqb1 i)⟩
    · intro y hy i
      have hyi := hy i (Set.mem_univ i)
      have hδ_le_e : δ ≤ ε / 2 := min_le_left _ _
      rw [abs_lt]
      constructor <;> linarith [hyi.1, hyi.2, hqa1 i, hqb2 i]
  have h_cover : ⋃₀ T_cov = Set.univ := by
    ext x
    simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
    obtain ⟨s, hs, hx, _⟩ := hex_rat_box x 1 zero_lt_one
    exact ⟨s, hs, hx⟩
  have h_pi : IsPiSystem S := by
    rintro s1 hs1 s2 hs2 _
    rcases hs1 with rfl | ⟨a1, b1, hb1, rfl⟩
    · simp [S]
    rcases hs2 with rfl | ⟨a2, b2, hb2, rfl⟩
    · simp [S]
    by_cases hne : ∀ i : Fin n, max (a1 i) (a2 i) < min (b1 i) (b2 i)
    · right
      refine ⟨fun i => max (a1 i) (a2 i), fun i => min (b1 i) (b2 i), ⟨?_, ?_⟩, ?_⟩
      · intro i
        exact ⟨le_trans (hb1.1 i).1 (le_max_left _ _), hne i,
          le_trans (min_le_left _ _) (hb1.1 i).2.2⟩
      · intro i j hij
        exact le_trans (min_le_left _ _) (le_trans (hb1.2 i j hij) (le_max_left _ _))
      · ext y
        simp only [Set.mem_inter_iff, boxSet, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioc,
          max_lt_iff, le_min_iff]
        exact ⟨fun ⟨h1, h2⟩ i => ⟨⟨(h1 i).1, (h2 i).1⟩, ⟨(h1 i).2, (h2 i).2⟩⟩,
          fun h => ⟨fun i => ⟨(h i).1.1, (h i).2.1⟩, fun i => ⟨(h i).1.2, (h i).2.2⟩⟩⟩
    · left
      push_neg at hne
      obtain ⟨i, hi⟩ := hne
      ext y
      simp only [Set.mem_inter_iff, boxSet, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioc,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      have hmax : max (a1 i) (a2 i) < y.1 i := max_lt (h1 i).1 (h2 i).1
      have hmin : y.1 i ≤ min (b1 i) (b2 i) := le_min (h1 i).2 (h2 i).2
      linarith
  have h_gen : (inferInstance : MeasurableSpace U) = MeasurableSpace.generateFrom S := by
    apply le_antisymm
    · rw [BorelSpace.measurable_eq (α := U)]
      refine MeasurableSpace.generateFrom_le fun G hG => ?_
      have hGeq : G = ⋃₀ {s ∈ T_cov | s ⊆ G} := by
        ext x
        simp only [Set.mem_sUnion, Set.mem_setOf_eq]
        constructor
        · intro hx
          have hG' : IsOpen G := hG
          rw [Metric.isOpen_iff] at hG'
          obtain ⟨ε, hε, hball⟩ := hG' x hx
          obtain ⟨s, hs, hxs, hrad⟩ := hex_rat_box x ε hε
          refine ⟨s, ⟨hs, fun y hy => hball ?_⟩, hxs⟩
          rw [Metric.mem_ball, Subtype.dist_eq, dist_pi_lt_iff hε]
          intro i
          simpa [Real.dist_eq] using hrad y hy i
        · rintro ⟨s, ⟨_, hsG⟩, hxs⟩
          exact hsG hxs
      rw [hGeq]
      exact MeasurableSet.sUnion (h_count.mono fun _ h => h.1) fun s hs =>
        MeasurableSpace.measurableSet_generateFrom (h_sub hs.1)
    · refine MeasurableSpace.generateFrom_le ?_
      rintro s (rfl | ⟨a, b, _, rfl⟩)
      · exact MeasurableSet.empty
      · exact (MeasurableSet.univ_pi fun i => measurableSet_Ioc).preimage measurable_subtype_coe
  have h_eq : ∀ s ∈ S, ν₁ s = ν₂ s := by
    rintro s (rfl | ⟨a, b, hbox, rfl⟩)
    · simp
    have hsmeas : MeasurableSet (boxSet a b) :=
      (MeasurableSet.univ_pi fun i => measurableSet_Ioc).preimage measurable_subtype_coe
    rw [Measure.comap_apply Subtype.val Subtype.val_injective hval_meas_img μ₁ hsmeas,
      Measure.comap_apply Subtype.val Subtype.val_injective hval_meas_img μ₂ hsmeas]
    have himg : Subtype.val '' boxSet a b =
        Set.univ.pi (fun i => Set.Ioc (a i) (b i)) ∩ U := by
      ext v; simp [boxSet, and_comm]
    rw [himg]
    have hRmeas : MeasurableSet (Set.univ.pi (fun i => Set.Ioc (a i) (b i))) :=
      MeasurableSet.univ_pi fun i => measurableSet_Ioc
    have h1 : μ₁ (Set.univ.pi (fun i => Set.Ioc (a i) (b i)) ∩ U) =
        μ₁ (Set.univ.pi (fun i => Set.Ioc (a i) (b i))) := by
      rw [← measure_inter_add_sdiff (Set.univ.pi (fun i => Set.Ioc (a i) (b i))) hUmeas]
      have h0 : μ₁ (Set.univ.pi (fun i => Set.Ioc (a i) (b i)) \ U) = 0 :=
        measure_mono_null (Set.sdiff_subset_compl _ _) hμ₁_compl
      rw [h0, add_zero]
    have h2 : μ₂ (Set.univ.pi (fun i => Set.Ioc (a i) (b i)) ∩ U) =
        μ₂ (Set.univ.pi (fun i => Set.Ioc (a i) (b i))) := by
      rw [← measure_inter_add_sdiff (Set.univ.pi (fun i => Set.Ioc (a i) (b i))) hUmeas]
      have h0 : μ₂ (Set.univ.pi (fun i => Set.Ioc (a i) (b i)) \ U) = 0 :=
        measure_mono_null (Set.sdiff_subset_compl _ _) hμ₂_compl
      rw [h0, add_zero]
    rw [h1, h2]
    rw [Measure.map_apply hΦmeas hRmeas, Measure.restrict_apply (hΦmeas hRmeas)]
    have hset : Φ ⁻¹' Set.univ.pi (fun i => Set.Ioc (a i) (b i)) ∩ {ω | N t ω = n} =
        {ω | N t ω = n ∧ Φ ω ∈ Set.univ.pi (fun i => Set.Ioc (a i) (b i))} := by
      ext ω; simp [and_comm]
    rw [hset, disjoint_box_prob_eq P rate N T hNlaw hNlevy harrival t ht n hn a b hbox.1 hbox.2]
    simp only [μ₂, c, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hRmeas]
  have hν_eq : ν₁ = ν₂ :=
    Measure.ext_of_generateFrom_of_cover_subset h_gen h_pi h_sub h_count h_cover
      (fun s hs => by
        have hle : ν₁ s ≤ μ₁ Set.univ := by
          have hsmeas : MeasurableSet s := by
            rcases hs with ⟨qa, qb, _, rfl⟩
            exact (MeasurableSet.univ_pi fun i => measurableSet_Ioc).preimage measurable_subtype_coe
          rw [Measure.comap_apply Subtype.val Subtype.val_injective hval_meas_img μ₁ hsmeas]
          exact measure_mono (Set.subset_univ _)
        exact ne_top_of_le_ne_top (by
          rw [Measure.map_apply hΦmeas MeasurableSet.univ, Set.preimage_univ,
            Measure.restrict_apply MeasurableSet.univ]
          exact measure_ne_top P _) hle)
      h_eq
  -- Conclude μ₁ A = μ₂ A for any measurable set A
  intro A hA
  have hA1 : μ₁ A = ν₁ ((Subtype.val : U → Fin n → ℝ) ⁻¹' A) := by
    rw [Measure.comap_apply Subtype.val Subtype.val_injective hval_meas_img μ₁ (hA.preimage measurable_subtype_coe)]
    have himg : (Subtype.val : U → Fin n → ℝ) '' ((Subtype.val : U → Fin n → ℝ) ⁻¹' A) = A ∩ U := by
      ext v; simp [and_comm]
    rw [himg, ← measure_inter_add_sdiff A hUmeas,
      measure_mono_null (Set.sdiff_subset_compl _ _) hμ₁_compl, add_zero]
  have hA2 : μ₂ A = ν₂ ((Subtype.val : U → Fin n → ℝ) ⁻¹' A) := by
    rw [Measure.comap_apply Subtype.val Subtype.val_injective hval_meas_img μ₂ (hA.preimage measurable_subtype_coe)]
    have himg : (Subtype.val : U → Fin n → ℝ) '' ((Subtype.val : U → Fin n → ℝ) ⁻¹' A) = A ∩ U := by
      ext v; simp [and_comm]
    rw [himg, ← measure_inter_add_sdiff A hUmeas,
      measure_mono_null (Set.sdiff_subset_compl _ _) hμ₂_compl, add_zero]
  have hμeq : μ₁ A = μ₂ A := by rw [hA1, hA2, hν_eq]
  rw [Measure.map_apply hΦmeas hA, Measure.restrict_apply (hΦmeas hA)] at hμeq
  have hset : Φ ⁻¹' A ∩ {ω | N t ω = n} = {ω | N t ω = n ∧ Φ ω ∈ A} := by
    ext ω; simp [and_comm]
  rw [hset] at hμeq
  simpa only [μ₂, c, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA] using hμeq

private lemma list_ofFn_perm_comp {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    (List.ofFn (x ∘ σ)).Perm (List.ofFn x) := by
  have hfin : ((List.finRange n).map σ).Perm (List.finRange n) := by
    rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange n).map σ.injective) (List.nodup_finRange n)]
    intro i
    simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
    exact ⟨σ.symm i, σ.apply_symm_apply i⟩
  simpa only [List.ofFn_eq_map, List.map_map] using hfin.map x

private lemma ordered_uniform_law
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (hn : 0 < n)
    (U V : Fin n → Ω → ℝ)
    (hUlaw : ∀ i, P.map (U i) =
      (ENNReal.ofReal (t : ℝ))⁻¹ • (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))))
    (hUind : ProbabilityTheory.iIndepFun U P)
    (hV : ∀ᵐ ω ∂P, Monotone (fun i : Fin n => V i ω) ∧
      (List.ofFn (fun i : Fin n => V i ω)).Perm (List.ofFn (fun i : Fin n => U i ω))) :
    ∀ (A : Set (Fin n → ℝ)), MeasurableSet A →
      P.map (fun ω => fun i : Fin n => V i ω) A =
        ENNReal.ofReal ((Nat.factorial n : ℝ) / ((t : ℝ) ^ n)) *
          volume (A ∩ closedSimplex n t) := by
  let Uvec : Ω → (Fin n → ℝ) := fun ω i => U i ω
  let Vvec : Ω → (Fin n → ℝ) := fun ω i => V i ω
  let Q : Set (Fin n → ℝ) := Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) (t : ℝ))
  have hQmeas : MeasurableSet Q := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hU_ae : ∀ i : Fin n, AEMeasurable (U i) P := by
    intro i
    by_contra hnot
    have h0 : P.map (U i) = 0 := Measure.map_of_not_aemeasurable hnot
    have h1 := congrArg (fun μ : Measure ℝ => μ Set.univ) (hUlaw i)
    rw [h0] at h1
    simp only [Measure.coe_zero, Pi.zero_apply, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc, sub_zero] at h1
    have htpos : (0 : ℝ≥0∞) < ENNReal.ofReal (t : ℝ) := ENNReal.ofReal_pos.mpr ht
    have hne : (ENNReal.ofReal (t : ℝ))⁻¹ * ENNReal.ofReal (t : ℝ) = 1 :=
      ENNReal.inv_mul_cancel (ne_of_gt htpos) ENNReal.ofReal_ne_top
    rw [hne] at h1
    exact zero_ne_one h1
  have hUvec_ae : AEMeasurable Uvec P := aemeasurable_pi_lambda _ hU_ae
  -- Law of Uvec is (t^n)⁻¹ • volume.restrict Q
  have hUvec_law : P.map Uvec = (ENNReal.ofReal ((t : ℝ) ^ n))⁻¹ • (volume.restrict Q) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map hU_ae).mp hUind]
    have : ∀ i : Fin n, SigmaFinite (P.map (U i)) := fun i => inferInstance
    refine Measure.pi_eq fun s hs => ?_
    simp_rw [hUlaw]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
    have hinter : Set.univ.pi s ∩ Q = Set.univ.pi (fun i => s i ∩ Set.Icc (0 : ℝ) (t : ℝ)) := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_univ_pi, Q, forall_and]
    rw [hinter, volume_pi, Measure.pi_pi]
    simp_rw [Measure.restrict_apply (hs _)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [← ENNReal.inv_pow, ← ENNReal.ofReal_pow t.coe_nonneg]
  -- Define measurable sorting map on distinct-coordinate tuples
  let C : Equiv.Perm (Fin n) → Set (Fin n → ℝ) := fun σ => {x : Fin n → ℝ | StrictMono (x ∘ σ)}
  have hC_meas : ∀ σ, MeasurableSet (C σ) := by
    intro σ
    have h : C σ = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), {x : Fin n → ℝ | x (σ i) < x (σ j)} := by
      ext x; simp [C, StrictMono]
    rw [h]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j))
  have hC_disj : Pairwise (fun σ₁ σ₂ => Disjoint (C σ₁) (C σ₂)) := by
    intro σ₁ σ₂ hne
    rw [Set.disjoint_left]
    intro x h1 h2
    apply hne
    have hperm : (List.ofFn (x ∘ σ₁)).Perm (List.ofFn (x ∘ σ₂)) :=
      (list_ofFn_perm_comp x σ₁).trans (list_ofFn_perm_comp x σ₂).symm
    have hpw1 : (List.ofFn (x ∘ σ₁)).Pairwise (· ≤ ·) :=
      List.pairwise_ofFn.mpr fun i j hij => le_of_lt (h1 hij)
    have hpw2 : (List.ofFn (x ∘ σ₂)).Pairwise (· ≤ ·) :=
      List.pairwise_ofFn.mpr fun i j hij => le_of_lt (h2 hij)
    have heql : List.ofFn (x ∘ σ₁) = List.ofFn (x ∘ σ₂) :=
      hperm.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hab hba) hpw1 hpw2
    have heqf : x ∘ σ₁ = x ∘ σ₂ := List.ofFn_inj.mp heql
    have hxinj : Function.Injective x := by
      intro a b hab
      have hcomp := h1.injective (show (x ∘ σ₁) (σ₁.symm a) = (x ∘ σ₁) (σ₁.symm b) by simpa using hab)
      exact σ₁.symm.injective hcomp
    ext i
    exact congrArg Fin.val (hxinj (congrFun heqf i))
  have hC_union : (⋃ σ : Equiv.Perm (Fin n), C σ) = (diagSet n)ᶜ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_compl_iff, diagSet, not_exists, Set.mem_setOf_eq]
    constructor
    · rintro ⟨σ, hσ⟩ i j hij heq
      have hcomp := hσ.injective (show (x ∘ σ) (σ.symm i) = (x ∘ σ) (σ.symm j) by simpa using heq)
      exact hij (σ.symm.injective hcomp)
    · intro hnd
      refine ⟨Tuple.sort x, fun i j hij => ?_⟩
      have hle : x (Tuple.sort x i) ≤ x (Tuple.sort x j) := Tuple.monotone_sort x (le_of_lt hij)
      refine lt_of_le_of_ne hle ?_
      exact hnd (Tuple.sort x i) (Tuple.sort x j) (fun h => ne_of_lt hij ((Tuple.sort x).injective h))
  classical
  let f : (Fin n → ℝ) → (Fin n → ℝ) := fun x =>
    if h : ∃ σ : Equiv.Perm (Fin n), x ∈ C σ then x ∘ h.choose else 0
  have hf_on_C : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ), x ∈ C σ → f x = x ∘ σ := by
    intro σ x hx
    have hex : ∃ τ : Equiv.Perm (Fin n), x ∈ C τ := ⟨σ, hx⟩
    simp only [f, dif_pos hex]
    have hτ : hex.choose = σ := by
      by_contra hne
      exact Set.disjoint_left.mp (hC_disj hne) hex.choose_spec hx
    rw [hτ]
  have hf_meas : Measurable f := by
    intro A hA
    have hpre : f ⁻¹' A =
        (⋃ σ : Equiv.Perm (Fin n), C σ ∩ (fun x : Fin n → ℝ => x ∘ σ) ⁻¹' A) ∪
        ((⋃ σ : Equiv.Perm (Fin n), C σ)ᶜ ∩ if (0 : Fin n → ℝ) ∈ A then Set.univ else ∅) := by
      ext x
      by_cases hex : ∃ σ : Equiv.Perm (Fin n), x ∈ C σ
      · obtain ⟨σ, hσ⟩ := hex
        have hmem : x ∈ ⋃ τ : Equiv.Perm (Fin n), C τ := Set.mem_iUnion.mpr ⟨σ, hσ⟩
        simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_compl_iff, hmem, not_true_eq_false, false_and, or_false]
        constructor
        · intro hfx
          refine ⟨σ, hσ, ?_⟩
          rwa [hf_on_C σ x hσ] at hfx
        · rintro ⟨τ, hτ, hAτ⟩
          rwa [hf_on_C τ x hτ]
      · have hnot : x ∉ ⋃ τ : Equiv.Perm (Fin n), C τ := by simpa using hex
        simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_compl_iff, hnot, not_false_eq_true, true_and, f, dif_neg hex]
        constructor
        · intro h0; right; simp [h0]
        · rintro (⟨τ, hτ, _⟩ | h0)
          · exact absurd ⟨τ, hτ⟩ hex
          · split_ifs at h0 with hA0
            · exact hA0
            · exact absurd h0 (Set.notMem_empty x)
    rw [hpre]
    refine MeasurableSet.union ?_ ?_
    · refine MeasurableSet.iUnion fun σ => (hC_meas σ).inter (hA.preimage ?_)
      exact measurable_pi_lambda _ fun i => measurable_pi_apply (σ i)
    · refine (MeasurableSet.iUnion hC_meas).compl.inter ?_
      split_ifs <;> measurability
  -- Show Vvec =ᵐ[P] f ∘ Uvec
  have hU_not_diag : ∀ᵐ ω ∂P, Uvec ω ∉ diagSet n := by
    rw [ae_iff]
    have hdiag_meas : MeasurableSet (diagSet n) := by
      unfold diagSet
      exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
        MeasurableSet.iUnion fun _ => measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
    have h0 : P (Uvec ⁻¹' diagSet n) = 0 := by
      rw [← Measure.map_apply_of_aemeasurable hUvec_ae hdiag_meas, hUvec_law]
      simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hdiag_meas]
      rw [measure_mono_null Set.inter_subset_left (volume_diagSet_zero n), mul_zero]
    simpa [Set.preimage] using h0
  have hV_ae_eq : Vvec =ᵐ[P] f ∘ Uvec := by
    filter_upwards [hV, hU_not_diag] with ω ⟨hVmono, hVperm⟩ hnd
    have hmem : Uvec ω ∈ (diagSet n)ᶜ := hnd
    rw [← hC_union, Set.mem_iUnion] at hmem
    obtain ⟨σ, hσ⟩ := hmem
    change Vvec ω = f (Uvec ω)
    rw [hf_on_C σ (Uvec ω) hσ]
    have hperm' : (List.ofFn (Vvec ω)).Perm (List.ofFn (Uvec ω ∘ σ)) :=
      hVperm.trans (list_ofFn_perm_comp (Uvec ω) σ).symm
    have hpw1 : (List.ofFn (Vvec ω)).Pairwise (· ≤ ·) :=
      List.pairwise_ofFn.mpr fun i j hij => hVmono (le_of_lt hij)
    have hpw2 : (List.ofFn (Uvec ω ∘ σ)).Pairwise (· ≤ ·) :=
      List.pairwise_ofFn.mpr fun i j hij => le_of_lt (hσ hij)
    exact List.ofFn_inj.mp (hperm'.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hab hba) hpw1 hpw2)
  -- Compute P.map Vvec A
  intro A hA
  rw [Measure.map_congr hV_ae_eq,
    Measure.map_apply_of_aemeasurable (hf_meas.comp_aemeasurable hUvec_ae) hA,
    Set.preimage_comp, ← Measure.map_apply_of_aemeasurable hUvec_ae (hf_meas hA), hUvec_law]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hf_meas hA)]
  -- Split (f ⁻¹' A) ∩ Q by removing diagSet n and decomposing over Equiv.Perm (Fin n)
  let Δ_strict : Set (Fin n → ℝ) := {v : Fin n → ℝ | (∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)) ∧ StrictMono v}
  have hΔs_meas : MeasurableSet Δ_strict := by
    have h1 : MeasurableSet {v : Fin n → ℝ | ∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)} := by
      have : {v : Fin n → ℝ | ∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)} =
          ⋂ i : Fin n, ({v : Fin n → ℝ | 0 ≤ v i} ∩ {v : Fin n → ℝ | v i ≤ (t : ℝ)}) := by ext v; simp
      rw [this]
      exact MeasurableSet.iInter fun i =>
        (measurableSet_le measurable_const (measurable_pi_apply i)).inter
        (measurableSet_le (measurable_pi_apply i) measurable_const)
    have h2 : MeasurableSet {v : Fin n → ℝ | StrictMono v} := by
      have : {v : Fin n → ℝ | StrictMono v} =
          ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), {v : Fin n → ℝ | v i < v j} := by
        ext v; simp [StrictMono]
      rw [this]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
    exact h1.inter h2
  have hdiag_meas : MeasurableSet (diagSet n) := by
    unfold diagSet
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun _ => measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
  have hvol_decomp : volume (f ⁻¹' A ∩ Q) =
      volume (⋃ σ : Equiv.Perm (Fin n), (fun x : Fin n → ℝ => x ∘ σ) ⁻¹' (A ∩ Δ_strict)) := by
    have h1 : volume (f ⁻¹' A ∩ Q) = volume ((f ⁻¹' A ∩ Q) \ diagSet n) := by
      rw [← measure_inter_add_diff (f ⁻¹' A ∩ Q) hdiag_meas]
      rw [measure_mono_null Set.inter_subset_right (volume_diagSet_zero n), zero_add]
    rw [h1]
    congr 1
    ext x
    simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨hfx, hxQ⟩, hnd⟩
      have hmem : x ∈ (diagSet n)ᶜ := hnd
      rw [← hC_union, Set.mem_iUnion] at hmem
      obtain ⟨σ, hσ⟩ := hmem
      refine ⟨σ, ?_, ?_, hσ⟩
      · rwa [hf_on_C σ x hσ] at hfx
      · intro i; exact hxQ (σ i) (Set.mem_univ _)
    · rintro ⟨σ, hAσ, hQσ, hσ⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rwa [hf_on_C σ x hσ]
      · intro i _
        have := hQσ (σ.symm i)
        simpa using this
      · have hmem : x ∈ ⋃ τ : Equiv.Perm (Fin n), C τ := Set.mem_iUnion.mpr ⟨σ, hσ⟩
        rwa [hC_union] at hmem
  rw [hvol_decomp]
  have hdisj_pieces : Pairwise (fun σ₁ σ₂ : Equiv.Perm (Fin n) =>
      Disjoint ((fun x : Fin n → ℝ => x ∘ σ₁) ⁻¹' (A ∩ Δ_strict))
               ((fun x : Fin n → ℝ => x ∘ σ₂) ⁻¹' (A ∩ Δ_strict))) := by
    intro σ₁ σ₂ hne
    refine (hC_disj hne).mono ?_ ?_
    · intro x hx; exact hx.2.2
    · intro x hx; exact hx.2.2
  rw [measure_iUnion hdisj_pieces (fun σ => (hA.inter hΔs_meas).preimage
    (measurable_pi_lambda _ fun i => measurable_pi_apply (σ i)))]
  have hpiece : ∀ σ : Equiv.Perm (Fin n),
      volume ((fun x : Fin n → ℝ => x ∘ σ) ⁻¹' (A ∩ Δ_strict)) = volume (A ∩ Δ_strict) := by
    intro σ
    have hmp := measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℝ)) σ.symm
    have heq_fn : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm)) =
        (fun x : Fin n → ℝ => x ∘ σ) := by
      ext x i
      have h := Equiv.piCongrLeft_apply_apply (fun _ : Fin n => ℝ) σ.symm x (σ i)
      simpa [MeasurableEquiv.piCongrLeft] using h
    rw [heq_fn, ← volume_pi] at hmp
    exact hmp.measure_preimage (hA.inter hΔs_meas).nullMeasurableSet
  simp_rw [hpiece, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]
  have hΔ_eq : volume (A ∩ Δ_strict) = volume (A ∩ closedSimplex n t) := by
    have hsub : A ∩ Δ_strict ⊆ A ∩ closedSimplex n t :=
      Set.inter_subset_inter_right A fun v ⟨hbd, hsm⟩ => ⟨hbd, hsm.monotone⟩
    have hdiff : (A ∩ closedSimplex n t) \ (A ∩ Δ_strict) ⊆ diagSet n := by
      intro v ⟨⟨_, ⟨_, hmono⟩⟩, hnot⟩
      by_contra hnd
      apply hnot
      refine ⟨‹_›, ‹_›, fun i j hij => lt_of_le_of_ne (hmono (le_of_lt hij)) ?_⟩
      intro heq
      exact hnd (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨ne_of_lt hij, heq⟩⟩⟩)
    have h0 : volume ((A ∩ closedSimplex n t) \ (A ∩ Δ_strict)) = 0 :=
      measure_mono_null hdiff (volume_diagSet_zero n)
    have hsum := measure_inter_add_sdiff (μ := volume) (A ∩ closedSimplex n t) (hA.inter hΔs_meas)
    rw [Set.inter_eq_right.mpr hsub, h0, add_zero] at hsum
    exact hsum
  rw [hΔ_eq, ← mul_assoc]
  congr 1
  have htn : (0 : ℝ) < (t : ℝ) ^ n := pow_pos ht n
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_inv_of_pos htn,
    ENNReal.ofReal_natCast, mul_comm]

end KyprianouEx22Helpers

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (hrate : 0 < rate)
    (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
    (hNlaw : ∀ t, P.map (N t) =
      ProbabilityTheory.poissonMeasure (rate * t))
    (hNlevy : ProbabilityTheory.IsLevyProcess
      (fun t ω => (N t ω : ℝ)) P)
    (harrival : ∀ᵐ ω ∂P, ∀ (n : ℕ), 0 < n →
      ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t)) :
    (∀ (t : ℝ≥0), 0 < t → ∀ (n : ℕ), 0 < n →
      ∀ (A : Set (Fin n → ℝ)), MeasurableSet A →
        P {ω | N t ω = n ∧
          (fun i : Fin n => ((T (i.val + 1) ω : ℝ))) ∈ A} =
        P {ω | N t ω = n} *
          ENNReal.ofReal ((Nat.factorial n : ℝ) / ((t : ℝ) ^ n)) *
          volume (A ∩
            {v : Fin n → ℝ |
              (∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)) ∧
              Monotone v})) ∧
    (∀ (t : ℝ≥0), 0 < t → ∀ (n : ℕ), 0 < n →
      ∀ (U V : Fin n → Ω → ℝ),
        (∀ i, P.map (U i) =
          (ENNReal.ofReal (t : ℝ))⁻¹ •
            (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)))) →
        ProbabilityTheory.iIndepFun U P →
        (∀ᵐ ω ∂P,
          Monotone (fun i : Fin n => V i ω) ∧
          (List.ofFn (fun i : Fin n => V i ω)).Perm
            (List.ofFn (fun i : Fin n => U i ω))) →
        ((P.restrict {ω | N t ω = n}).map
          (fun ω => fun i : Fin n => (T (i.val + 1) ω : ℝ))) =
        (P {ω | N t ω = n}) •
          (P.map (fun ω => fun i : Fin n => V i ω))) := by
  have hpart1 : ∀ (t : ℝ≥0), 0 < t → ∀ (n : ℕ), 0 < n →
      ∀ (A : Set (Fin n → ℝ)), MeasurableSet A →
        P {ω | N t ω = n ∧
          (fun i : Fin n => ((T (i.val + 1) ω : ℝ))) ∈ A} =
        P {ω | N t ω = n} *
          ENNReal.ofReal ((Nat.factorial n : ℝ) / ((t : ℝ) ^ n)) *
          volume (A ∩
            {v : Fin n → ℝ |
              (∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)) ∧
              Monotone v}) :=
    fun t ht n hn A hA =>
      KyprianouEx22Helpers.part_i_aux P rate N T hTmeas hNlaw hNlevy harrival t ht n hn A hA
  refine ⟨hpart1, fun t ht n hn U V hUlaw hUind hV => ?_⟩
  ext A hA
  have hΦmeas : Measurable (fun ω => fun i : Fin n => (T (i.val + 1) ω : ℝ)) :=
    measurable_pi_lambda _ fun i => NNReal.continuous_coe.measurable.comp (hTmeas (i.val + 1) (Nat.succ_pos _))
  rw [Measure.map_apply hΦmeas hA, Measure.restrict_apply (hΦmeas hA)]
  have hset : (fun ω => fun i : Fin n => (T (i.val + 1) ω : ℝ)) ⁻¹' A ∩ {ω | N t ω = n} =
      {ω | N t ω = n ∧ (fun i : Fin n => (T (i.val + 1) ω : ℝ)) ∈ A} := by
    ext ω; simp [and_comm]
  rw [hset, hpart1 t ht n hn A hA]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [KyprianouEx22Helpers.ordered_uniform_law P t ht n hn U V hUlaw hUind hV A hA, mul_assoc]
  rfl
