-- Prove2me | solution 1 for GoldieRenewal.Kesten.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:30:06.472333+00:00
-- url     : https://prove2.me/submissions/bc24540f-dc07-440a-81a2-eb746d0a2367

import Mathlib
import Definitions.Def_GoldieRenewal_Kesten_Perpetuity



namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! Generic partial products / sums of a sequence of pairs `(q, m)`. -/

def pP (g : ℕ → ℝ × ℝ) (l : ℕ) : ℝ := ∏ k ∈ Finset.range l, (g k).2
def pS (g : ℕ → ℝ × ℝ) (l : ℕ) : ℝ := ∑ i ∈ Finset.range l, pP g i * (g i).1
def pPF (g : ℕ → ℝ × ℝ) (j l : ℕ) : ℝ := ∏ k ∈ Finset.Ico j l, (g k).2
def pSF (g : ℕ → ℝ × ℝ) (j l : ℕ) : ℝ := ∑ i ∈ Finset.Ico j l, pPF g j i * (g i).1

lemma pP_eq (Q M : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) :
    pP (fun k => (Q k ω, M k ω)) l = piProd M l ω := rfl
lemma pS_eq (Q M : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) :
    pS (fun k => (Q k ω, M k ω)) l = partialSum Q M l ω := rfl
lemma pPF_eq (Q M : ℕ → Ω → ℝ) (j l : ℕ) (ω : Ω) :
    pPF (fun k => (Q k ω, M k ω)) j l = piProdFrom M j l ω := rfl
lemma pSF_eq (Q M : ℕ → Ω → ℝ) (j l : ℕ) (ω : Ω) :
    pSF (fun k => (Q k ω, M k ω)) j l = partialSumFrom Q M j l ω := rfl

/-- Extension of a tuple indexed by a finset to a sequence. -/
def extS (S : Finset ℕ) (v : (i : S) → ℝ × ℝ) (k : ℕ) : ℝ × ℝ :=
  if h : k ∈ S then v ⟨k, h⟩ else 0

lemma measurable_extS (S : Finset ℕ) (k : ℕ) :
    Measurable fun v : (i : S) → ℝ × ℝ => extS S v k := by
  unfold extS
  split_ifs with h
  · exact measurable_pi_apply (⟨k, h⟩ : {i // i ∈ S})
  · exact measurable_const

lemma measurable_pP (S : Finset ℕ) (l : ℕ) :
    Measurable fun v : (i : S) → ℝ × ℝ => pP (extS S v) l := by
  unfold pP
  exact Finset.measurable_prod _ (fun k _ => (measurable_extS S k).snd)

lemma measurable_pS (S : Finset ℕ) (l : ℕ) :
    Measurable fun v : (i : S) → ℝ × ℝ => pS (extS S v) l := by
  unfold pS
  exact Finset.measurable_sum _ (fun i _ => (measurable_pP S i).mul (measurable_extS S i).fst)

lemma measurable_pPF (S : Finset ℕ) (j l : ℕ) :
    Measurable fun v : (i : S) → ℝ × ℝ => pPF (extS S v) j l := by
  unfold pPF
  exact Finset.measurable_prod _ (fun k _ => (measurable_extS S k).snd)

lemma measurable_pSF (S : Finset ℕ) (j l : ℕ) :
    Measurable fun v : (i : S) → ℝ × ℝ => pSF (extS S v) j l := by
  unfold pSF
  exact Finset.measurable_sum _ (fun i _ => (measurable_pPF S j i).mul (measurable_extS S i).fst)

lemma extS_eq (f : ℕ → Ω → ℝ × ℝ) (S : Finset ℕ) (ω : Ω) (k : ℕ) (hk : k ∈ S) :
    extS S (fun i : S => f i ω) k = f k ω := by
  simp [extS, hk]

lemma pP_extS (f : ℕ → Ω → ℝ × ℝ) (S : Finset ℕ) (ω : Ω) (l : ℕ)
    (hl : ∀ k, k < l → k ∈ S) :
    pP (extS S (fun i : S => f i ω)) l = pP (fun k => f k ω) l := by
  unfold pP
  apply Finset.prod_congr rfl
  intro k hk
  rw [extS_eq _ _ _ _ (hl k (Finset.mem_range.mp hk))]

lemma pS_extS (f : ℕ → Ω → ℝ × ℝ) (S : Finset ℕ) (ω : Ω) (l : ℕ)
    (hl : ∀ k, k < l → k ∈ S) :
    pS (extS S (fun i : S => f i ω)) l = pS (fun k => f k ω) l := by
  unfold pS
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [pP_extS f S ω i (fun k hk => hl k (lt_trans hk hi')), extS_eq _ _ _ _ (hl i hi')]

lemma pPF_extS (f : ℕ → Ω → ℝ × ℝ) (S : Finset ℕ) (ω : Ω) (j l : ℕ)
    (hl : ∀ k, j ≤ k → k < l → k ∈ S) :
    pPF (extS S (fun i : S => f i ω)) j l = pPF (fun k => f k ω) j l := by
  unfold pPF
  apply Finset.prod_congr rfl
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  rw [extS_eq _ _ _ _ (hl k hk'.1 hk'.2)]

lemma pSF_extS (f : ℕ → Ω → ℝ × ℝ) (S : Finset ℕ) (ω : Ω) (j l : ℕ)
    (hl : ∀ k, j ≤ k → k < l → k ∈ S) :
    pSF (extS S (fun i : S => f i ω)) j l = pSF (fun k => f k ω) j l := by
  unfold pSF
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  rw [pPF_extS f S ω j i (fun k hk1 hk2 => hl k hk1 (lt_trans hk2 hi'.2)),
    extS_eq _ _ _ _ (hl i hi'.1 hi'.2)]

/-! Splitting identities. -/

lemma piProd_split (M : ℕ → Ω → ℝ) {j n : ℕ} (hjn : j ≤ n) (ω : Ω) :
    piProd M n ω = piProd M j ω * piProdFrom M j n ω := by
  unfold piProd piProdFrom
  exact (Finset.prod_range_mul_prod_Ico _ hjn).symm

lemma partialSum_split (Q M : ℕ → Ω → ℝ) {j n : ℕ} (hjn : j ≤ n) (ω : Ω) :
    partialSum Q M n ω = partialSum Q M j ω + piProd M j ω * partialSumFrom Q M j n ω := by
  unfold partialSum partialSumFrom
  rw [← Finset.sum_range_add_sum_Ico _ hjn, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Ico] at hi
  rw [piProd_split M hi.1 ω]
  ring

lemma measurable_piProd (M : ℕ → Ω → ℝ) (hM : ∀ i, Measurable (M i)) (l : ℕ) :
    Measurable (piProd M l) := by
  unfold piProd
  exact Finset.measurable_prod _ (fun k _ => hM k)

lemma measurable_partialSum (Q M : ℕ → Ω → ℝ) (hQ : ∀ i, Measurable (Q i))
    (hM : ∀ i, Measurable (M i)) (l : ℕ) : Measurable (partialSum Q M l) := by
  unfold partialSum
  exact Finset.measurable_sum _ (fun i _ => (measurable_piProd M hM i).mul (hQ i))

lemma measurable_piProdFrom (M : ℕ → Ω → ℝ) (hM : ∀ i, Measurable (M i)) (j l : ℕ) :
    Measurable (piProdFrom M j l) := by
  unfold piProdFrom
  exact Finset.measurable_prod _ (fun k _ => hM k)

lemma measurable_partialSumFrom (Q M : ℕ → Ω → ℝ) (hQ : ∀ i, Measurable (Q i))
    (hM : ∀ i, Measurable (M i)) (j l : ℕ) : Measurable (partialSumFrom Q M j l) := by
  unfold partialSumFrom
  exact Finset.measurable_sum _ (fun i _ => (measurable_piProdFrom M hM j i).mul (hQ i))

theorem proposition_4_2_core (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (ℝ × ℝ)) (Q M : ℕ → Ω → ℝ) (hQ : ∀ i, Measurable (Q i))
    (hM : ∀ i, Measurable (M i))
    (hindep : iIndepFun (fun i ω => (Q i ω, M i ω)) P)
    (hlaw : ∀ i, P.map (fun ω => (Q i ω, M i ω)) = μ)
    (n : ℕ) (x y : ℝ) (med : ℕ → ℝ)
    (hmed : ∀ j ∈ Finset.Icc 1 n,
      IsMedian (P.map (fun ω => partialSumFrom Q M j n ω + piProdFrom M j n ω * y)) (med j)) :
    P {ω | ∃ j ∈ Finset.Icc 1 n, x < partialSum Q M j ω + piProd M j ω * med j}
      ≤ 2 * P {ω | x < partialSum Q M n ω + piProd M n ω * y} := by
  classical
  set f : ℕ → Ω → ℝ × ℝ := fun i ω => (Q i ω, M i ω) with hf
  have hfm : ∀ i, Measurable (f i) := fun i => (hQ i).prodMk (hM i)
  -- the walk, the future and the first-passage events
  set S : ℕ → Ω → ℝ := fun j ω => partialSum Q M j ω + piProd M j ω * med j with hS
  set Z : ℕ → Ω → ℝ := fun j ω => partialSumFrom Q M j n ω + piProdFrom M j n ω * y with hZ
  have mS : ∀ j, Measurable (S j) := fun j =>
    (measurable_partialSum Q M hQ hM j).add ((measurable_piProd M hM j).mul_const _)
  have mZ : ∀ j, Measurable (Z j) := fun j =>
    (measurable_partialSumFrom Q M hQ hM j n).add
      ((measurable_piProdFrom M hM j n).mul_const _)
  set E : ℕ → Set Ω := fun j => {ω | x < S j ω ∧ ∀ i ∈ Finset.Ico 1 j, S i ω ≤ x} with hE
  set Gp : ℕ → Set Ω := fun j => {ω | 0 ≤ piProd M j ω} ∩ {ω | med j ≤ Z j ω} with hGp
  set Gn : ℕ → Set Ω := fun j => {ω | piProd M j ω < 0} ∩ {ω | Z j ω ≤ med j} with hGn
  set Tg : Set Ω := {ω | x < partialSum Q M n ω + piProd M n ω * y} with hTg
  have mE : ∀ j, MeasurableSet (E j) := by
    intro j
    have h1 : MeasurableSet {ω | x < S j ω} := measurableSet_lt measurable_const (mS j)
    have h2 : MeasurableSet {ω | ∀ i ∈ Finset.Ico 1 j, S i ω ≤ x} := by
      have : {ω | ∀ i ∈ Finset.Ico 1 j, S i ω ≤ x} = ⋂ i ∈ Finset.Ico 1 j, {ω | S i ω ≤ x} := by
        ext ω; simp
      rw [this]
      exact Finset.measurableSet_biInter _ (fun i _ => measurableSet_le (mS i) measurable_const)
    exact h1.inter h2
  have mGp : ∀ j, MeasurableSet (Gp j) := fun j =>
    (measurableSet_le measurable_const (measurable_piProd M hM j)).inter
      (measurableSet_le measurable_const (mZ j))
  have mGn : ∀ j, MeasurableSet (Gn j) := fun j =>
    (measurableSet_lt (measurable_piProd M hM j) measurable_const).inter
      (measurableSet_le (mZ j) measurable_const)
  -- Step 1: the max event is the disjoint union of the first-passage events
  have hunion : {ω | ∃ j ∈ Finset.Icc 1 n, x < partialSum Q M j ω + piProd M j ω * med j}
      = ⋃ j ∈ Finset.Icc 1 n, E j := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨j, hj, hx⟩
      have hex : ∃ j, 1 ≤ j ∧ j ≤ n ∧ x < S j ω := ⟨j, (Finset.mem_Icc.mp hj).1,
        (Finset.mem_Icc.mp hj).2, hx⟩
      refine ⟨Nat.find hex, Finset.mem_Icc.mpr ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2.1⟩,
        (Nat.find_spec hex).2.2, ?_⟩
      intro i hi
      rw [Finset.mem_Ico] at hi
      by_contra hcon
      push_neg at hcon
      exact Nat.find_min hex hi.2 ⟨hi.1, by linarith [(Nat.find_spec hex).2.1], hcon⟩
    · rintro ⟨j, hj, hx, _⟩
      exact ⟨j, hj, hx⟩
  have hdisj : (↑(Finset.Icc 1 n) : Set ℕ).PairwiseDisjoint E := by
    intro j hj j' hj' hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [hE, Set.mem_ofPred_eq] at h1 h2
    rcases lt_or_gt_of_ne hne with h | h
    · have := h2.2 j (Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_coe.mp hj)).1, h⟩)
      linarith [h1.1]
    · have := h1.2 j' (Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_coe.mp hj')).1, h⟩)
      linarith [h2.1]
  -- Step 2: the good events lie in the target
  have hsub : ∀ j ∈ Finset.Icc 1 n, (E j ∩ Gp j) ∪ (E j ∩ Gn j) ⊆ Tg := by
    intro j hj ω hω
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    simp only [hTg, Set.mem_ofPred_eq]
    rw [partialSum_split Q M hjn ω, piProd_split M hjn ω]
    have key : partialSum Q M j ω + piProd M j ω * partialSumFrom Q M j n ω +
        piProd M j ω * piProdFrom M j n ω * y = partialSum Q M j ω + piProd M j ω * Z j ω := by
      simp only [hZ]; ring
    rw [key]
    rcases hω with ⟨hEj, hp, hz⟩ | ⟨hEj, hp, hz⟩
    · simp only [hE, Set.mem_ofPred_eq] at hEj hp hz
      have : piProd M j ω * med j ≤ piProd M j ω * Z j ω := mul_le_mul_of_nonneg_left hz hp
      linarith [hEj.1]
    · simp only [hE, Set.mem_ofPred_eq] at hEj hp hz
      have : piProd M j ω * med j ≤ piProd M j ω * Z j ω :=
        mul_le_mul_of_nonpos_left hz hp.le
      linarith [hEj.1]
  -- Step 3: independence bound for each j
  have hhalf : ∀ j ∈ Finset.Icc 1 n, P (E j) ≤ 2 * P ((E j ∩ Gp j) ∪ (E j ∩ Gn j)) := by
    intro j hj
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    set Sf : Finset ℕ := Finset.range j with hSf
    set Tf : Finset ℕ := Finset.Ico j n with hTf
    have hST : Disjoint Sf Tf := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      rw [hSf, Finset.mem_range] at hk
      rw [hTf, Finset.mem_Ico] at hk'
      omega
    have hI := hindep.indepFun_finset Sf Tf hST hfm
    set past : Ω → ((i : Sf) → ℝ × ℝ) := fun ω i => f i ω with hpast
    set fut : Ω → ((i : Tf) → ℝ × ℝ) := fun ω i => f i ω with hfut
    -- the sets
    set Ap : Set ((i : Sf) → ℝ × ℝ) := {v | (x < pS (extS Sf v) j + pP (extS Sf v) j * med j ∧
        ∀ i ∈ Finset.Ico 1 j, pS (extS Sf v) i + pP (extS Sf v) i * med i ≤ x) ∧
        0 ≤ pP (extS Sf v) j} with hAp
    set An : Set ((i : Sf) → ℝ × ℝ) := {v | (x < pS (extS Sf v) j + pP (extS Sf v) j * med j ∧
        ∀ i ∈ Finset.Ico 1 j, pS (extS Sf v) i + pP (extS Sf v) i * med i ≤ x) ∧
        pP (extS Sf v) j < 0} with hAn
    set Bp : Set ((i : Tf) → ℝ × ℝ) :=
      {v | med j ≤ pSF (extS Tf v) j n + pPF (extS Tf v) j n * y} with hBp
    set Bn : Set ((i : Tf) → ℝ × ℝ) :=
      {v | pSF (extS Tf v) j n + pPF (extS Tf v) j n * y ≤ med j} with hBn
    have mSj : Measurable fun v : (i : Sf) → ℝ × ℝ => pS (extS Sf v) j + pP (extS Sf v) j * med j :=
      (measurable_pS Sf j).add ((measurable_pP Sf j).mul_const _)
    have mSi : ∀ i, Measurable fun v : (i : Sf) → ℝ × ℝ =>
        pS (extS Sf v) i + pP (extS Sf v) i * med i := fun i =>
      (measurable_pS Sf i).add ((measurable_pP Sf i).mul_const _)
    have mZT : Measurable fun v : (i : Tf) → ℝ × ℝ =>
        pSF (extS Tf v) j n + pPF (extS Tf v) j n * y :=
      (measurable_pSF Tf j n).add ((measurable_pPF Tf j n).mul_const _)
    have mA0 : MeasurableSet {v : (i : Sf) → ℝ × ℝ |
        x < pS (extS Sf v) j + pP (extS Sf v) j * med j ∧
        ∀ i ∈ Finset.Ico 1 j, pS (extS Sf v) i + pP (extS Sf v) i * med i ≤ x} := by
      have h2 : MeasurableSet {v : (i : Sf) → ℝ × ℝ | ∀ i ∈ Finset.Ico 1 j,
          pS (extS Sf v) i + pP (extS Sf v) i * med i ≤ x} := by
        have : {v : (i : Sf) → ℝ × ℝ | ∀ i ∈ Finset.Ico 1 j,
            pS (extS Sf v) i + pP (extS Sf v) i * med i ≤ x}
            = ⋂ i ∈ Finset.Ico 1 j, {v | pS (extS Sf v) i + pP (extS Sf v) i * med i ≤ x} := by
          ext v; simp
        rw [this]
        exact Finset.measurableSet_biInter _ (fun i _ => measurableSet_le (mSi i) measurable_const)
      exact (measurableSet_lt measurable_const mSj).inter h2
    have mAp : MeasurableSet Ap :=
      mA0.inter (measurableSet_le measurable_const (measurable_pP Sf j))
    have mAn : MeasurableSet An :=
      mA0.inter (measurableSet_lt (measurable_pP Sf j) measurable_const)
    have mBp : MeasurableSet Bp := measurableSet_le measurable_const mZT
    have mBn : MeasurableSet Bn := measurableSet_le mZT measurable_const
    -- identification of the preimages
    have hlS : ∀ l, l ≤ j → ∀ k, k < l → k ∈ Sf := fun l hl k hk =>
      Finset.mem_range.mpr (lt_of_lt_of_le hk hl)
    have hlT : ∀ k, j ≤ k → k < n → k ∈ Tf := fun k h1 h2 => Finset.mem_Ico.mpr ⟨h1, h2⟩
    have evS : ∀ ω, ∀ l, l ≤ j →
        pS (extS Sf (past ω)) l + pP (extS Sf (past ω)) l * med l = S l ω := by
      intro ω l hl
      simp only [hpast]
      rw [pS_extS f Sf ω l (hlS l hl), pP_extS f Sf ω l (hlS l hl)]
      rfl
    have evP : ∀ ω, pP (extS Sf (past ω)) j = piProd M j ω := by
      intro ω
      simp only [hpast]
      rw [pP_extS f Sf ω j (hlS j le_rfl)]
      rfl
    have evZ : ∀ ω, pSF (extS Tf (fut ω)) j n + pPF (extS Tf (fut ω)) j n * y = Z j ω := by
      intro ω
      simp only [hfut]
      rw [pSF_extS f Tf ω j n hlT, pPF_extS f Tf ω j n hlT]
      rfl
    have preAp : past ⁻¹' Ap = E j ∩ {ω | 0 ≤ piProd M j ω} := by
      ext ω
      simp only [Set.mem_preimage, hAp, hE, Set.mem_ofPred_eq, Set.mem_inter_iff]
      rw [evS ω j le_rfl, evP ω]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, fun i hi => ?_⟩, h3⟩
        have := h2 i hi
        rwa [evS ω i (Finset.mem_Ico.mp hi).2.le] at this
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, fun i hi => ?_⟩, h3⟩
        rw [evS ω i (Finset.mem_Ico.mp hi).2.le]
        exact h2 i hi
    have preAn : past ⁻¹' An = E j ∩ {ω | piProd M j ω < 0} := by
      ext ω
      simp only [Set.mem_preimage, hAn, hE, Set.mem_ofPred_eq, Set.mem_inter_iff]
      rw [evS ω j le_rfl, evP ω]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, fun i hi => ?_⟩, h3⟩
        have := h2 i hi
        rwa [evS ω i (Finset.mem_Ico.mp hi).2.le] at this
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, fun i hi => ?_⟩, h3⟩
        rw [evS ω i (Finset.mem_Ico.mp hi).2.le]
        exact h2 i hi
    have preBp : fut ⁻¹' Bp = {ω | med j ≤ Z j ω} := by
      ext ω
      simp only [Set.mem_preimage, hBp, Set.mem_ofPred_eq]
      rw [evZ ω]
    have preBn : fut ⁻¹' Bn = {ω | Z j ω ≤ med j} := by
      ext ω
      simp only [Set.mem_preimage, hBn, Set.mem_ofPred_eq]
      rw [evZ ω]
    -- the median bounds
    have hmedj := hmed j hj
    have hZp : (2 : ℝ≥0∞)⁻¹ ≤ P {ω | med j ≤ Z j ω} := by
      have := hmedj.1
      rw [Measure.map_apply (mZ j) measurableSet_Ici] at this
      exact this
    have hZn : (2 : ℝ≥0∞)⁻¹ ≤ P {ω | Z j ω ≤ med j} := by
      have := hmedj.2
      rw [Measure.map_apply (mZ j) measurableSet_Iic] at this
      exact this
    -- independence
    have hind := indepFun_iff_measure_inter_preimage_eq_mul.mp hI
    have ip := hind Ap Bp mAp mBp
    have inn := hind An Bn mAn mBn
    rw [preAp, preBp] at ip
    rw [preAn, preBn] at inn
    -- E j ∩ Gp j and E j ∩ Gn j
    have eGp : E j ∩ Gp j = (E j ∩ {ω | 0 ≤ piProd M j ω}) ∩ {ω | med j ≤ Z j ω} := by
      simp only [hGp]; rw [Set.inter_assoc]
    have eGn : E j ∩ Gn j = (E j ∩ {ω | piProd M j ω < 0}) ∩ {ω | Z j ω ≤ med j} := by
      simp only [hGn]; rw [Set.inter_assoc]
    have bp : (2 : ℝ≥0∞)⁻¹ * P (E j ∩ {ω | 0 ≤ piProd M j ω}) ≤ P (E j ∩ Gp j) := by
      rw [eGp, ip, mul_comm]
      gcongr
    have bn : (2 : ℝ≥0∞)⁻¹ * P (E j ∩ {ω | piProd M j ω < 0}) ≤ P (E j ∩ Gn j) := by
      rw [eGn, inn, mul_comm]
      gcongr
    -- E j splits
    have hEsplit : P (E j) = P (E j ∩ {ω | 0 ≤ piProd M j ω}) + P (E j ∩ {ω | piProd M j ω < 0}) := by
      rw [← measure_union]
      · congr 1
        ext ω
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · intro h
          rcases le_or_gt 0 (piProd M j ω) with h' | h'
          · exact Or.inl ⟨h, h'⟩
          · exact Or.inr ⟨h, h'⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · rw [Set.disjoint_left]
        rintro ω ⟨_, h1⟩ ⟨_, h2⟩
        simp only [Set.mem_ofPred_eq] at h1 h2
        linarith
      · exact (mE j).inter (measurableSet_lt (measurable_piProd M hM j) measurable_const)
    have hGsplit : P ((E j ∩ Gp j) ∪ (E j ∩ Gn j)) = P (E j ∩ Gp j) + P (E j ∩ Gn j) := by
      apply measure_union
      · rw [Set.disjoint_left]
        rintro ω ⟨_, h1, _⟩ ⟨_, h2, _⟩
        simp only [Set.mem_ofPred_eq] at h1 h2
        linarith
      · exact (mE j).inter (mGn j)
    rw [hGsplit, hEsplit]
    calc P (E j ∩ {ω | 0 ≤ piProd M j ω}) + P (E j ∩ {ω | piProd M j ω < 0})
        = 2 * ((2 : ℝ≥0∞)⁻¹ * P (E j ∩ {ω | 0 ≤ piProd M j ω}) +
            (2 : ℝ≥0∞)⁻¹ * P (E j ∩ {ω | piProd M j ω < 0})) := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
            one_mul, one_mul]
      _ ≤ 2 * (P (E j ∩ Gp j) + P (E j ∩ Gn j)) := by
          gcongr
  -- Step 4: assemble
  rw [hunion, measure_biUnion_finset hdisj (fun j _ => mE j)]
  have hdisj2 : (↑(Finset.Icc 1 n) : Set ℕ).PairwiseDisjoint
      (fun j => (E j ∩ Gp j) ∪ (E j ∩ Gn j)) := by
    intro j hj j' hj' hne
    have := hdisj hj hj' hne
    rw [Function.onFun] at this ⊢
    refine Disjoint.mono ?_ ?_ this
    · intro ω hω; rcases hω with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
    · intro ω hω; rcases hω with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
  calc ∑ j ∈ Finset.Icc 1 n, P (E j)
      ≤ ∑ j ∈ Finset.Icc 1 n, 2 * P ((E j ∩ Gp j) ∪ (E j ∩ Gn j)) :=
        Finset.sum_le_sum hhalf
    _ = 2 * ∑ j ∈ Finset.Icc 1 n, P ((E j ∩ Gp j) ∪ (E j ∩ Gn j)) := by
        rw [Finset.mul_sum]
    _ = 2 * P (⋃ j ∈ Finset.Icc 1 n, (E j ∩ Gp j) ∪ (E j ∩ Gn j)) := by
        rw [measure_biUnion_finset hdisj2
          (fun j _ => ((mE j).inter (mGp j)).union ((mE j).inter (mGn j)))]
    _ ≤ 2 * P Tg := by
        gcongr
        apply Set.iUnion₂_subset
        intro j hj
        exact hsub j hj

end GoldieRenewal.Kesten

open GoldieRenewal.Kesten
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (ℝ × ℝ)) (Q M : ℕ → Ω → ℝ) (hQ : ∀ i, Measurable (Q i))
    (hM : ∀ i, Measurable (M i))
    (hindep : iIndepFun (fun i ω => (Q i ω, M i ω)) P)
    (hlaw : ∀ i, P.map (fun ω => (Q i ω, M i ω)) = μ)
    (n : ℕ) (x y : ℝ) (med : ℕ → ℝ)
    (hmed : ∀ j ∈ Finset.Icc 1 n,
      IsMedian (P.map (fun ω => partialSumFrom Q M j n ω + piProdFrom M j n ω * y)) (med j)) :
    P {ω | ∃ j ∈ Finset.Icc 1 n, x < partialSum Q M j ω + piProd M j ω * med j}
      ≤ 2 * P {ω | x < partialSum Q M n ω + piProd M n ω * y} := by
  exact proposition_4_2_core P μ Q M hQ hM hindep hlaw n x y med hmed
