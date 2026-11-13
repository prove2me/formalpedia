-- Prove2me | solution 1 for MultiwayGap2325.Main.exists_nonOppositeCut_of_tendsto_gapSequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:09:55.318619+00:00
-- url     : https://prove2.me/submissions/455df648-bb0d-46c8-adb6-63f904d86ee3

import Mathlib
import Definitions.Def_MultiwayCut_Instance
import Definitions.Def_MultiwayGap2325_Main_RandomCuts
import Theorems.Thm_MultiwayGap2325_Main_gap_sequence_well_posed

section
set_option autoImplicit false

namespace MultiwayGap2325.Dev.CKR

open MeasureTheory Finset

/-! ## Combinatorics of the CKR rounding on Boolean "ball" vectors -/

section Comb

variable {m : ℕ}

/-- the set of admissible positions: the last one, or one whose ball captures the point -/
def posSet (σ : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool) : Finset (Fin (m + 1)) :=
  univ.filter fun j => j = Fin.last m ∨ b (σ j) = true

lemma posSet_nonempty (σ : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool) :
    (posSet σ b).Nonempty :=
  ⟨Fin.last m, by simp [posSet]⟩

/-- the capturing position -/
def pos (σ : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool) : Fin (m + 1) :=
  (posSet σ b).min' (posSet_nonempty σ b)

/-- the label chosen by the rounding -/
def labelOf (σ : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool) : Fin (m + 1) :=
  σ (pos σ b)

lemma pos_spec (σ : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool) :
    pos σ b = Fin.last m ∨ b (σ (pos σ b)) = true := by
  have := (posSet σ b).min'_mem (posSet_nonempty σ b)
  exact (Finset.mem_filter.mp this).2

lemma pos_le (σ : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool) (j : Fin (m + 1))
    (hj : j = Fin.last m ∨ b (σ j) = true) : pos σ b ≤ j :=
  (posSet σ b).min'_le j (by simp [posSet, hj])

/-- the event `A_i`: the first capturing ball (before the last position) is ball `i`,
and it separates the two points -/
def Aprop (bu bw : Fin (m + 1) → Bool) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin (m + 1)) :
    Prop :=
  σ⁻¹ i ≠ Fin.last m ∧ bu i ≠ bw i ∧
    ∀ j, j < σ⁻¹ i → bu (σ j) = false ∧ bw (σ j) = false

lemma Aprop_symm (bu bw : Fin (m + 1) → Bool) (σ : Equiv.Perm (Fin (m + 1)))
    (i : Fin (m + 1)) : Aprop bu bw σ i ↔ Aprop bw bu σ i := by
  unfold Aprop
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, Ne.symm h2, fun j hj => (h3 j hj).symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, Ne.symm h2, fun j hj => (h3 j hj).symm⟩

lemma exists_Aprop_of_lt (bu bw : Fin (m + 1) → Bool) (σ : Equiv.Perm (Fin (m + 1)))
    (h : pos σ bu < pos σ bw) : Aprop bu bw σ (σ (pos σ bu)) := by
  have hlast : pos σ bu ≠ Fin.last m := by
    intro he
    have := Fin.le_last (pos σ bw)
    rw [he] at h
    exact absurd h (not_lt.mpr this)
  have hu : bu (σ (pos σ bu)) = true := (pos_spec σ bu).resolve_left hlast
  refine ⟨by simpa using hlast, ?_, ?_⟩
  · rw [hu]
    intro hw
    have := pos_le σ bw (pos σ bu) (Or.inr hw.symm)
    exact absurd h (not_lt.mpr this)
  · intro j hj
    simp at hj
    constructor
    · by_contra hc
      have := pos_le σ bu j (Or.inr (by simpa using hc))
      exact absurd hj (not_lt.mpr this)
    · by_contra hc
      have := pos_le σ bw j (Or.inr (by simpa using hc))
      exact absurd (hj.trans h) (not_lt.mpr this)

lemma exists_Aprop (bu bw : Fin (m + 1) → Bool) (σ : Equiv.Perm (Fin (m + 1)))
    (h : labelOf σ bu ≠ labelOf σ bw) : ∃ i, Aprop bu bw σ i := by
  have hp : pos σ bu ≠ pos σ bw := fun he => h (by simp [labelOf, he])
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · exact ⟨_, exists_Aprop_of_lt bu bw σ hlt⟩
  · exact ⟨_, (Aprop_symm _ _ _ _).mpr (exists_Aprop_of_lt bw bu σ hgt)⟩

lemma Aprop_lt (bu bw : Fin (m + 1) → Bool) (σ : Equiv.Perm (Fin (m + 1)))
    (i l : Fin (m + 1)) (hil : i ≠ l) (hball : bu l = true ∨ bw l = true)
    (hA : Aprop bu bw σ i) : σ⁻¹ i < σ⁻¹ l := by
  by_contra hc
  push Not at hc
  have hne : σ⁻¹ l ≠ σ⁻¹ i := fun he => hil (σ⁻¹.injective he).symm
  have := hA.2.2 (σ⁻¹ l) (lt_of_le_of_ne hc hne)
  simp at this
  rcases hball with hb | hb <;> simp_all

lemma Aprop_disjoint (bu bw : Fin (m + 1) → Bool) (σ : Equiv.Perm (Fin (m + 1)))
    (i l : Fin (m + 1)) (hil : i ≠ l) (hball : bu l = true ∨ bw l = true)
    (hA : Aprop bu bw σ i) (hA' : Aprop bu bw (Equiv.swap i l * σ) i) : False := by
  have h1 := Aprop_lt bu bw σ i l hil hball hA
  have h2 := Aprop_lt bu bw _ i l hil hball hA'
  simp only [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right] at h2
  exact absurd h1 (not_lt.mpr h2.le)

lemma labelOf_single (σ : Equiv.Perm (Fin (m + 1))) (i : Fin (m + 1)) :
    labelOf σ (fun j => decide (j = i)) = i := by
  have h1 := pos_le σ (fun j => decide (j = i)) (σ⁻¹ i) (Or.inr (by simp))
  rcases pos_spec σ (fun j => decide (j = i)) with h | h
  · rw [h] at h1
    have : σ⁻¹ i = Fin.last m := le_antisymm (Fin.le_last _) h1
    simp [labelOf, h, ← this]
  · simpa [labelOf] using h

end Comb

/-! ## The threshold side -/

section Analytic

variable {m : ℕ}

/-- which balls of radius `ρ` (around the simplex vertices) contain the point `a` -/
noncomputable def bv (a : Fin (m + 1) → ℝ) (ρ : ℝ) : Fin (m + 1) → Bool :=
  fun i => decide (1 - a i ≤ ρ)

/-- the uniform measure on `(0,1)` -/
noncomputable abbrev μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

instance : IsProbabilityMeasure μ := ⟨by simp⟩

lemma meas_bv (a : Fin (m + 1) → ℝ) : Measurable (bv a) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine measurable_to_countable' fun c => ?_
  cases c
  · have : (fun ρ => bv a ρ i) ⁻¹' {false} = Set.Iio (1 - a i) := by
      ext ρ; simp [bv, lt_sub_iff_add_lt]
    rw [this]; exact measurableSet_Iio
  · have : (fun ρ => bv a ρ i) ⁻¹' {true} = Set.Ici (1 - a i) := by
      ext ρ; simp [bv]
    rw [this]; exact measurableSet_Ici

lemma meas_set (a b : Fin (m + 1) → ℝ)
    (Q : (Fin (m + 1) → Bool) → (Fin (m + 1) → Bool) → Prop) :
    MeasurableSet {ρ | Q (bv a ρ) (bv b ρ)} := by
  have hm : Measurable fun ρ => (bv a ρ, bv b ρ) := (meas_bv a).prodMk (meas_bv b)
  exact hm (Set.toFinite {p : (Fin (m + 1) → Bool) × (Fin (m + 1) → Bool) | Q p.1 p.2}).measurableSet

lemma ball_l (a b : Fin (m + 1) → ℝ) (i l : Fin (m + 1))
    (hl : max (a i) (b i) ≤ max (a l) (b l)) (ρ : ℝ) (h : bv a ρ i ≠ bv b ρ i) :
    bv a ρ l = true ∨ bv b ρ l = true := by
  have h' : 1 - a i ≤ ρ ∨ 1 - b i ≤ ρ := by
    by_contra hc
    push Not at hc
    apply h
    simp [bv, not_le.mpr hc.1, not_le.mpr hc.2]
  simp only [bv, decide_eq_true_eq]
  rcases le_total (a l) (b l) with hab | hab
  · rw [max_eq_right hab] at hl
    right
    rcases h' with h' | h' <;> linarith [le_max_left (a i) (b i), le_max_right (a i) (b i)]
  · rw [max_eq_left hab] at hl
    left
    rcases h' with h' | h' <;> linarith [le_max_left (a i) (b i), le_max_right (a i) (b i)]

lemma S_meas_le (a b : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    μ.real {ρ | bv a ρ i ≠ bv b ρ i} ≤ |a i - b i| := by
  have hsub : {ρ | bv a ρ i ≠ bv b ρ i} ⊆
      Set.Ico (1 - max (a i) (b i)) (1 - min (a i) (b i)) := by
    intro ρ hρ
    simp only [Set.mem_ofPred_eq, bv, ne_eq, decide_eq_decide] at hρ
    simp only [Set.mem_Ico]
    by_cases h1 : 1 - a i ≤ ρ
    · have h2 : ¬ 1 - b i ≤ ρ := fun h2 => hρ ⟨fun _ => h2, fun _ => h1⟩
      push Not at h2
      constructor
      · linarith [le_max_left (a i) (b i)]
      · linarith [min_le_right (a i) (b i)]
    · have h2 : 1 - b i ≤ ρ := by
        by_contra h2
        exact hρ ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      push Not at h1
      constructor
      · linarith [le_max_right (a i) (b i)]
      · linarith [min_le_left (a i) (b i)]
  have hle : μ {ρ | bv a ρ i ≠ bv b ρ i} ≤ ENNReal.ofReal |a i - b i| := by
    calc μ {ρ | bv a ρ i ≠ bv b ρ i} ≤ volume {ρ | bv a ρ i ≠ bv b ρ i} :=
          Measure.restrict_apply_le _ _
      _ ≤ volume (Set.Ico (1 - max (a i) (b i)) (1 - min (a i) (b i))) := measure_mono hsub
      _ = ENNReal.ofReal |a i - b i| := by
          rw [Real.volume_Ico, ← max_sub_min_eq_abs]
          congr 1
          rw [max_comm (b i), min_comm (b i)]
          ring
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this

lemma abs_le_halfL1 (a b : Fin (m + 1) → ℝ) (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1)
    (l : Fin (m + 1)) : |a l - b l| ≤ MultiwayCut.halfL1 a b := by
  unfold MultiwayCut.halfL1
  have h0 : ∑ i, (a i - b i) = 0 := by rw [Finset.sum_sub_distrib, ha, hb]; ring
  have e1 := Finset.add_sum_erase univ (fun i => a i - b i) (mem_univ l)
  have e2 := Finset.add_sum_erase univ (fun i => |a i - b i|) (mem_univ l)
  have h3 : |∑ i ∈ univ.erase l, (a i - b i)| ≤ ∑ i ∈ univ.erase l, |a i - b i| :=
    Finset.abs_sum_le_sum_abs _ _
  have h4 : ∑ i ∈ univ.erase l, (a i - b i) = -(a l - b l) := by linarith
  rw [h4, abs_neg] at h3
  linarith

lemma edge_bound (a b : Fin (m + 1) → ℝ) (ha : a ∈ stdSimplex ℝ (Fin (m + 1)))
    (hb : b ∈ stdSimplex ℝ (Fin (m + 1))) :
    ∑ σ : Equiv.Perm (Fin (m + 1)), μ.real {ρ | labelOf σ (bv a ρ) ≠ labelOf σ (bv b ρ)} ≤
      (Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ) * (3 / 2 * MultiwayCut.halfL1 a b) := by
  obtain ⟨l, -, hl⟩ := Finset.exists_max_image univ (fun i => max (a i) (b i)) univ_nonempty
  set N : ℝ := (Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  let A : Fin (m + 1) → Equiv.Perm (Fin (m + 1)) → Set ℝ :=
    fun i σ => {ρ | Aprop (bv a ρ) (bv b ρ) σ i}
  have h1 : ∀ σ : Equiv.Perm (Fin (m + 1)),
      μ.real {ρ | labelOf σ (bv a ρ) ≠ labelOf σ (bv b ρ)} ≤ ∑ i, μ.real (A i σ) := by
    intro σ
    refine (measureReal_mono ?_).trans (measureReal_iUnion_fintype_le _)
    intro ρ hρ
    simp only [Set.mem_iUnion]
    exact exists_Aprop _ _ σ hρ
  have hAS : ∀ i σ, A i σ ⊆ {ρ | bv a ρ i ≠ bv b ρ i} := fun i σ ρ hρ => hρ.2.1
  have hS : ∀ i σ, μ.real (A i σ) ≤ |a i - b i| := fun i σ =>
    (measureReal_mono (hAS i σ)).trans (S_meas_le a b i)
  have h2 : ∀ i, i ≠ l → ∑ σ, μ.real (A i σ) ≤ N / 2 * |a i - b i| := by
    intro i hil
    have e : ∑ σ, μ.real (A i σ) = ∑ σ, μ.real (A i (Equiv.swap i l * σ)) :=
      (Equiv.sum_comp (Equiv.mulLeft (Equiv.swap i l)) (fun σ => μ.real (A i σ))).symm
    have hpair : ∀ σ, μ.real (A i σ) + μ.real (A i (Equiv.swap i l * σ)) ≤ |a i - b i| := by
      intro σ
      have hmeas : MeasurableSet (A i (Equiv.swap i l * σ)) :=
        meas_set a b (fun bu bw => Aprop bu bw (Equiv.swap i l * σ) i)
      rw [← measureReal_union (s₂ := A i (Equiv.swap i l * σ)) _ hmeas]
      · exact (measureReal_mono (Set.union_subset (hAS i _) (hAS i _))).trans (S_meas_le a b i)
      · rw [Set.disjoint_left]
        intro ρ h h'
        exact Aprop_disjoint _ _ σ i l hil (ball_l a b i l (hl i (mem_univ _)) ρ h.2.1) h h'
    have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (univ : Finset (Equiv.Perm (Fin (m + 1)))))
      => hpair σ)
    rw [Finset.sum_add_distrib, ← e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    rw [← hN] at hsum
    linarith
  have h3 : ∀ i, ∑ σ, μ.real (A i σ) ≤
      N / 2 * |a i - b i| + (if l = i then N / 2 * |a i - b i| else 0) := by
    intro i
    by_cases hil : l = i
    · subst hil
      simp only [if_true]
      have := Finset.sum_le_sum (fun σ (_ : σ ∈ (univ : Finset (Equiv.Perm (Fin (m + 1)))))
        => hS l σ)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN] at this
      linarith
    · simp only [hil, if_false, add_zero]
      exact h2 i (Ne.symm hil)
  have hl' := abs_le_halfL1 a b ha.2 hb.2 l
  calc ∑ σ, μ.real {ρ | labelOf σ (bv a ρ) ≠ labelOf σ (bv b ρ)}
      ≤ ∑ σ, ∑ i, μ.real (A i σ) := Finset.sum_le_sum fun σ _ => h1 σ
    _ = ∑ i, ∑ σ, μ.real (A i σ) := Finset.sum_comm
    _ ≤ ∑ i, (N / 2 * |a i - b i| + (if l = i then N / 2 * |a i - b i| else 0)) :=
        Finset.sum_le_sum fun i _ => h3 i
    _ = N * MultiwayCut.halfL1 a b + N / 2 * |a l - b l| := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (mem_univ _), ← Finset.mul_sum]
        unfold MultiwayCut.halfL1
        ring
    _ ≤ N * (3 / 2 * MultiwayCut.halfL1 a b) := by
        have := mul_le_mul_of_nonneg_left hl' (by positivity : (0:ℝ) ≤ N / 2)
        linarith

end Analytic

/-! ## The rounding theorem -/

theorem ckr_main {V : Type*} {m : ℕ} (I : MultiwayCut.Instance V (m + 1))
    (x : V → Fin (m + 1) → ℝ) (hx : MultiwayCut.IsFeasibleEmbedding I x) :
    ∃ c : V → Fin (m + 1), MultiwayCut.IsFeasibleLabeling I c ∧
      MultiwayCut.cutWeight I c ≤ 3 / 2 * MultiwayCut.relaxValue I x := by
  let lab : Equiv.Perm (Fin (m + 1)) → ℝ → V → Fin (m + 1) :=
    fun σ ρ u => labelOf σ (bv (x u) ρ)
  let C : Equiv.Perm (Fin (m + 1)) → V × V → Set ℝ :=
    fun σ e => {ρ | labelOf σ (bv (x e.1) ρ) ≠ labelOf σ (bv (x e.2) ρ)}
  have hC : ∀ σ e, MeasurableSet (C σ e) := fun σ e =>
    meas_set (x e.1) (x e.2) (fun bu bw => labelOf σ bu ≠ labelOf σ bw)
  have hF : ∀ σ, (fun ρ => MultiwayCut.cutWeight I (lab σ ρ)) =
      fun ρ => ∑ e ∈ I.E, I.w e * (C σ e).indicator 1 ρ := by
    intro σ
    funext ρ
    unfold MultiwayCut.cutWeight
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Set.indicator_apply, C, lab]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1 h2
    · exact absurd h2 h1
    · simp
  have hint1 : ∀ σ e, Integrable (fun ρ => I.w e * (C σ e).indicator 1 ρ) μ := fun σ e =>
    ((integrable_const (1 : ℝ)).indicator (hC σ e)).const_mul _
  have hint : ∀ σ, Integrable (fun ρ => MultiwayCut.cutWeight I (lab σ ρ)) μ := by
    intro σ
    rw [hF]
    exact integrable_finsetSum _ fun e _ => hint1 σ e
  have hI : ∀ σ, ∫ ρ, MultiwayCut.cutWeight I (lab σ ρ) ∂μ =
      ∑ e ∈ I.E, I.w e * μ.real (C σ e) := by
    intro σ
    rw [hF, integral_finsetSum _ fun e _ => hint1 σ e]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [integral_const_mul, integral_indicator_one (hC σ e)]
  have hsum : ∑ σ : Equiv.Perm (Fin (m + 1)), ∫ ρ, MultiwayCut.cutWeight I (lab σ ρ) ∂μ ≤
      ∑ _σ : Equiv.Perm (Fin (m + 1)), 3 / 2 * MultiwayCut.relaxValue I x := by
    simp_rw [hI]
    rw [Finset.sum_comm]
    calc ∑ e ∈ I.E, ∑ σ : Equiv.Perm (Fin (m + 1)), I.w e * μ.real (C σ e)
        = ∑ e ∈ I.E, I.w e * ∑ σ : Equiv.Perm (Fin (m + 1)), μ.real (C σ e) := by
          simp [Finset.mul_sum]
      _ ≤ ∑ e ∈ I.E, I.w e * ((Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ) *
            (3 / 2 * MultiwayCut.halfL1 (x e.1) (x e.2))) :=
          Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_left
            (edge_bound (x e.1) (x e.2) (hx.1 _) (hx.1 _)) (I.w_nonneg e he)
      _ = ∑ _σ : Equiv.Perm (Fin (m + 1)), 3 / 2 * MultiwayCut.relaxValue I x := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, MultiwayCut.relaxValue,
            Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
  obtain ⟨σ, -, hσ⟩ := Finset.exists_le_of_sum_le univ_nonempty hsum
  have hN : μ (Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Ioo.compl, Set.compl_inter_self, measure_empty]
  obtain ⟨ρ, hρ, hle⟩ := exists_notMem_null_le_integral (hint σ) hN
  have hρ' : ρ ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hρ
  refine ⟨lab σ ρ, ?_, hle.trans hσ⟩
  intro i
  have hb : bv (x (I.t i)) ρ = fun j => decide (j = i) := by
    funext j
    rw [hx.2 i]
    by_cases hj : j = i
    · subst hj
      simp [bv, hρ'.1.le]
    · simp [bv, hj, hρ'.2]
  show labelOf σ (bv (x (I.t i)) ρ) = i
  rw [hb, labelOf_single]

theorem ckr_rounding {n k : ℕ} (hk : 1 ≤ k) (I : MultiwayCut.Instance (Fin n) k)
    (x : Fin n → Fin k → ℝ) (hx : MultiwayCut.IsFeasibleEmbedding I x) :
    ∃ c : Fin n → Fin k, MultiwayCut.IsFeasibleLabeling I c ∧
      MultiwayCut.cutWeight I c ≤ 3 / 2 * MultiwayCut.relaxValue I x := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact ckr_main I x hx

end MultiwayGap2325.Dev.CKR
end

section
/-! Shared interface for the proof of Appendix A (Lemma 2.2's cut extraction).
Do not change these definitions: four separate files (Kkst, Face, Compact, Realize) build on them. -/

set_option autoImplicit false

noncomputable section

open Classical

namespace MultiwayGap2325.Dev.AppA

open MultiwayGap2325.Main

/-- Dyadic grid points of `Δ_q` at level `m`: integer vectors with sum `2^m`. -/
def GridPt (q m : ℕ) : Type := {a : Fin q → Fin (2 ^ m + 1) // ∑ i, (a i : ℕ) = 2 ^ m}

instance (q m : ℕ) : Fintype (GridPt q m) := by unfold GridPt; infer_instance
instance (q m : ℕ) : DecidableEq (GridPt q m) := by unfold GridPt; infer_instance

/-- The simplex point `a / 2^m`. -/
def GridPt.toSimplex {q m : ℕ} (a : GridPt q m) : Simplex q :=
  ⟨fun i => ((a.1 i : ℕ) : ℝ) / 2 ^ m, by
    constructor
    · intro i; positivity
    · rw [← Finset.sum_div]
      have h := a.2
      have : (∑ i, (((a.1 i : ℕ)) : ℝ)) = (2 : ℝ) ^ m := by exact_mod_cast h
      rw [this]; field_simp⟩

/-- The grid point at the vertex `e_i`. -/
def GridPt.vertex {q m : ℕ} (i : Fin q) : GridPt q m :=
  ⟨fun j => if j = i then Fin.last _ else 0, by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp⟩

/-- The inclusion of level `m` into level `m+1` (`a ↦ 2a`). -/
def GridPt.up {q m : ℕ} (a : GridPt q m) : GridPt q (m + 1) :=
  ⟨fun i => ⟨2 * (a.1 i : ℕ), by have := (a.1 i).2; rw [pow_succ]; omega⟩, by
    simp only
    rw [← Finset.mul_sum, a.2, pow_succ]; ring⟩

/-- Labelings of the level-`m` grid. -/
abbrev Config (q m : ℕ) : Type := GridPt q m → CutLabel q

/-- Non-opposite on the grid: vertices keep their own label, labels lie in the support. -/
def IsNonOppConfig {q m : ℕ} (c : Config q m) : Prop :=
  (∀ i : Fin q, c (GridPt.vertex i) = some i) ∧
  ∀ (a : GridPt q m) (i : Fin q), c a = some i → 0 < ((a.1 i : ℕ))

/-- A law on level-`m` configurations: a probability vector supported on non-opposite configurations
whose separation probabilities are at most `g · d + ε` on every pair of grid points. -/
def IsGoodLaw {q m : ℕ} (g ε : ℝ) (μ : Config q m → ℝ) : Prop :=
  μ ∈ stdSimplex ℝ (Config q m) ∧
  (∀ c : Config q m, μ c ≠ 0 → IsNonOppConfig c) ∧
  ∀ a b : GridPt q m,
    (∑ c ∈ Finset.univ.filter (fun c : Config q m => c a ≠ c b), μ c) ≤
      g * simplexDistance a.toSimplex b.toSimplex + ε

/-- Restrict a level-`(m+1)` configuration to level `m`. -/
def restrictUp {q m : ℕ} (c : Config q (m + 1)) : Config q m := fun a => c a.up

/-- Each level's law is the marginal of the next. -/
def IsConsistent {q : ℕ} (μ : ∀ m, Config q m → ℝ) : Prop :=
  ∀ (m : ℕ) (c : Config q m),
    μ m c = ∑ c' ∈ Finset.univ.filter (fun c' : Config q (m + 1) => restrictUp c' = c), μ (m + 1) c'

/-- The finite Karger–Klein–Stein–Thorup–Young statement (part A). -/
def KkstFinite (k : ℕ) : Prop :=
  ∀ (F : Finset (Fin k → ℝ)) (hF : ∀ x ∈ F, x ∈ stdSimplex ℝ (Fin k))
    (hT : ∀ i : Fin k, (Pi.single i 1 : Fin k → ℝ) ∈ F),
    ∃ μ : (F → Fin k) → ℝ, μ ∈ stdSimplex ℝ (F → Fin k) ∧
      (∀ L : F → Fin k, μ L ≠ 0 → ∀ i : Fin k, L ⟨Pi.single i 1, hT i⟩ = i) ∧
      ∀ x y : F,
        (∑ L ∈ Finset.univ.filter (fun L : F → Fin k => L x ≠ L y), μ L) ≤
          gapSequence k * MultiwayCut.halfL1 x.1 y.1

end MultiwayGap2325.Dev.AppA
end
end

section
set_option autoImplicit false

open Classical

namespace MultiwayGap2325.Dev.AppA

open MultiwayGap2325.Main

namespace Kkst

variable {n k : ℕ}

lemma halfL1_nonneg (u v : Fin k → ℝ) : 0 ≤ MultiwayCut.halfL1 u v := by
  unfold MultiwayCut.halfL1
  have : 0 ≤ ∑ ℓ, |u ℓ - v ℓ| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  positivity

lemma cutWeight_nonneg (I : MultiwayCut.Instance (Fin n) k) (c : Fin n → Fin k) :
    0 ≤ MultiwayCut.cutWeight I c :=
  Finset.sum_nonneg (fun e he => I.w_nonneg e (Finset.mem_filter.1 he).1)

lemma relax_nonneg (I : MultiwayCut.Instance (Fin n) k) (x : Fin n → Fin k → ℝ) :
    0 ≤ MultiwayCut.relaxValue I x :=
  Finset.sum_nonneg (fun e he => mul_nonneg (I.w_nonneg e he) (halfL1_nonneg _ _))

lemma intBdd (I : MultiwayCut.Instance (Fin n) k) : BddBelow (integralValues I) :=
  ⟨0, by rintro r ⟨c, -, rfl⟩; exact cutWeight_nonneg I c⟩

lemma fracBdd (I : MultiwayCut.Instance (Fin n) k) : BddBelow (fractionalValues I) :=
  ⟨0, by rintro r ⟨x, -, rfl⟩; exact relax_nonneg I x⟩

lemma intOpt_nonneg (I : MultiwayCut.Instance (Fin n) k) : 0 ≤ integralOpt I :=
  Real.sInf_nonneg (by rintro r ⟨c, -, rfl⟩; exact cutWeight_nonneg I c)

lemma fracOpt_nonneg (I : MultiwayCut.Instance (Fin n) k) : 0 ≤ fractionalOpt I :=
  Real.sInf_nonneg (by rintro r ⟨x, -, rfl⟩; exact relax_nonneg I x)

lemma intOpt_le_three_halves (hk : 1 ≤ k) (I : MultiwayCut.Instance (Fin n) k)
    (hne : (fractionalValues I).Nonempty) : integralOpt I ≤ 3 / 2 * fractionalOpt I := by
  have h : ∀ r ∈ fractionalValues I, integralOpt I / (3 / 2) ≤ r := by
    rintro r ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hle⟩ := MultiwayGap2325.Dev.CKR.ckr_rounding hk I x hx
    have : integralOpt I ≤ MultiwayCut.cutWeight I c := csInf_le (intBdd I) ⟨c, hc, rfl⟩
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have := le_csInf hne h
  rw [div_le_iff₀ (by norm_num)] at this
  unfold fractionalOpt
  linarith

lemma fracValues_nonempty (I : MultiwayCut.Instance (Fin n) k) (h : fractionalOpt I ≠ 0) :
    (fractionalValues I).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  exact h (by unfold fractionalOpt; rw [hne, Real.sInf_empty])

lemma gap_le (hk : 1 ≤ k) (I : MultiwayCut.Instance (Fin n) k) : instanceGap I ≤ 3 / 2 := by
  unfold instanceGap
  split_ifs with h
  · norm_num
  · have hpos : 0 < fractionalOpt I := lt_of_le_of_ne (fracOpt_nonneg I) (Ne.symm h)
    rw [div_le_iff₀ hpos]
    exact intOpt_le_three_halves hk I (fracValues_nonempty I h)

lemma gap_nonneg (I : MultiwayCut.Instance (Fin n) k) : 0 ≤ instanceGap I := by
  unfold instanceGap
  split_ifs
  · norm_num
  · exact div_nonneg (intOpt_nonneg I) (fracOpt_nonneg I)

lemma bdd (hk : 1 ≤ k) : BddAbove (finiteGapValues k) :=
  ⟨3 / 2, by rintro r ⟨n, I, rfl⟩; exact gap_le hk I⟩

lemma G_nonneg (hk : 2 ≤ k) : 0 ≤ gapSequence k := by
  unfold gapSequence
  rw [if_pos hk]
  exact Real.sSup_nonneg (by rintro r ⟨n, I, rfl⟩; exact gap_nonneg I)

lemma intOpt_le_gap (hk : 2 ≤ k) (I : MultiwayCut.Instance (Fin n) k)
    (hne : (fractionalValues I).Nonempty) :
    integralOpt I ≤ gapSequence k * fractionalOpt I := by
  by_cases h : fractionalOpt I = 0
  · have := intOpt_le_three_halves (by omega) I hne
    rw [h] at this ⊢
    linarith
  · have hpos : 0 < fractionalOpt I := lt_of_le_of_ne (fracOpt_nonneg I) (Ne.symm h)
    have hmem : instanceGap I ∈ finiteGapValues k := ⟨n, I, rfl⟩
    have hle := le_csSup (bdd (by omega)) hmem
    unfold instanceGap at hle
    rw [if_neg h, div_le_iff₀ hpos] at hle
    unfold gapSequence
    rw [if_pos hk]
    exact hle

/-- Step 1: the gap bound for an arbitrary nonnegative weighting of all pairs of `F`. -/
lemma gap_bound (hk : 2 ≤ k) (F : Finset (Fin k → ℝ)) (hF : ∀ x ∈ F, x ∈ stdSimplex ℝ (Fin k))
    (hT : ∀ i : Fin k, (Pi.single i 1 : Fin k → ℝ) ∈ F) (w : F × F → ℝ) (hw : ∀ p, 0 ≤ w p) :
    ∃ L : F → Fin k, (∀ i : Fin k, L ⟨Pi.single i 1, hT i⟩ = i) ∧
      ∑ p, w p * (if L p.1 ≠ L p.2 then (1 : ℝ) else 0) ≤
        gapSequence k * ∑ p, w p * MultiwayCut.halfL1 p.1.1 p.2.1 := by
  let φ : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  let I : MultiwayCut.Instance (Fin (Fintype.card F)) k :=
    { E := Finset.univ
      w := fun q => w (φ q.1, φ q.2)
      w_nonneg := fun q _ => hw _
      t := fun i => φ.symm ⟨Pi.single i 1, hT i⟩
      t_injective := by
        intro i j h
        have h2 := congrArg (fun a => (φ a).1 i) h
        simp only [Equiv.apply_symm_apply, Pi.single_eq_same] at h2
        by_contra hij
        rw [Pi.single_eq_of_ne hij] at h2
        exact one_ne_zero h2 }
  let x : Fin (Fintype.card F) → Fin k → ℝ := fun a => (φ a).1
  have hx : MultiwayCut.IsFeasibleEmbedding I x :=
    ⟨fun a => hF _ (φ a).2, fun i => by simp [I, x]⟩
  have hne : (fractionalValues I).Nonempty := ⟨_, x, hx, rfl⟩
  obtain ⟨c0, hc0, -⟩ := MultiwayGap2325.Dev.CKR.ckr_rounding (by omega) I x hx
  have hfin : (integralValues I).Finite :=
    (Set.finite_range (MultiwayCut.cutWeight I)).subset (by rintro r ⟨c, -, rfl⟩; exact ⟨c, rfl⟩)
  obtain ⟨c, hc, hceq⟩ := Set.Nonempty.csInf_mem (s := integralValues I) ⟨_, c0, hc0, rfl⟩ hfin
  refine ⟨fun v => c (φ.symm v), fun i => hc i, ?_⟩
  have e1 : ∑ p, w p * (if c (φ.symm p.1) ≠ c (φ.symm p.2) then (1 : ℝ) else 0) =
      MultiwayCut.cutWeight I c := by
    unfold MultiwayCut.cutWeight
    rw [Finset.sum_filter, ← (Equiv.prodCongr φ φ).sum_comp]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rcases q with ⟨a, b⟩
    simp [I, Equiv.prodCongr_apply]
  have e2 : ∑ p, w p * MultiwayCut.halfL1 p.1.1 p.2.1 = MultiwayCut.relaxValue I x := by
    unfold MultiwayCut.relaxValue
    rw [← (Equiv.prodCongr φ φ).sum_comp]
    rfl
  rw [e1, e2]
  have h1 : MultiwayCut.cutWeight I c = integralOpt I := hceq.symm
  have h2 := intOpt_le_gap hk I hne
  have h3 : fractionalOpt I ≤ MultiwayCut.relaxValue I x := csInf_le (fracBdd I) ⟨x, hx, rfl⟩
  have h4 := G_nonneg hk
  rw [h1]
  exact h2.trans (mul_le_mul_of_nonneg_left h3 h4)

end Kkst

theorem kkst_finite {k : ℕ} (hk : 2 ≤ k) : KkstFinite k := by
  intro F hF hT
  set G := gapSequence k with hG
  let feas : (F → Fin k) → Prop := fun L => ∀ i : Fin k, L ⟨Pi.single i 1, hT i⟩ = i
  let v : (F → Fin k) → (F × F → ℝ) := fun L p =>
    (if L p.1 ≠ L p.2 then (1 : ℝ) else 0) - G * MultiwayCut.halfL1 p.1.1 p.2.1
  let T : ((F → Fin k) → ℝ) →ₗ[ℝ] (F × F → ℝ) := Fintype.linearCombination ℝ v
  let Z : Set ((F → Fin k) → ℝ) := {μ | ∀ L, ¬ feas L → μ L = 0}
  let S : Set ((F → Fin k) → ℝ) := stdSimplex ℝ (F → Fin k) ∩ Z
  let K : Set (F × F → ℝ) := T '' S
  let N : Set (F × F → ℝ) := {z | ∀ p, z p ≤ 0}
  have hZclosed : IsClosed Z := by
    simp only [Z, Set.ofPred_forall]
    exact isClosed_iInter fun L => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply L) continuous_const
  have hZconv : Convex ℝ Z := by
    intro a ha b hb s t _ _ _ L hL
    simp [ha L hL, hb L hL]
  have hKcomp : IsCompact K :=
    ((isCompact_stdSimplex ℝ (F → Fin k)).inter_right hZclosed).image
      T.continuous_of_finiteDimensional
  have hKconv : Convex ℝ K := ((convex_stdSimplex ℝ (F → Fin k)).inter hZconv).linear_image T
  have hNclosed : IsClosed N := by
    simp only [N, Set.ofPred_forall]
    exact isClosed_iInter fun p => isClosed_le (continuous_apply p) continuous_const
  have hNconv : Convex ℝ N := by
    intro a ha b hb s t hs ht _ p
    have h1 := mul_nonpos_iff.2 (Or.inl ⟨hs, ha p⟩)
    have h2 := mul_nonpos_iff.2 (Or.inl ⟨ht, hb p⟩)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  by_cases hdisj : Disjoint K N
  · exfalso
    obtain ⟨f, u, s, hfK, hus, hfN⟩ :=
      geometric_hahn_banach_compact_closed hKconv hKcomp hNconv hNclosed hdisj
    have h0 : s < 0 := by simpa using hfN 0 (by intro p; simp)
    let w : F × F → ℝ := fun p => - f (Pi.single p 1)
    have hw : ∀ p, 0 ≤ w p := by
      intro p
      by_contra hneg
      push Not at hneg
      have ha : 0 < f (Pi.single p 1) := by simp only [w] at hneg; linarith
      have hc : 0 ≤ (-s + 1) / f (Pi.single p 1) := div_nonneg (by linarith) ha.le
      have hmem : (-((-s + 1) / f (Pi.single p 1))) • (Pi.single p 1 : F × F → ℝ) ∈ N := by
        intro q
        by_cases hq : q = p
        · subst hq; simp; linarith
        · simp [Pi.single_eq_of_ne hq]
      have := hfN _ hmem
      rw [map_smul, smul_eq_mul, neg_mul, div_mul_cancel₀ _ ha.ne'] at this
      linarith
    have hf : ∀ z : F × F → ℝ, f z = - ∑ p, w p * z p := by
      intro z
      conv_lhs => rw [← Finset.univ_sum_single z]
      rw [map_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      have : (Pi.single p (z p) : F × F → ℝ) = z p • (Pi.single p 1 : F × F → ℝ) := by
        ext q; by_cases hq : q = p
        · subst hq; simp
        · simp [Pi.single_eq_of_ne hq]
      rw [this, map_smul, smul_eq_mul]
      simp only [w]; ring
    obtain ⟨L, hL, hle⟩ := Kkst.gap_bound hk F hF hT w hw
    have hmem : v L ∈ K := by
      refine ⟨Pi.single L 1, ⟨single_mem_stdSimplex ℝ L, fun L' hL' => ?_⟩, ?_⟩
      · have : L' ≠ L := fun h => hL' (h ▸ hL)
        simp [Pi.single_eq_of_ne this]
      · simp only [T, Fintype.linearCombination_apply]
        rw [Finset.sum_eq_single L]
        · simp
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · simp
    have h1 := hfK _ hmem
    rw [hf] at h1
    have h2 : ∑ p, w p * v L p = ∑ p, w p * (if L p.1 ≠ L p.2 then (1 : ℝ) else 0) -
        G * ∑ p, w p * MultiwayCut.halfL1 p.1.1 p.2.1 := by
      simp only [v, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun p _ => ?_)
      ring
    linarith
  · rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨z, ⟨μ, ⟨hμS, hμ0⟩, rfl⟩, hzN⟩ := hdisj
    refine ⟨μ, hμS, fun L hL => by_contra (fun h => hL (hμ0 L h)), fun x y => ?_⟩
    have h1 := hzN (x, y)
    simp only [T, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, v, mul_sub, Finset.sum_sub_distrib] at h1
    have hsum : ∑ L, μ L = 1 := hμS.2
    have h2 : ∑ L, μ L * (G * MultiwayCut.halfL1 x.1 y.1) = G * MultiwayCut.halfL1 x.1 y.1 := by
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [Finset.sum_filter]
    have h3 : ∑ L, (if L x ≠ L y then μ L else 0) = ∑ L, μ L * (if L x ≠ L y then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun L _ => ?_)
      split_ifs <;> simp
    rw [h3]
    linarith

end MultiwayGap2325.Dev.AppA
end

section
/-! Appendix A, the face law: restrict a finite KKST law on `Δ_k` to the face spanned by the
first `q` vertices, averaging over all coordinate permutations of `Fin k`. -/

set_option autoImplicit false

noncomputable section

open Classical

namespace MultiwayGap2325.Dev.AppA

open MultiwayGap2325.Main

namespace Face

/-- The embedding of a grid point of `Δ_q` into `Δ_k` (first `q` coordinates). -/
def emb {q M k : ℕ} (a : GridPt q M) (m : Fin k) : ℝ :=
  if h : m.val < q then ((a.1 ⟨m.val, h⟩ : ℕ) : ℝ) / 2 ^ M else 0

/-- The embedding, with coordinates permuted by `σ`. -/
def embP {q M k : ℕ} (σ : Equiv.Perm (Fin k)) (a : GridPt q M) : Fin k → ℝ :=
  fun l => emb a (σ⁻¹ l)

/-- The finite point set fed to the KKST statement. -/
def FF (q M k : ℕ) : Finset (Fin k → ℝ) :=
  (Finset.univ.image (fun p : Equiv.Perm (Fin k) × GridPt q M => embP p.1 p.2)) ∪
    Finset.univ.image (fun i : Fin k => (Pi.single i 1 : Fin k → ℝ))

lemma mem_FF_embP {q M k : ℕ} (σ : Equiv.Perm (Fin k)) (a : GridPt q M) :
    embP σ a ∈ FF q M k := by
  unfold FF
  exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(σ, a), Finset.mem_univ _, rfl⟩)

lemma mem_FF_single {q M k : ℕ} (i : Fin k) : (Pi.single i 1 : Fin k → ℝ) ∈ FF q M k := by
  unfold FF
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)

/-- The point of `FF` attached to `σ` and `a`. -/
def pt {q M k : ℕ} (σ : Equiv.Perm (Fin k)) (a : GridPt q M) : FF q M k :=
  ⟨embP σ a, mem_FF_embP σ a⟩

lemma sum_castLE {q k : ℕ} (hqk : q ≤ k) (g : Fin k → ℝ)
    (hg : ∀ m : Fin k, q ≤ m.val → g m = 0) :
    ∑ m, g m = ∑ i : Fin q, g (Fin.castLE hqk i) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hqk)
    (fun x _ y _ h => Fin.castLE_injective hqk h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro m _ hm
  apply hg
  by_contra hlt
  exact hm (Finset.mem_image.2 ⟨⟨m.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

lemma emb_castLE {q M k : ℕ} (hqk : q ≤ k) (a : GridPt q M) (i : Fin q) :
    emb a (Fin.castLE hqk i) = ((a.1 i : ℕ) : ℝ) / 2 ^ M := by
  unfold emb
  rw [dif_pos (by simp)]
  rfl

lemma emb_of_le {q M k : ℕ} (a : GridPt q M) (m : Fin k) (h : q ≤ m.val) : emb a m = 0 := by
  unfold emb
  rw [dif_neg (by omega)]

lemma embP_mem {q M k : ℕ} (hqk : q ≤ k) (σ : Equiv.Perm (Fin k)) (a : GridPt q M) :
    embP σ a ∈ stdSimplex ℝ (Fin k) := by
  constructor
  · intro l
    unfold embP emb
    split_ifs <;> positivity
  · unfold embP
    rw [Equiv.sum_comp σ⁻¹ (fun m => emb a m)]
    rw [sum_castLE hqk _ (fun m h => emb_of_le a m h)]
    simp only [emb_castLE]
    exact (a.toSimplex).2.2

lemma halfL1_pt {q M k : ℕ} (hqk : q ≤ k) (σ : Equiv.Perm (Fin k)) (a b : GridPt q M) :
    MultiwayCut.halfL1 (pt (k := k) σ a).1 (pt σ b).1 =
      simplexDistance a.toSimplex b.toSimplex := by
  unfold simplexDistance MultiwayCut.halfL1 pt embP
  congr 1
  simp only
  rw [Equiv.sum_comp σ⁻¹ (fun m => |emb a m - emb b m|)]
  rw [sum_castLE hqk _ (fun m h => by simp [emb_of_le a m h, emb_of_le b m h])]
  simp only [emb_castLE]
  rfl

lemma FF_mem {q M k : ℕ} (hqk : q ≤ k) : ∀ x ∈ FF q M k, x ∈ stdSimplex ℝ (Fin k) := by
  intro x hx
  unfold FF at hx
  rcases Finset.mem_union.1 hx with h | h
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 h
    exact embP_mem hqk p.1 p.2
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 h
    exact single_mem_stdSimplex ℝ i

/-- The face label read off from a `Fin k` label `m`. -/
def cfgOf {q M : ℕ} (a : GridPt q M) {k : ℕ} (m : Fin k) : CutLabel q :=
  if h : m.val < q then (if 0 < (a.1 ⟨m.val, h⟩ : ℕ) then some ⟨m.val, h⟩ else none) else none

/-- The `Fin k` label of `a`, pulled back through `σ`. -/
def lab {q M k : ℕ} (σ : Equiv.Perm (Fin k)) (L : FF q M k → Fin k) (a : GridPt q M) : Fin k :=
  σ⁻¹ (L (pt σ a))

/-- The configuration attached to `σ` and a labeling `L`. -/
def cfg {q M k : ℕ} (σ : Equiv.Perm (Fin k)) (L : FF q M k → Fin k) : Config q M :=
  fun a => cfgOf a (lab σ L a)

/-- Bad labels for `a`: inside the face, outside the support of `a`. -/
def Z {q M : ℕ} (k : ℕ) (a : GridPt q M) : Finset (Fin k) :=
  Finset.univ.filter (fun m : Fin k => ∃ h : m.val < q, (a.1 ⟨m.val, h⟩ : ℕ) = 0)

lemma cfgOf_ne {q M k : ℕ} (a b : GridPt q M) (m : Fin k) (h : cfgOf a m ≠ cfgOf b m) :
    m ∈ Z k a ∨ m ∈ Z k b := by
  unfold cfgOf at h
  unfold Z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hm : m.val < q
  · rw [dif_pos hm, dif_pos hm] at h
    by_cases ha : 0 < (a.1 ⟨m.val, hm⟩ : ℕ)
    · by_cases hb : 0 < (b.1 ⟨m.val, hm⟩ : ℕ)
      · rw [if_pos ha, if_pos hb] at h; exact absurd rfl h
      · right; exact ⟨hm, by omega⟩
    · left; exact ⟨hm, by omega⟩
  · rw [dif_neg hm, dif_neg hm] at h; exact absurd rfl h

lemma cfg_ne {q M k : ℕ} (σ : Equiv.Perm (Fin k)) (L : FF q M k → Fin k) (a b : GridPt q M)
    (h : cfg σ L a ≠ cfg σ L b) :
    L (pt σ a) ≠ L (pt σ b) ∨ lab σ L a ∈ Z k a ∨ lab σ L b ∈ Z k b := by
  by_cases hL : L (pt σ a) = L (pt σ b)
  · right
    have hl : lab σ L a = lab σ L b := by unfold lab; rw [hL]
    unfold cfg at h
    rw [hl] at h ⊢
    exact cfgOf_ne a b _ h
  · left; exact hL

lemma emb_swap {q M k : ℕ} (a : GridPt q M) (z w : Fin k) (hz : z ∈ Z k a) (hw : q ≤ w.val)
    (n : Fin k) : emb a (Equiv.swap z w n) = emb a n := by
  have h1 : emb a z = 0 := by
    unfold Z at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨hzq, hz0⟩ := hz
    unfold emb; rw [dif_pos hzq, hz0]; simp
  have h2 : emb a w = 0 := emb_of_le a w hw
  rw [Equiv.swap_apply_def]
  split_ifs with h3 h4
  · rw [h3, h1, h2]
  · rw [h4, h1, h2]
  · rfl

lemma pt_mul_swap {q M k : ℕ} (a : GridPt q M) (z w : Fin k) (hz : z ∈ Z k a) (hw : q ≤ w.val)
    (σ : Equiv.Perm (Fin k)) : pt (σ * Equiv.swap z w) a = pt σ a := by
  apply Subtype.ext
  funext l
  simp only [pt, embP, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]
  exact emb_swap a z w hz hw _

lemma lab_mul_swap {q M k : ℕ} (a : GridPt q M) (z w : Fin k) (hz : z ∈ Z k a)
    (hw : q ≤ w.val) (σ : Equiv.Perm (Fin k)) (L : FF q M k → Fin k) :
    lab (σ * Equiv.swap z w) L a = Equiv.swap z w (lab σ L a) := by
  unfold lab
  rw [pt_mul_swap a z w hz hw σ]
  simp only [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]

/-- Weight of a pair `(σ, L)`: uniform in `σ`, `μ0` in `L`. -/
def wt {q M k : ℕ} (μ0 : (FF q M k → Fin k) → ℝ)
    (p : Equiv.Perm (Fin k) × (FF q M k → Fin k)) : ℝ :=
  μ0 p.2 / (k.factorial : ℝ)

lemma wt_nonneg {q M k : ℕ} (μ0 : (FF q M k → Fin k) → ℝ) (h0 : ∀ L, 0 ≤ μ0 L)
    (p : Equiv.Perm (Fin k) × (FF q M k → Fin k)) : 0 ≤ wt μ0 p := by
  unfold wt; have := h0 p.2; positivity

lemma sum_const_perm {k : ℕ} (c : ℝ) :
    ∑ _σ : Equiv.Perm (Fin k), c / (k.factorial : ℝ) = c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma wt_sum {q M k : ℕ} (μ0 : (FF q M k → Fin k) → ℝ) (h1 : ∑ L, μ0 L = 1) :
    ∑ p, wt μ0 p = 1 := by
  rw [Fintype.sum_prod_type]
  have : ∀ _σ : Equiv.Perm (Fin k), ∑ L, wt μ0 (_σ, L) = 1 / (k.factorial : ℝ) := by
    intro σ
    unfold wt
    rw [← Finset.sum_div, h1]
  rw [Finset.sum_congr rfl (fun σ _ => this σ)]
  exact sum_const_perm 1

/-- Probability that `a` gets pulled-back label `m`. -/
def P {q M k : ℕ} (μ0 : (FF q M k → Fin k) → ℝ) (a : GridPt q M) (m : Fin k) : ℝ :=
  ∑ p : Equiv.Perm (Fin k) × (FF q M k → Fin k), if lab p.1 p.2 a = m then wt μ0 p else 0

lemma P_nonneg {q M k : ℕ} (μ0 : (FF q M k → Fin k) → ℝ) (h0 : ∀ L, 0 ≤ μ0 L)
    (a : GridPt q M) (m : Fin k) : 0 ≤ P μ0 a m := by
  unfold P
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact wt_nonneg μ0 h0 p
  · exact le_refl 0

lemma P_sum {q M k : ℕ} (μ0 : (FF q M k → Fin k) → ℝ) (h1 : ∑ L, μ0 L = 1)
    (a : GridPt q M) : ∑ m, P μ0 a m = 1 := by
  unfold P
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact wt_sum μ0 h1

lemma P_swap {q M k : ℕ} (μ0 : (FF q M k → Fin k) → ℝ) (a : GridPt q M) (z w : Fin k)
    (hz : z ∈ Z k a) (hw : q ≤ w.val) : P μ0 a z = P μ0 a w := by
  unfold P
  apply Fintype.sum_equiv
    (Equiv.prodCongr (Equiv.mulRight (Equiv.swap z w)) (Equiv.refl (FF q M k → Fin k)))
  intro p
  simp only [Equiv.prodCongr_apply, Equiv.coe_mulRight, Equiv.coe_refl, Prod.map_fst,
    Prod.map_snd, id]
  rw [lab_mul_swap a z w hz hw]
  have : (Equiv.swap z w (lab p.1 p.2 a) = w) ↔ (lab p.1 p.2 a = z) := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  by_cases h : lab p.1 p.2 a = z
  · rw [if_pos h, if_pos (this.2 h)]; rfl
  · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]

lemma card_W {q k : ℕ} (hqk : q ≤ k) :
    k - q ≤ (Finset.univ.filter (fun m : Fin k => ¬ m.val < q)).card := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (fun m : Fin k => m.val < q)
  rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at h
  omega

lemma P_le {q M k : ℕ} (hqk : q < k) (μ0 : (FF q M k → Fin k) → ℝ) (h0 : ∀ L, 0 ≤ μ0 L)
    (h1 : ∑ L, μ0 L = 1) (a : GridPt q M) (z : Fin k) (hz : z ∈ Z k a) :
    P μ0 a z ≤ 1 / ((k : ℝ) - q) := by
  set W := Finset.univ.filter (fun m : Fin k => ¬ m.val < q)
  have hsum : ∑ w ∈ W, P μ0 a w = (W.card : ℝ) * P μ0 a z := by
    rw [Finset.sum_congr rfl (fun w hw => (P_swap μ0 a z w hz (by
      simp only [W, Finset.mem_filter] at hw; omega)).symm)]
    simp
  have hle : ∑ w ∈ W, P μ0 a w ≤ 1 := by
    rw [← P_sum μ0 h1 a]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun m _ _ => P_nonneg μ0 h0 a m)
  have hc : ((k : ℝ) - q) ≤ (W.card : ℝ) := by
    have := card_W hqk.le (q := q) (k := k)
    have h2 : ((k - q : ℕ) : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast this
    rwa [Nat.cast_sub hqk.le] at h2
  have hpos : (0 : ℝ) < (k : ℝ) - q := by
    have : (q : ℝ) < k := by exact_mod_cast hqk
    linarith
  rw [le_div_iff₀ hpos]
  have := P_nonneg μ0 h0 a z
  nlinarith

lemma card_Z {q M k : ℕ} (hqk : q ≤ k) (a : GridPt q M) : (Z k a).card ≤ q := by
  have hsub : Z k a ⊆ Finset.univ.image (Fin.castLE hqk) := by
    intro m hm
    unfold Z at hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨h, _⟩ := hm
    exact Finset.mem_image.2 ⟨⟨m.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
  calc (Z k a).card ≤ (Finset.univ.image (Fin.castLE hqk)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
    _ = q := by simp

lemma bad_le {q M k : ℕ} (hqk : q < k) (μ0 : (FF q M k → Fin k) → ℝ) (h0 : ∀ L, 0 ≤ μ0 L)
    (h1 : ∑ L, μ0 L = 1) (a : GridPt q M) :
    (∑ p : Equiv.Perm (Fin k) × (FF q M k → Fin k),
      if lab p.1 p.2 a ∈ Z k a then wt μ0 p else 0) ≤ (q : ℝ) / ((k : ℝ) - q) := by
  have : (∑ p : Equiv.Perm (Fin k) × (FF q M k → Fin k),
      if lab p.1 p.2 a ∈ Z k a then wt μ0 p else 0) = ∑ m ∈ Z k a, P μ0 a m := by
    unfold P
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_ite_eq]
  rw [this]
  calc ∑ m ∈ Z k a, P μ0 a m ≤ ∑ _m ∈ Z k a, 1 / ((k : ℝ) - q) :=
        Finset.sum_le_sum (fun m hm => P_le hqk μ0 h0 h1 a m hm)
    _ = ((Z k a).card : ℝ) * (1 / ((k : ℝ) - q)) := by simp
    _ ≤ (q : ℝ) * (1 / ((k : ℝ) - q)) := by
        have hpos : (0 : ℝ) < (k : ℝ) - q := by
          have : (q : ℝ) < k := by exact_mod_cast hqk
          linarith
        have : ((Z k a).card : ℝ) ≤ q := by exact_mod_cast card_Z hqk.le a
        gcongr
    _ = (q : ℝ) / ((k : ℝ) - q) := by ring

lemma embP_vertex {q M k : ℕ} (hqk : q ≤ k) (σ : Equiv.Perm (Fin k)) (i : Fin q) :
    embP σ (GridPt.vertex (m := M) i) = (Pi.single (σ (Fin.castLE hqk i)) 1 : Fin k → ℝ) := by
  funext l
  unfold embP
  by_cases hl : l = σ (Fin.castLE hqk i)
  · subst hl
    rw [Pi.single_eq_same]
    have hs : σ⁻¹ (σ (Fin.castLE hqk i)) = Fin.castLE hqk i := by simp
    rw [hs, emb_castLE]
    simp [GridPt.vertex]
  · rw [Pi.single_eq_of_ne hl]
    have hne : σ⁻¹ l ≠ Fin.castLE hqk i := by
      intro h; apply hl; rw [← h]; simp
    unfold emb
    split_ifs with h
    · have : (⟨(σ⁻¹ l).val, h⟩ : Fin q) ≠ i := by
        intro h'; apply hne; apply Fin.ext; rw [← h']; rfl
      have h0 : (GridPt.vertex (m := M) i).1 ⟨(σ⁻¹ l).val, h⟩ = 0 := by
        unfold GridPt.vertex; dsimp only; rw [if_neg this]
      rw [h0]; simp
    · rfl

lemma cfg_nonOpp {q M k : ℕ} (hqk : q ≤ k) (σ : Equiv.Perm (Fin k)) (L : FF q M k → Fin k)
    (hL : ∀ i : Fin k, L ⟨Pi.single i 1, mem_FF_single i⟩ = i) :
    IsNonOppConfig (cfg σ L) := by
  constructor
  · intro i
    have hpt : pt σ (GridPt.vertex (m := M) i) =
        ⟨Pi.single (σ (Fin.castLE hqk i)) 1, mem_FF_single _⟩ :=
      Subtype.ext (embP_vertex hqk σ i)
    have hlab : lab σ L (GridPt.vertex i) = Fin.castLE hqk i := by
      unfold lab; rw [hpt, hL]; simp
    unfold cfg
    rw [hlab]
    unfold cfgOf
    rw [dif_pos (by simp)]
    have hpos : 0 < ((GridPt.vertex (m := M) i).1 ⟨(Fin.castLE hqk i).val, by simp⟩ : ℕ) := by
      have : (⟨(Fin.castLE hqk i).val, by simp⟩ : Fin q) = i := Fin.ext rfl
      rw [this]; simp [GridPt.vertex]
    rw [if_pos hpos]
    rfl
  · intro a i h
    unfold cfg cfgOf at h
    split_ifs at h with h1 h2
    cases h
    exact h2

end Face

open Face in
theorem face_law {q : ℕ} (hq : 2 ≤ q) (M k : ℕ) (hk : 2 * q ≤ k) (hkkst : KkstFinite k) :
    ∃ μ : Config q M → ℝ, IsGoodLaw (gapSequence k) ((2 * q : ℝ) / ((k : ℝ) - q)) μ := by
  have hqk : q < k := by omega
  obtain ⟨μ0, hμ0, hfeas, hsep⟩ :=
    hkkst (FF q M k) (FF_mem hqk.le) (fun i => mem_FF_single i)
  have h0 : ∀ L, 0 ≤ μ0 L := hμ0.1
  have h1 : ∑ L, μ0 L = 1 := hμ0.2
  refine ⟨fun c => ∑ p : Equiv.Perm (Fin k) × (FF q M k → Fin k),
    if cfg p.1 p.2 = c then wt μ0 p else 0, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro c
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact wt_nonneg μ0 h0 p
    · exact le_refl 0
  · simp only
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact wt_sum μ0 h1
  · intro c hc
    obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    by_cases hpc : cfg p.1 p.2 = c
    · rw [if_pos hpc] at hp
      have hμ : μ0 p.2 ≠ 0 := by
        intro h; apply hp; unfold wt; rw [h, zero_div]
      rw [← hpc]
      exact cfg_nonOpp hqk.le p.1 p.2 (hfeas p.2 hμ)
    · rw [if_neg hpc] at hp; exact absurd rfl hp
  · intro a b
    have hrw : (∑ c ∈ Finset.univ.filter (fun c : Config q M => c a ≠ c b),
        ∑ p : Equiv.Perm (Fin k) × (FF q M k → Fin k),
          if cfg p.1 p.2 = c then wt μ0 p else 0) =
        ∑ p : Equiv.Perm (Fin k) × (FF q M k → Fin k),
          if cfg p.1 p.2 a ≠ cfg p.1 p.2 b then wt μ0 p else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_ite_eq]
      simp
    rw [hrw]
    have hsplit : ∀ p : Equiv.Perm (Fin k) × (FF q M k → Fin k),
        (if cfg p.1 p.2 a ≠ cfg p.1 p.2 b then wt μ0 p else 0) ≤
          (if p.2 (pt p.1 a) ≠ p.2 (pt p.1 b) then wt μ0 p else 0) +
          (if lab p.1 p.2 a ∈ Z k a then wt μ0 p else 0) +
          (if lab p.1 p.2 b ∈ Z k b then wt μ0 p else 0) := by
      intro p
      have hw := wt_nonneg μ0 h0 p
      by_cases h : cfg p.1 p.2 a ≠ cfg p.1 p.2 b
      · rw [if_pos h]
        rcases cfg_ne p.1 p.2 a b h with h' | h' | h'
        · rw [if_pos h']; split_ifs <;> linarith
        · rw [if_pos h']; split_ifs <;> linarith
        · rw [if_pos h']; split_ifs <;> linarith
      · rw [if_neg h]; split_ifs <;> linarith
    have hT1 : (∑ p : Equiv.Perm (Fin k) × (FF q M k → Fin k),
        if p.2 (pt p.1 a) ≠ p.2 (pt p.1 b) then wt μ0 p else 0) ≤
        gapSequence k * simplexDistance a.toSimplex b.toSimplex := by
      rw [Fintype.sum_prod_type]
      have : ∀ σ : Equiv.Perm (Fin k), (∑ L : FF q M k → Fin k,
          if L (pt σ a) ≠ L (pt σ b) then wt μ0 (σ, L) else 0) ≤
          gapSequence k * simplexDistance a.toSimplex b.toSimplex / (k.factorial : ℝ) := by
        intro σ
        have hf : (∑ L : FF q M k → Fin k,
            if L (pt σ a) ≠ L (pt σ b) then wt μ0 (σ, L) else 0) =
            (∑ L ∈ Finset.univ.filter (fun L : FF q M k → Fin k => L (pt σ a) ≠ L (pt σ b)),
              μ0 L) / (k.factorial : ℝ) := by
          rw [Finset.sum_div, Finset.sum_filter]
          rfl
        rw [hf]
        have := hsep (pt σ a) (pt σ b)
        rw [halfL1_pt hqk.le] at this
        gcongr
      calc _ ≤ ∑ _σ : Equiv.Perm (Fin k),
            gapSequence k * simplexDistance a.toSimplex b.toSimplex / (k.factorial : ℝ) :=
            Finset.sum_le_sum (fun σ _ => this σ)
        _ = _ := sum_const_perm _
    have hT2 := bad_le hqk μ0 h0 h1 a
    have hT3 := bad_le hqk μ0 h0 h1 b
    calc _ ≤ ∑ p : Equiv.Perm (Fin k) × (FF q M k → Fin k),
          ((if p.2 (pt p.1 a) ≠ p.2 (pt p.1 b) then wt μ0 p else 0) +
          (if lab p.1 p.2 a ∈ Z k a then wt μ0 p else 0) +
          (if lab p.1 p.2 b ∈ Z k b then wt μ0 p else 0)) :=
          Finset.sum_le_sum (fun p _ => hsplit p)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ gapSequence k * simplexDistance a.toSimplex b.toSimplex +
            (q : ℝ) / ((k : ℝ) - q) + (q : ℝ) / ((k : ℝ) - q) := by linarith
      _ = _ := by ring


end MultiwayGap2325.Dev.AppA
end
end

section
set_option autoImplicit false
noncomputable section
open Classical
namespace MultiwayGap2325.Dev.AppA
open MultiwayGap2325.Main

namespace Compact

open Filter Topology

/-- Marginal of a law under `restrictUp`. -/
def marg {q m : ℕ} (μ : Config q (m + 1) → ℝ) (c : Config q m) : ℝ :=
  ∑ c' ∈ Finset.univ.filter (fun c' : Config q (m + 1) => restrictUp c' = c), μ c'

lemma sum_fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β)
    (μ : α → ℝ) (P : β → Prop) [DecidablePred P] :
    ∑ b ∈ Finset.univ.filter P, ∑ a ∈ Finset.univ.filter (fun a => f a = b), μ a =
      ∑ a ∈ Finset.univ.filter (fun a => P (f a)), μ a := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun a => P (f a)))
    (t := Finset.univ.filter P) (g := f)]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.filter_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    constructor
    · intro h; aesop
    · intro h; aesop
  · intro a ha; simpa using ha

lemma vertex_up {q m : ℕ} (i : Fin q) : (GridPt.vertex i : GridPt q m).up = GridPt.vertex i := by
  apply Subtype.ext; funext j
  apply Fin.ext
  by_cases hj : j = i
  · simp [GridPt.up, GridPt.vertex, hj, pow_succ]; ring
  · simp [GridPt.up, GridPt.vertex, hj]

lemma toSimplex_up {q m : ℕ} (a : GridPt q m) : a.up.toSimplex = a.toSimplex := by
  apply Subtype.ext; funext i
  simp only [GridPt.toSimplex, GridPt.up]
  push_cast
  rw [pow_succ]; field_simp

lemma nonOpp_restrict {q m : ℕ} {c : Config q (m + 1)} (hc : IsNonOppConfig c) :
    IsNonOppConfig (restrictUp c) := by
  refine ⟨fun i => ?_, fun a i h => ?_⟩
  · simp only [restrictUp]; rw [vertex_up]; exact hc.1 i
  · have := hc.2 a.up i h
    simp only [GridPt.up] at this
    omega

lemma marg_good {q m : ℕ} {g ε : ℝ} {μ : Config q (m + 1) → ℝ} (hμ : IsGoodLaw g ε μ) :
    IsGoodLaw g ε (marg μ) := by
  obtain ⟨⟨h0, h1⟩, hs, hd⟩ := hμ
  refine ⟨⟨fun c => Finset.sum_nonneg (fun c' _ => h0 c'), ?_⟩, fun c hc => ?_, fun a b => ?_⟩
  · have := sum_fiber (restrictUp (m := m)) μ (fun _ => True)
    rw [Finset.filter_true_of_mem (fun _ _ => trivial),
      Finset.filter_true_of_mem (fun _ _ => trivial)] at this
    unfold marg; rw [this, h1]
  · obtain ⟨c', hc', hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    rw [← hc']; exact nonOpp_restrict (hs c' hne)
  · unfold marg
    rw [sum_fiber (restrictUp (m := m)) μ (fun c => c a ≠ c b)]
    have := hd a.up b.up
    rw [toSimplex_up, toSimplex_up] at this
    exact this

/-- Iterated marginal, `k` levels down. -/
def pushK {q : ℕ} : ∀ (k m : ℕ), (Config q (m + k) → ℝ) → Config q m → ℝ
  | 0, _, μ => μ
  | k + 1, m, μ => pushK k m (marg μ)

lemma pushK_good {q : ℕ} {g ε : ℝ} (k m : ℕ) (μ : Config q (m + k) → ℝ)
    (hμ : IsGoodLaw g ε μ) : IsGoodLaw g ε (pushK k m μ) := by
  induction k with
  | zero => exact hμ
  | succ k ih => exact ih _ (marg_good hμ)

lemma pushK_succ {q : ℕ} (k : ℕ) : ∀ (m : ℕ) (ρ : ∀ M, Config q M → ℝ),
    pushK (k + 1) m (ρ (m + (k + 1))) = marg (pushK k (m + 1) (ρ (m + 1 + k))) := by
  induction k with
  | zero => intro m ρ; rfl
  | succ k ih =>
    intro m ρ
    exact ih m (fun M => marg (ρ (M + 1)))

lemma good_mono {q m : ℕ} {g ε ε' : ℝ} {μ : Config q m → ℝ} (hμ : IsGoodLaw g ε μ) (h : ε ≤ ε') :
    IsGoodLaw g ε' μ :=
  ⟨hμ.1, hμ.2.1, fun a b => (hμ.2.2 a b).trans (by linarith)⟩

/-- The `N`-th approximating family. -/
def nu {q : ℕ} (ρ : ∀ M, Config q M → ℝ) (N m : ℕ) : Config q m → ℝ :=
  pushK (N - m) m (ρ (m + (N - m)))

lemma nu_good {q : ℕ} {g : ℝ} (ρ : ∀ M, Config q M → ℝ)
    (hρ : ∀ M : ℕ, IsGoodLaw g (1 / ((M : ℝ) + 1)) (ρ M)) (N m : ℕ) :
    IsGoodLaw g (1 / ((N : ℝ) + 1)) (nu ρ N m) := by
  refine good_mono (pushK_good _ _ _ (hρ _)) ?_
  have : (N : ℝ) ≤ ((m + (N - m) : ℕ) : ℝ) := by exact_mod_cast (by omega)
  gcongr

lemma nu_cons {q : ℕ} (ρ : ∀ M, Config q M → ℝ) (N m : ℕ) (hm : m + 1 ≤ N) :
    nu ρ N m = marg (nu ρ N (m + 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, N - (m + 1) = k := ⟨_, rfl⟩
  have hk' : N - m = k + 1 := by omega
  unfold nu
  rw [hk, hk']
  exact pushK_succ k m ρ

end Compact

open MultiwayGap2325.Dev.AppA.Compact Filter Topology in
theorem compact_limit {q : ℕ} (hq : 2 ≤ q) (g : ℝ)
    (h : ∀ (M : ℕ) (ε : ℝ), 0 < ε → ∃ μ : Config q M → ℝ, IsGoodLaw g ε μ) :
    ∃ μ : ∀ m, Config q m → ℝ, (∀ m, IsGoodLaw g 0 (μ m)) ∧ IsConsistent μ := by
  choose ρ hρ using fun M : ℕ => h M (1 / ((M : ℝ) + 1)) (by positivity)
  set S : Set (∀ m, Config q m → ℝ) := Set.pi Set.univ (fun m => stdSimplex ℝ (Config q m))
  have hS : IsCompact S := isCompact_univ_pi (fun m => isCompact_stdSimplex ℝ _)
  have hmem : ∀ N, nu ρ N ∈ S := fun N m _ => (nu_good ρ hρ N m).1
  obtain ⟨μ, hμS, φ, hφ, hlim⟩ := hS.tendsto_subseq hmem
  have hc : ∀ m (c : Config q m),
      Tendsto (fun n => nu ρ (φ n) m c) atTop (𝓝 (μ m c)) := fun m c =>
    (((continuous_apply c).comp (continuous_apply m)).continuousAt.tendsto.comp hlim :)
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have herr : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφt
  refine ⟨μ, fun m => ⟨hμS m (Set.mem_univ _), fun c hne => ?_, fun a b => ?_⟩, fun m c => ?_⟩
  · obtain ⟨n, hn⟩ := ((hc m c).eventually_ne hne).exists
    exact (nu_good ρ hρ (φ n) m).2.1 c hn
  · refine le_of_tendsto_of_tendsto' (tendsto_finsetSum _ (fun c _ => hc m c))
      (tendsto_const_nhds.add herr) (fun n => (nu_good ρ hρ (φ n) m).2.2 a b)
  · refine tendsto_nhds_unique_of_eventuallyEq (hc m c)
      (tendsto_finsetSum _ (fun c' _ => hc (m + 1) c')) ?_
    filter_upwards [hφt.eventually_ge_atTop (m + 1)] with n hn
    rw [nu_cons ρ (φ n) m hn]
    rfl
end MultiwayGap2325.Dev.AppA
end
end

section
set_option autoImplicit false

noncomputable section

open Classical

namespace MultiwayGap2325.Dev.AppA

open MultiwayGap2325.Main

namespace Realize

/-! ### Generic partition of an interval by consecutive pieces -/

section Partition

variable {α : Type} [Fintype α]

/-- Weights indexed by `ℕ` through the canonical enumeration. -/
def vv (v : α → ℝ) (k : ℕ) : ℝ :=
  if h : k < Fintype.card α then v ((Fintype.equivFin α).symm ⟨k, h⟩) else 0

/-- Partial sums. -/
def FF (v : α → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, vv v j

/-- Left endpoint of the piece of `a`. -/
def off (v : α → ℝ) (a : α) : ℝ := FF v (Fintype.equivFin α a)

lemma vv_nonneg (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) (k : ℕ) : 0 ≤ vv v k := by
  unfold vv; split_ifs
  · exact hv _
  · exact le_refl _

lemma FF_mono (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) : Monotone (FF v) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold FF
  rw [Finset.sum_range_succ]
  linarith [vv_nonneg v hv n]

lemma FF_succ_e (v : α → ℝ) (a : α) :
    FF v ((Fintype.equivFin α a : ℕ) + 1) = off v a + v a := by
  unfold FF off
  rw [Finset.sum_range_succ]
  congr 1
  unfold vv
  rw [dif_pos (Fintype.equivFin α a).2]
  simp

lemma FF_zero (v : α → ℝ) : FF v 0 = 0 := by simp [FF]

lemma FF_card (v : α → ℝ) : FF v (Fintype.card α) = ∑ a, v a := by
  unfold FF
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← (Fintype.equivFin α).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  unfold vv
  rw [dif_pos j.2]

lemma off_uniq (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) (a b : α) (t : ℝ)
    (ha : off v a ≤ t ∧ t < off v a + v a) (hb : off v b ≤ t ∧ t < off v b + v b) : a = b := by
  have key : ∀ a b : α, (Fintype.equivFin α a : ℕ) < Fintype.equivFin α b →
      off v a ≤ t ∧ t < off v a + v a → off v b ≤ t ∧ t < off v b + v b → False := by
    intro a b hlt ha hb
    have h1 : FF v ((Fintype.equivFin α a : ℕ) + 1) ≤ FF v (Fintype.equivFin α b) :=
      FF_mono v hv hlt
    rw [FF_succ_e] at h1
    unfold off at ha hb h1
    linarith [ha.2, hb.1]
  rcases lt_trichotomy (Fintype.equivFin α a : ℕ) (Fintype.equivFin α b) with h | h | h
  · exact (key a b h ha hb).elim
  · exact (Fintype.equivFin α).injective (Fin.ext h)
  · exact (key b a h hb ha).elim

lemma FF_cover (v : α → ℝ) (t : ℝ) :
    ∀ n : ℕ, FF v 0 ≤ t → t < FF v n → ∃ i < n, FF v i ≤ t ∧ t < FF v (i + 1) := by
  intro n
  induction n with
  | zero => intro h0 h1; exact absurd (lt_of_le_of_lt h0 h1) (lt_irrefl _)
  | succ n ih =>
    intro h0 h1
    by_cases h : t < FF v n
    · obtain ⟨i, hi, hh⟩ := ih h0 h
      exact ⟨i, by omega, hh⟩
    · exact ⟨n, by omega, not_lt.mp h, h1⟩

lemma off_cover (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) (t : ℝ) :
    (∃ a, off v a ≤ t ∧ t < off v a + v a) ↔ (0 ≤ t ∧ t < ∑ a, v a) := by
  constructor
  · rintro ⟨a, h1, h2⟩
    constructor
    · have := FF_mono v hv (Nat.zero_le (Fintype.equivFin α a : ℕ))
      rw [FF_zero] at this
      unfold off at h1
      linarith
    · have := FF_mono v hv (show (Fintype.equivFin α a : ℕ) + 1 ≤ Fintype.card α by
        have := (Fintype.equivFin α a).2; omega)
      rw [FF_succ_e, FF_card] at this
      linarith
  · rintro ⟨h0, h1⟩
    rw [← FF_zero v] at h0
    rw [← FF_card v] at h1
    obtain ⟨i, hi, hh1, hh2⟩ := FF_cover v t _ h0 h1
    refine ⟨(Fintype.equivFin α).symm ⟨i, hi⟩, ?_, ?_⟩
    · unfold off; simpa using hh1
    · rw [← FF_succ_e]; simpa using hh2

end Partition

/-! ### Nested intervals realizing a consistent family -/

section Nested

variable {q : ℕ} (μ : ∀ m, Config q m → ℝ)

/-- Weights of the children of `p`. -/
def vpar (m : ℕ) (p : Config q m) : Config q (m + 1) → ℝ :=
  fun c => if restrictUp c = p then μ (m + 1) c else 0

/-- Left endpoints. -/
def L : (m : ℕ) → Config q m → ℝ
  | 0, c => off (μ 0) c
  | m + 1, c => L m (restrictUp c) + off (vpar μ m (restrictUp c)) c

/-- Membership in the interval of `c`. -/
def inI (m : ℕ) (c : Config q m) (t : ℝ) : Prop := L μ m c ≤ t ∧ t < L μ m c + μ m c

variable {μ}

lemma inI_succ (m : ℕ) (c : Config q (m + 1)) (t : ℝ) :
    inI μ (m + 1) c t ↔
      (off (vpar μ m (restrictUp c)) c ≤ t - L μ m (restrictUp c) ∧
        t - L μ m (restrictUp c) <
          off (vpar μ m (restrictUp c)) c + vpar μ m (restrictUp c) c) := by
  have hv : vpar μ m (restrictUp c) c = μ (m + 1) c := by simp [vpar]
  rw [hv]
  unfold inI
  simp only [L]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

lemma vpar_nonneg (hnn : ∀ m c, 0 ≤ μ m c) (m : ℕ) (p : Config q m) (c : Config q (m + 1)) :
    0 ≤ vpar μ m p c := by
  unfold vpar; split_ifs
  · exact hnn _ _
  · exact le_refl _

lemma sum_vpar (hcons : IsConsistent μ) (m : ℕ) (p : Config q m) :
    ∑ c, vpar μ m p c = μ m p := by
  rw [hcons m p, Finset.sum_filter]
  rfl

lemma inI_pos {m : ℕ} {c : Config q m} {t : ℝ} (h : inI μ m c t) : 0 < μ m c := by
  unfold inI at h; linarith [h.1, h.2]

lemma inI_nest (hnn : ∀ m c, 0 ≤ μ m c) (hcons : IsConsistent μ) {m : ℕ}
    {c : Config q (m + 1)} {t : ℝ} (h : inI μ (m + 1) c t) : inI μ m (restrictUp c) t := by
  rw [inI_succ] at h
  have := (off_cover _ (vpar_nonneg hnn m (restrictUp c)) _).mp ⟨c, h⟩
  rw [sum_vpar hcons] at this
  unfold inI
  constructor <;> linarith [this.1, this.2]

lemma inI_cover (hnn : ∀ m c, 0 ≤ μ m c) (hcons : IsConsistent μ) {m : ℕ}
    {p : Config q m} {t : ℝ} (h : inI μ m p t) :
    ∃ c : Config q (m + 1), restrictUp c = p ∧ inI μ (m + 1) c t := by
  have h' : 0 ≤ t - L μ m p ∧ t - L μ m p < ∑ c, vpar μ m p c := by
    rw [sum_vpar hcons]; unfold inI at h; constructor <;> linarith [h.1, h.2]
  obtain ⟨c, hc1, hc2⟩ := (off_cover _ (vpar_nonneg hnn m p) _).mpr h'
  have hpc : restrictUp c = p := by
    by_contra hne
    have : vpar μ m p c = 0 := by simp [vpar, hne]
    linarith
  refine ⟨c, hpc, ?_⟩
  rw [inI_succ, hpc]
  exact ⟨hc1, hc2⟩

lemma inI_uniq (hnn : ∀ m c, 0 ≤ μ m c) (hcons : IsConsistent μ) :
    ∀ (m : ℕ) (c c' : Config q m) (t : ℝ), inI μ m c t → inI μ m c' t → c = c' := by
  intro m
  induction m with
  | zero =>
    intro c c' t h h'
    exact off_uniq (μ 0) (hnn 0) c c' t h h'
  | succ m ih =>
    intro c c' t h h'
    have hp : restrictUp c = restrictUp c' := ih _ _ t (inI_nest hnn hcons h) (inI_nest hnn hcons h')
    rw [inI_succ] at h h'
    rw [← hp] at h'
    exact off_uniq _ (vpar_nonneg hnn m (restrictUp c)) c c' _ h h'

lemma inI_full (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ) :
    ∀ (m : ℕ) (t : ℝ), (0 ≤ t ∧ t < 1) ↔ ∃ c : Config q m, inI μ m c t := by
  intro m
  induction m with
  | zero =>
    intro t
    rw [← h1]
    exact (off_cover (μ 0) (hnn 0) t).symm
  | succ m ih =>
    intro t
    rw [ih]
    constructor
    · rintro ⟨p, hp⟩
      obtain ⟨c, -, hc⟩ := inI_cover hnn hcons hp
      exact ⟨c, hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨_, inI_nest hnn hcons hc⟩

end Nested

/-! ### The random configurations -/

section Omega

variable {q : ℕ} (μ : ∀ m, Config q m → ℝ)

/-- Move points outside `[0,1)` to `0`. -/
def clamp (t : ℝ) : ℝ := if t ∈ Set.Ico (0 : ℝ) 1 then t else 0

lemma clamp_mem (t : ℝ) : 0 ≤ clamp t ∧ clamp t < 1 := by
  unfold clamp
  split_ifs with h
  · exact h
  · norm_num

lemma measurable_clamp : Measurable clamp :=
  Measurable.ite measurableSet_Ico measurable_id measurable_const

/-- The level-`m` random configuration. -/
def omega (m : ℕ) (t : ℝ) : Config q m :=
  if h : ∃ c, inI μ m c (clamp t) then h.choose else fun _ => none

variable {μ}

lemma omega_spec (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ)
    (m : ℕ) (t : ℝ) : inI μ m (omega μ m t) (clamp t) := by
  have h : ∃ c, inI μ m c (clamp t) := (inI_full hnn h1 hcons m _).mp (clamp_mem t)
  unfold omega
  rw [dif_pos h]
  exact h.choose_spec

lemma omega_eq_iff (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ)
    (m : ℕ) (t : ℝ) (c : Config q m) : omega μ m t = c ↔ inI μ m c (clamp t) := by
  constructor
  · rintro rfl; exact omega_spec hnn h1 hcons m t
  · intro h; exact inI_uniq hnn hcons m _ _ _ (omega_spec hnn h1 hcons m t) h

lemma omega_restrict (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ)
    (m : ℕ) (t : ℝ) : restrictUp (omega μ (m + 1) t) = omega μ m t :=
  ((omega_eq_iff hnn h1 hcons m t _).mpr
    (inI_nest hnn hcons (omega_spec hnn h1 hcons (m + 1) t))).symm

lemma omega_pos (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ)
    (m : ℕ) (t : ℝ) : 0 < μ m (omega μ m t) := inI_pos (omega_spec hnn h1 hcons m t)

lemma omega_preimage (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ)
    (m : ℕ) (c : Config q m) :
    omega μ m ⁻¹' {c} = clamp ⁻¹' Set.Ico (L μ m c) (L μ m c + μ m c) := by
  ext t
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico]
  exact omega_eq_iff hnn h1 hcons m t c

lemma measurableSet_omega_preimage (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1)
    (hcons : IsConsistent μ) (m : ℕ) (c : Config q m) : MeasurableSet (omega μ m ⁻¹' {c}) := by
  rw [omega_preimage hnn h1 hcons]
  exact measurable_clamp measurableSet_Ico

/-- The probability measure. -/
def PP : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ico (0 : ℝ) 1)

instance : MeasureTheory.IsProbabilityMeasure PP := by
  constructor
  simp [PP]

lemma PP_omega (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ)
    (m : ℕ) (c : Config q m) : PP (omega μ m ⁻¹' {c}) = ENNReal.ofReal (μ m c) := by
  unfold PP
  rw [MeasureTheory.Measure.restrict_apply (measurableSet_omega_preimage hnn h1 hcons m c)]
  have : omega μ m ⁻¹' {c} ∩ Set.Ico 0 1 = Set.Ico (L μ m c) (L μ m c + μ m c) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, omega_eq_iff hnn h1 hcons]
    constructor
    · rintro ⟨h, ht⟩
      have : clamp t = t := by unfold clamp; rw [if_pos ht]
      rw [this] at h
      exact h
    · intro h
      have ht : t ∈ Set.Ico (0 : ℝ) 1 := (inI_full hnn h1 hcons m t).mpr ⟨c, h⟩
      have : clamp t = t := by unfold clamp; rw [if_pos ht]
      rw [this]
      exact ⟨h, ht⟩
  rw [this, Real.volume_Ico]
  congr 1
  ring

lemma PP_omega_finset (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ)
    (m : ℕ) (S : Finset (Config q m)) :
    PP (omega μ m ⁻¹' ↑S) = ENNReal.ofReal (∑ c ∈ S, μ m c) := by
  rw [← MeasureTheory.sum_measure_preimage_singleton S
    (fun c _ => measurableSet_omega_preimage hnn h1 hcons m c)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => hnn m c)]
  exact Finset.sum_congr rfl (fun c _ => PP_omega hnn h1 hcons m c)

end Omega

/-! ### Rounding to the dyadic grid -/

section Round

variable {q : ℕ}

/-- Partial sums of coordinates. -/
def cum (x : Fin q → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.univ.filter (fun j : Fin q => j.val < k), x j

/-- Rounded partial sums. -/
def AA (m : ℕ) (x : Fin q → ℝ) (k : ℕ) : ℕ := ⌊(2 : ℝ) ^ m * cum x k⌋₊

/-- Coordinates of the rounded point. -/
def coords (m : ℕ) (x : Fin q → ℝ) (i : Fin q) : ℕ := AA m x (i.val + 1) - AA m x i.val

lemma cum_succ (x : Fin q → ℝ) (i : Fin q) : cum x (i.val + 1) = cum x i.val + x i := by
  unfold cum
  rw [Finset.sum_filter, Finset.sum_filter]
  have : x i = ∑ j : Fin q, if j = i then x j else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst hji; simp
  · have : j.val ≠ i.val := fun h => hji (Fin.ext h)
    by_cases hj : j.val < i.val
    · simp [hj, hji, show j.val < i.val + 1 by omega]
    · simp [hj, hji, show ¬ j.val < i.val + 1 by omega]

lemma cum_mono (x : Fin q → ℝ) (hx : ∀ i, 0 ≤ x i) : Monotone (cum x) := by
  intro a b hab
  unfold cum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro j _ _; exact hx j

lemma cum_zero (x : Fin q → ℝ) : cum x 0 = 0 := by simp [cum]

lemma cum_q (x : Fin q → ℝ) (hx : x ∈ stdSimplex ℝ (Fin q)) : cum x q = 1 := by
  unfold cum
  rw [Finset.filter_true_of_mem (fun j _ => j.2)]
  exact hx.2

lemma cum_nonneg (x : Fin q → ℝ) (hx : ∀ i, 0 ≤ x i) (k : ℕ) : 0 ≤ cum x k := by
  rw [← cum_zero x]; exact cum_mono x hx (Nat.zero_le k)

lemma AA_mono (m : ℕ) (x : Fin q → ℝ) (hx : ∀ i, 0 ≤ x i) : Monotone (AA m x) := by
  intro a b hab
  unfold AA
  apply Nat.floor_le_floor
  exact mul_le_mul_of_nonneg_left (cum_mono x hx hab) (by positivity)

lemma AA_zero (m : ℕ) (x : Fin q → ℝ) : AA m x 0 = 0 := by simp [AA, cum_zero]

lemma AA_q (m : ℕ) (x : Fin q → ℝ) (hx : x ∈ stdSimplex ℝ (Fin q)) : AA m x q = 2 ^ m := by
  unfold AA
  rw [cum_q x hx, mul_one]
  exact_mod_cast Nat.floor_natCast (2 ^ m)

lemma sum_coords (m : ℕ) (x : Fin q → ℝ) (hx : x ∈ stdSimplex ℝ (Fin q)) :
    ∑ i, coords m x i = 2 ^ m := by
  unfold coords
  rw [Fin.sum_univ_eq_sum_range (fun k => AA m x (k + 1) - AA m x k) q]
  rw [Finset.sum_range_tsub (AA_mono m x hx.1) q, AA_q m x hx, AA_zero]
  simp

lemma coords_le (m : ℕ) (x : Fin q → ℝ) (hx : x ∈ stdSimplex ℝ (Fin q)) (i : Fin q) :
    coords m x i < 2 ^ m + 1 := by
  have := Finset.single_le_sum (f := fun i => coords m x i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  rw [sum_coords m x hx] at this
  omega

/-- The rounding map `π_m`. -/
def pi (m : ℕ) (x : Simplex q) : GridPt q m :=
  ⟨fun i => ⟨coords m x.1 i, coords_le m x.1 x.2 i⟩, sum_coords m x.1 x.2⟩

lemma pi_val (m : ℕ) (x : Simplex q) (i : Fin q) : (((pi m x).1 i : ℕ)) = coords m x.1 i := rfl

lemma pi_support (m : ℕ) (x : Simplex q) (i : Fin q) (h : 0 < (((pi m x).1 i : ℕ))) :
    0 < x.1 i := by
  rw [pi_val] at h
  unfold coords at h
  by_contra hneg
  have hle : cum x.1 (i.val + 1) ≤ cum x.1 i.val := by rw [cum_succ]; linarith [not_lt.mp hneg]
  have : AA m x.1 (i.val + 1) ≤ AA m x.1 i.val := by
    unfold AA
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left hle (by positivity))
  omega

lemma pi_vertex (m : ℕ) (i : Fin q) : pi m (simplexVertex i) = GridPt.vertex i := by
  have hcum : ∀ k : ℕ, cum (simplexVertex i).1 k = if i.val < k then 1 else 0 := by
    intro k
    unfold cum simplexVertex
    rw [Finset.sum_filter]
    rw [Finset.sum_eq_single i]
    · by_cases h : i.val < k <;> simp [h]
    · intro j _ hj; simp [hj]
    · simp
  have hAA : ∀ k : ℕ, AA m (simplexVertex i).1 k = if i.val < k then 2 ^ m else 0 := by
    intro k
    unfold AA
    rw [hcum k]
    by_cases h : i.val < k
    · simp only [h, if_true, mul_one]; exact_mod_cast Nat.floor_natCast (2 ^ m)
    · simp [h]
  apply Subtype.ext
  funext j
  apply Fin.ext
  rw [pi_val]
  unfold coords GridPt.vertex
  rw [hAA, hAA]
  by_cases hj : j = i
  · subst hj; simp
  · have : j.val ≠ i.val := fun h => hj (Fin.ext h)
    by_cases hlt : i.val < j.val
    · simp [hj, hlt, show i.val < j.val + 1 by omega]
    · simp [hj, hlt, show ¬ i.val < j.val + 1 by omega]

lemma floor_err (m : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    |((⌊(2 : ℝ) ^ m * c⌋₊ : ℕ) : ℝ) / 2 ^ m - c| ≤ (1 / 2) ^ m := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have h1 := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ m * c by positivity)
  have h2 := Nat.lt_floor_add_one ((2 : ℝ) ^ m * c)
  have key : ((⌊(2 : ℝ) ^ m * c⌋₊ : ℕ) : ℝ) / 2 ^ m - c =
      (((⌊(2 : ℝ) ^ m * c⌋₊ : ℕ) : ℝ) - 2 ^ m * c) / 2 ^ m := by
    field_simp
  rw [key, one_div_pow, abs_le]
  constructor
  · rw [← neg_div, div_le_div_iff_of_pos_right hp]; linarith
  · rw [div_le_div_iff_of_pos_right hp]; linarith

lemma coord_err (m : ℕ) (x : Simplex q) (i : Fin q) :
    |(((pi m x).1 i : ℕ) : ℝ) / 2 ^ m - x.1 i| ≤ 2 * (1 / 2) ^ m := by
  have hx := x.2.1
  rw [pi_val]
  unfold coords
  have hmono := AA_mono m x.1 hx (Nat.le_succ i.val)
  rw [Nat.cast_sub hmono]
  have e1 := floor_err m (cum x.1 (i.val + 1)) (cum_nonneg x.1 hx _)
  have e2 := floor_err m (cum x.1 i.val) (cum_nonneg x.1 hx _)
  have hxi : x.1 i = cum x.1 (i.val + 1) - cum x.1 i.val := by rw [cum_succ]; ring
  have : ((AA m x.1 (i.val + 1) : ℝ) - AA m x.1 i.val) / 2 ^ m - x.1 i =
      (((⌊(2 : ℝ) ^ m * cum x.1 (i.val + 1)⌋₊ : ℕ) : ℝ) / 2 ^ m - cum x.1 (i.val + 1)) -
      (((⌊(2 : ℝ) ^ m * cum x.1 i.val⌋₊ : ℕ) : ℝ) / 2 ^ m - cum x.1 i.val) := by
    rw [hxi]; unfold AA; ring
  rw [this]
  exact (abs_sub _ _).trans (by linarith)

lemma halfL1_triangle (u v w : Fin q → ℝ) :
    MultiwayCut.halfL1 u w ≤ MultiwayCut.halfL1 u v + MultiwayCut.halfL1 v w := by
  unfold MultiwayCut.halfL1
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  exact abs_sub_le _ _ _

lemma halfL1_symm (u v : Fin q → ℝ) : MultiwayCut.halfL1 u v = MultiwayCut.halfL1 v u := by
  unfold MultiwayCut.halfL1
  congr 1
  exact Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)

lemma dist_pi (m : ℕ) (x : Simplex q) :
    simplexDistance (pi m x).toSimplex x ≤ q * (1 / 2) ^ m := by
  unfold simplexDistance MultiwayCut.halfL1
  have : ∑ i, |((pi m x).toSimplex).1 i - x.1 i| ≤ ∑ _i : Fin q, 2 * (1 / 2 : ℝ) ^ m :=
    Finset.sum_le_sum (fun i _ => coord_err m x i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

lemma toSimplex_up {m : ℕ} (a : GridPt q m) : (a.up).toSimplex = a.toSimplex := by
  apply Subtype.ext
  funext i
  simp only [GridPt.toSimplex, GridPt.up]
  push_cast
  rw [pow_succ]
  field_simp

lemma dist_pi_pi (m : ℕ) (x y : Simplex q) :
    simplexDistance (pi m x).toSimplex (pi m y).toSimplex ≤
      simplexDistance x y + 2 * q * (1 / 2) ^ m := by
  unfold simplexDistance
  have h1 := halfL1_triangle (pi m x).toSimplex.1 x.1 (pi m y).toSimplex.1
  have h2 := halfL1_triangle x.1 y.1 (pi m y).toSimplex.1
  have h3 := dist_pi m x
  have h4 := dist_pi m y
  unfold simplexDistance at h3 h4
  rw [halfL1_symm y.1] at h2
  linarith

lemma dist_pi_succ (m : ℕ) (x : Simplex q) :
    simplexDistance (pi m x).up.toSimplex (pi (m + 1) x).toSimplex ≤ 2 * q * (1 / 2) ^ m := by
  rw [toSimplex_up]
  unfold simplexDistance
  have h1 := halfL1_triangle (pi m x).toSimplex.1 x.1 (pi (m + 1) x).toSimplex.1
  have h3 := dist_pi m x
  have h4 := dist_pi (m + 1) x
  unfold simplexDistance at h3 h4
  rw [halfL1_symm x.1] at h1
  have : (q : ℝ) * (1 / 2) ^ (m + 1) ≤ q * (1 / 2) ^ m := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [pow_succ]
    have : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
    linarith
  linarith

lemma measurable_coords (m : ℕ) : Measurable (fun x : Simplex q => coords m x.1) := by
  have hcum : ∀ k, Measurable (fun x : Simplex q => cum x.1 k) := by
    intro k
    unfold cum
    apply Finset.measurable_sum
    intro j _
    exact (measurable_pi_apply j).comp measurable_subtype_coe
  have hAA : ∀ k, Measurable (fun x : Simplex q => AA m x.1 k) := by
    intro k
    unfold AA
    exact (measurable_const.mul (hcum k)).nat_floor
  apply measurable_pi_lambda
  intro i
  exact (measurable_of_countable (fun p : ℕ × ℕ => p.1 - p.2)).comp
    ((hAA (i.val + 1)).prodMk (hAA i.val))

lemma measurableSet_pi_preimage (m : ℕ) (a : GridPt q m) : MeasurableSet (pi m ⁻¹' {a}) := by
  have : pi m ⁻¹' {a} = (fun x : Simplex q => coords m x.1) ⁻¹' {fun i => ((a.1 i : ℕ))} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl; rfl
    · intro h
      apply Subtype.ext
      funext i
      apply Fin.ext
      exact congrFun h i
  rw [this]
  exact measurable_coords m (measurableSet_singleton _)

end Round

/-! ### The limiting labeling -/

section Final

open Filter MeasureTheory

variable {q : ℕ} (μ : ∀ m, Config q m → ℝ)

/-- The level-`m` approximate labeling `Y_m(ξ, x) = ω_m(ξ)(π_m x)`. -/
def Y (m : ℕ) (p : ℝ × Simplex q) : CutLabel q := omega μ m p.1 (pi m p.2)

/-- The eventual value of `Y_m`, or `∗`. -/
def Clab (p : ℝ × Simplex q) : CutLabel q :=
  if h : ∃ v, ∀ᶠ m in atTop, Y μ m p = v then h.choose else none

variable {μ}

lemma Clab_eq (p : ℝ × Simplex q) (v : CutLabel q) (h : ∀ᶠ m in atTop, Y μ m p = v) :
    Clab μ p = v := by
  have hex : ∃ v, ∀ᶠ m in atTop, Y μ m p = v := ⟨v, h⟩
  unfold Clab
  rw [dif_pos hex]
  obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
  rw [← hm1, hm2]

lemma Clab_none (p : ℝ × Simplex q) (h : ¬ ∃ v, ∀ᶠ m in atTop, Y μ m p = v) :
    Clab μ p = none := by
  unfold Clab; rw [dif_neg h]

lemma measurable_Y (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ)
    (m : ℕ) : Measurable (Y μ m) := by
  apply measurable_to_countable'
  intro v
  have : Y μ m ⁻¹' {v} = ⋃ c : Config q m, ⋃ a : GridPt q m, ⋃ (_ : c a = v),
      (omega μ m ⁻¹' {c}) ×ˢ (pi m ⁻¹' {a}) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_prod, Y]
    constructor
    · intro h; exact ⟨_, _, h, rfl, rfl⟩
    · rintro ⟨c, a, h, h1, h2⟩; rw [h1, h2]; exact h
  rw [this]
  exact MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ =>
    (measurableSet_omega_preimage hnn h1 hcons m c).prod (measurableSet_pi_preimage m a)

lemma measurableSet_ev (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ)
    (v : CutLabel q) : MeasurableSet {p : ℝ × Simplex q | ∀ᶠ m in atTop, Y μ m p = v} := by
  have : {p : ℝ × Simplex q | ∀ᶠ m in atTop, Y μ m p = v} =
      ⋃ N : ℕ, ⋂ m : ℕ, ⋂ (_ : N ≤ m), Y μ m ⁻¹' {v} := by
    ext p
    simp [Filter.eventually_atTop]
  rw [this]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    measurable_Y hnn h1 hcons m (measurableSet_singleton v)

lemma measurable_Clab (hnn : ∀ m c, 0 ≤ μ m c) (h1 : ∑ c, μ 0 c = 1) (hcons : IsConsistent μ) :
    Measurable (Clab μ) := by
  apply measurable_to_countable'
  intro v
  have : Clab μ ⁻¹' {v} = {p | ∀ᶠ m in atTop, Y μ m p = v} ∪
      ((⋃ w, {p : ℝ × Simplex q | ∀ᶠ m in atTop, Y μ m p = w})ᶜ ∩ {_p | v = none}) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    by_cases h : ∃ w, ∀ᶠ m in atTop, Y μ m p = w
    · obtain ⟨w, hw⟩ := h
      rw [Clab_eq p w hw]
      constructor
      · rintro rfl; exact Or.inl hw
      · rintro (h' | ⟨h', -⟩)
        · obtain ⟨m, hm1, hm2⟩ := (hw.and h').exists
          rw [← hm1, hm2]
        · exact (h' w hw).elim
    · rw [Clab_none p h]
      have h : ∀ w, ¬ ∀ᶠ m in atTop, Y μ m p = w := fun w hw => h ⟨w, hw⟩
      constructor
      · rintro rfl; exact Or.inr ⟨h, rfl⟩
      · rintro (h' | ⟨-, h'⟩)
        · exact (h v h').elim
        · exact h'.symm
  rw [this]
  exact (measurableSet_ev hnn h1 hcons v).union
    ((MeasurableSet.iUnion fun w => measurableSet_ev hnn h1 hcons w).compl.inter
      (MeasurableSet.const _))

lemma omega_nonopp {g : ℝ} (hgood : ∀ m, IsGoodLaw g 0 (μ m)) (hcons : IsConsistent μ)
    (m : ℕ) (t : ℝ) : IsNonOppConfig (omega μ m t) :=
  (hgood m).2.1 _ (ne_of_gt (omega_pos (fun m c => (hgood m).1.1 c) (hgood 0).1.2 hcons m t))

lemma Clab_nonOpp {g : ℝ} (hgood : ∀ m, IsGoodLaw g 0 (μ m)) (hcons : IsConsistent μ)
    (t : ℝ) : IsNonOpposite (fun x => Clab μ (t, x)) := by
  constructor
  · intro i
    apply Clab_eq
    apply Filter.Eventually.of_forall
    intro m
    unfold Y
    simp only
    rw [pi_vertex]
    exact (omega_nonopp hgood hcons m t).1 i
  · intro x i h
    simp only at h
    by_cases hex : ∃ v, ∀ᶠ m in atTop, Y μ m (t, x) = v
    · unfold Clab at h
      rw [dif_pos hex] at h
      obtain ⟨m, hm⟩ := hex.choose_spec.exists
      rw [h] at hm
      exact pi_support m x i ((omega_nonopp hgood hcons m t).2 _ i hm)
    · rw [Clab_none _ hex] at h
      exact absurd h (by simp)

lemma halfL1_nonneg' (u v : Fin q → ℝ) : 0 ≤ MultiwayCut.halfL1 u v := by
  unfold MultiwayCut.halfL1
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => abs_nonneg _))

lemma sep_bound {g : ℝ} (hgood : ∀ m, IsGoodLaw g 0 (μ m)) (hcons : IsConsistent μ)
    (m : ℕ) (a b : GridPt q m) :
    PP {t | omega μ m t a ≠ omega μ m t b} ≤
      ENNReal.ofReal (g * simplexDistance a.toSimplex b.toSimplex) := by
  have : {t | omega μ m t a ≠ omega μ m t b} =
      omega μ m ⁻¹' ↑(Finset.univ.filter (fun c : Config q m => c a ≠ c b)) := by
    ext t; simp
  rw [this, PP_omega_finset (fun m c => (hgood m).1.1 c) (hgood 0).1.2 hcons]
  apply ENNReal.ofReal_le_ofReal
  have := (hgood m).2.2 a b
  linarith

lemma eventually_const {β : Type} (s : ℕ → β) (h : ∀ᶠ m in atTop, s m = s (m + 1)) :
    ∃ v, ∀ᶠ m in atTop, s m = v := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  refine ⟨s N, Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩⟩
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [← hN n hn, ih]

lemma ae_Clab {g : ℝ} (hg : 0 ≤ g) (hgood : ∀ m, IsGoodLaw g 0 (μ m)) (hcons : IsConsistent μ)
    (x : Simplex q) : ∀ᵐ t ∂PP, ∀ᶠ m in atTop, Y μ m (t, x) = Clab μ (t, x) := by
  have hnn : ∀ m c, 0 ≤ μ m c := fun m c => (hgood m).1.1 c
  have h1 : ∑ c, μ 0 c = 1 := (hgood 0).1.2
  set B : ℕ → Set ℝ := fun m => {t | Y μ m (t, x) ≠ Y μ (m + 1) (t, x)} with hB
  have hBm : ∀ m, PP (B m) ≤ ENNReal.ofReal ((g * (2 * q)) * (1 / 2) ^ m) := by
    intro m
    have : B m = {t | omega μ (m + 1) t (pi m x).up ≠ omega μ (m + 1) t (pi (m + 1) x)} := by
      ext t
      simp only [hB, Set.mem_ofPred_eq, Y]
      rw [← omega_restrict hnn h1 hcons m t]
      rfl
    rw [this]
    refine (sep_bound hgood hcons (m + 1) _ _).trans (ENNReal.ofReal_le_ofReal ?_)
    have := mul_le_mul_of_nonneg_left (dist_pi_succ m x) hg
    linarith
  have hsum : ∑' m, PP (B m) ≠ ⊤ := by
    have hs : Summable (fun m : ℕ => (g * (2 * q)) * (1 / 2 : ℝ) ^ m) :=
      summable_geometric_two.mul_left _
    have hle := ENNReal.tsum_le_tsum hBm
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hs] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  filter_upwards [ae_eventually_notMem hsum] with t ht
  have ht' : ∀ᶠ m in atTop, Y μ m (t, x) = Y μ (m + 1) (t, x) := by
    filter_upwards [ht] with m hm
    simpa [hB] using hm
  obtain ⟨v, hv⟩ := eventually_const (fun m => Y μ m (t, x)) ht'
  rw [Clab_eq _ v hv]
  exact hv

lemma approx {g : ℝ} (hg : 0 ≤ g) (hgood : ∀ m, IsGoodLaw g 0 (μ m)) (hcons : IsConsistent μ)
    (x y : Simplex q) :
    PP {t | Clab μ (t, x) ≠ Clab μ (t, y)} ≤ ENNReal.ofReal (g * simplexDistance x y) := by
  set E : ℕ → Set ℝ := fun N => {t | ∀ m, N ≤ m → Y μ m (t, x) ≠ Y μ m (t, y)} with hE
  have hmono : Monotone E := by
    intro N N' hNN' t ht m hm
    exact ht m (le_trans hNN' hm)
  have hsub : {t | Clab μ (t, x) ≠ Clab μ (t, y)} ≤ᵐ[PP] ⋃ N, E N := by
    filter_upwards [ae_Clab hg hgood hcons x, ae_Clab hg hgood hcons y] with t hx hy
    intro hne
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hx.and hy)
    refine Set.mem_iUnion.mpr ⟨N, fun m hm => ?_⟩
    rw [(hN m hm).1, (hN m hm).2]
    exact hne
  refine (measure_mono_ae hsub).trans ?_
  have hd : 0 ≤ g * simplexDistance x y := mul_nonneg hg (halfL1_nonneg' _ _)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  apply le_of_tendsto' (tendsto_measure_iUnion_atTop hmono)
  intro N
  simp only [Function.comp]
  have hεr : (0 : ℝ) < ε := hε
  set K : ℝ := g * (2 * q) with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨m0, hm0⟩ := exists_pow_lt_of_lt_one (show 0 < (ε : ℝ) / (K + 1) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  set m := max N m0
  have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ m0 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
  have hKm : K * (1 / 2) ^ m ≤ ε := by
    have h0 : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
    have : (K + 1) * ((1 / 2) ^ m0) < (K + 1) * ((ε : ℝ) / (K + 1)) :=
      mul_lt_mul_of_pos_left hm0 (by positivity)
    rw [mul_div_cancel₀ _ (by positivity)] at this
    nlinarith
  have hEm : E N ⊆ {t | omega μ m t (pi m x) ≠ omega μ m t (pi m y)} := by
    intro t ht
    exact ht m (le_max_left _ _)
  refine (measure_mono hEm).trans ((sep_bound hgood hcons m _ _).trans ?_)
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add hd hεr.le]
  apply ENNReal.ofReal_le_ofReal
  have := mul_le_mul_of_nonneg_left (dist_pi_pi m x y) hg
  have : g * (2 * q * (1 / 2) ^ m) = K * (1 / 2) ^ m := by rw [hK]; ring
  nlinarith

end Final

end Realize

open Realize in
theorem realize {q : ℕ} (hq : 2 ≤ q) (g : ℝ) (hg : 0 ≤ g) (μ : ∀ m, Config q m → ℝ)
    (hgood : ∀ m, IsGoodLaw g 0 (μ m)) (hcons : IsConsistent μ) :
    ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (P : MeasureTheory.Measure Ξ)
      (_ : MeasureTheory.IsProbabilityMeasure P) (C : RandomNonOppositeCut q Ξ P),
      HasApproximationFactor C g := by
  have hnn : ∀ m c, 0 ≤ μ m c := fun m c => (hgood m).1.1 c
  have h1 : ∑ c, μ 0 c = 1 := (hgood 0).1.2
  refine ⟨ℝ, inferInstance, PP, inferInstance,
    ⟨Clab μ, measurable_Clab hnn h1 hcons, Clab_nonOpp hgood hcons⟩, ?_⟩
  intro x y
  exact approx hg hgood hcons x y

end MultiwayGap2325.Dev.AppA
end
end

section
set_option autoImplicit false
open Classical
namespace MultiwayGap2325.Dev.AppA
open MultiwayGap2325.Main

end MultiwayGap2325.Dev.AppA

namespace MultiwayGap2325.Main
open MultiwayGap2325.Dev.AppA

theorem chk_exists_nonOppositeCut_of_tendsto_gapSequence (q : ℕ) (hq : 2 ≤ q) (g : ℝ)
    (hg : Filter.Tendsto gapSequence Filter.atTop (nhds g)) :
    ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (P : MeasureTheory.Measure Ξ)
      (_ : MeasureTheory.IsProbabilityMeasure P) (C : RandomNonOppositeCut q Ξ P),
      HasApproximationFactor C g := by
  obtain ⟨hk, hmono, -⟩ := gap_sequence_well_posed
  have hle : ∀ k, gapSequence k ≤ g := fun k => hmono.ge_of_tendsto hg k
  have hg1 : 1 ≤ g := le_trans (hk 2 le_rfl).2.2.2.2.2.2.1 (hle 2)
  have hdist : ∀ {M : ℕ} (a b : GridPt q M), 0 ≤ simplexDistance a.toSimplex b.toSimplex := by
    intro M a b
    unfold simplexDistance MultiwayCut.halfL1
    positivity
  have hlaw : ∀ (M : ℕ) (ε : ℝ), 0 < ε → ∃ μ : Config q M → ℝ, IsGoodLaw g ε μ := by
    intro M ε hε
    -- choose k with 2q ≤ k and 2q/(k-q) ≤ ε
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * q / ε + 2 * q)
    set k := N with hkdef
    have hk2q : 2 * q ≤ k := by
      have : ((2 * q : ℕ) : ℝ) < k := by push_cast; nlinarith [div_nonneg (by positivity : (0:ℝ) ≤ 2 * q) hε.le]
      exact_mod_cast this.le
    have hkq : (0 : ℝ) < (k : ℝ) - q := by
      have : ((2 * q : ℕ) : ℝ) ≤ k := by exact_mod_cast hk2q
      push_cast at this
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have herr : (2 * q : ℝ) / ((k : ℝ) - q) ≤ ε := by
      rw [div_le_iff₀ hkq]
      have h1 : 2 * (q : ℝ) / ε < k - q := by
        have : (q : ℝ) ≥ 0 := by positivity
        linarith
      have := (div_lt_iff₀ hε).mp h1
      linarith
    obtain ⟨μ, h1, h2, h3⟩ := face_law hq M k hk2q (kkst_finite (by omega))
    refine ⟨μ, h1, h2, fun a b => (h3 a b).trans ?_⟩
    have := mul_le_mul_of_nonneg_right (hle k) (hdist a b)
    linarith
  obtain ⟨μ, hgood, hcons⟩ := compact_limit hq g hlaw
  exact realize hq g (by linarith) μ hgood hcons

end MultiwayGap2325.Main
end

theorem solution : type_of% @MultiwayGap2325.Main.chk_exists_nonOppositeCut_of_tendsto_gapSequence := @MultiwayGap2325.Main.chk_exists_nonOppositeCut_of_tendsto_gapSequence
