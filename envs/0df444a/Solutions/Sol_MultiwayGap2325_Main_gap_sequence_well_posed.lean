-- Prove2me | solution 1 for MultiwayGap2325.Main.gap_sequence_well_posed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:45:27.067756+00:00
-- url     : https://prove2.me/submissions/5b7ad09b-d0b7-4215-9dc7-625db23ba552

import Mathlib
import Definitions.Def_MultiwayCut_Instance
import Definitions.Def_MultiwayGap2325_Main_FiniteGap

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
set_option autoImplicit false

noncomputable section

namespace MultiwayGap2325.Dev.WellPosed

open MultiwayCut MultiwayGap2325.Main

/-! ### Basic nonnegativity and nonemptiness -/

theorem cutWeight_nonneg {V : Type*} {k : ℕ} (I : Instance V k) (c : V → Fin k) :
    0 ≤ cutWeight I c := by
  unfold cutWeight
  apply Finset.sum_nonneg
  intro e he
  exact I.w_nonneg e (Finset.mem_filter.mp he).1

theorem halfL1_nonneg {k : ℕ} (u v : Fin k → ℝ) : 0 ≤ halfL1 u v := by
  unfold halfL1
  have : 0 ≤ ∑ ℓ, |u ℓ - v ℓ| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

theorem relaxValue_nonneg {V : Type*} {k : ℕ} (I : Instance V k) (x : V → Fin k → ℝ) :
    0 ≤ relaxValue I x := by
  unfold relaxValue
  apply Finset.sum_nonneg
  intro e he
  exact mul_nonneg (I.w_nonneg e he) (halfL1_nonneg _ _)

theorem integralValues_bdd {V : Type*} {k : ℕ} (I : Instance V k) :
    BddBelow (integralValues I) := by
  refine ⟨0, ?_⟩
  rintro r ⟨c, -, rfl⟩
  exact cutWeight_nonneg I c

theorem fractionalValues_bdd {V : Type*} {k : ℕ} (I : Instance V k) :
    BddBelow (fractionalValues I) := by
  refine ⟨0, ?_⟩
  rintro r ⟨x, -, rfl⟩
  exact relaxValue_nonneg I x

theorem exists_labeling {V : Type*} {k : ℕ} (hk : 1 ≤ k) (I : Instance V k) :
    ∃ c : V → Fin k, IsFeasibleLabeling I c := by
  classical
  refine ⟨fun v => if h : ∃ i, I.t i = v then h.choose else ⟨0, hk⟩, ?_⟩
  intro i
  have h : ∃ j, I.t j = I.t i := ⟨i, rfl⟩
  simp only [dif_pos h]
  exact I.t_injective h.choose_spec

theorem integralValues_nonempty {V : Type*} {k : ℕ} (hk : 1 ≤ k) (I : Instance V k) :
    (integralValues I).Nonempty := by
  obtain ⟨c, hc⟩ := exists_labeling hk I
  exact ⟨_, c, hc, rfl⟩

theorem fractionalValues_nonempty {V : Type*} {k : ℕ} (hk : 1 ≤ k) (I : Instance V k) :
    (fractionalValues I).Nonempty := by
  obtain ⟨c, hc⟩ := exists_labeling hk I
  refine ⟨_, fun v => Pi.single (c v) 1, ⟨fun v => single_mem_stdSimplex ℝ (c v), ?_⟩, rfl⟩
  intro i
  simp [hc i]

theorem fractionalOpt_nonneg {V : Type*} {k : ℕ} (hk : 1 ≤ k) (I : Instance V k) :
    0 ≤ fractionalOpt I := by
  apply le_csInf (fractionalValues_nonempty hk I)
  rintro r ⟨x, -, rfl⟩
  exact relaxValue_nonneg I x

/-! ### The CKR upper bound -/

section CKR

variable (hckr : ∀ {n k : ℕ}, 1 ≤ k → ∀ (I : MultiwayCut.Instance (Fin n) k)
      (x : Fin n → Fin k → ℝ), MultiwayCut.IsFeasibleEmbedding I x →
      ∃ c : Fin n → Fin k, MultiwayCut.IsFeasibleLabeling I c ∧
        MultiwayCut.cutWeight I c ≤ 3 / 2 * MultiwayCut.relaxValue I x)

include hckr in
theorem integralOpt_le {n k : ℕ} (hk : 1 ≤ k) (I : Instance (Fin n) k) :
    integralOpt I ≤ 3 / 2 * fractionalOpt I := by
  have : integralOpt I / (3 / 2) ≤ fractionalOpt I := by
    apply le_csInf (fractionalValues_nonempty hk I)
    rintro r ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hcx⟩ := hckr hk I x hx
    have h1 : integralOpt I ≤ cutWeight I c := csInf_le (integralValues_bdd I) ⟨c, hc, rfl⟩
    rw [div_le_iff₀ (by norm_num)]
    linarith
  rw [div_le_iff₀ (by norm_num)] at this
  linarith

include hckr in
theorem instanceGap_le {n k : ℕ} (hk : 1 ≤ k) (I : Instance (Fin n) k) :
    instanceGap I ≤ 3 / 2 := by
  unfold instanceGap
  split_ifs with h
  · norm_num
  · have hpos : 0 < fractionalOpt I := lt_of_le_of_ne (fractionalOpt_nonneg hk I) (Ne.symm h)
    rw [div_le_iff₀ hpos]
    exact integralOpt_le hckr hk I

end CKR

/-! ### The gap-one instance -/

theorem halfL1_single {k : ℕ} (i j : Fin k) (hij : i ≠ j) :
    halfL1 (Pi.single i (1 : ℝ)) (Pi.single j 1) = 1 := by
  unfold halfL1
  have : ∀ ℓ, |(Pi.single i (1 : ℝ) : Fin k → ℝ) ℓ - (Pi.single j (1 : ℝ) : Fin k → ℝ) ℓ|
      = (Pi.single i (1 : ℝ) : Fin k → ℝ) ℓ + (Pi.single j (1 : ℝ) : Fin k → ℝ) ℓ := by
    intro ℓ
    by_cases h1 : ℓ = i
    · subst h1
      simp [hij]
    · by_cases h2 : ℓ = j
      · subst h2
        simp [h1]
      · simp [h1, h2]
  simp only [this, Finset.sum_add_distrib, Finset.sum_pi_single']
  simp
  norm_num

/-- The one-edge instance on `Fin k`. -/
def oneEdge (k : ℕ) (hk : 2 ≤ k) : Instance (Fin k) k where
  E := {((⟨0, by omega⟩ : Fin k), (⟨1, by omega⟩ : Fin k))}
  w := fun _ => 1
  w_nonneg := fun _ _ => zero_le_one
  t := id
  t_injective := Function.injective_id

theorem oneEdge_integralValues (k : ℕ) (hk : 2 ≤ k) :
    integralValues (oneEdge k hk) = {1} := by
  ext r
  simp only [integralValues, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    have h0 := hc ⟨0, by omega⟩
    have h1 := hc ⟨1, by omega⟩
    simp only [oneEdge, id] at h0 h1
    simp only [cutWeight, oneEdge]
    rw [Finset.filter_singleton, if_pos]
    · simp
    · simp only [h0, h1]
      intro h
      simp [Fin.ext_iff] at h
  · rintro rfl
    refine ⟨id, fun i => rfl, ?_⟩
    simp only [cutWeight, oneEdge]
    rw [Finset.filter_singleton, if_pos]
    · simp
    · simp [Fin.ext_iff]

theorem oneEdge_fractionalValues (k : ℕ) (hk : 2 ≤ k) :
    fractionalValues (oneEdge k hk) = {1} := by
  ext r
  simp only [fractionalValues, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h0 := hx.2 ⟨0, by omega⟩
    have h1 := hx.2 ⟨1, by omega⟩
    simp only [oneEdge, id] at h0 h1
    simp only [relaxValue, oneEdge, Finset.sum_singleton, one_mul]
    rw [h0, h1]
    exact halfL1_single _ _ (by simp [Fin.ext_iff])
  · rintro rfl
    refine ⟨fun v => Pi.single v 1, ⟨fun v => single_mem_stdSimplex ℝ v, fun i => rfl⟩, ?_⟩
    simp only [relaxValue, oneEdge, Finset.sum_singleton, one_mul]
    exact (halfL1_single _ _ (by simp [Fin.ext_iff])).symm

theorem oneEdge_integralOpt (k : ℕ) (hk : 2 ≤ k) : integralOpt (oneEdge k hk) = 1 := by
  simp [integralOpt, oneEdge_integralValues]

theorem oneEdge_fractionalOpt (k : ℕ) (hk : 2 ≤ k) : fractionalOpt (oneEdge k hk) = 1 := by
  simp [fractionalOpt, oneEdge_fractionalValues]

theorem oneEdge_gap (k : ℕ) (hk : 2 ≤ k) : instanceGap (oneEdge k hk) = 1 := by
  simp [instanceGap, oneEdge_fractionalOpt, oneEdge_integralOpt]

/-! ### Adding an isolated terminal -/

section Extend

variable {n k : ℕ}

/-- Coordinate extension by a zero last coordinate. -/
def extV (y : Fin k → ℝ) : Fin (k + 1) → ℝ := fun j => Fin.lastCases (motive := fun _ => ℝ) 0 y j

@[simp] theorem extV_castSucc (y : Fin k → ℝ) (i : Fin k) : extV y (Fin.castSucc i) = y i := by
  simp [extV]

@[simp] theorem extV_last (y : Fin k → ℝ) : extV y (Fin.last k) = 0 := by
  simp [extV]

theorem extV_single (i : Fin k) : extV (Pi.single i (1 : ℝ)) = Pi.single (Fin.castSucc i) 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [(Fin.castSucc_lt_last i).ne]
  | cast j => simp [Pi.single_apply]

theorem extV_mem {y : Fin k → ℝ} (hy : y ∈ stdSimplex ℝ (Fin k)) :
    extV y ∈ stdSimplex ℝ (Fin (k + 1)) := by
  refine ⟨fun j => ?_, ?_⟩
  · induction j using Fin.lastCases with
    | last => simp
    | cast j => simpa using hy.1 j
  · rw [Fin.sum_univ_castSucc]
    simpa using hy.2

theorem halfL1_extV (a b : Fin k → ℝ) : halfL1 (extV a) (extV b) = halfL1 a b := by
  unfold halfL1
  rw [Fin.sum_univ_castSucc]
  simp

/-- Projection merging the last coordinate into coordinate `i0`. -/
def projV (i0 : Fin k) (z : Fin (k + 1) → ℝ) : Fin k → ℝ :=
  fun i => z (Fin.castSucc i) + if i = i0 then z (Fin.last k) else 0

theorem projV_mem (i0 : Fin k) {z : Fin (k + 1) → ℝ} (hz : z ∈ stdSimplex ℝ (Fin (k + 1))) :
    projV i0 z ∈ stdSimplex ℝ (Fin k) := by
  refine ⟨fun i => ?_, ?_⟩
  · unfold projV
    have := hz.1 (Fin.castSucc i)
    have := hz.1 (Fin.last k)
    split_ifs <;> linarith
  · unfold projV
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    have := hz.2
    rw [Fin.sum_univ_castSucc] at this
    simpa using this

theorem projV_single (i0 i : Fin k) :
    projV i0 (Pi.single (Fin.castSucc i) (1 : ℝ)) = Pi.single i 1 := by
  funext j
  simp [projV, Pi.single_apply, (Fin.castSucc_lt_last i).ne']

theorem halfL1_projV_le (i0 : Fin k) (a b : Fin (k + 1) → ℝ) :
    halfL1 (projV i0 a) (projV i0 b) ≤ halfL1 a b := by
  unfold halfL1
  have key : ∀ j : Fin k, |projV i0 a j - projV i0 b j| ≤
      |a (Fin.castSucc j) - b (Fin.castSucc j)| +
        if j = i0 then |a (Fin.last k) - b (Fin.last k)| else 0 := by
    intro j
    unfold projV
    split_ifs
    · have : a (Fin.castSucc j) + a (Fin.last k) - (b (Fin.castSucc j) + b (Fin.last k)) =
          (a (Fin.castSucc j) - b (Fin.castSucc j)) + (a (Fin.last k) - b (Fin.last k)) := by ring
      rw [this]
      exact abs_add_le _ _
    · simp
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => key j)
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsum
  rw [Fin.sum_univ_castSucc (f := fun ℓ => |a ℓ - b ℓ|)]
  simp only [Finset.mem_univ, if_true] at hsum
  linarith

/-- The new terminal map. -/
def extT (t : Fin k → Fin n) : Fin (k + 1) → Fin (n + 1) :=
  fun j => Fin.lastCases (motive := fun _ => Fin (n + 1)) (Fin.last n)
    (fun i => Fin.castSucc (t i)) j

@[simp] theorem extT_castSucc (t : Fin k → Fin n) (i : Fin k) :
    extT t (Fin.castSucc i) = Fin.castSucc (t i) := by simp [extT]

@[simp] theorem extT_last (t : Fin k → Fin n) : extT t (Fin.last k) = Fin.last n := by
  simp [extT]

theorem extT_injective {t : Fin k → Fin n} (ht : Function.Injective t) :
    Function.Injective (extT t) := by
  intro a b hab
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast b =>
      simp only [extT_last, extT_castSucc] at hab
      exact absurd hab.symm (Fin.castSucc_lt_last _).ne
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      simp only [extT_last, extT_castSucc] at hab
      exact absurd hab (Fin.castSucc_lt_last _).ne
    | cast b =>
      simp only [extT_castSucc, Fin.castSucc_inj] at hab
      rw [ht hab]

/-- The pair map on edges. -/
def csPair (e : Fin n × Fin n) : Fin (n + 1) × Fin (n + 1) :=
  (Fin.castSucc e.1, Fin.castSucc e.2)

theorem csPair_injective : Function.Injective (csPair (n := n)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [csPair, Prod.mk.injEq, Fin.castSucc_inj] at h
  rw [h.1, h.2]

/-- Add an isolated vertex as a new last terminal. -/
def extend (I : Instance (Fin n) k) : Instance (Fin (n + 1)) (k + 1) where
  E := I.E.image csPair
  w := fun p => if h : p.1 ≠ Fin.last n ∧ p.2 ≠ Fin.last n then
    I.w (p.1.castPred h.1, p.2.castPred h.2) else 0
  w_nonneg := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    split_ifs
    · simpa [csPair] using I.w_nonneg e he
    · exact le_rfl
  t := extT I.t
  t_injective := extT_injective I.t_injective

theorem extend_w (I : Instance (Fin n) k) (e : Fin n × Fin n) :
    (extend I).w (csPair e) = I.w e := by
  simp [extend, csPair, (Fin.castSucc_lt_last _).ne]

theorem cutWeight_eq (V : Type*) {m : ℕ} (I : Instance V m) (c : V → Fin m) :
    cutWeight I c = ∑ e ∈ I.E, if c e.1 ≠ c e.2 then I.w e else 0 := by
  unfold cutWeight
  rw [Finset.sum_filter]

theorem extend_cutWeight (I : Instance (Fin n) k) (c : Fin (n + 1) → Fin (k + 1)) :
    cutWeight (extend I) c = ∑ e ∈ I.E,
      if c (Fin.castSucc e.1) ≠ c (Fin.castSucc e.2) then I.w e else 0 := by
  rw [cutWeight_eq]
  change ∑ e ∈ I.E.image csPair, _ = _
  rw [Finset.sum_image (fun a _ b _ h => csPair_injective h)]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [extend_w]
  rfl

theorem extend_relaxValue (I : Instance (Fin n) k) (x : Fin (n + 1) → Fin (k + 1) → ℝ) :
    relaxValue (extend I) x = ∑ e ∈ I.E,
      I.w e * halfL1 (x (Fin.castSucc e.1)) (x (Fin.castSucc e.2)) := by
  unfold relaxValue
  change ∑ e ∈ I.E.image csPair, _ = _
  rw [Finset.sum_image (fun a _ b _ h => csPair_injective h)]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [extend_w]
  rfl

/-- Merge the last label into label `i0`. -/
def mergeL (i0 : Fin k) (j : Fin (k + 1)) : Fin k :=
  if h : j = Fin.last k then i0 else j.castPred h

@[simp] theorem mergeL_castSucc (i0 i : Fin k) : mergeL i0 (Fin.castSucc i) = i := by
  simp [mergeL, (Fin.castSucc_lt_last i).ne]

/-- Extend a labeling by sending the new vertex to the new label. -/
def extL (c : Fin n → Fin k) : Fin (n + 1) → Fin (k + 1) :=
  fun v => Fin.lastCases (motive := fun _ => Fin (k + 1)) (Fin.last k)
    (fun u => Fin.castSucc (c u)) v

@[simp] theorem extL_castSucc (c : Fin n → Fin k) (u : Fin n) :
    extL c (Fin.castSucc u) = Fin.castSucc (c u) := by simp [extL]

@[simp] theorem extL_last (c : Fin n → Fin k) : extL c (Fin.last n) = Fin.last k := by
  simp [extL]

/-- Extend an embedding. -/
def extX (x : Fin n → Fin k → ℝ) : Fin (n + 1) → Fin (k + 1) → ℝ :=
  fun v => Fin.lastCases (motive := fun _ => Fin (k + 1) → ℝ) (Pi.single (Fin.last k) 1)
    (fun u => extV (x u)) v

@[simp] theorem extX_castSucc (x : Fin n → Fin k → ℝ) (u : Fin n) :
    extX x (Fin.castSucc u) = extV (x u) := by simp [extX]

@[simp] theorem extX_last (x : Fin n → Fin k → ℝ) :
    extX x (Fin.last n) = Pi.single (Fin.last k) 1 := by simp [extX]

theorem extend_integralOpt (hk : 1 ≤ k) (I : Instance (Fin n) k) :
    integralOpt (extend I) = integralOpt I := by
  apply le_antisymm
  · apply le_csInf (integralValues_nonempty hk I)
    rintro r ⟨c, hc, rfl⟩
    have hfeas : IsFeasibleLabeling (extend I) (extL c) := by
      intro j
      induction j using Fin.lastCases with
      | last => simp [extend]
      | cast i =>
        show extL c (extT I.t (Fin.castSucc i)) = _
        simp [hc i]
    refine le_trans (csInf_le (integralValues_bdd _) ⟨extL c, hfeas, rfl⟩) (le_of_eq ?_)
    rw [extend_cutWeight, cutWeight_eq]
    simp
  · apply le_csInf (integralValues_nonempty (by omega) (extend I))
    rintro r ⟨c', hc', rfl⟩
    let i0 : Fin k := ⟨0, hk⟩
    let c : Fin n → Fin k := fun u => mergeL i0 (c' (Fin.castSucc u))
    have hfeas : IsFeasibleLabeling I c := by
      intro i
      have := hc' (Fin.castSucc i)
      change c' (extT I.t (Fin.castSucc i)) = _ at this
      simp only [extT_castSucc] at this
      simp only [c, this, mergeL_castSucc]
    refine le_trans (csInf_le (integralValues_bdd _) ⟨c, hfeas, rfl⟩) ?_
    rw [extend_cutWeight, cutWeight_eq]
    apply Finset.sum_le_sum
    intro e he
    by_cases h : c' (Fin.castSucc e.1) = c' (Fin.castSucc e.2)
    · have : c e.1 = c e.2 := by simp only [c, h]
      simp [this, h]
    · split_ifs
      · exact le_rfl
      · exact I.w_nonneg e he

theorem extend_fractionalOpt (hk : 1 ≤ k) (I : Instance (Fin n) k) :
    fractionalOpt (extend I) = fractionalOpt I := by
  apply le_antisymm
  · apply le_csInf (fractionalValues_nonempty hk I)
    rintro r ⟨x, hx, rfl⟩
    have hfeas : IsFeasibleEmbedding (extend I) (extX x) := by
      refine ⟨fun v => ?_, fun j => ?_⟩
      · induction v using Fin.lastCases with
        | last => simpa using single_mem_stdSimplex ℝ (Fin.last k)
        | cast u => simpa using extV_mem (hx.1 u)
      · induction j using Fin.lastCases with
        | last => simp [extend]
        | cast i =>
          show extX x (extT I.t (Fin.castSucc i)) = _
          simp [hx.2 i, extV_single]
    refine le_trans (csInf_le (fractionalValues_bdd _) ⟨extX x, hfeas, rfl⟩) (le_of_eq ?_)
    rw [extend_relaxValue]
    unfold relaxValue
    simp [halfL1_extV]
  · apply le_csInf (fractionalValues_nonempty (by omega) (extend I))
    rintro r ⟨x', hx', rfl⟩
    let i0 : Fin k := ⟨0, hk⟩
    let x : Fin n → Fin k → ℝ := fun u => projV i0 (x' (Fin.castSucc u))
    have hfeas : IsFeasibleEmbedding I x := by
      refine ⟨fun v => projV_mem i0 (hx'.1 _), fun i => ?_⟩
      have := hx'.2 (Fin.castSucc i)
      change x' (extT I.t (Fin.castSucc i)) = _ at this
      simp only [extT_castSucc] at this
      simp only [x, this, projV_single]
    refine le_trans (csInf_le (fractionalValues_bdd _) ⟨x, hfeas, rfl⟩) ?_
    rw [extend_relaxValue]
    unfold relaxValue
    apply Finset.sum_le_sum
    intro e he
    exact mul_le_mul_of_nonneg_left (halfL1_projV_le i0 _ _) (I.w_nonneg e he)

theorem extend_gap (hk : 1 ≤ k) (I : Instance (Fin n) k) :
    instanceGap (extend I) = instanceGap I := by
  simp only [instanceGap, extend_integralOpt hk, extend_fractionalOpt hk]

end Extend

theorem finiteGapValues_mono {k : ℕ} (hk : 1 ≤ k) :
    finiteGapValues k ⊆ finiteGapValues (k + 1) := by
  rintro r ⟨n, I, rfl⟩
  exact ⟨n + 1, extend I, (extend_gap hk I).symm⟩

section Final

variable (hckr : ∀ {n k : ℕ}, 1 ≤ k → ∀ (I : MultiwayCut.Instance (Fin n) k)
      (x : Fin n → Fin k → ℝ), MultiwayCut.IsFeasibleEmbedding I x →
      ∃ c : Fin n → Fin k, MultiwayCut.IsFeasibleLabeling I c ∧
        MultiwayCut.cutWeight I c ≤ 3 / 2 * MultiwayCut.relaxValue I x)

include hckr in
theorem finite_bdd {k : ℕ} (hk : 1 ≤ k) : BddAbove (finiteGapValues k) := by
  refine ⟨3 / 2, ?_⟩
  rintro r ⟨n, I, rfl⟩
  exact instanceGap_le hckr hk I

theorem one_mem_finite {k : ℕ} (hk : 2 ≤ k) : (1 : ℝ) ∈ finiteGapValues k :=
  ⟨k, oneEdge k hk, (oneEdge_gap k hk).symm⟩

theorem one_mem_positive {k : ℕ} (hk : 2 ≤ k) : (1 : ℝ) ∈ positiveGapValues k :=
  ⟨k, oneEdge k hk, by rw [oneEdge_fractionalOpt]; norm_num,
    by rw [oneEdge_fractionalOpt, oneEdge_integralOpt]; norm_num⟩

theorem finite_eq_positive {k : ℕ} (hk : 2 ≤ k) :
    finiteGapValues k = positiveGapValues k := by
  ext r
  constructor
  · rintro ⟨n, I, rfl⟩
    by_cases h : fractionalOpt I = 0
    · rw [instanceGap, if_pos h]
      exact one_mem_positive hk
    · have hpos : 0 < fractionalOpt I :=
        lt_of_le_of_ne (fractionalOpt_nonneg (by omega) I) (Ne.symm h)
      exact ⟨n, I, hpos, by rw [instanceGap, if_neg h]⟩
  · rintro ⟨n, I, hpos, rfl⟩
    exact ⟨n, I, by rw [instanceGap, if_neg hpos.ne']⟩

include hckr in
theorem gapSequence_le (k : ℕ) : gapSequence k ≤ 3 / 2 := by
  unfold gapSequence
  split_ifs with hk
  · exact csSup_le ⟨1, one_mem_finite hk⟩ (fun r ⟨n, I, hr⟩ => hr ▸ instanceGap_le hckr (by omega) I)
  · norm_num

include hckr in
theorem one_le_gapSequence (k : ℕ) : 1 ≤ gapSequence k := by
  unfold gapSequence
  split_ifs with hk
  · exact le_csSup (finite_bdd hckr (by omega)) (one_mem_finite hk)
  · exact le_rfl

include hckr in
theorem gapSequence_monotone : Monotone gapSequence := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : 2 ≤ k
  · have hk1 : 2 ≤ k + 1 := by omega
    unfold gapSequence
    rw [if_pos hk, if_pos hk1]
    exact csSup_le_csSup (finite_bdd hckr (by omega)) ⟨1, one_mem_finite hk⟩
      (finiteGapValues_mono (by omega))
  · have : gapSequence k = 1 := by unfold gapSequence; rw [if_neg hk]
    rw [this]
    exact one_le_gapSequence hckr (k + 1)

end Final

end MultiwayGap2325.Dev.WellPosed

namespace MultiwayGap2325.Main

open MultiwayGap2325.Dev.WellPosed in
theorem chk_gap_sequence_well_posed_of
    (hckr : ∀ {n k : ℕ}, 1 ≤ k → ∀ (I : MultiwayCut.Instance (Fin n) k)
      (x : Fin n → Fin k → ℝ), MultiwayCut.IsFeasibleEmbedding I x →
      ∃ c : Fin n → Fin k, MultiwayCut.IsFeasibleLabeling I c ∧
        MultiwayCut.cutWeight I c ≤ 3 / 2 * MultiwayCut.relaxValue I x) :
    (∀ k : ℕ, 2 ≤ k →
      (∃ n : ℕ, ∃ I : MultiwayCut.Instance (Fin n) k,
        0 < fractionalOpt I ∧ instanceGap I = 1) ∧
      (finiteGapValues k).Nonempty ∧ BddAbove (finiteGapValues k) ∧
      (positiveGapValues k).Nonempty ∧ BddAbove (positiveGapValues k) ∧
      sSup (finiteGapValues k) = sSup (positiveGapValues k) ∧
      1 ≤ gapSequence k ∧ gapSequence k ≤ (3 : ℝ) / 2) ∧
    Monotone gapSequence ∧
    ∃ g : ℝ, Filter.Tendsto gapSequence Filter.atTop (nhds g) := by
  refine ⟨fun k hk => ?_, gapSequence_monotone hckr, ?_⟩
  · have hpe := finite_eq_positive hk
    refine ⟨⟨k, oneEdge k hk, by rw [oneEdge_fractionalOpt]; norm_num, oneEdge_gap k hk⟩,
      ⟨1, one_mem_finite hk⟩, finite_bdd hckr (by omega), ⟨1, one_mem_positive hk⟩,
      hpe ▸ finite_bdd hckr (by omega), by rw [hpe], one_le_gapSequence hckr k,
      gapSequence_le hckr k⟩
  · refine ⟨_, tendsto_atTop_ciSup (gapSequence_monotone hckr) ⟨3 / 2, ?_⟩⟩
    rintro r ⟨k, rfl⟩
    exact gapSequence_le hckr k

end MultiwayGap2325.Main
end
end

section
set_option autoImplicit false

namespace MultiwayGap2325.Main

theorem chk_gap_sequence_well_posed :
    (∀ k : ℕ, 2 ≤ k →
      (∃ n : ℕ, ∃ I : MultiwayCut.Instance (Fin n) k,
        0 < fractionalOpt I ∧ instanceGap I = 1) ∧
      (finiteGapValues k).Nonempty ∧ BddAbove (finiteGapValues k) ∧
      (positiveGapValues k).Nonempty ∧ BddAbove (positiveGapValues k) ∧
      sSup (finiteGapValues k) = sSup (positiveGapValues k) ∧
      1 ≤ gapSequence k ∧ gapSequence k ≤ (3 : ℝ) / 2) ∧
    Monotone gapSequence ∧
    ∃ g : ℝ, Filter.Tendsto gapSequence Filter.atTop (nhds g) :=
  chk_gap_sequence_well_posed_of
    (fun hk I x hx => MultiwayGap2325.Dev.CKR.ckr_rounding hk I x hx)

end MultiwayGap2325.Main
end

theorem solution : type_of% @MultiwayGap2325.Main.chk_gap_sequence_well_posed := @MultiwayGap2325.Main.chk_gap_sequence_well_posed
