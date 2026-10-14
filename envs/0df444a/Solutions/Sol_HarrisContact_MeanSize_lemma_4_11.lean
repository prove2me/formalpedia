-- Prove2me | solution 1 for HarrisContact.MeanSize.lemma_4_11
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:19:53.175973+00:00
-- url     : https://prove2.me/submissions/313bcb95-1aba-4acf-857d-7cecab05fb82

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal


namespace HarrisContact.MeanSize
open HarrisContact.Extinction

theorem hc_card_nbrs_le {d : ℕ} (x : Site d) : (nbrs x).card ≤ 2 * d := by
  classical
  let g : Fin d × Bool → Site d := fun p => Function.update x p.1 (x p.1 + if p.2 then 1 else -1)
  have hsub : nbrs x ⊆ Finset.univ.image g := by
    intro y hy
    simp only [nbrs, Finset.mem_filter] at hy
    obtain ⟨-, hy2⟩ := hy
    have hex : ∃ i, x i ≠ y i := by
      by_contra hc
      push_neg at hc
      simp [hc] at hy2
    obtain ⟨i, hi⟩ := hex
    have hsplit := Finset.add_sum_erase Finset.univ (fun j => |x j - y j|) (Finset.mem_univ i)
    rw [hy2] at hsplit
    have hge : 1 ≤ |x i - y i| := by
      have : x i - y i ≠ 0 := sub_ne_zero.mpr hi
      rcases lt_or_gt_of_ne this with h | h
      · rw [abs_of_neg h]; omega
      · rw [abs_of_pos h]; omega
    have hrest : ∑ j ∈ Finset.univ.erase i, |x j - y j| = 0 := by
      have h0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, |x j - y j| :=
        Finset.sum_nonneg (fun j _ => abs_nonneg _)
      linarith
    have hi1 : |x i - y i| = 1 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)] at hrest
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨(i, decide (y i = x i + 1)), ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [g, Function.update_self]
      rcases abs_eq (zero_le_one) |>.mp hi1 with h | h
      · have : y j ≠ x j + 1 := by omega
        simp [this]; omega
      · have : y j = x j + 1 := by omega
        simp [this]
    · have := hrest j (by simp [hj])
      simp only [g, Function.update_of_ne hj]
      rw [abs_eq_zero, sub_eq_zero] at this
      exact this
  calc (nbrs x).card ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [Finset.card_univ]; ring

theorem hc_occ_le {d : ℕ} (ξ : Config d) (x : Site d) : occ ξ x ≤ 2 * d :=
  (Finset.card_le_card Finset.inter_subset_right).trans (hc_card_nbrs_le x)

theorem hc_card_bdry_le {d : ℕ} (ξ : Config d) : (bdry ξ).card ≤ 2 * d * ξ.card := by
  calc (bdry ξ).card ≤ (ξ.biUnion nbrs).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ ∑ y ∈ ξ, (nbrs y).card := Finset.card_biUnion_le
    _ ≤ ∑ y ∈ ξ, 2 * d := Finset.sum_le_sum fun y _ => hc_card_nbrs_le y
    _ = 2 * d * ξ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem hc_succ_sum {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) (hμ : 0 ≤ μ)
    (hl : ∀ x ∈ bdry ξ, 0 ≤ lam (occ ξ x)) (F : Config d → ℝ≥0∞) :
    ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * F ζ =
      ∑ x ∈ ξ, ENNReal.ofReal μ * F (ξ.erase x) +
        ∑ x ∈ bdry ξ, ENNReal.ofReal (lam (occ ξ x)) * F (insert x ξ) := by
  have h1 : ∀ ζ, ENNReal.ofReal (rate μ lam ξ ζ) =
      (∑ x ∈ ξ, if ζ = ξ.erase x then ENNReal.ofReal μ else 0) +
        ∑ x ∈ bdry ξ, if ζ = insert x ξ then ENNReal.ofReal (lam (occ ξ x)) else 0 := by
    intro ζ
    unfold rate
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hμ])
        (Finset.sum_nonneg fun x hx => by split_ifs <;> simp [hl x hx]),
      ENNReal.ofReal_sum_of_nonneg (fun x _ => by split_ifs <;> simp [hμ]),
      ENNReal.ofReal_sum_of_nonneg (fun x hx => by split_ifs <;> simp [hl x hx])]
    congr 1
    · exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
    · exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
  simp_rw [h1, add_mul, Finset.sum_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)

theorem hc_transN_mono {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) :
    ∀ n t (ξ η : Config d), transN μ lam n t ξ η ≤ transN μ lam (n + 1) t ξ η := by
  intro n
  induction n with
  | zero => intro t ξ η; simp only [transN.eq_2]; exact le_add_right (le_refl _)
  | succ n ih =>
    intro t ξ η
    simp only [transN.eq_2]
    refine add_le_add le_rfl (lintegral_mono fun s => ?_)
    gcongr with ζ hζ
    have := ih (t - s) ζ η
    simp only [transN.eq_2] at this
    exact this

theorem hc_tsum_lintegral_le {α ι : Type*} [MeasurableSpace α] (ν : Measure α)
    (f : ι → α → ℝ≥0∞) : ∑' i, ∫⁻ a, f i a ∂ν ≤ ∫⁻ a, ∑' i, f i a ∂ν := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have h : ∀ s : Finset ι, ∑ i ∈ s, ∫⁻ a, f i a ∂ν ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂ν := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      simp_rw [Finset.sum_insert hj]
      exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)
  exact (h s).trans (lintegral_mono fun a => ENNReal.sum_le_tsum s)

theorem hc_tsum_iSup_le {ι : Type*} (a : ℕ → ι → ℝ≥0∞) (hmono : ∀ i, Monotone (fun n => a n i))
    (B : ℝ≥0∞) (h : ∀ n, ∑' i, a n i ≤ B) : ∑' i, ⨆ n, a n i ≤ B := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [ENNReal.finsetSum_iSup_of_monotone hmono]
  exact iSup_le fun n => (ENNReal.sum_le_tsum s).trans (h n)

/-! ## measurability and the backward equation for `m` -/

theorem hc_meas_transN {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) :
    ∀ n (ξ η : Config d), Measurable (fun t => transN μ lam n t ξ η) := by
  have h0 : ∀ (ξ η : Config d), Measurable (fun t => transN μ lam 0 t ξ η) := by
    intro ξ η
    simp only [transN.eq_1]
    split_ifs
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact measurable_const
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro ξ η
    simp only [transN.eq_2]
    refine (h0 ξ η).add ?_
    set S : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1} with hS
    have hSm : MeasurableSet S :=
      (measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_fst)
    let G : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * p.2))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * transN μ lam n (p.1 - p.2) ζ η
    have hG : Measurable G := by
      refine Measurable.mul (ENNReal.measurable_ofReal.comp (by fun_prop)) ?_
      refine Finset.measurable_sum _ fun ζ _ => ?_
      exact measurable_const.mul ((ih ζ η).comp (measurable_fst.sub measurable_snd))
    have heq : (fun t => ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * transN μ lam n (t - s) ζ η) =
        fun t => ∫⁻ s, S.indicator G (t, s) := by
      funext t
      rw [← lintegral_indicator measurableSet_Icc]
      refine lintegral_congr fun s => ?_
      simp only [Set.indicator, Set.mem_Icc, hS, Set.mem_setOf_eq, G]
    rw [heq]
    exact (hG.indicator hSm).lintegral_prod_right'

/-- `a n t ξ = Σ_η P^{(n)}_t(ξ,η) |η|`. -/
noncomputable def hcA {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (n : ℕ) (t : ℝ) (ξ : Config d) : ℝ≥0∞ :=
  ∑' η, transN μ lam n t ξ η * (η.card : ℝ≥0∞)

theorem hc_meas_A {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (n : ℕ) (ξ : Config d) :
    Measurable (fun t => hcA μ lam n t ξ) := by
  unfold hcA
  exact Measurable.ennreal_tsum fun η => (hc_meas_transN μ lam n ξ η).mul_const _

theorem hc_A_mono {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (t : ℝ) (ξ : Config d) :
    Monotone (fun n => hcA μ lam n t ξ) := by
  refine monotone_nat_of_le_succ fun n => ?_
  unfold hcA
  exact ENNReal.tsum_le_tsum fun η => by gcongr; exact hc_transN_mono μ lam n t ξ η

theorem hc_meanSize_eq_iSup {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (t : ℝ) (ξ : Config d) :
    meanSize μ lam t ξ = ⨆ n, hcA μ lam n t ξ := by
  unfold meanSize Extinction.trans hcA
  simp_rw [ENNReal.iSup_mul]
  refine le_antisymm ?_ (iSup_le fun n => ENNReal.tsum_le_tsum fun η => le_iSup (fun n =>
    transN μ lam n t ξ η * (η.card : ℝ≥0∞)) n)
  refine hc_tsum_iSup_le (fun n η => transN μ lam n t ξ η * (η.card : ℝ≥0∞)) ?_ _ ?_
  · intro η
    exact monotone_nat_of_le_succ fun n => by gcongr; exact hc_transN_mono μ lam n t ξ η
  · intro n
    exact le_iSup (fun n => ∑' η, transN μ lam n t ξ η * (η.card : ℝ≥0∞)) n

theorem hc_A_succ {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (n : ℕ) (t : ℝ) (ξ : Config d) :
    hcA μ lam (n + 1) t ξ = ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) * (ξ.card : ℝ≥0∞) +
      ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcA μ lam n (t - s) ζ := by
  unfold hcA
  simp only [transN.eq_2, transN.eq_1, add_mul, ite_mul, zero_mul]
  rw [ENNReal.tsum_add]
  congr 1
  · rw [tsum_eq_single ξ (fun η h => if_neg (Ne.symm h))]
    simp
  · simp_rw [← lintegral_mul_const' _ _ (ENNReal.natCast_ne_top _)]
    rw [← lintegral_tsum]
    · refine lintegral_congr fun s => ?_
      simp only [mul_assoc, Finset.sum_mul]
      rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      congr 1
      refine Finset.sum_congr rfl fun ζ _ => ?_
      rw [ENNReal.tsum_mul_left]
    · intro η
      refine Measurable.aemeasurable ?_
      refine Measurable.mul_const (Measurable.mul (ENNReal.measurable_ofReal.comp (by fun_prop)) ?_) _
      refine Finset.measurable_sum _ fun ζ _ => ?_
      exact measurable_const.mul ((hc_meas_transN μ lam n ζ η).comp (measurable_const.sub measurable_id))

/-- The backward (first-jump) equation for the mean size. -/
theorem hc_meanSize_backward {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (t : ℝ) (ξ : Config d) :
    meanSize μ lam t ξ = ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) * (ξ.card : ℝ≥0∞) +
      ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * meanSize μ lam (t - s) ζ := by
  rw [hc_meanSize_eq_iSup]
  have hshift : ⨆ n, hcA μ lam n t ξ = ⨆ n, hcA μ lam (n + 1) t ξ := by
    refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun n => le_iSup (fun n => hcA μ lam n t ξ) (n + 1))
    exact (hc_A_mono μ lam t ξ (Nat.le_succ n)).trans (le_iSup (fun n => hcA μ lam (n + 1) t ξ) n)
  rw [hshift]
  simp_rw [hc_A_succ, ← ENNReal.add_iSup]
  congr 1
  rw [← lintegral_iSup]
  · refine lintegral_congr fun s => ?_
    rw [← ENNReal.mul_iSup]
    congr 1
    rw [← ENNReal.finsetSum_iSup_of_monotone]
    · refine Finset.sum_congr rfl fun ζ _ => ?_
      rw [← ENNReal.mul_iSup, hc_meanSize_eq_iSup]
    · intro ζ m k hmk
      exact mul_le_mul' le_rfl (hc_A_mono μ lam (t - s) ζ hmk)
  · intro n
    refine Measurable.mul (ENNReal.measurable_ofReal.comp (by fun_prop)) ?_
    refine Finset.measurable_sum _ fun ζ _ => ?_
    exact measurable_const.mul ((hc_meas_A μ lam n ζ).comp (measurable_const.sub measurable_id))
  · intro m k hmk s
    dsimp only
    gcongr with ζ hζ
    exact hc_A_mono μ lam (t - s) ζ hmk


/-! ## general weights -/

noncomputable def hcW {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (w : Config d → ℕ) (n : ℕ) (t : ℝ) (ξ : Config d) :
    ℝ≥0∞ :=
  ∑' η, transN μ lam n t ξ η * (w η : ℝ≥0∞)

theorem hc_meas_W {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (w : Config d → ℕ) (n : ℕ) (ξ : Config d) :
    Measurable (fun t => hcW μ lam w n t ξ) := by
  unfold hcW
  exact Measurable.ennreal_tsum fun η => (hc_meas_transN μ lam n ξ η).mul_const _

theorem hc_W_mono {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (w : Config d → ℕ) (t : ℝ) (ξ : Config d) :
    Monotone (fun n => hcW μ lam w n t ξ) := by
  refine monotone_nat_of_le_succ fun n => ?_
  unfold hcW
  exact ENNReal.tsum_le_tsum fun η => by gcongr; exact hc_transN_mono μ lam n t ξ η

theorem hc_W_zero {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (w : Config d → ℕ) (t : ℝ) (ξ : Config d) :
    hcW μ lam w 0 t ξ = ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) * (w ξ : ℝ≥0∞) := by
  unfold hcW
  simp only [transN.eq_1, ite_mul, zero_mul]
  rw [tsum_eq_single ξ (fun η h => if_neg (Ne.symm h))]
  simp

theorem hc_W_succ {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (w : Config d → ℕ) (n : ℕ) (t : ℝ) (ξ : Config d) :
    hcW μ lam w (n + 1) t ξ = ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) * (w ξ : ℝ≥0∞) +
      ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcW μ lam w n (t - s) ζ := by
  unfold hcW
  simp only [transN.eq_2, transN.eq_1, add_mul, ite_mul, zero_mul]
  rw [ENNReal.tsum_add]
  congr 1
  · rw [tsum_eq_single ξ (fun η h => if_neg (Ne.symm h))]
    simp
  · simp_rw [← lintegral_mul_const' _ _ (ENNReal.natCast_ne_top _)]
    rw [← lintegral_tsum]
    · refine lintegral_congr fun s => ?_
      simp only [mul_assoc, Finset.sum_mul]
      rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      congr 1
      refine Finset.sum_congr rfl fun ζ _ => ?_
      rw [ENNReal.tsum_mul_left]
    · intro η
      refine Measurable.aemeasurable ?_
      refine Measurable.mul_const (Measurable.mul (ENNReal.measurable_ofReal.comp (by fun_prop)) ?_) _
      refine Finset.measurable_sum _ fun ζ _ => ?_
      exact measurable_const.mul ((hc_meas_transN μ lam n ζ η).comp (measurable_const.sub measurable_id))

/-! ## the "at least `n` jumps" probabilities -/

noncomputable def hcB {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) : ℕ → ℝ → Config d → ℝ≥0∞
  | 0, _, _ => 1
  | n + 1, t, ξ => ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcB μ lam n (t - s) ζ

theorem hc_meas_B {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) :
    ∀ n (ξ : Config d), Measurable (fun t => hcB μ lam n t ξ) := by
  intro n
  induction n with
  | zero => intro ξ; simp only [hcB]; exact measurable_const
  | succ n ih =>
    intro ξ
    simp only [hcB]
    set S : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1} with hS
    have hSm : MeasurableSet S :=
      (measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_fst)
    let G : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * p.2))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcB μ lam n (p.1 - p.2) ζ
    have hG : Measurable G := by
      refine Measurable.mul (ENNReal.measurable_ofReal.comp (by fun_prop)) ?_
      refine Finset.measurable_sum _ fun ζ _ => ?_
      exact measurable_const.mul ((ih ζ).comp (measurable_fst.sub measurable_snd))
    have heq : (fun t => ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcB μ lam n (t - s) ζ) =
        fun t => ∫⁻ s, S.indicator G (t, s) := by
      funext t
      rw [← lintegral_indicator measurableSet_Icc]
      refine lintegral_congr fun s => ?_
      simp only [Set.indicator, Set.mem_Icc, hS, Set.mem_setOf_eq, G]
    rw [heq]
    exact (hG.indicator hSm).lintegral_prod_right'

/-! ## explicit integrals -/

theorem hc_realint (a c T u v : ℝ) (huv : u ≤ v) :
    (a - c) * ∫ s in u..v, Real.exp (-(a * s)) * Real.exp (-(c * (T - s))) =
      Real.exp (-(c * (T - u)) - a * u) - Real.exp (-(c * (T - v)) - a * v) := by
  have hd : ∀ s ∈ Set.uIcc u v, HasDerivAt (fun s => -Real.exp (-(c * (T - s)) - a * s))
      ((a - c) * (Real.exp (-(a * s)) * Real.exp (-(c * (T - s))))) s := by
    intro s _
    have h1 : HasDerivAt (fun s => -(c * (T - s)) - a * s) (c - a) s := by
      have := ((((hasDerivAt_id s).const_sub T).const_mul c).neg).sub ((hasDerivAt_id s).const_mul a)
      exact this.congr_deriv (by simp)
    have h2 := h1.exp.neg
    refine h2.congr_deriv ?_
    rw [← Real.exp_add]
    have : -(c * (T - s)) - a * s = -(a * s) + -(c * (T - s)) := by ring
    rw [this]; ring
  have hcont : Continuous (fun s => (a - c) * (Real.exp (-(a * s)) * Real.exp (-(c * (T - s))))) := by
    fun_prop
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
  ring

theorem hc_lint (a c T u v b : ℝ) (huv : u ≤ v) (hb : 0 ≤ b) :
    ∫⁻ s in Set.Ioc u v, ENNReal.ofReal (Real.exp (-(a * s))) *
        ENNReal.ofReal (b * Real.exp (-(c * (T - s)))) =
      ENNReal.ofReal (b * ∫ s in u..v, Real.exp (-(a * s)) * Real.exp (-(c * (T - s)))) := by
  have hcont : Continuous (fun s => b * (Real.exp (-(a * s)) * Real.exp (-(c * (T - s))))) := by
    fun_prop
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le huv,
    ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      (Filter.Eventually.of_forall fun s => by positivity)]
  refine lintegral_congr fun s => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1; ring

theorem hc_lint_Icc (a c T u v b : ℝ) (huv : u ≤ v) (hb : 0 ≤ b) :
    ∫⁻ s in Set.Icc u v, ENNReal.ofReal (Real.exp (-(a * s))) *
        ENNReal.ofReal (b * Real.exp (-(c * (T - s)))) =
      ENNReal.ofReal (b * ∫ s in u..v, Real.exp (-(a * s)) * Real.exp (-(c * (T - s)))) := by
  rw [← hc_lint a c T u v b huv hb]
  exact setLIntegral_congr Ioc_ae_eq_Icc.symm

theorem hc_realint_nonneg (a c T u v : ℝ) (huv : u ≤ v) :
    0 ≤ ∫ s in u..v, Real.exp (-(a * s)) * Real.exp (-(c * (T - s))) :=
  intervalIntegral.integral_nonneg huv fun s _ => by positivity

/-! ## rate sums -/

theorem hc_exitRate_facts {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) :
    0 ≤ ∑ x ∈ bdry ξ, lam (occ ξ x) ∧ 0 ≤ exitRate μ lam ξ := by
  have h1 : 0 ≤ ∑ x ∈ bdry ξ, lam (occ ξ x) := Finset.sum_nonneg fun x _ => hlam _ (hc_occ_le ξ x)
  refine ⟨h1, ?_⟩
  unfold exitRate; positivity

theorem hc_sum_rate {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) (G : ℝ≥0∞) :
    ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * G = ENNReal.ofReal (exitRate μ lam ξ) * G := by
  rw [hc_succ_sum μ lam ξ hμ (fun x _ => hlam _ (hc_occ_le ξ x)) (fun _ => G)]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]
  congr 1
  unfold exitRate
  rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun x _ => hlam _ (hc_occ_le ξ x)),
    ENNReal.ofReal_sum_of_nonneg (fun x _ => hlam _ (hc_occ_le ξ x)), Finset.sum_const, nsmul_eq_mul,
    ENNReal.ofReal_mul hμ, ENNReal.ofReal_natCast, mul_comm]

theorem hc_sum_rate_mem {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) (x : Site d) (hx : x ∈ ξ) (G : ℝ≥0∞) :
    ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * (if x ∈ ζ then G else 0) =
      ENNReal.ofReal (exitRate μ lam ξ - μ) * G := by
  rw [hc_succ_sum μ lam ξ hμ (fun x _ => hlam _ (hc_occ_le ξ x)) (fun ζ => if x ∈ ζ then G else 0)]
  have h1 : ∑ w ∈ ξ.erase x, ENNReal.ofReal μ * (if x ∈ ξ.erase w then G else 0) =
      ∑ w ∈ ξ.erase x, ENNReal.ofReal μ * G := by
    refine Finset.sum_congr rfl fun w hw => ?_
    have : x ∈ ξ.erase w := Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hw).1 h.symm, hx⟩
    rw [if_pos this]
  have h2 : ∑ z ∈ bdry ξ, ENNReal.ofReal (lam (occ ξ z)) * (if x ∈ insert z ξ then G else 0) =
      ∑ z ∈ bdry ξ, ENNReal.ofReal (lam (occ ξ z)) * G :=
    Finset.sum_congr rfl fun z _ => by rw [if_pos (Finset.mem_insert_of_mem hx)]
  rw [← Finset.add_sum_erase ξ _ hx, if_neg (Finset.notMem_erase x ξ), mul_zero, zero_add, h1, h2,
    ← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]
  congr 1
  unfold exitRate
  have hc : ((ξ.erase x).card : ℝ) = ξ.card - 1 := by
    rw [Finset.card_erase_of_mem hx, Nat.cast_sub (Finset.card_pos.mpr ⟨x, hx⟩)]; simp
  have : μ * ξ.card + ∑ x ∈ bdry ξ, lam (occ ξ x) - μ = μ * (ξ.erase x).card + ∑ x ∈ bdry ξ, lam (occ ξ x) := by
    rw [hc]; ring
  rw [this, ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun x _ => hlam _ (hc_occ_le ξ x)),
    ENNReal.ofReal_sum_of_nonneg (fun x _ => hlam _ (hc_occ_le ξ x)), Finset.sum_const, nsmul_eq_mul,
    ENNReal.ofReal_mul hμ, ENNReal.ofReal_natCast, mul_comm]

theorem hc_sum_rate_card {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) (G : ℝ) (hG : 0 ≤ G) :
    ENNReal.ofReal ((exitRate μ lam ξ - μ) * ξ.card * G) ≤
      ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * (ENNReal.ofReal G * (ζ.card : ℝ≥0∞)) := by
  have hlb : ∀ x ∈ bdry ξ, 0 ≤ lam (occ ξ x) := fun x _ => hlam _ (hc_occ_le ξ x)
  rw [hc_succ_sum μ lam ξ hμ hlb]
  have e : ∑ x ∈ ξ, ENNReal.ofReal μ * (ENNReal.ofReal G * ((ξ.erase x).card : ℝ≥0∞)) +
        ∑ x ∈ bdry ξ, ENNReal.ofReal (lam (occ ξ x)) * (ENNReal.ofReal G * ((insert x ξ).card : ℝ≥0∞)) =
      ENNReal.ofReal (∑ x ∈ ξ, μ * (G * (ξ.erase x).card) +
        ∑ x ∈ bdry ξ, lam (occ ξ x) * (G * (insert x ξ).card)) := by
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun x _ => by positivity)
      (Finset.sum_nonneg fun x hx => mul_nonneg (hlb x hx) (by positivity)),
      ENNReal.ofReal_sum_of_nonneg (fun x _ => by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun x hx => mul_nonneg (hlb x hx) (by positivity))]
    congr 1
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [ENNReal.ofReal_mul hμ, ENNReal.ofReal_mul hG, ENNReal.ofReal_natCast]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [ENNReal.ofReal_mul (hlb x hx), ENNReal.ofReal_mul hG, ENNReal.ofReal_natCast]
  rw [e]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ∑ x ∈ ξ, μ * (G * ((ξ.erase x).card : ℝ)) = ξ.card * (μ * (G * (ξ.card - 1))) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.card_erase_of_mem hx, Nat.cast_sub (Finset.card_pos.mpr ⟨x, hx⟩)]
    simp
  have h2 : ∑ x ∈ bdry ξ, lam (occ ξ x) * (G * ((insert x ξ).card : ℝ)) =
      (∑ x ∈ bdry ξ, lam (occ ξ x)) * (G * (ξ.card + 1)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x ∉ ξ := (Finset.mem_sdiff.mp hx).2
    rw [Finset.card_insert_of_notMem hx']
    push_cast; ring
  rw [h1, h2]
  unfold exitRate
  have hL := (hc_exitRate_facts μ lam hμ hlam ξ).1
  nlinarith [mul_nonneg hL hG]

/-! ## survival of a tagged particle -/

theorem hc_surv {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (x : Site d) :
    ∀ n (t : ℝ), 0 ≤ t → ∀ ξ : Config d, x ∈ ξ →
      ENNReal.ofReal (Real.exp (-(μ * t))) ≤
        hcW μ lam (fun η => if x ∈ η then 1 else 0) n t ξ + hcB μ lam (n + 1) t ξ := by
  intro n
  induction n with
  | zero =>
    intro t ht ξ hx
    set q := exitRate μ lam ξ with hq
    have hq0 : 0 ≤ q := (hc_exitRate_facts μ lam hμ hlam ξ).2
    rw [hc_W_zero, hcB.eq_2]
    simp_rw [hcB.eq_1, hc_sum_rate μ lam hμ hlam, mul_one]
    have := hc_lint_Icc q 0 t 0 t q ht hq0 |>.symm
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at this
    rw [← this]
    have hI := hc_realint q 0 t 0 t ht
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, sub_zero, mul_zero] at hI
    rw [if_pos hx, Nat.cast_one, mul_one, ← hq, ← ENNReal.ofReal_add (Real.exp_pos _).le
      (mul_nonneg hq0 (intervalIntegral.integral_nonneg ht fun s _ => (Real.exp_pos _).le)), hI]
    apply ENNReal.ofReal_le_ofReal
    have : Real.exp (-(μ * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h00 : Real.exp (0 - q * t) = Real.exp (-(q * t)) := by ring_nf
    rw [h00]
    linarith
  | succ n ih =>
    intro t ht ξ hx
    set q := exitRate μ lam ξ with hq
    have hq0 : 0 ≤ q := (hc_exitRate_facts μ lam hμ hlam ξ).2
    have hqμ : 0 ≤ q - μ := by
      have hL := (hc_exitRate_facts μ lam hμ hlam ξ).1
      have h1 : (1 : ℝ) ≤ ξ.card := by exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
      rw [hq]; unfold exitRate; nlinarith
    rw [hc_W_succ, if_pos hx, Nat.cast_one, mul_one, hcB.eq_2]
    rw [add_assoc, ← lintegral_add_left]
    · have hstep : ∀ s ∈ Set.Icc 0 t,
          ENNReal.ofReal (Real.exp (-(q * s))) * ENNReal.ofReal ((q - μ) * Real.exp (-(μ * (t - s)))) ≤
          ENNReal.ofReal (Real.exp (-(q * s))) *
              ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
                hcW μ lam (fun η => if x ∈ η then 1 else 0) n (t - s) ζ +
            ENNReal.ofReal (Real.exp (-(q * s))) *
              ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcB μ lam (n + 1) (t - s) ζ := by
        intro s hs
        have hts : 0 ≤ t - s := by linarith [hs.2]
        rw [← mul_add, ← Finset.sum_add_distrib]
        gcongr
        rw [ENNReal.ofReal_mul hqμ, ← hc_sum_rate_mem μ lam hμ hlam ξ x hx]
        gcongr with ζ hζ
        simp_rw [← mul_add]
        gcongr
        split_ifs with hxζ
        · exact ih (t - s) hts ζ hxζ
        · exact bot_le
      calc ENNReal.ofReal (Real.exp (-(μ * t)))
          ≤ ENNReal.ofReal (Real.exp (-(q * t))) +
              ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(q * s))) *
                ENNReal.ofReal ((q - μ) * Real.exp (-(μ * (t - s)))) := by
            rw [hc_lint_Icc q μ t 0 t (q - μ) ht hqμ, hc_realint q μ t 0 t ht,
              ← ENNReal.ofReal_add (Real.exp_pos _).le]
            · apply ENNReal.ofReal_le_ofReal
              have e1 : Real.exp (-(μ * (t - 0)) - q * 0) = Real.exp (-(μ * t)) := by ring_nf
              have e2 : Real.exp (-(μ * (t - t)) - q * t) = Real.exp (-(q * t)) := by ring_nf
              rw [e1, e2]; linarith
            · rw [hc_realint q μ t 0 t ht |>.symm]
              exact mul_nonneg hqμ (hc_realint_nonneg _ _ _ _ _ ht)
        _ ≤ _ := add_le_add le_rfl (setLIntegral_mono' measurableSet_Icc hstep)
    · refine Measurable.mul (ENNReal.measurable_ofReal.comp (by fun_prop)) ?_
      refine Finset.measurable_sum _ fun ζ _ => ?_
      exact measurable_const.mul ((hc_meas_W μ lam _ n ζ).comp (measurable_const.sub measurable_id))


/-! ## non-explosion: `B_n → 0` -/

noncomputable def hcg (C m : ℝ) : ℝ := C * m / (1 + C * m)

noncomputable def hcP (C : ℝ) (n : ℕ) (m : ℝ) : ℝ := ∏ k ∈ Finset.range n, hcg C (m + k)

theorem hcg_nonneg {C m : ℝ} (hC : 0 ≤ C) (hm : 0 ≤ m) : 0 ≤ hcg C m := by
  unfold hcg; positivity

theorem hcg_mono {C m m' : ℝ} (hC : 0 ≤ C) (hm : 0 ≤ m) (hmm : m ≤ m') : hcg C m ≤ hcg C m' := by
  unfold hcg
  have hm' : 0 ≤ m' := hm.trans hmm
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hmm hC]

theorem hcP_nonneg {C : ℝ} (n : ℕ) {m : ℝ} (hC : 0 ≤ C) (hm : 0 ≤ m) : 0 ≤ hcP C n m :=
  Finset.prod_nonneg fun k _ => hcg_nonneg hC (by positivity)

theorem hcP_mono {C : ℝ} (n : ℕ) {m m' : ℝ} (hC : 0 ≤ C) (hm : 0 ≤ m) (hmm : m ≤ m') :
    hcP C n m ≤ hcP C n m' :=
  Finset.prod_le_prod (fun k _ => hcg_nonneg hC (by positivity))
    (fun k _ => hcg_mono hC (by positivity) (by linarith))

theorem hcP_succ (C : ℝ) (n : ℕ) (m : ℝ) : hcP C (n + 1) m = hcg C m * hcP C n (m + 1) := by
  unfold hcP
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun k _ => ?_
    congr 1; push_cast; ring

theorem hcP_tendsto (C m : ℝ) (hC : 0 ≤ C) (hm : 0 ≤ m) :
    Tendsto (fun n => hcP C n m) atTop (𝓝 0) := by
  set α := 1 / (1 + C * m + C) with hα
  have hαpos : 0 < α := by positivity
  have hS : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, 1 / (1 + C * (m + k))) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop hαpos)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hα, div_mul_div_comm, one_mul]
    have hk : (0:ℝ) ≤ k := k.cast_nonneg
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_nonneg hC hk, mul_nonneg (mul_nonneg hC hm) hk]
  have hE := Real.tendsto_exp_neg_atTop_nhds_zero.comp hS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE (fun n => hcP_nonneg n hC hm)
    (fun n => ?_)
  show hcP C n m ≤ Real.exp (-(∑ k ∈ Finset.range n, 1 / (1 + C * (m + k))))
  unfold hcP
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod (fun k _ => hcg_nonneg hC (by positivity)) fun k _ => ?_
  unfold hcg
  have hk : (0:ℝ) ≤ k := k.cast_nonneg
  have hpos : 0 < 1 + C * (m + k) := by positivity
  have := Real.add_one_le_exp (-(1 / (1 + C * (m + k))))
  have e : C * (m + k) / (1 + C * (m + k)) = -(1 / (1 + C * (m + k))) + 1 := by
    field_simp; ring
  linarith [e]

theorem hc_card_succ_le {d : ℕ} (ξ ζ : Config d) (h : ζ ∈ succ ξ) : ζ.card ≤ ξ.card + 1 := by
  unfold succ at h
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.card_erase_le).trans (Nat.le_succ _)
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact Finset.card_insert_le _ _

theorem hc_q_le {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (Λ : ℝ) (hΛ0 : 0 ≤ Λ)
    (hlamΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ) (ξ : Config d) :
    exitRate μ lam ξ ≤ (μ + 2 * d * Λ) * ξ.card := by
  unfold exitRate
  have : ∑ x ∈ bdry ξ, lam (occ ξ x) ≤ 2 * d * Λ * ξ.card := by
    calc ∑ x ∈ bdry ξ, lam (occ ξ x) ≤ ∑ x ∈ bdry ξ, Λ :=
          Finset.sum_le_sum fun x _ => hlamΛ _ (hc_occ_le ξ x)
      _ = (bdry ξ).card * Λ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * d * ξ.card : ℕ) : ℝ) * Λ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hc_card_bdry_le ξ) hΛ0
      _ = 2 * d * Λ * ξ.card := by push_cast; ring
  nlinarith

theorem hc_B_bound {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (Λ : ℝ) (hΛ0 : 0 ≤ Λ)
    (hlamΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ) :
    ∀ n (t : ℝ), 0 ≤ t → ∀ ξ : Config d,
      hcB μ lam n t ξ ≤ ENNReal.ofReal (Real.exp t * hcP (μ + 2 * d * Λ) n ξ.card) := by
  set C := μ + 2 * (d : ℝ) * Λ with hC
  have hC0 : 0 ≤ C := by positivity
  intro n
  induction n with
  | zero =>
    intro t ht ξ
    rw [hcB.eq_1]
    simp only [hcP, Finset.range_zero, Finset.prod_empty, mul_one]
    exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp ht)
  | succ n ih =>
    intro t ht ξ
    set q := exitRate μ lam ξ with hq
    have hq0 : 0 ≤ q := (hc_exitRate_facts μ lam hμ hlam ξ).2
    have hqC : q ≤ C * ξ.card := hc_q_le μ lam Λ hΛ0 hlamΛ ξ
    set P := hcP C n ((ξ.card : ℝ) + 1) with hP
    have hP0 : 0 ≤ P := hcP_nonneg n hC0 (by positivity)
    rw [hcB.eq_2]
    have hpt : ∀ s ∈ Set.Icc 0 t,
        ENNReal.ofReal (Real.exp (-(q * s))) *
          ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcB μ lam n (t - s) ζ ≤
        ENNReal.ofReal (Real.exp (-(q * s))) *
          ENNReal.ofReal (q * P * Real.exp (-((-1) * (t - s)))) := by
      intro s hs
      have hts : 0 ≤ t - s := by linarith [hs.2]
      gcongr
      calc ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcB μ lam n (t - s) ζ
          ≤ ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
              ENNReal.ofReal (P * Real.exp (-((-1) * (t - s)))) := by
            gcongr with ζ hζ
            refine (ih (t - s) hts ζ).trans (ENNReal.ofReal_le_ofReal ?_)
            have : Real.exp (-((-1) * (t - s))) = Real.exp (t - s) := by ring_nf
            rw [this, mul_comm P]
            gcongr
            exact hcP_mono n hC0 (by positivity) (by exact_mod_cast hc_card_succ_le ξ ζ hζ)
        _ = ENNReal.ofReal (q * P * Real.exp (-((-1) * (t - s)))) := by
            rw [hc_sum_rate μ lam hμ hlam, ← ENNReal.ofReal_mul hq0, mul_assoc]
    refine (setLIntegral_mono' measurableSet_Icc hpt).trans ?_
    rw [hc_lint_Icc q (-1) t 0 t (q * P) ht (mul_nonneg hq0 hP0)]
    apply ENNReal.ofReal_le_ofReal
    set I := ∫ s in (0:ℝ)..t, Real.exp (-(q * s)) * Real.exp (-((-1) * (t - s))) with hI
    have hI0 : 0 ≤ I := hc_realint_nonneg _ _ _ _ _ ht
    have hId := hc_realint q (-1) t 0 t ht
    rw [← hI] at hId
    have e1 : Real.exp (-((-1) * (t - 0)) - q * 0) = Real.exp t := by ring_nf
    rw [e1] at hId
    have hqI : (q + 1) * I ≤ Real.exp t := by
      have := Real.exp_pos (-((-1) * (t - t)) - q * t)
      have e2 : q - -1 = q + 1 := by ring
      rw [e2] at hId; linarith
    have hm0 : (0 : ℝ) ≤ ξ.card := by positivity
    have h1 : q * I ≤ C * ξ.card * I := mul_le_mul_of_nonneg_right hqC hI0
    have h2 : C * ξ.card * ((q + 1) * I) ≤ C * ξ.card * Real.exp t :=
      mul_le_mul_of_nonneg_left hqI (by positivity)
    have key : q * I * (1 + C * ξ.card) ≤ Real.exp t * (C * ξ.card) := by nlinarith
    have key2 : q * I ≤ Real.exp t * hcg C ξ.card := by
      unfold hcg
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      exact key
    rw [hcP_succ, ← hP]
    calc q * P * I = (q * I) * P := by ring
      _ ≤ (Real.exp t * hcg C ξ.card) * P := mul_le_mul_of_nonneg_right key2 hP0
      _ = _ := by ring

theorem hc_B_tendsto {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (Λ : ℝ) (hΛ0 : 0 ≤ Λ)
    (hlamΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ) (t : ℝ) (ht : 0 ≤ t) (ξ : Config d) :
    Tendsto (fun n => hcB μ lam n t ξ) atTop (𝓝 0) := by
  have hC0 : 0 ≤ μ + 2 * (d : ℝ) * Λ := by positivity
  have h1 : Tendsto (fun n => ENNReal.ofReal (Real.exp t * hcP (μ + 2 * d * Λ) n ξ.card)) atTop (𝓝 0) := by
    have := ((hcP_tendsto _ _ hC0 (by positivity : (0:ℝ) ≤ ξ.card)).const_mul (Real.exp t))
    rw [mul_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun n => bot_le)
    (fun n => hc_B_bound μ lam hμ hlam Λ hΛ0 hlamΛ n t ht ξ)

/-! ## the lower bound `m_t(ξ) ≥ e^{-μt} |ξ|` -/

theorem hc_base {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (t : ℝ) (ht : 0 ≤ t) (ξ : Config d) :
    ENNReal.ofReal (Real.exp (-(μ * t))) * (ξ.card : ℝ≥0∞) ≤ meanSize μ lam t ξ := by
  classical
  set Λ := (Finset.range (2 * d + 1)).sup' (by simp) lam with hΛ
  have hlamΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ := fun k hk =>
    Finset.le_sup' lam (Finset.mem_range.mpr (by omega))
  have hΛ0 : 0 ≤ Λ := h0 ▸ hlamΛ 0 (Nat.zero_le _)
  have hx : ∀ x ∈ ξ, ENNReal.ofReal (Real.exp (-(μ * t))) ≤
      ⨆ n, hcW μ lam (fun η => if x ∈ η then 1 else 0) n t ξ := by
    intro x hx
    have hT : Tendsto (fun n => (⨆ n, hcW μ lam (fun η => if x ∈ η then 1 else 0) n t ξ) +
        hcB μ lam (n + 1) t ξ) atTop
        (𝓝 ((⨆ n, hcW μ lam (fun η => if x ∈ η then 1 else 0) n t ξ) + 0)) :=
      tendsto_const_nhds.add ((hc_B_tendsto μ lam hμ hlam Λ hΛ0 hlamΛ t ht ξ).comp
        (tendsto_add_atTop_nat 1))
    rw [add_zero] at hT
    refine ge_of_tendsto' hT fun n => ?_
    exact (hc_surv μ lam hμ hlam x n t ht ξ hx).trans (add_le_add (le_iSup
      (fun n => hcW μ lam (fun η => if x ∈ η then 1 else 0) n t ξ) n) le_rfl)
  calc ENNReal.ofReal (Real.exp (-(μ * t))) * (ξ.card : ℝ≥0∞)
      = ∑ x ∈ ξ, ENNReal.ofReal (Real.exp (-(μ * t))) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ ξ, ⨆ n, hcW μ lam (fun η => if x ∈ η then 1 else 0) n t ξ :=
        Finset.sum_le_sum hx
    _ = ⨆ n, ∑ x ∈ ξ, hcW μ lam (fun η => if x ∈ η then 1 else 0) n t ξ := by
        rw [ENNReal.finsetSum_iSup_of_monotone]
        intro x
        exact hc_W_mono μ lam _ t ξ
    _ ≤ ⨆ n, hcA μ lam n t ξ := by
        refine iSup_mono fun n => ?_
        unfold hcW hcA
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine ENNReal.tsum_le_tsum fun η => ?_
        rw [← Finset.mul_sum]
        gcongr
        rw [← Nat.cast_sum, ← Finset.card_filter]
        exact_mod_cast Finset.card_le_card (fun y hy => (Finset.mem_filter.mp hy).2)
    _ = meanSize μ lam t ξ := (hc_meanSize_eq_iSup μ lam t ξ).symm

/-! ## Lemma 4.11 -/

theorem lemma_4_11_core {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ t h : ℝ, 0 ≤ t → 0 ≤ h → ∀ ξ : HarrisContact.Extinction.Config d,
      ENNReal.ofReal (Real.exp (-(μ * h))) * HarrisContact.Extinction.meanSize μ lam t ξ ≤ HarrisContact.Extinction.meanSize μ lam (t + h) ξ := by
  intro t0 h ht0 hh ξ0
  -- the integrand of the backward equation at time `t + h`
  let F : ℝ → Config d → ℝ → ℝ≥0∞ := fun t ξ s =>
    ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
      ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * meanSize μ lam (t + h - s) ζ
  have hM : ∀ t, 0 ≤ t → ∀ ξ : Config d, meanSize μ lam (t + h) ξ =
      ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * (t + h)))) * (ξ.card : ℝ≥0∞) +
        ((∫⁻ s in Set.Icc 0 t, F t ξ s) + ∫⁻ s in Set.Ioc t (t + h), F t ξ s) := by
    intro t ht ξ
    rw [hc_meanSize_backward, ← lintegral_union measurableSet_Ioc]
    · rw [Set.Icc_union_Ioc_eq_Icc ht (by linarith)]
    · exact Set.disjoint_left.mpr fun s h1 h2 => by linarith [h1.2, h2.1]
  have hK : ∀ t, 0 ≤ t → ∀ ξ : Config d,
      ENNReal.ofReal (Real.exp (-(μ * h))) *
          (ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) * (ξ.card : ℝ≥0∞)) ≤
        ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * (t + h)))) * (ξ.card : ℝ≥0∞) +
          ∫⁻ s in Set.Ioc t (t + h), F t ξ s := by
    intro t ht ξ
    set q := exitRate μ lam ξ with hq
    have hb : 0 ≤ (q - μ) * ξ.card := by
      rcases Nat.eq_zero_or_pos ξ.card with h0 | hpos
      · simp [h0]
      · have hL := (hc_exitRate_facts μ lam hμ hlam ξ).1
        have h1 : (1 : ℝ) ≤ ξ.card := by exact_mod_cast hpos
        have : 0 ≤ q - μ := by rw [hq]; unfold exitRate; nlinarith
        positivity
    have hpt : ∀ s ∈ Set.Ioc t (t + h),
        ENNReal.ofReal (Real.exp (-(q * s))) *
          ENNReal.ofReal ((q - μ) * ξ.card * Real.exp (-(μ * (t + h - s)))) ≤ F t ξ s := by
      intro s hs
      have hr : 0 ≤ t + h - s := by linarith [hs.2]
      simp only [F]
      gcongr
      refine (hc_sum_rate_card μ lam hμ hlam ξ _ (Real.exp_pos _).le).trans ?_
      gcongr with ζ hζ
      exact hc_base μ lam hμ h0 hlam _ hr ζ
    refine le_trans ?_ (add_le_add le_rfl (setLIntegral_mono' measurableSet_Ioc hpt))
    rw [hc_lint q μ (t + h) t (t + h) _ (by linarith) hb]
    have hId := hc_realint q μ (t + h) t (t + h) (by linarith)
    set I := ∫ s in t..(t + h), Real.exp (-(q * s)) * Real.exp (-(μ * (t + h - s))) with hI
    have e1 : Real.exp (-(μ * (t + h - t)) - q * t) = Real.exp (-(μ * h)) * Real.exp (-(q * t)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(μ * (t + h - (t + h))) - q * (t + h)) = Real.exp (-(q * (t + h))) := by
      ring_nf
    rw [e1, e2] at hId
    have hcard : (ξ.card : ℝ≥0∞) = ENNReal.ofReal (ξ.card : ℝ) := (ENNReal.ofReal_natCast _).symm
    rw [hcard, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg hb (hc_realint_nonneg _ _ _ _ _ (by linarith)))]
    apply ENNReal.ofReal_le_ofReal
    have : (q - μ) * ξ.card * I = ξ.card * ((q - μ) * I) := by ring
    rw [this, hId]
    nlinarith
  have hclaim : ∀ n, ∀ t, 0 ≤ t → ∀ ξ : Config d,
      ENNReal.ofReal (Real.exp (-(μ * h))) * hcA μ lam n t ξ ≤ meanSize μ lam (t + h) ξ := by
    intro n
    induction n with
    | zero =>
      intro t ht ξ
      have : hcA μ lam 0 t ξ = hcW μ lam Finset.card 0 t ξ := rfl
      rw [this, hc_W_zero, hM t ht ξ]
      refine (hK t ht ξ).trans ?_
      exact add_le_add le_rfl le_add_self
    | succ n ih =>
      intro t ht ξ
      rw [hc_A_succ, hM t ht ξ, mul_add]
      have hI : ENNReal.ofReal (Real.exp (-(μ * h))) *
          ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
            ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcA μ lam n (t - s) ζ ≤
          ∫⁻ s in Set.Icc 0 t, F t ξ s := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        have hts : 0 ≤ t - s := by linarith [hs.2]
        simp only [F]
        rw [mul_left_comm, Finset.mul_sum]
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun ζ hζ => ?_)
        rw [mul_left_comm]
        refine mul_le_mul' le_rfl ?_
        have := ih (t - s) hts ζ
        rwa [show t - s + h = t + h - s by ring] at this
      calc _ ≤ (ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * (t + h)))) * (ξ.card : ℝ≥0∞) +
              ∫⁻ s in Set.Ioc t (t + h), F t ξ s) + ∫⁻ s in Set.Icc 0 t, F t ξ s :=
            add_le_add (hK t ht ξ) hI
        _ = _ := by ring
  rw [hc_meanSize_eq_iSup, ENNReal.mul_iSup]
  exact iSup_le fun n => hclaim n t0 ht0 ξ0

end HarrisContact.MeanSize

open HarrisContact.MeanSize


theorem solution {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ t h : ℝ, 0 ≤ t → 0 ≤ h → ∀ ξ : HarrisContact.Extinction.Config d,
      ENNReal.ofReal (Real.exp (-(μ * h))) * HarrisContact.Extinction.meanSize μ lam t ξ ≤ HarrisContact.Extinction.meanSize μ lam (t + h) ξ := by
  exact lemma_4_11_core hd μ lam hμ h0 hlam
