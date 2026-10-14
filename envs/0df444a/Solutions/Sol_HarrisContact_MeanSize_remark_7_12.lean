-- Prove2me | solution 1 for HarrisContact.MeanSize.remark_7_12
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:30:05.36099+00:00
-- url     : https://prove2.me/submissions/3080ee91-2565-48f4-b2bb-fda5b13c8d07

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


/-! ## translation invariance -/

theorem hc_mem_nbrs {d : ℕ} (x y : Site d) : y ∈ nbrs x ↔ ∑ i, |x i - y i| = 1 := by
  unfold nbrs
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨fun i => ?_, h⟩
    have : |x i - y i| ≤ 1 := h ▸ Finset.single_le_sum (f := fun j => |x j - y j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have := abs_le.mp this
    constructor <;> omega

/-- translation of a configuration by `v`. -/
noncomputable def hcT {d : ℕ} (v : Site d) (ξ : Config d) : Config d :=
  ξ.map (Equiv.addRight v).toEmbedding

theorem hc_mem_T {d : ℕ} (v y : Site d) (ξ : Config d) : y ∈ hcT v ξ ↔ y - v ∈ ξ := by
  unfold hcT
  simp only [Finset.mem_map_equiv]
  simp [sub_eq_add_neg]

theorem hc_nbrs_shift {d : ℕ} (v x y : Site d) : y ∈ nbrs (x + v) ↔ y - v ∈ nbrs x := by
  rw [hc_mem_nbrs, hc_mem_nbrs]
  have : ∀ i, (x + v) i - y i = x i - (y - v) i := fun i => by simp only [Pi.add_apply, Pi.sub_apply]; ring
  simp_rw [this]

theorem hc_T_inj {d : ℕ} (v : Site d) {ξ η : Config d} : hcT v ξ = hcT v η ↔ ξ = η :=
  Finset.map_inj

theorem hc_T_card {d : ℕ} (v : Site d) (ξ : Config d) : (hcT v ξ).card = ξ.card :=
  Finset.card_map _

theorem hc_T_erase {d : ℕ} (v x : Site d) (ξ : Config d) :
    (hcT v ξ).erase (x + v) = hcT v (ξ.erase x) := by
  ext y; simp only [Finset.mem_erase, hc_mem_T]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (by rw [← h]; abel), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (by rw [h]; abel), h2⟩

theorem hc_T_insert {d : ℕ} (v x : Site d) (ξ : Config d) :
    insert (x + v) (hcT v ξ) = hcT v (insert x ξ) := by
  ext y; simp only [Finset.mem_insert, hc_mem_T]
  constructor
  · rintro (h | h)
    · left; rw [h]; abel
    · right; exact h
  · rintro (h | h)
    · left; rw [← h]; abel
    · right; exact h

theorem hc_T_occ {d : ℕ} (v x : Site d) (ξ : Config d) :
    occ (hcT v ξ) (x + v) = occ ξ x := by
  unfold occ
  have : hcT v ξ ∩ nbrs (x + v) = hcT v (ξ ∩ nbrs x) := by
    ext y; simp only [Finset.mem_inter, hc_mem_T, hc_nbrs_shift]
  rw [this, hc_T_card]

theorem hc_mem_bdry {d : ℕ} (ξ : Config d) (y : Site d) :
    y ∈ bdry ξ ↔ (∃ w ∈ ξ, y ∈ nbrs w) ∧ y ∉ ξ := by
  unfold bdry; simp only [Finset.mem_sdiff, Finset.mem_biUnion]

theorem hc_T_bdry {d : ℕ} (v : Site d) (ξ : Config d) : bdry (hcT v ξ) = hcT v (bdry ξ) := by
  ext y
  rw [hc_mem_bdry, hc_mem_T v y ξ, hc_mem_T v y (bdry ξ), hc_mem_bdry]
  constructor
  · rintro ⟨⟨w, hw, hyw⟩, hy⟩
    refine ⟨⟨w - v, (hc_mem_T v w ξ).mp hw, ?_⟩, hy⟩
    have : w = (w - v) + v := by abel
    rw [this, hc_nbrs_shift] at hyw; exact hyw
  · rintro ⟨⟨w, hw, hyw⟩, hy⟩
    refine ⟨⟨w + v, (hc_mem_T v _ ξ).mpr (by simpa using hw), ?_⟩, hy⟩
    rw [hc_nbrs_shift]; exact hyw

theorem hc_T_sum {d : ℕ} {M : Type*} [AddCommMonoid M] (v : Site d) (ξ : Config d) (f : Site d → M) :
    ∑ x ∈ hcT v ξ, f x = ∑ x ∈ ξ, f (x + v) := by
  unfold hcT; rw [Finset.sum_map]; rfl

theorem hc_T_exitRate {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (v : Site d) (ξ : Config d) :
    exitRate μ lam (hcT v ξ) = exitRate μ lam ξ := by
  unfold exitRate
  rw [hc_T_card, hc_T_bdry, hc_T_sum]
  simp_rw [hc_T_occ]

theorem hc_T_transN {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (v : Site d) :
    ∀ n t (ξ η : Config d), transN μ lam n t (hcT v ξ) (hcT v η) = transN μ lam n t ξ η := by
  have hl : ∀ ξ : Config d, ∀ x ∈ bdry ξ, 0 ≤ lam (occ ξ x) := fun ξ x _ => hlam _ (hc_occ_le ξ x)
  have h0 : ∀ t (ξ η : Config d), transN μ lam 0 t (hcT v ξ) (hcT v η) = transN μ lam 0 t ξ η := by
    intro t ξ η
    simp only [transN.eq_1, hc_T_inj, hc_T_exitRate]
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro t ξ η
    simp only [transN.eq_2]
    rw [h0, hc_T_exitRate]
    congr 1
    refine lintegral_congr fun s => ?_
    congr 1
    rw [hc_succ_sum μ lam _ hμ (hl _), hc_succ_sum μ lam _ hμ (hl _), hc_T_sum, hc_T_bdry, hc_T_sum]
    congr 1
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [hc_T_erase, ih]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [hc_T_insert, ih, hc_T_occ]

theorem hc_T_meanSize {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (v : Site d) (t : ℝ) (ξ : Config d) :
    meanSize μ lam t (hcT v ξ) = meanSize μ lam t ξ := by
  unfold meanSize
  rw [← (Equiv.finsetCongr (Equiv.addRight v)).tsum_eq]
  refine tsum_congr fun η => ?_
  have : (Equiv.finsetCongr (Equiv.addRight v)) η = hcT v η := rfl
  rw [this, hc_T_card]
  unfold Extinction.trans
  simp_rw [hc_T_transN μ lam hμ hlam v]


/-! ## counting neighbours -/

theorem hc_card_nbrs {d : ℕ} (x : Site d) : (nbrs x).card = 2 * d := by
  classical
  refine le_antisymm (hc_card_nbrs_le x) ?_
  let g : Fin d × Bool → Site d := fun p => Function.update x p.1 (x p.1 + if p.2 then 1 else -1)
  have hg : Function.Injective g := by
    rintro ⟨i, b⟩ ⟨j, b'⟩ h
    by_cases hij : i = j
    · subst hij
      have := congrFun h i
      simp only [g, Function.update_self] at this
      cases b <;> cases b' <;> simp_all
    · have := congrFun h i
      simp only [g, Function.update_self, Function.update_of_ne hij] at this
      split_ifs at this <;> omega
  have hsub : Finset.univ.image g ⊆ nbrs x := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨⟨i, b⟩, rfl⟩ := hy
    rw [hc_mem_nbrs, Finset.sum_eq_single i]
    · simp only [g, Function.update_self]; split_ifs <;> simp
    · intro j _ hj; simp [g, Function.update_of_ne hj]
    · simp
  calc 2 * d = (Finset.univ : Finset (Fin d × Bool)).card := by simp [Finset.card_univ]; ring
    _ = (Finset.univ.image g).card := (Finset.card_image_of_injective _ hg).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem hc_nbrs_symm {d : ℕ} (x y : Site d) : y ∈ nbrs x ↔ x ∈ nbrs y := by
  rw [hc_mem_nbrs, hc_mem_nbrs]
  have : ∀ i, |x i - y i| = |y i - x i| := fun i => abs_sub_comm _ _
  simp_rw [this]

theorem hc_not_mem_nbrs_self {d : ℕ} (x : Site d) : x ∉ nbrs x := by
  rw [hc_mem_nbrs]; simp

theorem hc_sum_occ {d : ℕ} (ξ : Config d) :
    ∑ z ∈ bdry ξ, occ ξ z = ∑ w ∈ ξ, (nbrs w \ ξ).card := by
  classical
  have h1 : ∀ z, occ ξ z = ∑ w ∈ ξ, if z ∈ nbrs w then 1 else 0 := by
    intro z
    unfold occ
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    congr 1; ext w; simp [Finset.mem_inter, Finset.mem_filter, hc_nbrs_symm z w]
  have h2 : ∀ w ∈ ξ, (nbrs w \ ξ).card = ∑ z ∈ bdry ξ, if z ∈ nbrs w then 1 else 0 := by
    intro w hw
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    congr 1; ext z; simp only [Finset.mem_sdiff, Finset.mem_filter, hc_mem_bdry]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨⟨w, hw, h1⟩, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
  rw [Finset.sum_congr rfl fun z _ => h1 z, Finset.sum_comm]
  exact Finset.sum_congr rfl fun w hw => (h2 w hw).symm

theorem hc_rate_insert {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) (z : Site d) (hz : z ∈ bdry ξ) :
    rate μ lam ξ (insert z ξ) = lam (occ ξ z) := by
  have hzξ : z ∉ ξ := ((hc_mem_bdry ξ z).mp hz).2
  unfold rate
  rw [Finset.sum_eq_zero, zero_add, Finset.sum_eq_single z]
  · simp
  · intro w hw hwz
    rw [if_neg]
    intro h
    have : z ∈ insert w ξ := h ▸ Finset.mem_insert_self z ξ
    rcases Finset.mem_insert.mp this with h' | h'
    · exact hwz h'.symm
    · exact hzξ h'
  · intro h; exact absurd hz h
  · intro w _
    rw [if_neg]
    intro h
    have : z ∈ ξ.erase w := h ▸ Finset.mem_insert_self z ξ
    exact hzξ (Finset.mem_of_mem_erase this)

theorem hc_sum_occ_pair {d : ℕ} (x y : Site d) (hxy : y ∈ nbrs x) :
    ∑ z ∈ bdry ({x, y} : Config d), occ {x, y} z = 4 * d - 2 := by
  have hne : x ≠ y := fun h => hc_not_mem_nbrs_self x (h ▸ hxy)
  have hyx : x ∈ nbrs y := (hc_nbrs_symm x y).mp hxy
  rw [hc_sum_occ, Finset.sum_pair hne]
  have e1 : nbrs x \ {x, y} = (nbrs x).erase y := by
    ext z; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun h => h2 (Or.inr h), h1⟩
    · rintro ⟨h1, h2⟩; refine ⟨h2, ?_⟩
      rintro (h | h)
      · exact hc_not_mem_nbrs_self x (h ▸ h2)
      · exact h1 h
  have e2 : nbrs y \ {x, y} = (nbrs y).erase x := by
    ext z; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun h => h2 (Or.inl h), h1⟩
    · rintro ⟨h1, h2⟩; refine ⟨h2, ?_⟩
      rintro (h | h)
      · exact h1 h
      · exact hc_not_mem_nbrs_self y (h ▸ h2)
  rw [e1, e2, Finset.card_erase_of_mem hxy, Finset.card_erase_of_mem hyx, hc_card_nbrs, hc_card_nbrs]
  omega

theorem eq_7_7_core {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) (x y : HarrisContact.Extinction.Site d) (hxy : y ∈ HarrisContact.Extinction.nbrs x)
    (t : ℝ) (ht : 0 ≤ t) :
    HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) t ({x, y} : HarrisContact.Extinction.Config d) =
      2 * ENNReal.ofReal (Real.exp (-((2 + (4 * (d : ℝ) - 2) * l) * t))) +
      ∫⁻ s in Set.Icc 0 t,
        ENNReal.ofReal ((2 + (4 * (d : ℝ) - 2) * l) * Real.exp (-((2 + (4 * (d : ℝ) - 2) * l) * s))) *
          (ENNReal.ofReal (2 / (2 + (4 * (d : ℝ) - 2) * l)) *
              HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) (t - s) {x} +
            ∑ z ∈ HarrisContact.Extinction.bdry ({x, y} : HarrisContact.Extinction.Config d),
              ENNReal.ofReal (HarrisContact.Extinction.jump 1 (fun k => (k : ℝ) * l) {x, y} (insert z {x, y})) *
                HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) (t - s) (insert z {x, y})) := by
  set K := 2 + (4 * (d : ℝ) - 2) * l with hKdef
  set Lam : ℕ → ℝ := fun k => (k : ℝ) * l with hLam
  have hne : x ≠ y := fun h => hc_not_mem_nbrs_self x (h ▸ hxy)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hKpos : 0 < K := by rw [hKdef]; nlinarith
  have hK : exitRate 1 Lam ({x, y} : Config d) = K := by
    unfold exitRate
    rw [Finset.card_pair hne]
    have : ∑ z ∈ bdry ({x, y} : Config d), Lam (occ {x, y} z) =
        ((∑ z ∈ bdry ({x, y} : Config d), occ {x, y} z : ℕ) : ℝ) * l := by
      rw [Nat.cast_sum, Finset.sum_mul]
    rw [this, hc_sum_occ_pair x y hxy, hKdef]
    have h4 : 2 ≤ 4 * d := by omega
    push_cast [Nat.cast_sub h4]
    ring
  have hlamnn : ∀ k, k ≤ 2 * d → 0 ≤ Lam k := fun k _ => by simp only [hLam]; positivity
  have hl' : ∀ z ∈ bdry ({x, y} : Config d), 0 ≤ Lam (occ {x, y} z) := fun z _ => by simp only [hLam]; positivity
  have hmy : ∀ r, meanSize 1 Lam r ({y} : Config d) = meanSize 1 Lam r {x} := by
    intro r
    have : hcT (x - y) ({y} : Config d) = {x} := by
      unfold hcT; rw [Finset.map_singleton]; simp
    rw [← this, hc_T_meanSize 1 Lam zero_le_one hlamnn]
  rw [hc_meanSize_backward, hK, Finset.card_pair hne]
  congr 1
  · push_cast; ring
  refine lintegral_congr fun s => ?_
  have he : 0 ≤ Real.exp (-(K * s)) := (Real.exp_pos _).le
  have hKe : 0 ≤ K * Real.exp (-(K * s)) := mul_nonneg hKpos.le he
  have hA : ENNReal.ofReal (K * Real.exp (-(K * s))) * ENNReal.ofReal (2 / K) =
      ENNReal.ofReal (Real.exp (-(K * s))) * 2 := by
    rw [← ENNReal.ofReal_mul hKe, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul he]
    congr 1; field_simp
  have hB : ∀ r : ℝ, ENNReal.ofReal (K * Real.exp (-(K * s))) * ENNReal.ofReal (r / K) =
      ENNReal.ofReal (Real.exp (-(K * s))) * ENNReal.ofReal r := by
    intro r
    rw [← ENNReal.ofReal_mul hKe, ← ENNReal.ofReal_mul he]
    congr 1; field_simp
  have hjump : ∀ z ∈ bdry ({x, y} : Config d),
      jump 1 Lam {x, y} (insert z {x, y}) = Lam (occ {x, y} z) / K := by
    intro z hz
    unfold jump
    rw [hK, if_neg hKpos.ne', hc_rate_insert 1 Lam _ z hz]
  rw [hc_succ_sum 1 Lam _ zero_le_one hl', Finset.sum_pair hne, Finset.erase_insert_eq_erase,
    Finset.erase_eq_of_notMem (by simpa using hne), Finset.pair_comm, Finset.erase_insert_eq_erase,
    Finset.erase_eq_of_notMem (by simpa using hne.symm), Finset.pair_comm, hmy]
  conv_rhs => rw [mul_add, ← mul_assoc, hA, Finset.mul_sum]
  have hS : ∑ z ∈ bdry ({x, y} : Config d), ENNReal.ofReal (K * Real.exp (-(K * s))) *
        (ENNReal.ofReal (jump 1 Lam {x, y} (insert z {x, y})) * meanSize 1 Lam (t - s) (insert z {x, y})) =
      ENNReal.ofReal (Real.exp (-(K * s))) * ∑ z ∈ bdry ({x, y} : Config d),
        ENNReal.ofReal (Lam (occ {x, y} z)) * meanSize 1 Lam (t - s) (insert z {x, y}) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [hjump z hz, ← mul_assoc, hB, mul_assoc]
  rw [hS]
  simp only [ENNReal.ofReal_one, one_mul]
  ring


/-! ## Theorem 7.6: a Lyapunov function -/

/-- `D(ξ) = Σ_{x ∈ ξ} ξ(N_x)`, twice the number of internal edges. -/
noncomputable def hcD {d : ℕ} (ξ : Config d) : ℕ := ∑ x ∈ ξ, occ ξ x

theorem hc_occ_erase {d : ℕ} (ξ : Config d) (x y : Site d) :
    occ (ξ.erase x) y + (if x ∈ ξ ∧ x ∈ nbrs y then 1 else 0) = occ ξ y := by
  unfold occ
  rw [Finset.erase_inter]
  split_ifs with h
  · exact Finset.card_erase_add_one (Finset.mem_inter.mpr h)
  · rw [Finset.erase_eq_of_notMem (fun h' => h (Finset.mem_inter.mp h')), add_zero]

theorem hc_D_erase {d : ℕ} (ξ : Config d) (x : Site d) (hx : x ∈ ξ) :
    hcD ξ = hcD (ξ.erase x) + 2 * occ ξ x := by
  classical
  unfold hcD
  rw [← Finset.add_sum_erase ξ _ hx]
  have h1 : ∀ y ∈ ξ.erase x, occ ξ y = occ (ξ.erase x) y + (if x ∈ nbrs y then 1 else 0) := by
    intro y _
    rw [← hc_occ_erase ξ x y]; simp [hx]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have h2 : ∑ y ∈ ξ.erase x, (if x ∈ nbrs y then 1 else 0) = occ ξ x := by
    rw [← Finset.card_filter]
    unfold occ
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter]
    rw [← hc_nbrs_symm x y]
    constructor
    · rintro ⟨⟨_, hy⟩, h⟩; exact ⟨hy, h⟩
    · rintro ⟨hy, h⟩
      refine ⟨⟨fun e => hc_not_mem_nbrs_self x ?_, hy⟩, h⟩
      rw [e] at h; exact h
  rw [h2]; ring

theorem hc_D_insert {d : ℕ} (ξ : Config d) (z : Site d) (hz : z ∉ ξ) :
    hcD (insert z ξ) = hcD ξ + 2 * occ ξ z := by
  rw [hc_D_erase (insert z ξ) z (Finset.mem_insert_self z ξ), Finset.erase_insert hz]
  unfold occ
  rw [Finset.insert_inter_of_notMem (hc_not_mem_nbrs_self z)]

theorem hc_D_le {d : ℕ} (ξ : Config d) : hcD ξ ≤ 2 * d * ξ.card := by
  unfold hcD
  calc ∑ x ∈ ξ, occ ξ x ≤ ∑ x ∈ ξ, 2 * d := Finset.sum_le_sum fun x _ => hc_occ_le ξ x
    _ = 2 * d * ξ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem hc_bdry_occ_add_D {d : ℕ} (ξ : Config d) :
    ∑ z ∈ bdry ξ, occ ξ z + hcD ξ = 2 * d * ξ.card := by
  rw [hc_sum_occ]
  unfold hcD
  rw [← Finset.sum_add_distrib]
  have : ∀ w ∈ ξ, (nbrs w \ ξ).card + occ ξ w = 2 * d := by
    intro w _
    unfold occ
    rw [Finset.inter_comm, Finset.card_sdiff_add_card_inter, hc_card_nbrs]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The Lyapunov function `V(ξ) = (1 + ρ)|ξ| − (ρ/2) D(ξ)`. -/
noncomputable def hcV {d : ℕ} (ρ : ℝ) (ξ : Config d) : ℝ := (1 + ρ) * ξ.card - ρ / 2 * hcD ξ

theorem hc_V_nonneg {d : ℕ} (ρ : ℝ) (hρ : 0 ≤ ρ) (hρd : ρ * (2 * d - 1) < 1) (ξ : Config d) :
    0 ≤ hcV ρ ξ := by
  unfold hcV
  have h1 : (hcD ξ : ℝ) ≤ 2 * d * ξ.card := by exact_mod_cast hc_D_le ξ
  have h2 : (0 : ℝ) ≤ ξ.card := by positivity
  have h3 : ρ * d ≤ 1 + ρ := by
    have : (0:ℝ) ≤ d := by positivity
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hρ, mul_le_mul_of_nonneg_right h3 h2]

theorem hc_drift {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρd : ρ * (2 * d - 1) < 1)
    (hlamρ : ∀ k, 1 ≤ k → k ≤ 2 * d → lam k ≤ ρ * μ * k) (ξ : Config d) :
    μ * (1 - (2 * d - 1) * ρ) * ξ.card +
        (∑ x ∈ ξ, μ * hcV ρ (ξ.erase x) + ∑ z ∈ bdry ξ, lam (occ ξ z) * hcV ρ (insert z ξ)) ≤
      exitRate μ lam ξ * hcV ρ ξ := by
  have e1 : ∑ x ∈ ξ, μ * hcV ρ (ξ.erase x) =
      ∑ x ∈ ξ, (μ * hcV ρ ξ - μ * (1 + ρ) + μ * ρ * (occ ξ x : ℝ)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    unfold hcV
    have hD : (hcD ξ : ℝ) = hcD (ξ.erase x) + 2 * occ ξ x := by exact_mod_cast hc_D_erase ξ x hx
    have hc : ((ξ.erase x).card : ℝ) = ξ.card - 1 := by
      rw [Finset.card_erase_of_mem hx, Nat.cast_sub (Finset.card_pos.mpr ⟨x, hx⟩)]; simp
    rw [hD, hc]; ring
  have e2 : ∑ z ∈ bdry ξ, lam (occ ξ z) * hcV ρ (insert z ξ) =
      ∑ z ∈ bdry ξ, (lam (occ ξ z) * hcV ρ ξ + lam (occ ξ z) * (1 + ρ - ρ * (occ ξ z : ℝ))) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' : z ∉ ξ := ((hc_mem_bdry ξ z).mp hz).2
    unfold hcV
    have hD : (hcD (insert z ξ) : ℝ) = hcD ξ + 2 * occ ξ z := by exact_mod_cast hc_D_insert ξ z hz'
    rw [hD, Finset.card_insert_of_notMem hz']; push_cast; ring
  have hS : ∑ z ∈ bdry ξ, lam (occ ξ z) * (1 + ρ - ρ * (occ ξ z : ℝ)) ≤
      ∑ z ∈ bdry ξ, ρ * μ * (occ ξ z : ℝ) := by
    refine Finset.sum_le_sum fun z hz => ?_
    have hk1 : 1 ≤ occ ξ z := by
      obtain ⟨⟨w, hw, hzw⟩, _⟩ := (hc_mem_bdry ξ z).mp hz
      unfold occ
      exact Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr ⟨hw, (hc_nbrs_symm w z).mp hzw⟩⟩
    have hk2 := hc_occ_le ξ z
    have hk1' : (1 : ℝ) ≤ occ ξ z := by exact_mod_cast hk1
    have hk2' : (occ ξ z : ℝ) ≤ 2 * d := by exact_mod_cast hk2
    have hl := hlamρ _ hk1 hk2
    have hl0 := hlam _ hk2
    have hpos : 0 ≤ 1 + ρ - ρ * (occ ξ z : ℝ) := by nlinarith
    have : lam (occ ξ z) * (1 + ρ - ρ * (occ ξ z : ℝ)) ≤ ρ * μ * occ ξ z * (1 + ρ - ρ * (occ ξ z : ℝ)) :=
      mul_le_mul_of_nonneg_right hl hpos
    have hρμ : 0 ≤ ρ * μ * (occ ξ z : ℝ) := by positivity
    nlinarith [mul_nonneg hρμ (mul_nonneg hρ (sub_nonneg.mpr hk1'))]
  have hB : (∑ z ∈ bdry ξ, (occ ξ z : ℝ)) + hcD ξ = 2 * d * ξ.card := by
    exact_mod_cast hc_bdry_occ_add_D ξ
  rw [e1, e2, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum] at hS
  simp only [Finset.sum_const, nsmul_eq_mul] at *
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hDsum : ∑ x ∈ ξ, (occ ξ x : ℝ) = hcD ξ := by unfold hcD; push_cast; rfl
  rw [hDsum]
  unfold exitRate
  linear_combination hS + (ρ * μ) * hB

/-! ## integrals over `(0, ∞)` -/

theorem hc_conv (φ ψ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hψ : Measurable ψ) :
    ∫⁻ t in Set.Ioi 0, ∫⁻ s in Set.Icc 0 t, φ s * ψ (t - s) ≤
      (∫⁻ s in Set.Ici 0, φ s) * ∫⁻ u in Set.Ici 0, ψ u := by
  set φ' := (Set.Ici (0:ℝ)).indicator φ with hφ'def
  set ψ' := (Set.Ici (0:ℝ)).indicator ψ with hψ'def
  have hφ' : Measurable φ' := hφ.indicator measurableSet_Ici
  have hψ' : Measurable ψ' := hψ.indicator measurableSet_Ici
  calc ∫⁻ t in Set.Ioi 0, ∫⁻ s in Set.Icc 0 t, φ s * ψ (t - s)
      ≤ ∫⁻ t, ∫⁻ s, φ' s * ψ' (t - s) := by
        refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun t => ?_)
        rw [← lintegral_indicator measurableSet_Icc]
        refine lintegral_mono fun s => ?_
        by_cases hs : s ∈ Set.Icc 0 t
        · rw [Set.indicator_of_mem hs]
          have h1 : s ∈ Set.Ici (0:ℝ) := hs.1
          have h2 : t - s ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith [hs.2]
          rw [hφ'def, hψ'def, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
        · rw [Set.indicator_of_notMem hs]; exact bot_le
    _ = ∫⁻ s, ∫⁻ t, φ' s * ψ' (t - s) := by
        refine lintegral_lintegral_swap ?_
        exact (Measurable.mul (hφ'.comp measurable_snd)
          (hψ'.comp (measurable_fst.sub measurable_snd))).aemeasurable
    _ = ∫⁻ s, φ' s * ∫⁻ u, ψ' u := by
        refine lintegral_congr fun s => ?_
        rw [lintegral_const_mul (φ' s) (f := fun t => ψ' (t - s)) (hψ'.comp (measurable_id.sub measurable_const)),
          lintegral_sub_right_eq_self (fun u => ψ' u) s]
    _ = (∫⁻ s in Set.Ici 0, φ s) * ∫⁻ u in Set.Ici 0, ψ u := by
        rw [lintegral_mul_const _ hφ', lintegral_indicator measurableSet_Ici,
          lintegral_indicator measurableSet_Ici]

theorem hc_lint_exp (q : ℝ) (hq : 0 < q) :
    ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (Real.exp (-(q * t))) = ENNReal.ofReal (1 / q) := by
  have h1 : (fun t : ℝ => Real.exp (-(q * t))) = fun t => Real.exp (-q * t) := by
    funext t; ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [h1, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero, neg_div_neg_eq]
  · rw [h1]; exact integrableOn_exp_mul_Ioi (by linarith) 0
  · exact Filter.Eventually.of_forall fun t => (Real.exp_pos _).le

theorem hc_G_succ_le {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (n : ℕ) (ξ : Config d)
    (hq : 0 < exitRate μ lam ξ) :
    ∫⁻ t in Set.Ioi 0, hcA μ lam (n + 1) t ξ ≤ ENNReal.ofReal (1 / exitRate μ lam ξ) *
      ((ξ.card : ℝ≥0∞) + ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
        ∫⁻ t in Set.Ioi 0, hcA μ lam n t ζ) := by
  set q := exitRate μ lam ξ with hqdef
  have hE : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s)))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hψ : Measurable (fun u => ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcA μ lam n u ζ) :=
    Finset.measurable_sum _ fun ζ _ => measurable_const.mul (hc_meas_A μ lam n ζ)
  have hIci : ∀ f : ℝ → ℝ≥0∞, ∫⁻ s in Set.Ici 0, f s = ∫⁻ s in Set.Ioi 0, f s :=
    fun f => setLIntegral_congr Ioi_ae_eq_Ici.symm
  simp_rw [hc_A_succ]
  rw [lintegral_add_left ((hE.mul_const _)), lintegral_mul_const _ hE, hc_lint_exp q hq, mul_add]
  refine add_le_add (le_of_eq rfl) ?_
  refine (hc_conv _ _ hE hψ).trans (le_of_eq ?_)
  rw [hIci, hIci, hc_lint_exp q hq, lintegral_finsetSum (f := fun ζ t => ENNReal.ofReal (rate μ lam ξ ζ) * hcA μ lam n t ζ) _
    fun ζ _ => measurable_const.mul (hc_meas_A μ lam n ζ)]
  congr 1
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [lintegral_const_mul _ (hc_meas_A μ lam n ζ)]

theorem hc_A_empty {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    hcA μ lam n t (∅ : Config d) = 0 := by
  cases n with
  | zero =>
    have : hcA μ lam 0 t (∅ : Config d) = hcW μ lam Finset.card 0 t ∅ := rfl
    rw [this, hc_W_zero]; simp
  | succ n =>
    rw [hc_A_succ]
    have : succ (∅ : Config d) = ∅ := by simp [succ, bdry]
    simp [this]

theorem hc_rateV {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (V : Config d → ℝ) (hV : ∀ ξ, 0 ≤ V ξ) (ξ : Config d) :
    ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * ENNReal.ofReal (V ζ) =
      ENNReal.ofReal (∑ x ∈ ξ, μ * V (ξ.erase x) + ∑ z ∈ bdry ξ, lam (occ ξ z) * V (insert z ξ)) := by
  have hlb : ∀ x ∈ bdry ξ, 0 ≤ lam (occ ξ x) := fun x _ => hlam _ (hc_occ_le ξ x)
  rw [hc_succ_sum μ lam ξ hμ hlb (fun ζ => ENNReal.ofReal (V ζ)),
    ENNReal.ofReal_add (Finset.sum_nonneg fun x _ => mul_nonneg hμ (hV _))
      (Finset.sum_nonneg fun x hx => mul_nonneg (hlb x hx) (hV _)),
    ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg hμ (hV _)),
    ENNReal.ofReal_sum_of_nonneg (fun x hx => mul_nonneg (hlb x hx) (hV _))]
  congr 1
  · exact Finset.sum_congr rfl fun x _ => (ENNReal.ofReal_mul hμ).symm
  · exact Finset.sum_congr rfl fun x hx => (ENNReal.ofReal_mul (hlb x hx)).symm

theorem theorem_7_6_core {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsub : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k / μ < k / (2 * (d : ℝ) - 1)) :
    ∀ ξ : HarrisContact.Extinction.Config d, ∫⁻ t in Set.Ioi (0 : ℝ), HarrisContact.Extinction.meanSize μ lam t ξ < ∞ := by
  intro ξ0
  have hne : (Finset.Icc 1 (2 * d)).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  set ρ := (Finset.Icc 1 (2 * d)).sup' hne (fun k => lam k / (k * μ)) with hρdef
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2d : (0 : ℝ) < 2 * d - 1 := by linarith
  have hle : ∀ k, 1 ≤ k → k ≤ 2 * d → lam k / (k * μ) ≤ ρ := fun k h1 h2 =>
    Finset.le_sup' (fun k => lam k / (k * μ)) (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hρ0 : 0 ≤ ρ := (div_nonneg (hlam 1 (by omega)) (by positivity)).trans (hle 1 le_rfl (by omega))
  have hρlt : ρ < 1 / (2 * d - 1) := by
    rw [hρdef, Finset.sup'_lt_iff]
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    have hk : (0 : ℝ) < k := by exact_mod_cast h1
    have := hsub k h1 h2
    rw [div_lt_div_iff₀ hμ h2d] at this
    rw [div_lt_div_iff₀ (by positivity) h2d]
    nlinarith
  have hρd : ρ * (2 * d - 1) < 1 := by
    rw [lt_div_iff₀ h2d] at hρlt; linarith
  have hlamρ : ∀ k, 1 ≤ k → k ≤ 2 * d → lam k ≤ ρ * μ * k := by
    intro k h1 h2
    have hk : (0 : ℝ) < k := by exact_mod_cast h1
    have := hle k h1 h2
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  set δ := μ * (1 - (2 * d - 1) * ρ) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; apply mul_pos hμ; nlinarith
  have hV0 : ∀ ξ : Config d, 0 ≤ hcV ρ ξ := hc_V_nonneg ρ hρ0 hρd
  have hVδ : ∀ ξ : Config d, 0 ≤ hcV ρ ξ / δ := fun ξ => div_nonneg (hV0 ξ) hδ0.le
  -- main bound
  have hG : ∀ n (ξ : Config d), ∫⁻ t in Set.Ioi 0, hcA μ lam n t ξ ≤ ENNReal.ofReal (hcV ρ ξ / δ) := by
    intro n
    induction n with
    | zero =>
      intro ξ
      by_cases hξ : ξ = ∅
      · subst hξ; simp_rw [hc_A_empty]; simp
      have hcard : (1 : ℝ) ≤ ξ.card := by
        exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hξ)
      have hL := (hc_exitRate_facts μ lam hμ.le hlam ξ).1
      have hq : 0 < exitRate μ lam ξ := by unfold exitRate; nlinarith
      have hA0 : ∀ t, hcA μ lam 0 t ξ = ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) * (ξ.card : ℝ≥0∞) :=
        fun t => hc_W_zero μ lam Finset.card t ξ
      simp_rw [hA0]
      rw [lintegral_mul_const (f := fun t => ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t)))) _
          (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun t : ℝ => Real.exp (-(exitRate μ lam ξ * t)))),
        hc_lint_exp _ hq,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hdr := hc_drift μ lam hμ hlam ρ hρ0 hρd hlamρ ξ
      have hs : 0 ≤ ∑ x ∈ ξ, μ * hcV ρ (ξ.erase x) + ∑ z ∈ bdry ξ, lam (occ ξ z) * hcV ρ (insert z ξ) :=
        add_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg hμ.le (hV0 _))
          (Finset.sum_nonneg fun z _ => mul_nonneg (hlam _ (hc_occ_le ξ z)) (hV0 _))
      rw [one_div_mul_eq_div, div_le_div_iff₀ hq hδ0]
      linarith
    | succ n ih =>
      intro ξ
      by_cases hξ : ξ = ∅
      · subst hξ; simp_rw [hc_A_empty]; simp
      have hcard : (1 : ℝ) ≤ ξ.card := by
        exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hξ)
      have hL := (hc_exitRate_facts μ lam hμ.le hlam ξ).1
      set q := exitRate μ lam ξ with hqdef
      have hq : 0 < q := by rw [hqdef]; unfold exitRate; nlinarith
      refine (hc_G_succ_le μ lam n ξ hq).trans ?_
      calc ENNReal.ofReal (1 / q) * ((ξ.card : ℝ≥0∞) + ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
            ∫⁻ t in Set.Ioi 0, hcA μ lam n t ζ)
          ≤ ENNReal.ofReal (1 / q) * ((ξ.card : ℝ≥0∞) + ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
            ENNReal.ofReal (hcV ρ ζ / δ)) := by
            gcongr with ζ hζ
            exact ih ζ
        _ = ENNReal.ofReal (1 / q) * ENNReal.ofReal (ξ.card +
              (∑ x ∈ ξ, μ * (hcV ρ (ξ.erase x) / δ) + ∑ z ∈ bdry ξ, lam (occ ξ z) * (hcV ρ (insert z ξ) / δ))) := by
            rw [hc_rateV μ lam hμ.le hlam (fun ζ => hcV ρ ζ / δ) hVδ ξ,
              ENNReal.ofReal_add (by positivity)
                (add_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg hμ.le (hVδ _))
                  (Finset.sum_nonneg fun z _ => mul_nonneg (hlam _ (hc_occ_le ξ z)) (hVδ _))),
              ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (hcV ρ ξ / δ) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            have hdr := hc_drift μ lam hμ hlam ρ hρ0 hρd hlamρ ξ
            have e : ∑ x ∈ ξ, μ * (hcV ρ (ξ.erase x) / δ) + ∑ z ∈ bdry ξ, lam (occ ξ z) * (hcV ρ (insert z ξ) / δ) =
                (∑ x ∈ ξ, μ * hcV ρ (ξ.erase x) + ∑ z ∈ bdry ξ, lam (occ ξ z) * hcV ρ (insert z ξ)) / δ := by
              rw [add_div, Finset.sum_div, Finset.sum_div]
              congr 1
              · exact Finset.sum_congr rfl fun x _ => by ring
              · exact Finset.sum_congr rfl fun x _ => by ring
            rw [e, one_div_mul_eq_div, div_le_div_iff₀ hq hδ0]
            have : (ξ.card + (∑ x ∈ ξ, μ * hcV ρ (ξ.erase x) + ∑ z ∈ bdry ξ, lam (occ ξ z) * hcV ρ (insert z ξ)) / δ) * δ =
                δ * ξ.card + (∑ x ∈ ξ, μ * hcV ρ (ξ.erase x) + ∑ z ∈ bdry ξ, lam (occ ξ z) * hcV ρ (insert z ξ)) := by
              field_simp
            rw [this]
            linarith
  have hmeas : ∀ n, Measurable (fun t => hcA μ lam n t ξ0) := fun n => hc_meas_A μ lam n ξ0
  calc ∫⁻ t in Set.Ioi (0 : ℝ), meanSize μ lam t ξ0
      = ∫⁻ t in Set.Ioi (0 : ℝ), ⨆ n, hcA μ lam n t ξ0 := by
        simp_rw [hc_meanSize_eq_iSup]
    _ = ⨆ n, ∫⁻ t in Set.Ioi (0 : ℝ), hcA μ lam n t ξ0 :=
        lintegral_iSup hmeas (fun m k hmk t => hc_A_mono μ lam t ξ0 hmk)
    _ ≤ ENNReal.ofReal (hcV ρ ξ0 / δ) := iSup_le fun n => hG n ξ0
    _ < ∞ := ENNReal.ofReal_lt_top


/-! ## Remark 7.12 -/

theorem hc_meas_meanSize {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) :
    Measurable (fun t => meanSize μ lam t ξ) := by
  have : (fun t => meanSize μ lam t ξ) = fun t => ⨆ n, hcA μ lam n t ξ := by
    funext t; exact hc_meanSize_eq_iSup μ lam t ξ
  rw [this]
  exact Measurable.iSup fun n => hc_meas_A μ lam n ξ

theorem remark_7_12_core {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsub : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k / μ < k / (2 * (d : ℝ) - 1)) :
    ∀ ξ : HarrisContact.Extinction.Config d, Tendsto (fun t : ℝ => HarrisContact.Extinction.meanSize μ lam t ξ) atTop (𝓝 0) := by
  intro ξ
  set f : ℝ → ℝ≥0∞ := fun t => meanSize μ lam t ξ with hf
  have hfm : Measurable f := hc_meas_meanSize μ lam ξ
  have hfin : ∫⁻ t in Set.Ioi (0 : ℝ), f t ≠ ∞ :=
    (theorem_7_6_core hd μ lam hμ h0 hlam hsub ξ).ne
  -- tails of the integral tend to zero
  have htail : Tendsto (fun T : ℝ => ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Ioi T).indicator f t) atTop (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (l := atTop) (F := fun T => (Set.Ioi T).indicator f) (f := fun _ => 0) f
      (Filter.Eventually.of_forall fun T => hfm.indicator measurableSet_Ioi)
      (Filter.Eventually.of_forall fun T => Filter.Eventually.of_forall fun t =>
        Set.indicator_le_self _ _ t) hfin
      (Filter.Eventually.of_forall fun t => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop t] with T hT
        rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact hT)])
    simpa using this
  -- lower bound of the tail by the value at `T`
  have hlow : ∀ T : ℝ, 0 ≤ T → ENNReal.ofReal (Real.exp (-μ)) * f T ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Ioi T).indicator f t := by
    intro T hT
    calc ENNReal.ofReal (Real.exp (-μ)) * f T
        = ∫⁻ t in Set.Ioc T (T + 1), ENNReal.ofReal (Real.exp (-μ)) * f T := by
          rw [setLIntegral_const, Real.volume_Ioc, show T + 1 - T = 1 by ring, ENNReal.ofReal_one, mul_one]
      _ ≤ ∫⁻ t in Set.Ioc T (T + 1), f t := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          have h1 : 0 ≤ t - T := by linarith [ht.1]
          have h2 := lemma_4_11_core hd μ lam hμ.le h0 hlam T (t - T) hT h1 ξ
          rw [show T + (t - T) = t by ring] at h2
          refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) h2
          apply Real.exp_le_exp.mpr
          nlinarith [ht.2]
      _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Ioi T).indicator f t := by
          rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioi]
          refine lintegral_mono fun t => ?_
          by_cases ht : t ∈ Set.Ioc T (T + 1)
          · have h1 : t ∈ Set.Ioi (0 : ℝ) := by simp only [Set.mem_Ioi]; linarith [ht.1]
            have h2 : t ∈ Set.Ioi T := ht.1
            rw [Set.indicator_of_mem ht, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
          · rw [Set.indicator_of_notMem ht]; exact bot_le
  have hc : ENNReal.ofReal (Real.exp μ) * ENNReal.ofReal (Real.exp (-μ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  have hT2 : Tendsto (fun T : ℝ => ENNReal.ofReal (Real.exp μ) *
      ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Ioi T).indicator f t) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.exp μ)) htail (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT2
    (Filter.Eventually.of_forall fun T => bot_le) ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with T hT
  calc f T = ENNReal.ofReal (Real.exp μ) * (ENNReal.ofReal (Real.exp (-μ)) * f T) := by
        rw [← mul_assoc, hc, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl (hlow T hT)

end HarrisContact.MeanSize

open HarrisContact.MeanSize


theorem solution {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsub : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k / μ < k / (2 * (d : ℝ) - 1)) :
    ∀ ξ : HarrisContact.Extinction.Config d, Tendsto (fun t : ℝ => HarrisContact.Extinction.meanSize μ lam t ξ) atTop (𝓝 0) := by
  exact remark_7_12_core hd μ lam hμ h0 hlam hsub
