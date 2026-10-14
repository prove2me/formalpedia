-- Prove2me | solution 1 for HarrisContact.MeanSize.eq_7_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:11:35.368923+00:00
-- url     : https://prove2.me/submissions/b825a8f3-4880-4c2e-bb7a-b73b28f1fcd4

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

end HarrisContact.MeanSize

open HarrisContact.MeanSize


theorem solution {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) (x y : HarrisContact.Extinction.Site d) (hxy : y ∈ HarrisContact.Extinction.nbrs x)
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
  exact eq_7_7_core hd l hl x y hxy t ht
