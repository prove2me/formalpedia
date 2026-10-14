-- Prove2me | solution 1 for HarrisContact.Extinction.eq_7_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:10:51.908979+00:00
-- url     : https://prove2.me/submissions/d0074dbc-55a6-4897-b4eb-b4a50df0bc0e

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal


namespace HarrisContact.Extinction

lemma hc_mem_nbrs_iff {d : ℕ} (x y : Site d) : y ∈ nbrs x ↔ ∑ i, |x i - y i| = 1 := by
  unfold nbrs
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Fintype.mem_piFinset]
    intro i
    have hle : |x i - y i| ≤ 1 := by
      rw [← h]
      exact Finset.single_le_sum (f := fun i => |x i - y i|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    have := abs_le.mp hle
    rw [Finset.mem_Icc]
    constructor <;> omega

lemma hc_nbrs_symm {d : ℕ} (x y : Site d) : y ∈ nbrs x ↔ x ∈ nbrs y := by
  rw [hc_mem_nbrs_iff, hc_mem_nbrs_iff]
  have : ∀ i, |x i - y i| = |y i - x i| := fun i => abs_sub_comm _ _
  simp only [this]

lemma hc_not_mem_nbrs_self {d : ℕ} (x : Site d) : x ∉ nbrs x := by
  rw [hc_mem_nbrs_iff]; simp

lemma hc_card_nbrs_le {d : ℕ} (x : Site d) : (nbrs x).card ≤ 2 * d := by
  classical
  have hsub : nbrs x ⊆ (Finset.univ : Finset (Fin d × Bool)).image
      (fun p => Function.update x p.1 (x p.1 + if p.2 then 1 else -1)) := by
    intro z hz
    rw [hc_mem_nbrs_iff] at hz
    rw [Finset.mem_image]
    have hex : ∃ i, x i ≠ z i := by
      by_contra hne
      push_neg at hne
      simp [hne] at hz
    obtain ⟨i, hi⟩ := hex
    have hsplit := Finset.add_sum_erase Finset.univ (fun j => |x j - z j|) (Finset.mem_univ i)
    rw [hz] at hsplit
    have hpos : 0 < |x i - z i| := abs_pos.mpr (sub_ne_zero.mpr hi)
    have hrest_nn : 0 ≤ ∑ j ∈ Finset.univ.erase i, |x j - z j| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hi1 : |x i - z i| = 1 := by omega
    have hrest : ∑ j ∈ Finset.univ.erase i, |x j - z j| = 0 := by omega
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)] at hrest
    refine ⟨(i, decide (z i = x i + 1)), Finset.mem_univ _, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      rcases (abs_eq (zero_le_one)).mp hi1 with h | h
      · have : z j ≠ x j + 1 := by omega
        simp [this]; omega
      · have : z j = x j + 1 := by omega
        simp [this]
    · rw [Function.update_of_ne hj]
      have := hrest j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
      rw [abs_eq_zero, sub_eq_zero] at this
      exact this
  calc (nbrs x).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [Finset.card_univ]; ring

lemma hc_occ_le {d : ℕ} (ξ : Config d) (x : Site d) : occ ξ x ≤ 2 * d :=
  (Finset.card_le_card Finset.inter_subset_right).trans (hc_card_nbrs_le x)

/-- ordered adjacent pairs inside ξ -/
noncomputable def hcPC {d : ℕ} (ξ : Config d) : ℕ := ∑ x ∈ ξ, occ ξ x

lemma hc_occ_insert_self {d : ℕ} (ξ : Config d) (x : Site d) : occ (insert x ξ) x = occ ξ x := by
  unfold occ; rw [Finset.insert_inter_of_notMem (hc_not_mem_nbrs_self x)]

lemma hc_occ_insert_other {d : ℕ} (ξ : Config d) (x y : Site d) (hx : x ∉ ξ) :
    occ (insert x ξ) y = occ ξ y + if x ∈ nbrs y then 1 else 0 := by
  unfold occ
  split_ifs with h
  · rw [Finset.insert_inter_of_mem h,
      Finset.card_insert_of_notMem (fun h' => hx (Finset.mem_inter.mp h').1)]
  · rw [Finset.insert_inter_of_notMem h]; simp

lemma hc_occ_eq_sum {d : ℕ} (ξ : Config d) (x : Site d) :
    occ ξ x = ∑ y ∈ ξ, if x ∈ nbrs y then 1 else 0 := by
  classical
  rw [← Finset.card_filter]
  unfold occ
  congr 1
  ext y; simp [Finset.mem_filter, Finset.mem_inter, hc_nbrs_symm x y]

lemma hc_pc_insert {d : ℕ} (ξ : Config d) (x : Site d) (hx : x ∉ ξ) :
    hcPC (insert x ξ) = hcPC ξ + 2 * occ ξ x := by
  unfold hcPC
  rw [Finset.sum_insert hx, hc_occ_insert_self]
  rw [Finset.sum_congr rfl (fun y _ => hc_occ_insert_other ξ x y hx), Finset.sum_add_distrib]
  rw [← hc_occ_eq_sum]; ring

lemma hc_occ_erase_self {d : ℕ} (ξ : Config d) (x : Site d) : occ (ξ.erase x) x = occ ξ x := by
  unfold occ
  congr 1
  ext y
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h1⟩, h2⟩
    rintro rfl; exact hc_not_mem_nbrs_self _ h2

lemma hc_pc_erase {d : ℕ} (ξ : Config d) (x : Site d) (hx : x ∈ ξ) :
    hcPC ξ = hcPC (ξ.erase x) + 2 * occ ξ x := by
  have h := hc_pc_insert (ξ.erase x) x (Finset.notMem_erase x ξ)
  rw [Finset.insert_erase hx, hc_occ_erase_self] at h
  exact h

lemma hc_bdry_occ_sum {d : ℕ} (ξ : Config d) :
    ∑ x ∈ bdry ξ, occ ξ x + hcPC ξ ≤ 2 * d * ξ.card := by
  classical
  have h1 : ∑ x ∈ bdry ξ, occ ξ x = ∑ y ∈ ξ, ((bdry ξ).filter (fun x => x ∈ nbrs y)).card := by
    simp only [Finset.card_filter]
    simp only [hc_occ_eq_sum]
    exact Finset.sum_comm
  rw [h1]; unfold hcPC occ
  rw [← Finset.sum_add_distrib]
  calc _ ≤ ∑ y ∈ ξ, 2 * d := Finset.sum_le_sum (fun y hy => ?_)
    _ = _ := by simp [mul_comm]
  rw [← Finset.card_union_of_disjoint]
  · refine (Finset.card_le_card ?_).trans (hc_card_nbrs_le y)
    intro z hz; rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact (Finset.mem_inter.mp h).2
  · rw [Finset.disjoint_left]; intro z hz hz'
    have := (Finset.mem_filter.mp hz).1
    unfold bdry at this; exact (Finset.mem_sdiff.mp this).2 (Finset.mem_inter.mp hz').1

lemma hc_occ_pos {d : ℕ} (ξ : Config d) (x : Site d) (hx : x ∈ bdry ξ) : 1 ≤ occ ξ x := by
  unfold bdry at hx
  obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hx).1
  unfold occ
  exact Finset.card_pos.mpr ⟨y, Finset.mem_inter.mpr ⟨hy, (hc_nbrs_symm y x).mp hxy⟩⟩

lemma hc_card_bdry {d : ℕ} (ξ : Config d) : (bdry ξ).card ≤ 2 * d * ξ.card := by
  unfold bdry
  calc _ ≤ (ξ.biUnion nbrs).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ ∑ y ∈ ξ, (nbrs y).card := Finset.card_biUnion_le
    _ ≤ ∑ y ∈ ξ, 2 * d := Finset.sum_le_sum (fun y _ => hc_card_nbrs_le y)
    _ = _ := by simp [mul_comm]

lemma hc_pc_le {d : ℕ} (ξ : Config d) : hcPC ξ ≤ 2 * d * ξ.card := by
  have := hc_bdry_occ_sum ξ; omega

lemma hc_sum_rate_mul {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) (f : Config d → ℝ) :
    ∑ ζ ∈ succ ξ, rate μ lam ξ ζ * f ζ =
      μ * ∑ x ∈ ξ, f (ξ.erase x) + ∑ x ∈ bdry ξ, lam (occ ξ x) * f (insert x ξ) := by
  classical
  unfold rate
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, ite_mul, zero_mul]
  congr 1
  · rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.sum_ite_eq']
    rw [if_pos (by unfold succ; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.sum_ite_eq']
    rw [if_pos (by unfold succ; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))]

lemma hc_sum_rate {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) :
    ∑ ζ ∈ succ ξ, rate μ lam ξ ζ = exitRate μ lam ξ := by
  have := hc_sum_rate_mul μ lam ξ (fun _ => 1)
  simp only [mul_one] at this
  rw [this]; unfold exitRate; simp

lemma hc_rate_nonneg {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ η : Config d) : 0 ≤ rate μ lam ξ η := by
  unfold rate
  apply add_nonneg
  · exact Finset.sum_nonneg (fun x _ => by split_ifs <;> linarith)
  · exact Finset.sum_nonneg (fun x _ => by
      split_ifs
      · exact hlam _ (hc_occ_le ξ x)
      · exact le_refl _)

noncomputable def hcV {d : ℕ} (c : ℝ) (ξ : Config d) : ℝ := (ξ.card : ℝ) - c / 2 * (hcPC ξ : ℝ)

lemma hcV_erase {d : ℕ} (c : ℝ) (ξ : Config d) (x : Site d) (hx : x ∈ ξ) :
    hcV c (ξ.erase x) = hcV c ξ - 1 + c * occ ξ x := by
  unfold hcV
  have h1 := hc_pc_erase ξ x hx
  have h2 := Finset.card_erase_add_one hx
  have h1' : (hcPC ξ : ℝ) = hcPC (ξ.erase x) + 2 * occ ξ x := by exact_mod_cast h1
  have h2' : ((ξ.erase x).card : ℝ) + 1 = ξ.card := by exact_mod_cast h2
  rw [h1', ← h2']; ring

lemma hcV_insert {d : ℕ} (c : ℝ) (ξ : Config d) (x : Site d) (hx : x ∉ ξ) :
    hcV c (insert x ξ) = hcV c ξ + 1 - c * occ ξ x := by
  unfold hcV
  rw [hc_pc_insert ξ x hx, Finset.card_insert_of_notMem hx]; push_cast; ring

lemma hcV_le {d : ℕ} (c : ℝ) (hc0 : 0 ≤ c) (ξ : Config d) : hcV c ξ ≤ ξ.card := by
  unfold hcV
  have : (0:ℝ) ≤ c / 2 * (hcPC ξ : ℝ) := by positivity
  linarith

lemma hcV_ge {d : ℕ} (c : ℝ) (hc0 : 0 ≤ c) (hc1 : 2 * d * c ≤ 1) (ξ : Config d) :
    (ξ.card : ℝ) / 2 ≤ hcV c ξ := by
  unfold hcV
  have h : (hcPC ξ : ℝ) ≤ 2 * d * ξ.card := by exact_mod_cast hc_pc_le ξ
  have hcard : (0:ℝ) ≤ ξ.card := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hc0]

lemma hc_drift {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (lb c : ℝ) (hlb : 0 ≤ lb) (hc0 : 0 ≤ c) (hc1 : 2 * d * c ≤ 1) (hcμ : c * μ = lb * (1 - c))
    (hcmp : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k ≤ k * lb) (ξ : Config d) :
    ∑ ζ ∈ succ ξ, rate μ lam ξ ζ * hcV c ζ ≤
      exitRate μ lam ξ * hcV c ξ - (μ - 2 * d * lb * (1 - c)) * ξ.card := by
  rw [hc_sum_rate_mul]
  have hb : ∀ x ∈ bdry ξ, x ∉ ξ := fun x hx => (Finset.mem_sdiff.mp hx).2
  have hs1 : ∑ x ∈ ξ, hcV c (ξ.erase x) = ∑ x ∈ ξ, (hcV c ξ - 1 + c * occ ξ x) :=
    Finset.sum_congr rfl (fun x hx => hcV_erase c ξ x hx)
  have hs2 : ∑ x ∈ bdry ξ, lam (occ ξ x) * hcV c (insert x ξ) =
      ∑ x ∈ bdry ξ, lam (occ ξ x) * (hcV c ξ + 1 - c * occ ξ x) :=
    Finset.sum_congr rfl (fun x hx => by rw [hcV_insert c ξ x (hb x hx)])
  rw [hs1, hs2]
  unfold exitRate
  have hterm : ∀ x ∈ bdry ξ, lam (occ ξ x) * (hcV c ξ + 1 - c * occ ξ x) ≤
      lam (occ ξ x) * hcV c ξ + lb * (1 - c) * occ ξ x := by
    intro x hx
    have ho1 : (1:ℝ) ≤ occ ξ x := by exact_mod_cast hc_occ_pos ξ x hx
    have ho2 : (occ ξ x : ℝ) ≤ 2 * d := by exact_mod_cast hc_occ_le ξ x
    have hl := hcmp (occ ξ x) (hc_occ_pos ξ x hx) (hc_occ_le ξ x)
    have h1co : 0 ≤ 1 - c * occ ξ x := by nlinarith
    have : lam (occ ξ x) * (1 - c * occ ξ x) ≤ lb * (1 - c) * occ ξ x := by
      calc lam (occ ξ x) * (1 - c * occ ξ x) ≤ (occ ξ x * lb) * (1 - c * occ ξ x) :=
            mul_le_mul_of_nonneg_right hl h1co
        _ ≤ lb * (1 - c) * occ ξ x := by
          have := mul_nonneg (mul_nonneg (mul_nonneg hlb hc0) (sub_nonneg.mpr ho1))
            (by linarith : (0:ℝ) ≤ occ ξ x)
          nlinarith
    nlinarith
  have hsumb := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at hsumb
  have hocc := hc_bdry_occ_sum ξ
  have hocc' : (∑ x ∈ bdry ξ, (occ ξ x : ℝ)) + hcPC ξ ≤ 2 * d * ξ.card := by exact_mod_cast hocc
  have hpc : (hcPC ξ : ℝ) = ∑ x ∈ ξ, (occ ξ x : ℝ) := by unfold hcPC; push_cast; rfl
  have he : ∑ x ∈ ξ, (hcV c ξ - 1 + c * occ ξ x) = ξ.card * hcV c ξ - ξ.card + c * hcPC ξ := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hpc]; simp
  rw [he]
  have hlbc : 0 ≤ lb * (1 - c) := by rw [← hcμ]; exact mul_nonneg hc0 hμ
  have := mul_le_mul_of_nonneg_left hocc' hlbc
  have hk : μ * (c * hcPC ξ) = lb * (1 - c) * hcPC ξ := by rw [← hcμ]; ring
  have hk2 : μ * (↑ξ.card * hcV c ξ - ↑ξ.card + c * ↑(hcPC ξ)) =
      μ * ↑ξ.card * hcV c ξ - μ * ↑ξ.card + lb * (1 - c) * hcPC ξ := by rw [← hk]; ring
  rw [hk2]
  nlinarith

lemma hc_key_eq (q t : ℝ) (ht : 0 ≤ t) (φ φ' : ℝ → ℝ) (hφ : ∀ r, HasDerivAt φ (φ' r) r)
    (hφ'c : Continuous φ')
    (hnn : ∀ s ∈ Set.Icc 0 t, 0 ≤ Real.exp (-(q * s)) * (q * φ (t - s) + φ' (t - s))) :
    ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(q * s)) * (q * φ (t - s) + φ' (t - s))) =
      ENNReal.ofReal (φ t - Real.exp (-(q * t)) * φ 0) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr (fun r => (hφ r).continuousAt)
  have hcont : Continuous (fun s => Real.exp (-(q * s)) * (q * φ (t - s) + φ' (t - s))) := by
    fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => -(Real.exp (-(q * s)) * φ (t - s)))]
    · simp; ring
    · intro s _
      have h0 : HasDerivAt (fun s => -(q * s)) (-q) s := by
        exact (hasDerivAt_const_mul q).fun_neg
      have h1 : HasDerivAt (fun s => Real.exp (-(q * s))) (Real.exp (-(q * s)) * (-q)) s :=
        h0.exp
      have h3 : HasDerivAt (fun s => t - s) (-1) s := by
        simpa using (hasDerivAt_id s).const_sub t
      have h2 : HasDerivAt (fun s => φ (t - s)) (φ' (t - s) * (-1)) s :=
        (hφ (t - s)).comp s h3
      exact ((h1.mul h2).fun_neg).congr_deriv (by ring)
    · exact hcont.intervalIntegrable _ _
  · exact hcont.integrableOn_Icc
  · exact (ae_restrict_mem measurableSet_Icc).mono (fun s hs => hnn s hs)

lemma hc_key_le (q t : ℝ) (ht : 0 ≤ t) (φ φ' : ℝ → ℝ) (hφ : ∀ r, HasDerivAt φ (φ' r) r)
    (hφ'c : Continuous φ')
    (hnn : ∀ s ∈ Set.Icc 0 t, 0 ≤ Real.exp (-(q * s)) * (q * φ (t - s) + φ' (t - s)))
    (f : ℝ → ℝ≥0∞)
    (hf : ∀ s ∈ Set.Icc 0 t,
      f s ≤ ENNReal.ofReal (Real.exp (-(q * s)) * (q * φ (t - s) + φ' (t - s)))) :
    ∫⁻ s in Set.Icc 0 t, f s ≤ ENNReal.ofReal (φ t - Real.exp (-(q * t)) * φ 0) := by
  rw [← hc_key_eq q t ht φ φ' hφ hφ'c hnn]
  exact setLIntegral_mono' measurableSet_Icc hf

lemma hc_conv {d : ℕ} (e : ℝ) (he : 0 ≤ e) (S : Finset (Config d)) (w h : Config d → ℝ)
    (hw : ∀ ζ, 0 ≤ w ζ) (hh : ∀ ζ, 0 ≤ h ζ) :
    ENNReal.ofReal e * ∑ ζ ∈ S, ENNReal.ofReal (w ζ) * ENNReal.ofReal (h ζ) =
      ENNReal.ofReal (e * ∑ ζ ∈ S, w ζ * h ζ) := by
  rw [ENNReal.ofReal_mul he, ENNReal.ofReal_sum_of_nonneg
    (fun ζ _ => mul_nonneg (hw ζ) (hh ζ))]
  congr 1
  exact Finset.sum_congr rfl (fun ζ _ => (ENNReal.ofReal_mul (hw ζ)).symm)

lemma hc_exitRate_nonneg {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) : 0 ≤ exitRate μ lam ξ := by
  rw [← hc_sum_rate]
  exact Finset.sum_nonneg (fun ζ _ => hc_rate_nonneg μ lam hμ hlam ξ ζ)

/-- generic supersolution bound -/
lemma hc_super {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) (t : ℝ) (ht : 0 ≤ t)
    (h : ℝ → Config d → ℝ) (hh : ∀ r ζ, 0 ≤ h r ζ) (φ φ' : ℝ → ℝ)
    (hφ : ∀ r, HasDerivAt φ (φ' r) r) (hφ'c : Continuous φ')
    (hpt : ∀ r, 0 ≤ r → ∑ ζ ∈ succ ξ, rate μ lam ξ ζ * h r ζ ≤
      exitRate μ lam ξ * φ r + φ' r) :
    ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * ENNReal.ofReal (h (t - s) ζ) ≤
      ENNReal.ofReal (φ t - Real.exp (-(exitRate μ lam ξ * t)) * φ 0) := by
  have hrn := hc_rate_nonneg μ lam hμ hlam ξ
  apply hc_key_le _ t ht φ φ' hφ hφ'c
  · intro s hs
    apply mul_nonneg (Real.exp_pos _).le
    refine le_trans ?_ (hpt (t - s) (by linarith [hs.2]))
    exact Finset.sum_nonneg (fun ζ _ => mul_nonneg (hrn ζ) (hh _ ζ))
  · intro s hs
    rw [hc_conv _ (Real.exp_pos _).le _ _ _ hrn (hh (t - s))]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left (hpt (t - s) (by linarith [hs.2])) (Real.exp_pos _).le

lemma hc_transN_succ {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (n : ℕ) (t : ℝ) (ξ η : Config d) :
    transN μ lam (n + 1) t ξ η = transN μ lam 0 t ξ η +
      ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * transN μ lam n (t - s) ζ η := by
  conv_lhs => rw [transN]

lemma hc_exitRate_empty {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) : exitRate μ lam (∅ : Config d) = 0 := by
  unfold exitRate bdry; simp

lemma hc_const {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * 1 =
      ENNReal.ofReal (1 - Real.exp (-(exitRate μ lam ξ * t))) := by
  have hrn := hc_rate_nonneg μ lam hμ hlam ξ
  have hq := hc_exitRate_nonneg μ lam hμ hlam ξ
  have := hc_key_eq (exitRate μ lam ξ) t ht (fun _ => 1) (fun _ => 0)
    (fun r => hasDerivAt_const r 1) continuous_const
    (fun s _ => by simp only [mul_one, add_zero]; positivity)
  simp only [mul_one, add_zero] at this
  rw [← this]
  apply lintegral_congr; intro s
  simp only [mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ζ _ => hrn ζ), hc_sum_rate,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]

lemma hc_main_ind {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (B : ℕ → ℝ → Config d → ℝ≥0∞)
    (hB0 : ∀ t, 0 ≤ t → ∀ ξ : Config d, ξ ≠ ∅ → 1 ≤ B 0 t ξ)
    (hBm : ∀ n t (ξ : Config d), Measurable (fun s =>
      ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * B n (t - s) ζ))
    (hBs : ∀ n t, 0 ≤ t → ∀ ξ : Config d, ξ ≠ ∅ →
      (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * B n (t - s) ζ) +
          ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) ≤ B (n + 1) t ξ) :
    ∀ n t, 0 ≤ t → ∀ ξ : Config d, 1 ≤ transN μ lam n t ξ ∅ + B n t ξ := by
  have hE : ∀ t, transN μ lam 0 t (∅ : Config d) ∅ = 1 := by
    intro t; simp [transN, hc_exitRate_empty]
  have hEn : ∀ n t, 1 ≤ transN μ lam n t (∅ : Config d) ∅ := by
    intro n t; cases n with
    | zero => rw [hE]
    | succ n => rw [hc_transN_succ, hE]; exact le_self_add
  intro n
  induction n with
  | zero =>
    intro t ht ξ
    by_cases hξ : ξ = ∅
    · subst hξ; exact (hEn 0 t).trans le_self_add
    · exact (hB0 t ht ξ hξ).trans le_add_self
  | succ n ih =>
    intro t ht ξ
    by_cases hξ : ξ = ∅
    · subst hξ; exact (hEn _ t).trans le_self_add
    · rw [hc_transN_succ]
      have h0 : transN μ lam 0 t ξ ∅ = 0 := by simp [transN, hξ]
      rw [h0, zero_add]
      have hq0 := hc_exitRate_nonneg μ lam hμ hlam ξ
      have he1 : Real.exp (-(exitRate μ lam ξ * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      have hsplit : (1 : ℝ≥0∞) = ENNReal.ofReal (1 - Real.exp (-(exitRate μ lam ξ * t))) +
          ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) := by
        rw [← ENNReal.ofReal_add (sub_nonneg.2 he1) (Real.exp_pos _).le]; simp
      rw [hsplit, ← hc_const μ lam hμ hlam ξ t ht]
      refine le_trans ?_ (add_le_add le_rfl (hBs n t ht ξ hξ))
      rw [← add_assoc]
      refine add_le_add ?_ le_rfl
      rw [← lintegral_add_right' _ (hBm n t ξ).aemeasurable]
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      rw [← mul_add, ← Finset.sum_add_distrib]
      gcongr with ζ hζ
      rw [← mul_add]
      gcongr
      exact ih (t - s) (by linarith [hs.2]) ζ

lemma hc_sum_lam_le {d : ℕ} (lam : ℕ → ℝ) (Λ : ℝ) (hΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ)
    (hΛ0 : 0 ≤ Λ) (ξ : Config d) :
    ∑ x ∈ bdry ξ, lam (occ ξ x) ≤ 2 * d * Λ * ξ.card := by
  calc ∑ x ∈ bdry ξ, lam (occ ξ x) ≤ ∑ x ∈ bdry ξ, Λ :=
        Finset.sum_le_sum (fun x _ => hΛ _ (hc_occ_le ξ x))
    _ = (bdry ξ).card * Λ := by simp
    _ ≤ (2 * d * ξ.card) * Λ := by
        apply mul_le_mul_of_nonneg_right _ hΛ0
        exact_mod_cast hc_card_bdry ξ
    _ = _ := by ring

lemma hc_exitRate_le {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (Λ : ℝ)
    (hΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ) (hΛ0 : 0 ≤ Λ) (ξ : Config d) :
    exitRate μ lam ξ ≤ (μ + 2 * d * Λ) * ξ.card := by
  unfold exitRate
  have := hc_sum_lam_le lam Λ hΛ hΛ0 ξ
  nlinarith

lemma hc_size_drift {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (Λ : ℝ)
    (hΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ) (hΛ0 : 0 ≤ Λ) (ξ : Config d) :
    ∑ ζ ∈ succ ξ, rate μ lam ξ ζ * ((ζ.card : ℝ) + 1) ≤
      (exitRate μ lam ξ + 2 * d * Λ) * ((ξ.card : ℝ) + 1) := by
  rw [hc_sum_rate_mul]
  have hb : ∀ x ∈ bdry ξ, x ∉ ξ := fun x hx => (Finset.mem_sdiff.mp hx).2
  have hs1 : ∑ x ∈ ξ, (((ξ.erase x).card : ℝ) + 1) = ∑ x ∈ ξ, (ξ.card : ℝ) :=
    Finset.sum_congr rfl (fun x hx => by exact_mod_cast Finset.card_erase_add_one hx)
  have hs2 : ∑ x ∈ bdry ξ, lam (occ ξ x) * (((insert x ξ).card : ℝ) + 1) =
      ∑ x ∈ bdry ξ, lam (occ ξ x) * ((ξ.card : ℝ) + 2) :=
    Finset.sum_congr rfl (fun x hx => by
      rw [Finset.card_insert_of_notMem (hb x hx)]; push_cast; ring)
  rw [hs1, hs2, ← Finset.sum_mul]
  unfold exitRate
  have := hc_sum_lam_le lam Λ hΛ hΛ0 ξ
  have hc : (0:ℝ) ≤ ξ.card := by positivity
  simp only [Finset.sum_const, nsmul_eq_mul]
  nlinarith [mul_nonneg hμ hc, mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * d) hΛ0) hc]

lemma hc_meas {d : ℕ} (q t : ℝ) (S : Finset (Config d)) (w : Config d → ℝ≥0∞)
    (g : ℝ → Config d → ℝ≥0∞) (hg : ∀ ζ, Measurable (fun r => g r ζ)) :
    Measurable (fun s => ENNReal.ofReal (Real.exp (-(q * s))) * ∑ ζ ∈ S, w ζ * g (t - s) ζ) := by
  apply Measurable.mul
  · exact ENNReal.measurable_ofReal.comp (by fun_prop)
  · apply Finset.measurable_sum
    intro ζ _
    exact measurable_const.mul ((hg ζ).comp (measurable_const.sub measurable_id))

noncomputable def hcB {d : ℕ} (c γ c₁ Q : ℝ) (M : ℕ) (n : ℕ) (t : ℝ) (ξ : Config d) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.exp (-(γ * t)) * hcV c ξ) +
    min 1 (ENNReal.ofReal (Real.exp (c₁ * t) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1)) +
      ENNReal.ofReal (Real.exp (Q * t) / 2 ^ n))

lemma hcB_meas {d : ℕ} (c γ c₁ Q : ℝ) (M n : ℕ) (ζ : Config d) :
    Measurable (fun r => hcB c γ c₁ Q M n r ζ) := by
  unfold hcB
  have h1 : Measurable (fun r : ℝ => ENNReal.ofReal (2 * Real.exp (-(γ * r)) * hcV c ζ)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have h2 : Measurable (fun r : ℝ =>
      ENNReal.ofReal (Real.exp (c₁ * r) * ((ζ.card : ℝ) + 1) / ((M : ℝ) + 1))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have h3 : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (Q * r) / 2 ^ n)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  fun_prop

lemma hcB_step {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (lb c : ℝ) (hlb : 0 ≤ lb) (hc0 : 0 ≤ c) (hc1 : 2 * d * c ≤ 1) (hcμ : c * μ = lb * (1 - c))
    (hcmp : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k ≤ k * lb)
    (γ : ℝ) (hγ : γ = μ - 2 * d * lb * (1 - c)) (hγ0 : 0 ≤ γ)
    (Λ : ℝ) (hΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ) (hΛ0 : 0 ≤ Λ) (M : ℕ)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ξ : Config d) (hξ : ξ ≠ ∅) :
    (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          hcB c γ (2 * d * Λ) ((μ + 2 * d * Λ) * M) M n (t - s) ζ) +
      ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) ≤
      hcB c γ (2 * d * Λ) ((μ + 2 * d * Λ) * M) M (n + 1) t ξ := by
  have hrn := hc_rate_nonneg μ lam hμ hlam ξ
  have hq0 : 0 ≤ exitRate μ lam ξ := hc_exitRate_nonneg μ lam hμ hlam ξ
  have hcard : 1 ≤ (ξ.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hξ)
  have hqμ : μ ≤ exitRate μ lam ξ := by
    have : μ * ξ.card ≤ exitRate μ lam ξ := by
      unfold exitRate
      have : 0 ≤ ∑ x ∈ bdry ξ, lam (occ ξ x) :=
        Finset.sum_nonneg (fun x _ => hlam _ (hc_occ_le ξ x))
      linarith
    nlinarith
  have hγq : γ ≤ exitRate μ lam ξ := by
    have h1 : 0 ≤ lb * (1 - c) := by rw [← hcμ]; exact mul_nonneg hc0 hμ
    have : γ ≤ μ := by
      rw [hγ]
      have : 0 ≤ 2 * (d : ℝ) * lb * (1 - c) := by
        have : (0:ℝ) ≤ 2 * d := by positivity
        nlinarith
      linarith
    linarith
  have hV0 : ∀ ζ : Config d, 0 ≤ hcV c ζ := fun ζ => le_trans (by positivity) (hcV_ge c hc0 hc1 ζ)
  have hVξ : 1 / 2 ≤ hcV c ξ := le_trans (by linarith) (hcV_ge c hc0 hc1 ξ)
  have hexp_t : Real.exp (-(exitRate μ lam ξ * t)) ≤ Real.exp (-(γ * t)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  -- split the integrand
  have hsplit1 : ∀ s, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          hcB c γ (2 * d * Λ) ((μ + 2 * d * Λ) * M) M n (t - s) ζ =
      ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          ENNReal.ofReal (2 * Real.exp (-(γ * (t - s))) * hcV c ζ) +
      ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * (t - s)) * ((ζ.card : ℝ) + 1) /
            ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * (t - s)) / 2 ^ n)) := by
    intro s; unfold hcB
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun ζ _ => by rw [mul_add])
  rw [lintegral_congr hsplit1]
  rw [lintegral_add_left (hc_meas _ t _ _ (fun r ζ => ENNReal.ofReal (2 * Real.exp (-(γ * r)) * hcV c ζ))
    (fun ζ => ENNReal.measurable_ofReal.comp (by fun_prop)))]
  -- A part
  have hAint := hc_super μ lam hμ hlam ξ t ht (fun r ζ => 2 * Real.exp (-(γ * r)) * hcV c ζ)
    (fun r ζ => by have := hV0 ζ; positivity)
    (fun r => 2 * Real.exp (-(γ * r)) * hcV c ξ) (fun r => -γ * (2 * Real.exp (-(γ * r)) * hcV c ξ))
    (fun r => ((((hasDerivAt_const_mul γ).fun_neg.exp).const_mul 2).mul_const (hcV c ξ)).congr_deriv
      (by ring))
    (by fun_prop)
    (by
      intro r _
      have hd := hc_drift μ lam hμ hlam lb c hlb hc0 hc1 hcμ hcmp ξ
      have hVle := hcV_le c hc0 ξ
      have he : 0 < 2 * Real.exp (-(γ * r)) := by positivity
      have hrw : ∑ ζ ∈ succ ξ, rate μ lam ξ ζ * (2 * Real.exp (-(γ * r)) * hcV c ζ) =
          2 * Real.exp (-(γ * r)) * ∑ ζ ∈ succ ξ, rate μ lam ξ ζ * hcV c ζ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ζ _ => by ring)
      rw [hrw, ← hγ] at *
      have := mul_le_mul_of_nonneg_left hd he.le
      have h2 : 0 ≤ 2 * Real.exp (-(γ * r)) * (γ * (ξ.card - hcV c ξ)) :=
        mul_nonneg he.le (mul_nonneg hγ0 (by linarith))
      nlinarith)
  have h4 : (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          ENNReal.ofReal (2 * Real.exp (-(γ * (t - s))) * hcV c ζ)) +
      ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) ≤
      ENNReal.ofReal (2 * Real.exp (-(γ * t)) * hcV c ξ) := by
    have hAt : Real.exp (-(exitRate μ lam ξ * t)) ≤ 2 * Real.exp (-(γ * t)) * hcV c ξ := by
      have := Real.exp_pos (-(γ * t))
      nlinarith
    calc _ ≤ ENNReal.ofReal (2 * Real.exp (-(γ * t)) * hcV c ξ -
            Real.exp (-(exitRate μ lam ξ * t))) +
          ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) := by
          refine add_le_add (hAint.trans (ENNReal.ofReal_le_ofReal ?_)) le_rfl
          simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
          have := Real.exp_pos (-(exitRate μ lam ξ * t))
          nlinarith
      _ = _ := by
          rw [← ENNReal.ofReal_add (by linarith) (Real.exp_pos _).le, sub_add_cancel]
  -- the min part
  have hGMle1 : (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * (t - s)) * ((ζ.card : ℝ) + 1) /
            ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * (t - s)) / 2 ^ n))) ≤ 1 := by
    calc _ ≤ ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
          ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * 1 := by
          apply setLIntegral_mono' measurableSet_Icc
          intro s _
          gcongr with ζ hζ
          exact min_le_left _ _
      _ = _ := hc_const μ lam hμ hlam ξ t ht
      _ ≤ 1 := ENNReal.ofReal_le_one.mpr (by linarith [Real.exp_pos (-(exitRate μ lam ξ * t))])
  have hMint : (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * (t - s)) * ((ζ.card : ℝ) + 1) /
            ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * (t - s)) / 2 ^ n))) ≤
      min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * t) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1)) +
        ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * t) / 2 ^ (n + 1))) := by
    by_cases hM : M ≤ ξ.card
    · have hY1 : 1 ≤ Real.exp (2 * d * Λ * t) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1) := by
        rw [le_div_iff₀ (by positivity)]
        have : (1:ℝ) ≤ Real.exp (2 * d * Λ * t) := Real.one_le_exp (by positivity)
        have : (M : ℝ) ≤ ξ.card := by exact_mod_cast hM
        nlinarith
      rw [min_eq_left]
      · exact hGMle1
      · exact le_trans (ENNReal.one_le_ofReal.mpr hY1) le_self_add
    · push_neg at hM
      have hqQ : exitRate μ lam ξ ≤ (μ + 2 * d * Λ) * M := by
        have := hc_exitRate_le μ lam Λ hΛ hΛ0 ξ
        have h2 : (ξ.card : ℝ) ≤ M := by exact_mod_cast hM.le
        have : 0 ≤ μ + 2 * d * Λ := by positivity
        nlinarith
      apply le_min hGMle1
      have hY := hc_super μ lam hμ hlam ξ t ht
        (fun r ζ => Real.exp (2 * d * Λ * r) * ((ζ.card : ℝ) + 1) / ((M : ℝ) + 1))
        (fun r ζ => by positivity)
        (fun r => Real.exp (2 * d * Λ * r) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1))
        (fun r => 2 * d * Λ * (Real.exp (2 * d * Λ * r) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1)))
        (fun r => ((((hasDerivAt_const_mul (2 * d * Λ)).exp).mul_const _).div_const _).congr_deriv
          (by ring))
        (by fun_prop)
        (by
          intro r _
          have hsd := hc_size_drift μ lam hμ Λ hΛ hΛ0 ξ
          have hK : 0 < Real.exp (2 * d * Λ * r) / ((M : ℝ) + 1) := by positivity
          have hrw : ∑ ζ ∈ succ ξ, rate μ lam ξ ζ *
              (Real.exp (2 * d * Λ * r) * ((ζ.card : ℝ) + 1) / ((M : ℝ) + 1)) =
              Real.exp (2 * d * Λ * r) / ((M : ℝ) + 1) *
                ∑ ζ ∈ succ ξ, rate μ lam ξ ζ * ((ζ.card : ℝ) + 1) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ζ _ => by ring)
          rw [hrw]
          have := mul_le_mul_of_nonneg_left hsd hK.le
          calc _ ≤ _ := this
            _ = _ := by ring)
      have hZ := hc_super μ lam hμ hlam ξ t ht
        (fun r ζ => Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ n)
        (fun r ζ => by positivity)
        (fun r => Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ (n + 1))
        (fun r => (μ + 2 * d * Λ) * M * (Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ (n + 1)))
        (fun r => (((hasDerivAt_const_mul ((μ + 2 * d * Λ) * M)).exp).div_const _).congr_deriv
          (by ring))
        (by fun_prop)
        (by
          intro r _
          rw [← Finset.sum_mul, hc_sum_rate]
          have hE : 0 < Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ (n + 1) := by positivity
          have : Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ n =
              2 * (Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ (n + 1)) := by
            rw [pow_succ]; field_simp
          rw [this]
          nlinarith)
      calc _ ≤ ∫⁻ s in Set.Icc 0 t,
            (ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
              ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
                ENNReal.ofReal (Real.exp (2 * d * Λ * (t - s)) * ((ζ.card : ℝ) + 1) /
                  ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
              ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
                ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * (t - s)) / 2 ^ n)) := by
            apply setLIntegral_mono' measurableSet_Icc
            intro s _
            rw [← mul_add, ← Finset.sum_add_distrib]
            gcongr with ζ hζ
            rw [← mul_add]
            gcongr
            exact min_le_right _ _
        _ = _ := lintegral_add_left (hc_meas _ t _ _ (fun r ζ => ENNReal.ofReal
              (Real.exp (2 * d * Λ * r) * ((ζ.card : ℝ) + 1) / ((M : ℝ) + 1)))
              (fun ζ => ENNReal.measurable_ofReal.comp (by fun_prop))) _
        _ ≤ _ := by
            refine add_le_add (hY.trans (ENNReal.ofReal_le_ofReal ?_))
              (hZ.trans (ENNReal.ofReal_le_ofReal ?_))
            · have : 0 ≤ Real.exp (-(exitRate μ lam ξ * t)) *
                  (Real.exp (2 * d * Λ * 0) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1)) := by
                positivity
              linarith
            · have : 0 ≤ Real.exp (-(exitRate μ lam ξ * t)) *
                  (Real.exp ((μ + 2 * d * Λ) * M * 0) / 2 ^ (n + 1)) := by positivity
              linarith
  unfold hcB
  calc _ = ((∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          ENNReal.ofReal (2 * Real.exp (-(γ * (t - s))) * hcV c ζ)) +
      ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t)))) +
      (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * (t - s)) * ((ζ.card : ℝ) + 1) /
            ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * (t - s)) / 2 ^ n))) := by
        rw [add_right_comm]
    _ ≤ _ := add_le_add h4 hMint

lemma hc_surv_le {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (lb c : ℝ) (hlb : 0 ≤ lb) (hc0 : 0 ≤ c) (hc1 : 2 * d * c ≤ 1) (hcμ : c * μ = lb * (1 - c))
    (hcmp : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k ≤ k * lb)
    (γ : ℝ) (hγ : γ = μ - 2 * d * lb * (1 - c)) (hγ0 : 0 ≤ γ)
    (Λ : ℝ) (hΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ) (hΛ0 : 0 ≤ Λ)
    (t : ℝ) (ht : 0 ≤ t) (ξ : Config d) :
    surv μ lam t ξ ≤ ENNReal.ofReal (2 * Real.exp (-(γ * t)) * hcV c ξ) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0:ℝ) < ε := hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * Real.exp (2 * d * Λ * t) * ((ξ.card : ℝ) + 1) / ε)
  have hQ0 : 0 ≤ (μ + 2 * d * Λ) * M := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (by positivity : (0:ℝ) < ε / (2 * Real.exp ((μ + 2 * d * Λ) * M * t)))
    (by norm_num : (1/2 : ℝ) < 1)
  have hind := hc_main_ind μ lam hμ hlam (hcB c γ (2 * d * Λ) ((μ + 2 * d * Λ) * M) M)
    (by
      intro t' ht' ξ' _
      unfold hcB
      have h1 : 1 ≤ Real.exp ((μ + 2 * d * Λ) * M * t') / 2 ^ 0 := by
        rw [pow_zero, div_one]; exact Real.one_le_exp (by positivity)
      rw [min_eq_left (le_trans (ENNReal.one_le_ofReal.mpr h1) le_add_self)]
      exact le_add_self)
    (fun n t ξ => hc_meas _ t _ _ _ (fun ζ => hcB_meas c γ _ _ M n ζ))
    (fun n t ht ξ hξ => hcB_step μ lam hμ hlam lb c hlb hc0 hc1 hcμ hcmp γ hγ hγ0 Λ hΛ hΛ0 M
      n t ht ξ hξ) n t ht ξ
  have htr : transN μ lam n t ξ ∅ ≤ trans μ lam t ξ ∅ :=
    le_iSup (fun n => transN μ lam n t ξ ∅) n
  have hY : Real.exp (2 * d * Λ * t) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε'] at hM
    nlinarith
  have hZ : Real.exp ((μ + 2 * d * Λ) * M * t) / 2 ^ n ≤ ε / 2 := by
    have hE := Real.exp_pos ((μ + 2 * d * Λ) * M * t)
    rw [lt_div_iff₀ (by positivity)] at hn
    have : Real.exp ((μ + 2 * d * Λ) * M * t) / 2 ^ n =
        (1/2) ^ n * Real.exp ((μ + 2 * d * Λ) * M * t) := by
      rw [one_div_pow]; field_simp
    rw [this]; nlinarith
  unfold surv
  rw [tsub_le_iff_left]
  refine hind.trans ?_
  unfold hcB
  calc _ ≤ trans μ lam t ξ ∅ + (ENNReal.ofReal (2 * Real.exp (-(γ * t)) * hcV c ξ) +
        (ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2))) := by
        refine add_le_add htr (add_le_add le_rfl ((min_le_right _ _).trans ?_))
        exact add_le_add (ENNReal.ofReal_le_ofReal hY) (ENNReal.ofReal_le_ofReal hZ)
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
          ENNReal.ofReal_coe_nnreal]

theorem theorem_7_1_core {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsub : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → (2 * (d : ℝ) - 1) * lam k < k * μ) :
    ∀ ξ : Config d, survInf μ lam ξ = 0 := by
  intro ξ
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hμpos : 0 < μ := by
    have h1 := hsub 1 le_rfl (by omega)
    have h2 := hlam 1 (by omega)
    push_cast at h1
    nlinarith
  obtain ⟨k₀, hk₀mem, hk₀max⟩ := Finset.exists_max_image (Finset.Icc 1 (2 * d))
    (fun k : ℕ => lam k / k) ⟨1, by simp; omega⟩
  have hk₀ := Finset.mem_Icc.mp hk₀mem
  have hk₀pos : (0:ℝ) < k₀ := by exact_mod_cast (by omega : 0 < k₀)
  set lb := lam k₀ / k₀ with hlbdef
  have hlb : 0 ≤ lb := div_nonneg (hlam k₀ hk₀.2) (Nat.cast_nonneg _)
  have hlbμ : (2 * (d:ℝ) - 1) * lb < μ := by
    have := hsub k₀ hk₀.1 hk₀.2
    rw [hlbdef, mul_div_assoc', div_lt_iff₀ hk₀pos]; linarith
  have hcmp : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k ≤ k * lb := by
    intro k hk1 hk2
    have := hk₀max k (Finset.mem_Icc.mpr ⟨hk1, hk2⟩)
    have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    rw [div_le_iff₀ hkpos] at this; linarith
  have hpos : 0 < μ + lb := by linarith
  set c := lb / (μ + lb) with hcdef
  have hc0 : 0 ≤ c := div_nonneg hlb hpos.le
  have hc1 : 2 * d * c ≤ 1 := by
    rw [hcdef, mul_div_assoc', div_le_one hpos]; nlinarith
  have h1c : 1 - c = μ / (μ + lb) := by rw [hcdef]; field_simp; ring
  have hcμ : c * μ = lb * (1 - c) := by rw [h1c, hcdef]; field_simp
  set γ := μ - 2 * d * lb * (1 - c) with hγ
  have hγpos : 0 < γ := by
    have : 2 * d * lb * (1 - c) < μ := by
      rw [h1c, mul_div_assoc', div_lt_iff₀ hpos]; nlinarith
    linarith
  set Λ := ∑ k ∈ Finset.range (2 * d + 1), lam k with hΛdef
  have hΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ := by
    intro k hk
    exact Finset.single_le_sum (f := lam) (fun i hi => hlam i (by simp at hi; omega))
      (by simp; omega)
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg (fun i hi => hlam i (by simp at hi; omega))
  have hsl := hc_surv_le μ lam hμ hlam lb c hlb hc0 hc1 hcμ hcmp γ hγ hγpos.le Λ hΛ hΛ0
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0:ℝ) < ε := hε
  have hV0 : 0 ≤ hcV c ξ := le_trans (by positivity) (hcV_ge c hc0 hc1 ξ)
  set T := 2 * hcV c ξ / (γ * ε) with hT
  have hT0 : 0 ≤ T := by positivity
  have hγT : γ * T = 2 * hcV c ξ / ε := by rw [hT]; field_simp
  have hbound : 2 * Real.exp (-(γ * T)) * hcV c ξ ≤ ε := by
    have h1 : γ * T + 1 ≤ Real.exp (γ * T) := Real.add_one_le_exp _
    rw [Real.exp_neg, hγT] at *
    have hE := Real.exp_pos (2 * hcV c ξ / ε)
    rw [mul_comm 2, mul_assoc, inv_mul_eq_div, div_le_iff₀ hE]
    have : 2 * hcV c ξ / ε * ε = 2 * hcV c ξ := by field_simp
    nlinarith
  calc survInf μ lam ξ ≤ surv μ lam (((⟨T, hT0⟩ : ℝ≥0)) : ℝ) ξ :=
        iInf_le (fun t : ℝ≥0 => surv μ lam t ξ) ⟨T, hT0⟩
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(γ * T)) * hcV c ξ) := hsl T hT0 ξ
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hbound
    _ = 0 + (ε : ℝ≥0∞) := by rw [zero_add, ENNReal.ofReal_coe_nnreal]

theorem pi1_pos_imp_core {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) :
    ∀ x : Site d, 0 < survInf 1 (fun k => (k : ℝ) * l) {x} → 1 ≤ (2 * (d : ℝ) - 1) * l := by
  intro x hx
  by_contra h
  push_neg at h
  have h7 := theorem_7_1_core hd 1 (fun k => (k : ℝ) * l) zero_le_one (by simp)
    (fun k _ => by positivity)
    (fun k hk1 _ => by
      have : (1:ℝ) ≤ k := by exact_mod_cast hk1
      nlinarith) {x}
  rw [h7] at hx
  exact lt_irrefl _ hx

lemma hcE_step {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (Λ : ℝ) (hΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ) (hΛ0 : 0 ≤ Λ) (M : ℕ)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ξ : Config d) :
    (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * (t - s)) * ((ζ.card : ℝ) + 1) /
            ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * (t - s)) / 2 ^ n))) ≤
      min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * t) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1)) +
        ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * t) / 2 ^ (n + 1))) := by
  have hrn := hc_rate_nonneg μ lam hμ hlam ξ
  have hq0 : 0 ≤ exitRate μ lam ξ := hc_exitRate_nonneg μ lam hμ hlam ξ
  have hGMle1 : (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * (t - s)) * ((ζ.card : ℝ) + 1) /
            ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * (t - s)) / 2 ^ n))) ≤ 1 := by
    calc _ ≤ ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
          ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * 1 := by
          apply setLIntegral_mono' measurableSet_Icc
          intro s _
          gcongr with ζ hζ
          exact min_le_left _ _
      _ = _ := hc_const μ lam hμ hlam ξ t ht
      _ ≤ 1 := ENNReal.ofReal_le_one.mpr (by linarith [Real.exp_pos (-(exitRate μ lam ξ * t))])
  have hMint : (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * (t - s)) * ((ζ.card : ℝ) + 1) /
            ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * (t - s)) / 2 ^ n))) ≤
      min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * t) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1)) +
        ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * t) / 2 ^ (n + 1))) := by
    by_cases hM : M ≤ ξ.card
    · have hY1 : 1 ≤ Real.exp (2 * d * Λ * t) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1) := by
        rw [le_div_iff₀ (by positivity)]
        have : (1:ℝ) ≤ Real.exp (2 * d * Λ * t) := Real.one_le_exp (by positivity)
        have : (M : ℝ) ≤ ξ.card := by exact_mod_cast hM
        nlinarith
      rw [min_eq_left]
      · exact hGMle1
      · exact le_trans (ENNReal.one_le_ofReal.mpr hY1) le_self_add
    · push_neg at hM
      have hqQ : exitRate μ lam ξ ≤ (μ + 2 * d * Λ) * M := by
        have := hc_exitRate_le μ lam Λ hΛ hΛ0 ξ
        have h2 : (ξ.card : ℝ) ≤ M := by exact_mod_cast hM.le
        have : 0 ≤ μ + 2 * d * Λ := by positivity
        nlinarith
      apply le_min hGMle1
      have hY := hc_super μ lam hμ hlam ξ t ht
        (fun r ζ => Real.exp (2 * d * Λ * r) * ((ζ.card : ℝ) + 1) / ((M : ℝ) + 1))
        (fun r ζ => by positivity)
        (fun r => Real.exp (2 * d * Λ * r) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1))
        (fun r => 2 * d * Λ * (Real.exp (2 * d * Λ * r) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1)))
        (fun r => ((((hasDerivAt_const_mul (2 * d * Λ)).exp).mul_const _).div_const _).congr_deriv
          (by ring))
        (by fun_prop)
        (by
          intro r _
          have hsd := hc_size_drift μ lam hμ Λ hΛ hΛ0 ξ
          have hK : 0 < Real.exp (2 * d * Λ * r) / ((M : ℝ) + 1) := by positivity
          have hrw : ∑ ζ ∈ succ ξ, rate μ lam ξ ζ *
              (Real.exp (2 * d * Λ * r) * ((ζ.card : ℝ) + 1) / ((M : ℝ) + 1)) =
              Real.exp (2 * d * Λ * r) / ((M : ℝ) + 1) *
                ∑ ζ ∈ succ ξ, rate μ lam ξ ζ * ((ζ.card : ℝ) + 1) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ζ _ => by ring)
          rw [hrw]
          have := mul_le_mul_of_nonneg_left hsd hK.le
          calc _ ≤ _ := this
            _ = _ := by ring)
      have hZ := hc_super μ lam hμ hlam ξ t ht
        (fun r ζ => Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ n)
        (fun r ζ => by positivity)
        (fun r => Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ (n + 1))
        (fun r => (μ + 2 * d * Λ) * M * (Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ (n + 1)))
        (fun r => (((hasDerivAt_const_mul ((μ + 2 * d * Λ) * M)).exp).div_const _).congr_deriv
          (by ring))
        (by fun_prop)
        (by
          intro r _
          rw [← Finset.sum_mul, hc_sum_rate]
          have hE : 0 < Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ (n + 1) := by positivity
          have : Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ n =
              2 * (Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ (n + 1)) := by
            rw [pow_succ]; field_simp
          rw [this]
          nlinarith)
      calc _ ≤ ∫⁻ s in Set.Icc 0 t,
            (ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
              ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
                ENNReal.ofReal (Real.exp (2 * d * Λ * (t - s)) * ((ζ.card : ℝ) + 1) /
                  ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
              ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
                ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * (t - s)) / 2 ^ n)) := by
            apply setLIntegral_mono' measurableSet_Icc
            intro s _
            rw [← mul_add, ← Finset.sum_add_distrib]
            gcongr with ζ hζ
            rw [← mul_add]
            gcongr
            exact min_le_right _ _
        _ = _ := lintegral_add_left (hc_meas _ t _ _ (fun r ζ => ENNReal.ofReal
              (Real.exp (2 * d * Λ * r) * ((ζ.card : ℝ) + 1) / ((M : ℝ) + 1)))
              (fun ζ => ENNReal.measurable_ofReal.comp (by fun_prop))) _
        _ ≤ _ := by
            refine add_le_add (hY.trans (ENNReal.ofReal_le_ofReal ?_))
              (hZ.trans (ENNReal.ofReal_le_ofReal ?_))
            · have : 0 ≤ Real.exp (-(exitRate μ lam ξ * t)) *
                  (Real.exp (2 * d * Λ * 0) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1)) := by
                positivity
              linarith
            · have : 0 ≤ Real.exp (-(exitRate μ lam ξ * t)) *
                  (Real.exp ((μ + 2 * d * Λ) * M * 0) / 2 ^ (n + 1)) := by positivity
              linarith
  exact hMint

lemma hc_transN_meas {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) :
    ∀ n (ζ η : Config d), Measurable (fun t => transN μ lam n t ζ η) := by
  intro n
  induction n with
  | zero =>
    intro ζ η
    simp only [transN]
    split_ifs
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact measurable_const
  | succ n ih =>
    intro ζ η
    simp only [hc_transN_succ]
    apply Measurable.add
    · simp only [transN]
      split_ifs
      · exact ENNReal.measurable_ofReal.comp (by fun_prop)
      · exact measurable_const
    · let S : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1}
      have hS : MeasurableSet S :=
        (measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst)
      let g : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (-(exitRate μ lam ζ * p.2))) *
        ∑ ζ' ∈ succ ζ, ENNReal.ofReal (rate μ lam ζ ζ') * transN μ lam n (p.1 - p.2) ζ' η
      have hg : Measurable g := by
        apply Measurable.mul
        · exact ENNReal.measurable_ofReal.comp (by fun_prop)
        · apply Finset.measurable_sum
          intro ζ' _
          exact measurable_const.mul ((ih ζ' η).comp (measurable_fst.sub measurable_snd))
      have heq : (fun t => ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ζ * s))) *
          ∑ ζ' ∈ succ ζ, ENNReal.ofReal (rate μ lam ζ ζ') * transN μ lam n (t - s) ζ' η) =
          fun t => ∫⁻ s, S.indicator g (t, s) := by
        funext t
        rw [← lintegral_indicator measurableSet_Icc]
        congr 1
      rw [heq]
      exact (hg.indicator hS).lintegral_prod_right'

lemma hc_transN_mono {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) :
    ∀ n t (ξ η : Config d), transN μ lam n t ξ η ≤ transN μ lam (n + 1) t ξ η := by
  intro n
  induction n with
  | zero => intro t ξ η; rw [hc_transN_succ]; exact le_self_add
  | succ n ih =>
    intro t ξ η
    rw [hc_transN_succ μ lam (n + 1), hc_transN_succ μ lam n]
    refine add_le_add le_rfl (lintegral_mono (fun s => ?_))
    gcongr with ζ hζ
    exact ih _ _ _

lemma hc_mass_eq {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (n : ℕ) (t : ℝ) (ξ : Config d) :
    ∑' η, transN μ lam (n + 1) t ξ η =
      ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) +
      ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * ∑' η, transN μ lam n (t - s) ζ η := by
  simp only [hc_transN_succ]
  rw [ENNReal.tsum_add]
  congr 1
  · simp only [transN]
    simp_rw [@eq_comm _ ξ]
    rw [tsum_ite_eq]
  · rw [← lintegral_tsum]
    · congr 1
      funext s
      rw [ENNReal.tsum_mul_left]
      congr 1
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      exact Finset.sum_congr rfl (fun ζ _ => ENNReal.tsum_mul_left)
    · intro η
      exact (hc_meas _ t _ _ (fun r ζ => transN μ lam n r ζ η)
        (fun ζ => hc_transN_meas μ lam n ζ η)).aemeasurable

lemma hc_mass_le {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ n t, 0 ≤ t → ∀ ξ : Config d, ∑' η, transN μ lam n t ξ η ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro t ht ξ
    simp only [transN]
    simp_rw [@eq_comm _ ξ]
    rw [tsum_ite_eq]
    apply ENNReal.ofReal_le_one.mpr
    rw [Real.exp_le_one_iff]
    have := hc_exitRate_nonneg μ lam hμ hlam ξ
    nlinarith
  | succ n ih =>
    intro t ht ξ
    rw [hc_mass_eq]
    have hq0 := hc_exitRate_nonneg μ lam hμ hlam ξ
    have he1 : Real.exp (-(exitRate μ lam ξ * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    calc _ ≤ ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) +
          ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
            ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * 1 := by
          refine add_le_add le_rfl (setLIntegral_mono' measurableSet_Icc (fun s hs => ?_))
          gcongr with ζ hζ
          exact ih (t - s) (by linarith [hs.2]) ζ
      _ = 1 := by
          rw [hc_const μ lam hμ hlam ξ t ht, ← ENNReal.ofReal_add (Real.exp_pos _).le
            (sub_nonneg.2 he1)]
          simp

lemma hc_mass_ge {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (Λ : ℝ) (hΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ) (hΛ0 : 0 ≤ Λ) (M : ℕ) :
    ∀ n t, 0 ≤ t → ∀ ξ : Config d, 1 ≤ ∑' η, transN μ lam n t ξ η +
      min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * t) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1)) +
        ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * t) / 2 ^ n)) := by
  intro n
  induction n with
  | zero =>
    intro t ht ξ
    have h1 : 1 ≤ Real.exp ((μ + 2 * d * Λ) * M * t) / 2 ^ 0 := by
      rw [pow_zero, div_one]; exact Real.one_le_exp (by positivity)
    rw [min_eq_left (le_trans (ENNReal.one_le_ofReal.mpr h1) le_add_self)]
    exact le_add_self
  | succ n ih =>
    intro t ht ξ
    rw [hc_mass_eq]
    have hq0 := hc_exitRate_nonneg μ lam hμ hlam ξ
    have he1 : Real.exp (-(exitRate μ lam ξ * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hsplit : (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * t))) +
        ENNReal.ofReal (1 - Real.exp (-(exitRate μ lam ξ * t))) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (sub_nonneg.2 he1)]; simp
    have hEm : Measurable (fun s => ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * (t - s)) * ((ζ.card : ℝ) + 1) /
            ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * (t - s)) / 2 ^ n))) := by
      refine hc_meas _ t _ _ (fun r ζ => min 1 (ENNReal.ofReal (Real.exp (2 * d * Λ * r) *
        ((ζ.card : ℝ) + 1) / ((M : ℝ) + 1)) +
            ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ n))) (fun ζ => ?_)
      have h2 : Measurable (fun r : ℝ =>
          ENNReal.ofReal (Real.exp (2 * d * Λ * r) * ((ζ.card : ℝ) + 1) / ((M : ℝ) + 1))) :=
        ENNReal.measurable_ofReal.comp (by fun_prop)
      have h3 : Measurable (fun r : ℝ =>
          ENNReal.ofReal (Real.exp ((μ + 2 * d * Λ) * M * r) / 2 ^ n)) :=
        ENNReal.measurable_ofReal.comp (by fun_prop)
      fun_prop
    conv_lhs => rw [hsplit, ← hc_const μ lam hμ hlam ξ t ht]
    rw [add_assoc]
    refine add_le_add le_rfl ?_
    refine le_trans ?_ (add_le_add le_rfl (hcE_step μ lam hμ hlam Λ hΛ hΛ0 M n t ht ξ))
    rw [← lintegral_add_right' _ hEm.aemeasurable]
    apply setLIntegral_mono' measurableSet_Icc
    intro s hs
    rw [← mul_add, ← Finset.sum_add_distrib]
    gcongr with ζ hζ
    rw [← mul_add]
    gcongr
    exact ih (t - s) (by linarith [hs.2]) ζ

theorem theorem_4_3_core {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ : Config d, ∑' η : Config d, trans μ lam t ξ η = 1 := by
  intro t ht ξ
  set Λ := ∑ k ∈ Finset.range (2 * d + 1), lam k with hΛdef
  have hΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ := by
    intro k hk
    exact Finset.single_le_sum (f := lam) (fun i hi => hlam i (by simp at hi; omega))
      (by simp; omega)
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg (fun i hi => hlam i (by simp at hi; omega))
  have hmono : ∀ η, Monotone (fun n => transN μ lam n t ξ η) :=
    fun η => monotone_nat_of_le_succ (fun n => hc_transN_mono μ lam n t ξ η)
  apply le_antisymm
  · unfold trans
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    rw [ENNReal.finsetSum_iSup_of_monotone hmono]
    apply iSup_le
    intro n
    exact (ENNReal.sum_le_tsum F).trans (hc_mass_le μ lam hμ hlam n t ht ξ)
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hε' : (0:ℝ) < ε := hε
    obtain ⟨M, hM⟩ := exists_nat_gt (2 * Real.exp (2 * d * Λ * t) * ((ξ.card : ℝ) + 1) / ε)
    have hQ0 : 0 ≤ (μ + 2 * d * Λ) * M := by positivity
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (by positivity : (0:ℝ) < ε / (2 * Real.exp ((μ + 2 * d * Λ) * M * t)))
      (by norm_num : (1/2 : ℝ) < 1)
    have hind := hc_mass_ge μ lam hμ hlam Λ hΛ hΛ0 M n t ht ξ
    have htr : ∑' η, transN μ lam n t ξ η ≤ ∑' η, trans μ lam t ξ η :=
      ENNReal.tsum_le_tsum (fun η => le_iSup (fun n => transN μ lam n t ξ η) n)
    have hY : Real.exp (2 * d * Λ * t) * ((ξ.card : ℝ) + 1) / ((M : ℝ) + 1) ≤ ε / 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε'] at hM
      nlinarith
    have hZ : Real.exp ((μ + 2 * d * Λ) * M * t) / 2 ^ n ≤ ε / 2 := by
      have hE := Real.exp_pos ((μ + 2 * d * Λ) * M * t)
      rw [lt_div_iff₀ (by positivity)] at hn
      have : Real.exp ((μ + 2 * d * Λ) * M * t) / 2 ^ n =
          (1/2) ^ n * Real.exp ((μ + 2 * d * Λ) * M * t) := by
        rw [one_div_pow]; field_simp
      rw [this]; nlinarith
    refine hind.trans ?_
    calc _ ≤ ∑' η, trans μ lam t ξ η + (ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2)) := by
          refine add_le_add htr ((min_le_right _ _).trans ?_)
          exact add_le_add (ENNReal.ofReal_le_ofReal hY) (ENNReal.ofReal_le_ofReal hZ)
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
            ENNReal.ofReal_coe_nnreal]

section Invariance
variable {d : ℕ} (σ : Site d ≃ Site d) (hσ : ∀ a b, σ b ∈ nbrs (σ a) ↔ b ∈ nbrs a)
include hσ

lemma hc_nbrs_map (a : Site d) : nbrs (σ a) = (nbrs a).map σ.toEmbedding := by
  ext w
  rw [Finset.mem_map_equiv]
  have := hσ a (σ.symm w)
  rw [Equiv.apply_symm_apply] at this
  exact this

lemma hc_occ_map (ξ : Config d) (a : Site d) : occ (ξ.map σ.toEmbedding) (σ a) = occ ξ a := by
  classical
  unfold occ
  rw [hc_nbrs_map σ hσ, ← Finset.map_inter, Finset.card_map]

lemma hc_bdry_map (ξ : Config d) : bdry (ξ.map σ.toEmbedding) = (bdry ξ).map σ.toEmbedding := by
  classical
  unfold bdry
  rw [Finset.map_sdiff]
  congr 1
  ext w
  simp only [Finset.mem_biUnion, Finset.mem_map_equiv]
  constructor
  · rintro ⟨y, hy, hw⟩
    refine ⟨σ.symm y, hy, ?_⟩
    have := hc_nbrs_map σ hσ (σ.symm y)
    rw [Equiv.apply_symm_apply] at this
    rw [this, Finset.mem_map_equiv] at hw
    exact hw
  · rintro ⟨y, hy, hw⟩
    refine ⟨σ y, by simpa using hy, ?_⟩
    rw [hc_nbrs_map σ hσ, Finset.mem_map_equiv]
    exact hw

lemma hc_exitRate_map (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) :
    exitRate μ lam (ξ.map σ.toEmbedding) = exitRate μ lam ξ := by
  unfold exitRate
  rw [Finset.card_map, hc_bdry_map σ hσ, Finset.sum_map]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => by rw [Equiv.coe_toEmbedding, hc_occ_map σ hσ])

lemma hc_rate_map (μ : ℝ) (lam : ℕ → ℝ) (ξ η : Config d) :
    rate μ lam (ξ.map σ.toEmbedding) (η.map σ.toEmbedding) = rate μ lam ξ η := by
  classical
  unfold rate
  rw [hc_bdry_map σ hσ, Finset.sum_map, Finset.sum_map]
  congr 1
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    have h2 : (Finset.map σ.toEmbedding ξ).erase (σ.toEmbedding x) =
        (ξ.erase x).map σ.toEmbedding := (Finset.map_erase _ _ _).symm
    rw [h2]; simp only [Finset.map_inj]
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    have h2 : insert (σ.toEmbedding x) (ξ.map σ.toEmbedding) =
        (insert x ξ).map σ.toEmbedding := (Finset.map_insert _ _ _).symm
    have h3 : occ (ξ.map σ.toEmbedding) (σ.toEmbedding x) = occ ξ x := hc_occ_map σ hσ ξ x
    rw [h2, h3]; simp only [Finset.map_inj]

lemma hc_succ_map (ξ : Config d) :
    succ (ξ.map σ.toEmbedding) = (succ ξ).image (fun ζ => ζ.map σ.toEmbedding) := by
  classical
  unfold succ
  rw [hc_bdry_map σ hσ, Finset.image_union, Finset.image_image, Finset.image_image]
  congr 1
  · ext ζ
    simp only [Finset.mem_image, Finset.mem_map, Function.comp]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (Finset.map_erase _ _ _)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨σ.toEmbedding x, ⟨x, hx, rfl⟩, (Finset.map_erase _ _ _).symm⟩
  · ext ζ
    simp only [Finset.mem_image, Finset.mem_map, Function.comp]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (Finset.map_insert _ _ _)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨σ.toEmbedding x, ⟨x, hx, rfl⟩, (Finset.map_insert _ _ _).symm⟩

lemma hc_transN_map (μ : ℝ) (lam : ℕ → ℝ) :
    ∀ n t (ξ η : Config d), transN μ lam n t (ξ.map σ.toEmbedding) (η.map σ.toEmbedding) =
      transN μ lam n t ξ η := by
  classical
  intro n
  induction n with
  | zero =>
    intro t ξ η
    simp only [transN, Finset.map_inj, hc_exitRate_map σ hσ]
  | succ n ih =>
    intro t ξ η
    rw [hc_transN_succ, hc_transN_succ]
    congr 1
    · simp only [transN, Finset.map_inj, hc_exitRate_map σ hσ]
    · rw [hc_exitRate_map σ hσ, hc_succ_map σ hσ]
      congr 1
      funext s
      congr 1
      rw [Finset.sum_image (fun a _ b _ h => Finset.map_injective _ h)]
      exact Finset.sum_congr rfl (fun ζ _ => by rw [hc_rate_map σ hσ, ih])

lemma hc_survInf_map (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) :
    survInf μ lam (ξ.map σ.toEmbedding) = survInf μ lam ξ := by
  unfold survInf surv trans
  have : (∅ : Config d) = (∅ : Config d).map σ.toEmbedding := (Finset.map_empty _).symm
  rw [this]
  simp only [hc_transN_map σ hσ]
  rw [← this]

end Invariance

lemma hc_translate_ok {d : ℕ} (a : Site d) :
    ∀ x y, (Equiv.addRight a) y ∈ nbrs ((Equiv.addRight a) x) ↔ y ∈ nbrs x := by
  intro x y
  rw [hc_mem_nbrs_iff, hc_mem_nbrs_iff]
  simp

lemma hc_transN_mono_t {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) :
    ∀ n (ζ : Config d) (t t' : ℝ), t ≤ t' → transN μ lam n t ζ ∅ ≤ transN μ lam n t' ζ ∅ := by
  have h0 : ∀ (ζ : Config d) (t t' : ℝ), transN μ lam 0 t ζ ∅ ≤ transN μ lam 0 t' ζ ∅ := by
    intro ζ t t'
    simp only [transN]
    split_ifs with h
    · subst h; simp [hc_exitRate_empty]
    · exact le_rfl
  intro n
  induction n with
  | zero => intro ζ t t' _; exact h0 ζ t t'
  | succ n ih =>
    intro ζ t t' htt
    rw [hc_transN_succ, hc_transN_succ]
    refine add_le_add (h0 ζ t t') ?_
    calc _ ≤ ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ζ * s))) *
          ∑ ζ' ∈ succ ζ, ENNReal.ofReal (rate μ lam ζ ζ') * transN μ lam n (t' - s) ζ' ∅ := by
          apply lintegral_mono
          intro s
          dsimp only
          gcongr with ζ' hζ'
          exact ih ζ' _ _ (by linarith)
      _ ≤ _ := lintegral_mono_set (Set.Icc_subset_Icc_right htt)

lemma hc_trans_mono_t {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ζ : Config d) (t t' : ℝ) (htt : t ≤ t') :
    trans μ lam t ζ ∅ ≤ trans μ lam t' ζ ∅ :=
  iSup_mono (fun n => hc_transN_mono_t μ lam n ζ t t' htt)

lemma hc_trans_le_one {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (t : ℝ) (ht : 0 ≤ t) (ζ η : Config d) :
    trans μ lam t ζ η ≤ 1 :=
  iSup_le (fun n => (ENNReal.le_tsum η).trans (hc_mass_le μ lam hμ hlam n t ht ζ))

lemma hc_trans_backward {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (t : ℝ) (ξ : Config d) (hξ : ξ ≠ ∅) :
    trans μ lam t ξ ∅ = ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
      ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * trans μ lam (t - s) ζ ∅ := by
  have hmono : ∀ r (ζ : Config d), Monotone (fun n => transN μ lam n r ζ ∅) :=
    fun r ζ => monotone_nat_of_le_succ (fun n => hc_transN_mono μ lam n r ζ ∅)
  unfold trans
  have hshift : ⨆ n, transN μ lam n t ξ ∅ = ⨆ n, transN μ lam (n + 1) t ξ ∅ :=
    le_antisymm (iSup_mono (fun n => hc_transN_mono μ lam n t ξ ∅))
      (iSup_le fun n => le_iSup (fun n => transN μ lam n t ξ ∅) (n + 1))
  have h0 : transN μ lam 0 t ξ ∅ = 0 := by simp [transN, hξ]
  rw [hshift]
  simp only [hc_transN_succ, h0, zero_add]
  rw [← lintegral_iSup]
  · congr 1
    funext s
    simp_rw [ENNReal.mul_iSup]
    rw [ENNReal.finsetSum_iSup_of_monotone, ENNReal.mul_iSup]
    intro ζ a b hab
    exact mul_le_mul_right (hmono _ ζ hab) _
  · intro n
    exact hc_meas _ t _ _ (fun r ζ => transN μ lam n r ζ ∅) (fun ζ => hc_transN_meas μ lam n ζ ∅)
  · intro a b hab s
    simp only
    gcongr with ζ hζ
    exact hmono _ ζ hab

lemma hc_int_exp (q t : ℝ) (hq : 0 < q) (ht : 0 ≤ t) :
    ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(q * s))) =
      ENNReal.ofReal ((1 - Real.exp (-(q * t))) / q) := by
  have := hc_key_eq q t ht (fun _ => 1 / q) (fun _ => 0) (fun r => hasDerivAt_const r _)
    continuous_const (fun s _ => by
      simp only [add_zero]; rw [mul_one_div_cancel hq.ne']; simp [(Real.exp_pos _).le])
  rw [show (1 - Real.exp (-(q * t))) / q = 1 / q - Real.exp (-(q * t)) * (1 / q) by ring, ← this]
  apply lintegral_congr; intro s
  simp only [add_zero]; rw [mul_one_div_cancel hq.ne', mul_one]

noncomputable def hcA {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, trans μ lam t ξ ∅

lemma hc_survInf_eq {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) :
    survInf μ lam ξ = 1 - hcA μ lam ξ := by
  unfold survInf surv hcA
  rw [ENNReal.sub_iSup ENNReal.one_ne_top]

lemma hcA_le_one {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) : hcA μ lam ξ ≤ 1 :=
  iSup_le (fun t => hc_trans_le_one μ lam hμ hlam t t.2 ξ ∅)

lemma hcA_eq {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) (hq : 0 < exitRate μ lam ξ) :
    hcA μ lam ξ = ∑ ζ ∈ succ ξ,
      ENNReal.ofReal (rate μ lam ξ ζ / exitRate μ lam ξ) * hcA μ lam ζ := by
  have hξ : ξ ≠ ∅ := by
    rintro rfl; rw [hc_exitRate_empty] at hq; exact lt_irrefl _ hq
  have hrn := hc_rate_nonneg μ lam hμ hlam ξ
  set q := exitRate μ lam ξ with hqdef
  have hcoef : ∀ ζ, ENNReal.ofReal (rate μ lam ξ ζ / q) =
      ENNReal.ofReal (1 / q) * ENNReal.ofReal (rate μ lam ξ ζ) := by
    intro ζ
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  apply le_antisymm
  · apply iSup_le
    intro t
    rw [hc_trans_backward μ lam t ξ hξ]
    calc _ ≤ ∫⁻ s in Set.Icc 0 (t : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) *
          ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcA μ lam ζ := by
          apply setLIntegral_mono' measurableSet_Icc
          intro s hs
          gcongr with ζ hζ
          exact le_iSup_of_le (⟨(t:ℝ) - s, by linarith [hs.2]⟩ : ℝ≥0) le_rfl
      _ = (∫⁻ s in Set.Icc 0 (t : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))) *
          ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcA μ lam ζ :=
          lintegral_mul_const _ (ENNReal.measurable_ofReal.comp (by fun_prop))
      _ ≤ ENNReal.ofReal (1 / q) * ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * hcA μ lam ζ := by
          rw [hc_int_exp q t hq t.2]
          gcongr
          linarith [Real.exp_pos (-(q * t))]
      _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun ζ _ => by rw [hcoef, mul_assoc])
  · have hmonoT : ∀ ζ : Config d, Monotone (fun T : ℝ≥0 =>
        ENNReal.ofReal (rate μ lam ξ ζ / q) * trans μ lam T ζ ∅) :=
      fun ζ a b hab => mul_le_mul_right (hc_trans_mono_t μ lam ζ a b hab) _
    unfold hcA
    simp_rw [ENNReal.mul_iSup]
    rw [ENNReal.finsetSum_iSup_of_monotone hmonoT]
    apply iSup_le
    intro T
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hε' : (0:ℝ) < ε := hε
    set τ : ℝ := 1 / (q * ε) with hτ
    have hτ0 : 0 ≤ τ := by positivity
    have hexpτ : Real.exp (-(q * τ)) ≤ ε := by
      have h1 := Real.add_one_le_exp (q * τ)
      have hqτ : q * τ = 1 / ε := by rw [hτ]; field_simp
      rw [Real.exp_neg, hqτ]
      rw [hqτ] at h1
      rw [inv_le_comm₀ (Real.exp_pos _) hε']
      have : (1:ℝ) / (ε:ℝ) ≤ 1 / (ε:ℝ) + 1 := by linarith
      calc (ε:ℝ)⁻¹ = 1 / (ε:ℝ) := by ring
        _ ≤ _ := this.trans h1
    set X := ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * trans μ lam T ζ ∅ with hX
    have hXle : X ≤ ENNReal.ofReal q := by
      calc X ≤ ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * 1 := by
            rw [hX]
            gcongr with ζ hζ; exact hc_trans_le_one μ lam hμ hlam T T.2 ζ ∅
        _ = ENNReal.ofReal q := by
            simp only [mul_one]
            rw [← ENNReal.ofReal_sum_of_nonneg (fun ζ _ => hrn ζ), hc_sum_rate]
    -- lower bound for trans at time T + τ
    have hlow : ENNReal.ofReal ((1 - Real.exp (-(q * τ))) / q) * X ≤
        trans μ lam ((T : ℝ) + τ) ξ ∅ := by
      have hm : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s)))) :=
        ENNReal.measurable_ofReal.comp (by fun_prop)
      rw [hc_trans_backward μ lam _ ξ hξ, ← hc_int_exp q τ hq hτ0,
        ← lintegral_mul_const _ hm]
      calc _ ≤ ∫⁻ s in Set.Icc 0 τ, ENNReal.ofReal (Real.exp (-(q * s))) *
            ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * trans μ lam ((T : ℝ) + τ - s) ζ ∅ := by
            apply setLIntegral_mono' measurableSet_Icc
            intro s hs
            rw [hX]
            gcongr with ζ hζ
            exact hc_trans_mono_t μ lam ζ _ _ (by linarith [hs.2])
        _ ≤ _ := lintegral_mono_set (Set.Icc_subset_Icc_right (by linarith [T.2]))
    have hTle : trans μ lam ((T : ℝ) + τ) ξ ∅ ≤ ⨆ t : ℝ≥0, trans μ lam t ξ ∅ :=
      le_iSup_of_le (⟨(T : ℝ) + τ, by positivity⟩ : ℝ≥0) le_rfl
    have hsum : ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ / q) * trans μ lam T ζ ∅ =
        ENNReal.ofReal (1 / q) * X := by
      rw [hX, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun ζ _ => by rw [hcoef, mul_assoc])
    rw [hsum]
    have hsplit : ENNReal.ofReal (1 / q) = ENNReal.ofReal ((1 - Real.exp (-(q * τ))) / q) +
        ENNReal.ofReal (Real.exp (-(q * τ)) / q) := by
      have he1 : Real.exp (-(q * τ)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      rw [← ENNReal.ofReal_add (div_nonneg (by linarith) hq.le) (by positivity)]
      congr 1; ring
    rw [hsplit, add_mul]
    refine add_le_add (hlow.trans hTle) ?_
    calc ENNReal.ofReal (Real.exp (-(q * τ)) / q) * X ≤
        ENNReal.ofReal (Real.exp (-(q * τ)) / q) * ENNReal.ofReal q := by gcongr
      _ = ENNReal.ofReal (Real.exp (-(q * τ))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hexpτ
      _ = ε := ENNReal.ofReal_coe_nnreal

lemma hc_jump_nonneg {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ ζ : Config d) : 0 ≤ jump μ lam ξ ζ := by
  unfold jump
  split_ifs
  · norm_num
  · norm_num
  · exact div_nonneg (hc_rate_nonneg μ lam hμ hlam ξ ζ) (hc_exitRate_nonneg μ lam hμ hlam ξ)

lemma hc_jumpPow_nonneg {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ n (ξ η : Config d), 0 ≤ jumpPow μ lam n ξ η := by
  intro n
  induction n with
  | zero => intro ξ η; simp only [jumpPow]; split_ifs <;> norm_num
  | succ n ih =>
    intro ξ η
    simp only [jumpPow]
    exact Finset.sum_nonneg (fun ζ _ => mul_nonneg (hc_jump_nonneg μ lam hμ hlam ξ ζ) (ih ζ η))

lemma hc_rate_self {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) : rate μ lam ξ ξ = 0 := by
  unfold rate
  have h1 : ∀ x ∈ ξ, (if ξ = ξ.erase x then μ else 0) = 0 :=
    fun x hx => if_neg (fun h => (Finset.erase_eq_self.mp h.symm) hx)
  have h2 : ∀ x ∈ bdry ξ, (if ξ = insert x ξ then lam (occ ξ x) else 0) = 0 :=
    fun x hx => if_neg (fun h => (Finset.mem_sdiff.mp hx).2 (Finset.insert_eq_self.mp h.symm))
  rw [Finset.sum_eq_zero h1, Finset.sum_eq_zero h2, add_zero]

lemma hc_harm1 {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) :
    survInf μ lam ξ = ∑ ζ ∈ insert ξ (succ ξ),
      ENNReal.ofReal (jump μ lam ξ ζ) * survInf μ lam ζ := by
  classical
  by_cases hq : exitRate μ lam ξ = 0
  · rw [Finset.sum_eq_single_of_mem ξ (Finset.mem_insert_self _ _)]
    · simp [jump, hq]
    · intro b _ hb; simp [jump, hq, hb]
  · have hq' : 0 < exitRate μ lam ξ :=
      lt_of_le_of_ne (hc_exitRate_nonneg μ lam hμ hlam ξ) (Ne.symm hq)
    have hj : ∀ ζ, jump μ lam ξ ζ = rate μ lam ξ ζ / exitRate μ lam ξ :=
      fun ζ => by simp [jump, hq]
    simp only [hj]
    rw [Finset.sum_insert_zero (by rw [hc_rate_self, zero_div, ENNReal.ofReal_zero, zero_mul])]
    rw [hc_survInf_eq, hcA_eq μ lam hμ hlam ξ hq']
    simp only [hc_survInf_eq]
    have hc1 : ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ / exitRate μ lam ξ) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun ζ _ =>
        div_nonneg (hc_rate_nonneg μ lam hμ hlam ξ ζ) hq'.le), ← Finset.sum_div, hc_sum_rate,
        div_self hq, ENNReal.ofReal_one]
    rw [Finset.sum_congr rfl (fun ζ _ => ENNReal.mul_sub (fun _ _ => ENNReal.ofReal_ne_top))]
    have hA : ∑ ζ ∈ succ ξ, (ENNReal.ofReal (rate μ lam ξ ζ / exitRate μ lam ξ) * 1 -
        ENNReal.ofReal (rate μ lam ξ ζ / exitRate μ lam ξ) * hcA μ lam ζ) +
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ / exitRate μ lam ξ) * hcA μ lam ζ =
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ / exitRate μ lam ξ) * 1 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ζ _ =>
        tsub_add_cancel_of_le (mul_le_mul_right (hcA_le_one μ lam hμ hlam ζ) _))
    have hfin : ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ / exitRate μ lam ξ) *
        hcA μ lam ζ ≠ ∞ := by
      apply ne_top_of_le_ne_top ENNReal.one_ne_top
      rw [← hc1]
      exact Finset.sum_le_sum (fun ζ _ => by
        simpa using mul_le_mul_right (hcA_le_one μ lam hμ hlam ζ) _)
    rw [ENNReal.eq_sub_of_add_eq hfin hA]
    simp only [mul_one]
    rw [hc1]

lemma hc_harmN {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ n (ξ : Config d), survInf μ lam ξ =
      ∑' η : Config d, ENNReal.ofReal (jumpPow μ lam n ξ η) * survInf μ lam η := by
  intro n
  induction n with
  | zero =>
    intro ξ
    simp only [jumpPow, apply_ite ENNReal.ofReal, ENNReal.ofReal_one, ENNReal.ofReal_zero,
      ite_mul, one_mul, zero_mul]
    simp_rw [@eq_comm _ ξ]
    rw [tsum_ite_eq]
  | succ n ih =>
    intro ξ
    have hsplit : ∀ η, ENNReal.ofReal (jumpPow μ lam (n + 1) ξ η) =
        ∑ ζ ∈ insert ξ (succ ξ), ENNReal.ofReal (jump μ lam ξ ζ) *
          ENNReal.ofReal (jumpPow μ lam n ζ η) := by
      intro η
      simp only [jumpPow]
      rw [ENNReal.ofReal_sum_of_nonneg (fun ζ _ => mul_nonneg (hc_jump_nonneg μ lam hμ hlam ξ ζ)
        (hc_jumpPow_nonneg μ lam hμ hlam n ζ η))]
      exact Finset.sum_congr rfl (fun ζ _ => ENNReal.ofReal_mul (hc_jump_nonneg μ lam hμ hlam ξ ζ))
    simp only [hsplit, Finset.sum_mul]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    rw [hc_harm1 μ lam hμ hlam ξ]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    simp_rw [mul_assoc]
    rw [ENNReal.tsum_mul_left, ← ih ζ]

lemma hc_survInf_empty {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) : survInf μ lam (∅ : Config d) = 0 := by
  have h' : surv μ lam ((0:ℝ≥0):ℝ) (∅ : Config d) = 0 := by
    unfold surv
    apply tsub_eq_zero_of_le
    unfold trans
    exact le_iSup_of_le 0 (by simp [transN, hc_exitRate_empty])
  exact le_antisymm ((iInf_le _ 0).trans (le_of_eq h')) bot_le

lemma hc_survInf_subadd {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ)
    (hsubadd : ∀ t : ℝ, 0 ≤ t → ∀ ξ η : Config d,
      surv μ lam t (ξ ∪ η) ≤ surv μ lam t ξ + surv μ lam t η) (ξ η : Config d) :
    survInf μ lam (ξ ∪ η) ≤ survInf μ lam ξ + survInf μ lam η := by
  have hanti : ∀ (ζ : Config d) (a b : ℝ≥0), a ≤ b → surv μ lam b ζ ≤ surv μ lam a ζ :=
    fun ζ a b hab => tsub_le_tsub_left (hc_trans_mono_t μ lam ζ a b hab) 1
  unfold survInf
  rw [ENNReal.iInf_add_iInf (fun i j => ⟨max i j, add_le_add (hanti ξ _ _ (le_max_left i j))
    (hanti η _ _ (le_max_right i j))⟩)]
  exact iInf_mono (fun t => hsubadd t t.2 ξ η)

lemma hc_survInf_card {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ)
    (hsubadd : ∀ t : ℝ, 0 ≤ t → ∀ ξ η : Config d,
      surv μ lam t (ξ ∪ η) ≤ surv μ lam t ξ + surv μ lam t η) (x : Site d) :
    ∀ η : Config d, survInf μ lam η ≤ (η.card : ℝ≥0∞) * survInf μ lam {x} := by
  classical
  intro η
  induction η using Finset.induction_on with
  | empty => rw [hc_survInf_empty]; exact bot_le
  | insert y η' hy ih =>
    have hyx : survInf μ lam {y} = survInf μ lam {x} := by
      have := hc_survInf_map (Equiv.addRight (y - x)) (hc_translate_ok (y - x)) μ lam {x}
      rw [Finset.map_singleton] at this
      simpa using this
    rw [Finset.insert_eq]
    calc survInf μ lam ({y} ∪ η') ≤ survInf μ lam {y} + survInf μ lam η' :=
          hc_survInf_subadd μ lam hsubadd _ _
      _ ≤ survInf μ lam {x} + (η'.card : ℝ≥0∞) * survInf μ lam {x} := by rw [hyx]; gcongr
      _ = _ := by
          rw [← Finset.insert_eq, Finset.card_insert_of_notMem hy]; push_cast; ring

theorem first_step_display_core {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (h0 : lam 0 = 0) (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsubadd : ∀ t : ℝ, 0 ≤ t → ∀ ξ η : Config d,
      surv μ lam t (ξ ∪ η) ≤ surv μ lam t ξ + surv μ lam t η) :
    ∀ (n : ℕ), 1 ≤ n → ∀ x : Site d,
      (survInf μ lam {x} =
          ∑' η : Config d, ENNReal.ofReal (jumpPow μ lam n {x} η) * survInf μ lam η) ∧
        survInf μ lam {x} ≤
          survInf μ lam {x} *
            ∑' η : Config d, ENNReal.ofReal (jumpPow μ lam n {x} η) * (η.card : ℝ≥0∞) := by
  intro n _ x
  have h1 := hc_harmN μ lam hμ hlam n {x}
  refine ⟨h1, ?_⟩
  calc survInf μ lam {x} = ∑' η : Config d, ENNReal.ofReal (jumpPow μ lam n {x} η) *
        survInf μ lam η := h1
    _ ≤ ∑' η : Config d, ENNReal.ofReal (jumpPow μ lam n {x} η) *
        ((η.card : ℝ≥0∞) * survInf μ lam {x}) :=
        ENNReal.tsum_le_tsum (fun η => mul_le_mul_right (hc_survInf_card μ lam hsubadd x η) _)
    _ = _ := by
        rw [← ENNReal.tsum_mul_left]
        congr 1; funext η; ring

lemma hc_nbr_form {d : ℕ} (x z : Site d) (hz : z ∈ nbrs x) :
    ∃ i : Fin d, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ z = Function.update x i (x i + s) := by
  rw [hc_mem_nbrs_iff] at hz
  have hex : ∃ i, x i ≠ z i := by
    by_contra hne
    push_neg at hne
    simp [hne] at hz
  obtain ⟨i, hi⟩ := hex
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => |x j - z j|) (Finset.mem_univ i)
  rw [hz] at hsplit
  have hpos : 0 < |x i - z i| := abs_pos.mpr (sub_ne_zero.mpr hi)
  have hrest_nn : 0 ≤ ∑ j ∈ Finset.univ.erase i, |x j - z j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hi1 : |x i - z i| = 1 := by omega
  have hrest : ∑ j ∈ Finset.univ.erase i, |x j - z j| = 0 := by omega
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)] at hrest
  refine ⟨i, z i - x i, ?_, ?_⟩
  · rcases (abs_eq (zero_le_one)).mp hi1 with h | h
    · right; omega
    · left; omega
  · funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj]
      have := hrest j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
      rw [abs_eq_zero, sub_eq_zero] at this
      exact this.symm

lemma hc_update_mem_nbrs {d : ℕ} (x : Site d) (i : Fin d) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    Function.update x i (x i + s) ∈ nbrs x := by
  rw [hc_mem_nbrs_iff]
  rw [Finset.sum_eq_single i]
  · simp; rcases hs with h | h <;> simp [h]
  · intro b _ hb; simp [Function.update_of_ne hb]
  · simp

lemma hc_card_nbrs {d : ℕ} (x : Site d) : (nbrs x).card = 2 * d := by
  classical
  apply le_antisymm (hc_card_nbrs_le x)
  have hinj : Function.Injective
      (fun p : Fin d × Bool => Function.update x p.1 (x p.1 + if p.2 then 1 else -1)) := by
    rintro ⟨i, b⟩ ⟨i', b'⟩ h
    simp only at h
    have hii : i = i' := by
      by_contra hne
      have := congrFun h i
      rw [Function.update_self, Function.update_of_ne hne] at this
      split_ifs at this <;> omega
    subst hii
    have := congrFun h i
    simp only [Function.update_self] at this
    cases b <;> cases b' <;> simp_all
  calc 2 * d = (Finset.univ : Finset (Fin d × Bool)).card := by
        simp [Finset.card_univ]; ring
    _ = ((Finset.univ : Finset (Fin d × Bool)).image
        (fun p : Fin d × Bool => Function.update x p.1 (x p.1 + if p.2 then 1 else -1))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (nbrs x).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp hz
        exact hc_update_mem_nbrs x i _ (by cases b <;> simp)

/-- signed coordinate swap about x -/
def hcSig {d : ℕ} (x : Site d) (i j : Fin d) (e : ℤ) (k : Fin d) : ℤ :=
  if k = j ∨ k = i then e else 1

lemma hcSig_mul {d : ℕ} (x : Site d) (i j : Fin d) (e : ℤ) (he : e * e = 1) (k : Fin d) :
    hcSig x i j e k * hcSig x i j e (Equiv.swap i j k) = 1 := by
  unfold hcSig
  by_cases h1 : k = j
  · subst h1; simp [Equiv.swap_apply_right, he]
  · by_cases h2 : k = i
    · subst h2; simp [Equiv.swap_apply_left, he]
    · rw [Equiv.swap_apply_of_ne_of_ne h2 h1]; simp [h1, h2]

def hcIso {d : ℕ} (x : Site d) (i j : Fin d) (e : ℤ) (he : e * e = 1) : Site d ≃ Site d where
  toFun w := fun k => x k + hcSig x i j e k * (w (Equiv.swap i j k) - x (Equiv.swap i j k))
  invFun w := fun k => x k + hcSig x i j e k * (w (Equiv.swap i j k) - x (Equiv.swap i j k))
  left_inv w := by
    funext k
    simp only [Equiv.swap_apply_self, add_sub_cancel_left]
    have := hcSig_mul x i j e he k
    linear_combination (w k - x k) * this
  right_inv w := by
    funext k
    simp only [Equiv.swap_apply_self, add_sub_cancel_left]
    have := hcSig_mul x i j e he k
    linear_combination (w k - x k) * this

lemma hcIso_ok {d : ℕ} (x : Site d) (i j : Fin d) (e : ℤ) (he : e * e = 1) :
    ∀ a b, (hcIso x i j e he) b ∈ nbrs ((hcIso x i j e he) a) ↔ b ∈ nbrs a := by
  intro a b
  rw [hc_mem_nbrs_iff, hc_mem_nbrs_iff]
  have habs : ∀ k, |hcSig x i j e k| = 1 := by
    intro k; unfold hcSig
    split_ifs
    · have : |e| * |e| = 1 := by rw [← abs_mul, he]; rfl
      nlinarith [abs_nonneg e]
    · rfl
  have : ∑ k, |(hcIso x i j e he) a k - (hcIso x i j e he) b k| = ∑ k, |a k - b k| := by
    simp only [hcIso, Equiv.coe_fn_mk]
    have h2 : ∀ k, |x k + hcSig x i j e k * (a (Equiv.swap i j k) - x (Equiv.swap i j k)) -
        (x k + hcSig x i j e k * (b (Equiv.swap i j k) - x (Equiv.swap i j k)))| =
        |a (Equiv.swap i j k) - b (Equiv.swap i j k)| := by
      intro k
      rw [show x k + hcSig x i j e k * (a (Equiv.swap i j k) - x (Equiv.swap i j k)) -
        (x k + hcSig x i j e k * (b (Equiv.swap i j k) - x (Equiv.swap i j k))) =
        hcSig x i j e k * (a (Equiv.swap i j k) - b (Equiv.swap i j k)) by ring, abs_mul, habs,
        one_mul]
    simp only [h2]
    exact Equiv.sum_comp (Equiv.swap i j) (fun k => |a k - b k|)
  rw [this]

lemma hc_pair_inv {d : ℕ} (l : ℝ) (x y z : Site d) (hy : y ∈ nbrs x) (hz : z ∈ nbrs x) :
    survInf 1 (fun k => (k : ℝ) * l) (insert z {x}) =
      survInf 1 (fun k => (k : ℝ) * l) ({x, y} : Config d) := by
  classical
  obtain ⟨i, s, hs, rfl⟩ := hc_nbr_form x z hz
  obtain ⟨j, s', hs', rfl⟩ := hc_nbr_form x y hy
  have he : (s * s') * (s * s') = 1 := by
    rcases hs with h | h <;> rcases hs' with h' | h' <;> simp [h, h']
  have hmap := hc_survInf_map (hcIso x i j (s * s') he) (hcIso_ok x i j (s * s') he) 1
    (fun k => (k : ℝ) * l) (insert (Function.update x i (x i + s)) {x})
  rw [← hmap]
  congr 1
  rw [Finset.map_insert, Finset.map_singleton, Finset.pair_comm]
  congr 1
  · funext k
    simp [hcIso]
  · congr 1
    funext k
    simp only [Equiv.coe_toEmbedding, hcIso, Equiv.coe_fn_mk]
    by_cases hk : k = j
    · subst hk
      simp only [Equiv.swap_apply_right, Function.update_self, add_sub_cancel_left]
      unfold hcSig
      simp only [true_or, if_true]
      rcases hs with h | h <;> rcases hs' with h' | h' <;> simp [h, h']
    · rw [Function.update_of_ne hk]
      have hsk : Equiv.swap i j k ≠ i := by
        intro h; apply hk
        have := congrArg (Equiv.swap i j) h
        rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
        exact this
      rw [Function.update_of_ne hsk]; ring

theorem eq_7_2_core {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) :
    ∀ x y : Site d, ∑ i, |x i - y i| = 1 →
      survInf 1 (fun k => (k : ℝ) * l) {x} =
        ENNReal.ofReal (2 * d * l / (1 + 2 * d * l)) *
          survInf 1 (fun k => (k : ℝ) * l) {x, y} := by
  classical
  intro x y hxy
  have hy : y ∈ nbrs x := (hc_mem_nbrs_iff x y).mpr hxy
  set lam : ℕ → ℝ := fun k => (k : ℝ) * l with hlamdef
  have hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k := fun k _ => by simp only [hlamdef]; positivity
  have hbdry : bdry ({x} : Config d) = nbrs x := by
    unfold bdry
    rw [Finset.singleton_biUnion]
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, fun hzx => hc_not_mem_nbrs_self x (hzx ▸ h)⟩
  have hocc : ∀ z ∈ nbrs x, occ ({x} : Config d) z = 1 := by
    intro z hz
    unfold occ
    rw [Finset.singleton_inter_of_mem ((hc_nbrs_symm x z).mp hz)]
    rfl
  have hq : exitRate 1 lam ({x} : Config d) = 1 + 2 * d * l := by
    unfold exitRate
    rw [hbdry, Finset.sum_congr rfl (fun z hz => by rw [hocc z hz])]
    simp [hlamdef, hc_card_nbrs]
  have hqpos : 0 < exitRate 1 lam ({x} : Config d) := by rw [hq]; positivity
  have hfin : ∀ ζ : Config d, survInf 1 lam ζ ≠ ∞ := fun ζ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (by
      rw [hc_survInf_eq]; exact tsub_le_self)
  set g : Config d → ℝ := fun ζ => (survInf 1 lam ζ).toReal with hg
  have hg0 : ∀ ζ, 0 ≤ g ζ := fun ζ => ENNReal.toReal_nonneg
  have hgS : ∀ ζ, survInf 1 lam ζ = ENNReal.ofReal (g ζ) := fun ζ =>
    (ENNReal.ofReal_toReal (hfin ζ)).symm
  rw [hc_harm1 1 lam zero_le_one hlam {x}]
  have hj : ∀ ζ, jump 1 lam {x} ζ = rate 1 lam {x} ζ / exitRate 1 lam {x} :=
    fun ζ => by simp [jump, hqpos.ne']
  simp only [hj]
  rw [Finset.sum_insert_zero (by rw [hc_rate_self, zero_div, ENNReal.ofReal_zero, zero_mul])]
  simp only [hgS]
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [show (∑ ζ ∈ succ ({x} : Config d), ENNReal.ofReal (rate 1 lam {x} ζ / exitRate 1 lam {x}) *
      ENNReal.ofReal (g ζ)) = ENNReal.ofReal (∑ ζ ∈ succ ({x} : Config d),
        rate 1 lam {x} ζ / exitRate 1 lam {x} * g ζ) by
    rw [ENNReal.ofReal_sum_of_nonneg (fun ζ _ => mul_nonneg (div_nonneg
      (hc_rate_nonneg 1 lam zero_le_one hlam _ ζ) hqpos.le) (hg0 ζ))]
    exact Finset.sum_congr rfl (fun ζ _ => (ENNReal.ofReal_mul (div_nonneg
      (hc_rate_nonneg 1 lam zero_le_one hlam _ ζ) hqpos.le)).symm)]
  congr 1
  have h1 : ∑ ζ ∈ succ ({x} : Config d), rate 1 lam {x} ζ / exitRate 1 lam {x} * g ζ =
      (1 / exitRate 1 lam {x}) * ∑ ζ ∈ succ ({x} : Config d), rate 1 lam {x} ζ * g ζ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ζ _ => by ring)
  have hge : g ∅ = 0 := by simp [hg, hc_survInf_empty]
  have hpair : ∀ z ∈ nbrs x, g (insert z {x}) = g {x, y} := by
    intro z hz; simp only [hg]; rw [hc_pair_inv l x y z hy hz]
  rw [h1, hc_sum_rate_mul, hbdry, Finset.sum_singleton, Finset.erase_singleton, hge]
  have hs2 : ∑ z ∈ nbrs x, lam (occ {x} z) * g (insert z {x}) =
      ∑ z ∈ nbrs x, l * g {x, y} :=
    Finset.sum_congr rfl (fun z hz => by rw [hocc z hz, hpair z hz]; simp [hlamdef])
  rw [hs2, Finset.sum_const, hc_card_nbrs, hq]
  simp only [nsmul_eq_mul, mul_zero, zero_add]
  push_cast
  field_simp

end HarrisContact.Extinction

open HarrisContact.Extinction


theorem solution {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) :
    ∀ x y : Site d, ∑ i, |x i - y i| = 1 →
      survInf 1 (fun k => (k : ℝ) * l) {x} =
        ENNReal.ofReal (2 * d * l / (1 + 2 * d * l)) * survInf 1 (fun k => (k : ℝ) * l) {x, y} := by
  exact eq_7_2_core hd l hl
