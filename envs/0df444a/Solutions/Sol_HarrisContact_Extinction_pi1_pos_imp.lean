-- Prove2me | solution 1 for HarrisContact.Extinction.pi1_pos_imp
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:53:31.60779+00:00
-- url     : https://prove2.me/submissions/655e0e27-f8de-479d-b38f-2fd12ba96cbb

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

end HarrisContact.Extinction

open HarrisContact.Extinction


theorem solution {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) :
    ∀ x : Site d, 0 < survInf 1 (fun k => (k : ℝ) * l) {x} → 1 ≤ (2 * (d : ℝ) - 1) * l := by
  exact pi1_pos_imp_core hd l hl
