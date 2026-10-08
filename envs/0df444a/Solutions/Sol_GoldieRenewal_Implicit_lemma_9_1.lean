-- Prove2me | solution 1 for GoldieRenewal.Implicit.lemma_9_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:30:05.642687+00:00
-- url     : https://prove2.me/submissions/1e62f989-37ab-4874-b252-500a34a31b70

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_DRi
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GoldieRenewal.Implicit

lemma cellIco_disjoint (h : ℝ) (hh : 0 < h) :
    Pairwise (Function.onFun Disjoint (fun n : ℤ => Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h))) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro x hx1 hx2
  simp only [Set.mem_Ico] at hx1 hx2
  have h1 : (m:ℝ) < n + 1 := by
    by_contra hc; push_neg at hc
    have : ((n:ℝ) + 1) * h ≤ m * h := mul_le_mul_of_nonneg_right hc hh.le
    linarith
  have h2 : (n:ℝ) < m + 1 := by
    by_contra hc; push_neg at hc
    have : ((m:ℝ) + 1) * h ≤ n * h := mul_le_mul_of_nonneg_right hc hh.le
    linarith
  have h1' : m < n + 1 := by exact_mod_cast h1
  have h2' : n < m + 1 := by exact_mod_cast h2
  omega

lemma cellIco_iUnion (h : ℝ) (hh : 0 < h) :
    (⋃ n : ℤ, Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rw [Set.mem_iUnion]
  refine ⟨⌊x / h⌋, ?_, ?_⟩
  · have := Int.floor_le (x / h)
    rwa [le_div_iff₀ hh] at this
  · have := Int.lt_floor_add_one (x / h)
    rwa [div_lt_iff₀ hh] at this

lemma tsum_cellIco (f : ℝ → ℝ) (h : ℝ) (hh : 0 < h) :
    ∑' n : ℤ, ∫⁻ x in Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h), ENNReal.ofReal (f x) =
      ∫⁻ x, ENNReal.ofReal (f x) := by
  rw [← lintegral_iUnion (fun n => measurableSet_Ico) (cellIco_disjoint h hh), cellIco_iUnion h hh,
    Measure.restrict_univ]

lemma lintegral_ge_const_mul (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) (c : ℝ)
    (hc : ∀ x ∈ s, c ≤ f x) :
    ENNReal.ofReal c * volume s ≤ ∫⁻ x in s, ENNReal.ofReal (f x) := by
  have : ∫⁻ x in s, ENNReal.ofReal c ≤ ∫⁻ x in s, ENNReal.ofReal (f x) :=
    setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hc x hx))
  rwa [setLIntegral_const] at this

theorem lemma_9_1_core (f : ℝ → ℝ) (hf_nonneg : ∀ t, 0 ≤ f t) (hf_int : Integrable f)
    (θ : ℝ → ℝ) (hθ : Tendsto θ (𝓝[>] 0) (𝓝 1))
    (hshift : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, θ ε * f t ≤ f (t + ε)) :
    IsDRi f := by
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (f x) with hI
  have hI_fin : I < ∞ := by
    have := hf_int.hasFiniteIntegral
    refine lt_of_eq_of_lt ?_ this
    apply lintegral_congr; intro x
    rw [Real.enorm_eq_ofReal (hf_nonneg x)]
  have hθδ : ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ → 1 - δ ≤ θ ε := by
    intro δ hδ
    have : Set.Ioi (1 - δ) ∈ 𝓝 (1:ℝ) := Ioi_mem_nhds (by linarith)
    have h2 := hθ this
    rw [Filter.mem_map, mem_nhdsGT_iff_exists_Ioo_subset] at h2
    obtain ⟨u, hu, hsub⟩ := h2
    refine ⟨u, hu, fun ε hε hεu => ?_⟩
    have := hsub ⟨hε, hεu⟩
    exact le_of_lt this
  have hshift' : ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ x z : ℝ, x ≤ z → z - x < ε₀ → (1 - δ) * f x ≤ f z := by
    intro δ hδ
    obtain ⟨ε₀, hε₀, hθ'⟩ := hθδ δ hδ
    refine ⟨ε₀, hε₀, fun x z hxz hzx => ?_⟩
    rcases eq_or_lt_of_le hxz with heq | hlt
    · subst heq; nlinarith [hf_nonneg x]
    · have h1 := hshift (z - x) (by linarith) x
      rw [add_sub_cancel] at h1
      have h2 := hθ' (z - x) (by linarith) hzx
      nlinarith [hf_nonneg x]
  set J : ℝ → ℤ → ℝ≥0∞ := fun h n =>
    ∫⁻ x in Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h), ENNReal.ofReal (f x) with hJ
  have hJsum : ∀ h : ℝ, 0 < h → ∑' n : ℤ, J h n = I := fun h hh => tsum_cellIco f h hh
  have hJsum' : ∀ h : ℝ, 0 < h → ∑' n : ℤ, J h (n + 1) = I := by
    intro h hh
    rw [← hJsum h hh]
    exact (Equiv.addRight (1:ℤ)).tsum_eq (fun n => J h n)
  constructor
  · intro h hh
    obtain ⟨ε₀, hε₀, hsh⟩ := hshift' (1/2) (by norm_num)
    set ε₁ := min h ε₀ / 2 with hε₁
    have hmin : 0 < min h ε₀ := lt_min hh hε₀
    have hε₁pos : 0 < ε₁ := by positivity
    have hε₁h : ε₁ ≤ h := by have := min_le_left h ε₀; linarith
    have hε₁ε₀ : ε₁ < ε₀ := by have := min_le_right h ε₀; linarith
    have hpt : ∀ n : ℤ, ∀ x ∈ cell h n,
        ENNReal.ofReal |f x| * ENNReal.ofReal ((1/2) * ε₁) ≤ J h n + J h (n+1) := by
      intro n x hx
      rw [abs_of_nonneg (hf_nonneg x)]
      have h1 : ENNReal.ofReal ((1/2) * f x) * volume (Set.Ioo x (x + ε₁)) ≤
          ∫⁻ z in Set.Ioo x (x + ε₁), ENNReal.ofReal (f z) :=
        lintegral_ge_const_mul f _ measurableSet_Ioo _ (fun z hz => by
          have := hsh x z hz.1.le (by linarith [hz.2]); linarith)
      rw [Real.volume_Ioo, add_sub_cancel_left] at h1
      have h2 : ∫⁻ z in Set.Ioo x (x + ε₁), ENNReal.ofReal (f z) ≤
          ∫⁻ z in Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1 + 1) * h), ENNReal.ofReal (f z) := by
        apply lintegral_mono_set
        intro z hz
        simp only [cell, Set.mem_Icc] at hx
        simp only [Set.mem_Ioo] at hz
        constructor <;> nlinarith
      have h3 : ∫⁻ z in Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1 + 1) * h), ENNReal.ofReal (f z) =
          J h n + J h (n+1) := by
        rw [← Set.Ico_union_Ico_eq_Ico (b := ((n:ℝ) + 1) * h) (by nlinarith) (by nlinarith),
          lintegral_union measurableSet_Ico Set.Ico_disjoint_Ico_same]
        simp only [hJ, Int.cast_add, Int.cast_one]
      calc ENNReal.ofReal (f x) * ENNReal.ofReal ((1/2) * ε₁)
          = ENNReal.ofReal ((1/2) * f x) * ENNReal.ofReal ε₁ := by
            rw [← ENNReal.ofReal_mul (hf_nonneg x),
              ← ENNReal.ofReal_mul (by linarith [hf_nonneg x])]
            congr 1; ring
        _ ≤ _ := h1
        _ ≤ _ := h2
        _ = _ := h3
    set c : ℝ≥0∞ := ENNReal.ofReal ((1/2) * ε₁) with hc
    have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
    have hsup : ∀ n : ℤ, cellSupAbs f h n ≤ (J h n + J h (n+1)) / c := by
      intro n
      unfold cellSupAbs
      apply iSup₂_le
      intro x hx
      exact (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hcT)).2 (hpt n x hx)
    calc ∑' n : ℤ, cellSupAbs f h n ≤ ∑' n : ℤ, (J h n + J h (n+1)) / c :=
          ENNReal.tsum_le_tsum hsup
      _ = (∑' n : ℤ, (J h n + J h (n+1))) / c := by
          simp only [div_eq_mul_inv]; rw [ENNReal.tsum_mul_right]
      _ = (I + I) / c := by rw [ENNReal.tsum_add, hJsum h hh, hJsum' h hh]
      _ < ∞ := ENNReal.div_lt_top (by finiteness) hc0
  · rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    set I' := I.toReal with hI'
    have hI'0 : 0 ≤ I' := ENNReal.toReal_nonneg
    obtain ⟨δ, hδ0, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ENNReal.ofReal (δ / (1 - δ)) * I ≤ ε := by
      rcases eq_or_ne ε ⊤ with hT | hT
      · exact ⟨1/2, by norm_num, by norm_num, by rw [hT]; exact le_top⟩
      · have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hT
        refine ⟨min (1/2) (ε.toReal / (2 * (I' + 1))), lt_min (by norm_num) (by positivity), ?_, ?_⟩
        · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
        · set δ := min (1/2) (ε.toReal / (2 * (I' + 1))) with hδ
          have hδa : δ ≤ 1/2 := min_le_left _ _
          have hδb : δ ≤ ε.toReal / (2 * (I' + 1)) := min_le_right _ _
          have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
          have hIeq : I = ENNReal.ofReal I' := (ENNReal.ofReal_toReal hI_fin.ne).symm
          rw [hIeq, ← ENNReal.ofReal_mul (div_nonneg hδ0.le (by linarith)), ← ENNReal.ofReal_toReal hT]
          apply ENNReal.ofReal_le_ofReal
          have h1 : δ / (1 - δ) ≤ 2 * δ := by
            rw [div_le_iff₀ (by linarith)]; nlinarith
          have h2 : 2 * δ * (I' + 1) ≤ ε.toReal := by
            rw [le_div_iff₀ (by positivity)] at hδb; linarith
          calc δ / (1 - δ) * I' ≤ 2 * δ * I' := mul_le_mul_of_nonneg_right h1 hI'0
            _ ≤ 2 * δ * (I' + 1) := by nlinarith
            _ ≤ ε.toReal := h2
    obtain ⟨ε₀, hε₀, hsh⟩ := hshift' δ hδ0
    have hmem : Set.Ioo (0:ℝ) (ε₀ / 2) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hmem] with h hh
    obtain ⟨hh0, hhε⟩ := hh
    have h1δ : 0 < 1 - δ := by linarith
    set a : ℤ → ℝ := fun n => sInf (f '' cell h n) with ha
    have hcell_ne : ∀ n : ℤ, (cell h n).Nonempty := fun n =>
      ⟨(n:ℝ) * h, by simp only [cell, Set.mem_Icc]; constructor <;> nlinarith⟩
    have hbdd : ∀ n : ℤ, BddBelow (f '' cell h n) := fun n =>
      ⟨0, by rintro _ ⟨x, _, rfl⟩; exact hf_nonneg x⟩
    have ha_le : ∀ n : ℤ, ∀ x ∈ cell h n, a n ≤ f x := fun n x hx =>
      csInf_le (hbdd n) ⟨x, hx, rfl⟩
    have ha_nonneg : ∀ n : ℤ, 0 ≤ a n := fun n =>
      le_csInf ((hcell_ne n).image f) (by rintro _ ⟨x, _, rfl⟩; exact hf_nonneg x)
    have hsupa : ∀ n : ℤ, ∀ x ∈ cell h n, (1 - δ) * f x ≤ a (n+1) := by
      intro n x hx
      apply le_csInf ((hcell_ne (n+1)).image f)
      rintro _ ⟨z, hz, rfl⟩
      simp only [cell, Set.mem_Icc] at hx hz
      push_cast at hz
      have e1 : ((n:ℝ) + 1 + 1) * h = n * h + 2 * h := by ring
      apply hsh x z (by linarith) (by linarith)
    have hO_nonneg : ∀ n : ℤ, 0 ≤ a (n+1) / (1 - δ) - a n := by
      intro n
      obtain ⟨x, hx⟩ := hcell_ne n
      have h1 := hsupa n x hx
      have h2 := ha_le n x hx
      rw [sub_nonneg, le_div_iff₀ h1δ]
      nlinarith
    have hosc : ∀ n : ℤ, cellOsc f h n ≤ ENNReal.ofReal (a (n+1) / (1 - δ) - a n) := by
      intro n
      unfold cellOsc
      apply iSup₂_le; intro x hx
      apply iSup₂_le; intro y hy
      apply ENNReal.ofReal_le_ofReal
      have h1 := hsupa n x hx
      have h2 := ha_le n y hy
      have h3 : f x ≤ a (n+1) / (1 - δ) := by rw [le_div_iff₀ h1δ]; linarith
      linarith
    set A : ℝ≥0∞ := ∑' n : ℤ, ENNReal.ofReal (a n) with hA
    have hhA : ENNReal.ofReal h * A ≤ I := by
      rw [hA, ← ENNReal.tsum_mul_left, ← hJsum h hh0]
      apply ENNReal.tsum_le_tsum
      intro n
      have := lintegral_ge_const_mul f (Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h)) measurableSet_Ico
        (a n) (fun x hx => ha_le n x (Set.Ico_subset_Icc_self hx))
      rw [Real.volume_Ico] at this
      rw [mul_comm]
      convert this using 2
      congr 1; ring
    have hA_fin : A < ∞ := by
      have hh' : ENNReal.ofReal h ≠ 0 := (ENNReal.ofReal_pos.2 hh0).ne'
      rw [mul_comm] at hhA
      have := (ENNReal.le_div_iff_mul_le (Or.inl hh') (Or.inl ENNReal.ofReal_ne_top)).2 hhA
      exact lt_of_le_of_lt this (ENNReal.div_lt_top hI_fin.ne hh')
    have htel : ∑' n : ℤ, ENNReal.ofReal (a (n+1) / (1 - δ) - a n) + A =
        ENNReal.ofReal (1 / (1 - δ)) * A := by
      rw [hA, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      have : ∀ n : ℤ, ENNReal.ofReal (a (n+1) / (1 - δ) - a n) + ENNReal.ofReal (a n) =
          ENNReal.ofReal (1 / (1 - δ)) * ENNReal.ofReal (a (n+1)) := by
        intro n
        rw [← ENNReal.ofReal_add (hO_nonneg n) (ha_nonneg n),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
      simp_rw [this]
      exact (Equiv.addRight (1:ℤ)).tsum_eq
        (fun n => ENNReal.ofReal (1 / (1 - δ)) * ENNReal.ofReal (a n))
    have hOsum : ∑' n : ℤ, ENNReal.ofReal (a (n+1) / (1 - δ) - a n) ≤
        ENNReal.ofReal (δ / (1 - δ)) * A := by
      have h1 : ∑' n : ℤ, ENNReal.ofReal (a (n+1) / (1 - δ) - a n) =
          ENNReal.ofReal (1 / (1 - δ)) * A - A :=
        ENNReal.eq_sub_of_add_eq hA_fin.ne htel
      rw [h1]
      have h2 : ENNReal.ofReal (1 / (1 - δ)) * A - A = (ENNReal.ofReal (1 / (1 - δ)) - 1) * A := by
        rw [ENNReal.sub_mul (fun _ _ => hA_fin.ne), one_mul]
      rw [h2]
      gcongr
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ zero_le_one]
      apply ENNReal.ofReal_le_ofReal
      rw [div_sub_one h1δ.ne']
      apply le_of_eq; congr 1; ring
    calc ENNReal.ofReal h * ∑' n : ℤ, cellOsc f h n
        ≤ ENNReal.ofReal h * ∑' n : ℤ, ENNReal.ofReal (a (n+1) / (1 - δ) - a n) :=
          by gcongr with n; exact hosc n
      _ ≤ ENNReal.ofReal h * (ENNReal.ofReal (δ / (1 - δ)) * A) := by gcongr
      _ = ENNReal.ofReal (δ / (1 - δ)) * (ENNReal.ofReal h * A) := by ring
      _ ≤ ENNReal.ofReal (δ / (1 - δ)) * I := by gcongr
      _ ≤ ε := hδε

end GoldieRenewal.Implicit

open GoldieRenewal.Implicit


theorem solution (f : ℝ → ℝ) (hf_nonneg : ∀ t, 0 ≤ f t) (hf_int : Integrable f)
    (θ : ℝ → ℝ) (hθ : Tendsto θ (𝓝[>] 0) (𝓝 1))
    (hshift : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, θ ε * f t ≤ f (t + ε)) :
    IsDRi f := by
  exact lemma_9_1_core f hf_nonneg hf_int θ hθ hshift
