-- Prove2me | solution 1 for GoldieRenewal.Implicit.lemma_9_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:33:22.196972+00:00
-- url     : https://prove2.me/submissions/de854123-b55c-4b61-a755-fc137cb73306

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_DRi
open MeasureTheory
open MeasureTheory Filter Topology
open scoped ENNReal Convolution

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


lemma tsum_cellIco' (g : ℝ → ℝ≥0∞) (h : ℝ) (hh : 0 < h) :
    ∑' n : ℤ, ∫⁻ x in Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h), g x = ∫⁻ x, g x := by
  rw [← lintegral_iUnion (fun n => measurableSet_Ico) (cellIco_disjoint h hh), cellIco_iUnion h hh,
    Measure.restrict_univ]

/-- the exponential kernel `e^{-y} 1_{y ≥ 0}` -/
noncomputable def kerE (y : ℝ) : ℝ := if 0 ≤ y then Real.exp (-y) else 0

lemma kerE_nonneg (y : ℝ) : 0 ≤ kerE y := by
  unfold kerE; split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

lemma kerE_le_one (y : ℝ) : kerE y ≤ 1 := by
  unfold kerE; split_ifs with h
  · rw [Real.exp_le_one_iff]; linarith
  · exact zero_le_one

lemma kerE_measurable : Measurable kerE :=
  Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

lemma kerE_integrable : Integrable kerE := by
  have : kerE = Set.indicator (Set.Ici 0) (fun y => Real.exp (-y)) := by
    ext y; simp [kerE, Set.indicator]
  rw [this, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_neg_Ioi 0

lemma kerE_shift (y ε : ℝ) (hε : 0 ≤ ε) : Real.exp (-ε) * kerE y ≤ kerE (y + ε) := by
  unfold kerE
  split_ifs with h1 h2 h2
  · rw [← Real.exp_add]; apply le_of_eq; congr 1; ring
  · exfalso; apply h2; linarith
  · rw [mul_zero]; exact (Real.exp_pos _).le
  · rw [mul_zero]

theorem lemma_9_2_core (f : ℝ → ℝ) (hf : Integrable f) : IsDRi (smooth f) := by
  set S : ℝ → ℝ := fun t => ∫ u, |f u| * kerE (t - u) with hS
  have hfa : Integrable (fun u => |f u|) := hf.abs
  have hkm : ∀ t : ℝ, Measurable (fun u => kerE (t - u)) := fun t =>
    kerE_measurable.comp (measurable_const.sub measurable_id)
  have hint : ∀ t : ℝ, Integrable (fun u => |f u| * kerE (t - u)) := by
    intro t
    refine hfa.mono' (hfa.aestronglyMeasurable.mul (hkm t).aestronglyMeasurable) ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (kerE_nonneg _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (kerE_le_one _)
  have hint' : ∀ t : ℝ, Integrable (fun u => f u * kerE (t - u)) := by
    intro t
    refine hfa.mono' (hf.aestronglyMeasurable.mul (hkm t).aestronglyMeasurable) ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kerE_nonneg _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (kerE_le_one _)
  have hS_nonneg : ∀ t, 0 ≤ S t := fun t =>
    integral_nonneg (fun u => mul_nonneg (abs_nonneg _) (kerE_nonneg _))
  have hsmooth_eq : ∀ t, smooth f t = ∫ u, f u * kerE (t - u) := by
    intro t
    unfold smooth
    rw [← integral_indicator measurableSet_Iic]
    congr 1; ext u
    simp only [Set.indicator, Set.mem_Iic, kerE]
    by_cases hu : u ≤ t
    · simp [hu, show 0 ≤ t - u by linarith, mul_comm]
    · simp [hu, show ¬ (0 ≤ t - u) by intro h; exact hu (by linarith)]
  have hsmooth_le : ∀ t, |smooth f t| ≤ S t := by
    intro t
    rw [hsmooth_eq, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; ext u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kerE_nonneg _)]
  have hS_int : Integrable S := by
    have : S = (fun u => |f u|) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] kerE := by
      ext t; rw [hS]; simp only; rw [convolution_lsmul]; rfl
    rw [this]
    exact hfa.integrable_convolution _ kerE_integrable
  have hS_shift : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, Real.exp (-ε) * S t ≤ S (t + ε) := by
    intro ε hε t
    rw [hS]; simp only
    rw [← integral_const_mul]
    apply integral_mono ((hint t).const_mul _) (hint (t + ε))
    intro u
    simp only
    have := kerE_shift (t - u) ε hε.le
    rw [show t + ε - u = t - u + ε by ring]
    calc Real.exp (-ε) * (|f u| * kerE (t - u)) = |f u| * (Real.exp (-ε) * kerE (t - u)) := by ring
      _ ≤ |f u| * kerE (t - u + ε) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hθ : Tendsto (fun ε : ℝ => Real.exp (-ε)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun ε : ℝ => Real.exp (-ε)) (𝓝 0) (𝓝 (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).tendsto 0
    rw [neg_zero, Real.exp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hSdri : IsDRi S := lemma_9_1_core S hS_nonneg hS_int _ hθ hS_shift
  have hsupS : ∀ h n, cellSupAbs (smooth f) h n ≤ cellSupAbs S h n := by
    intro h n; unfold cellSupAbs
    refine iSup₂_mono fun x hx => ?_
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonneg (hS_nonneg x)]; exact hsmooth_le x
  -- oscillation estimate
  have hosc_est : ∀ s t : ℝ, s ≤ t →
      |smooth f t - smooth f s| ≤ (1 - Real.exp (-(t - s))) * S s + ∫ u in Set.Ioc s t, |f u| := by
    intro s t hst
    rw [hsmooth_eq, hsmooth_eq, ← Real.norm_eq_abs, ← integral_sub (hint' t) (hint' s)]
    set g : ℝ → ℝ := fun u => (1 - Real.exp (-(t - s))) * (|f u| * kerE (s - u)) +
      (Set.Ioc s t).indicator (fun u => |f u|) u with hg
    have hg_int : Integrable g := ((hint s).const_mul _).add (hfa.indicator measurableSet_Ioc)
    have hexp1 : Real.exp (-(t - s)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have hbound : ∀ u, ‖f u * kerE (t - u) - f u * kerE (s - u)‖ ≤ g u := by
      intro u
      rw [hg]; simp only
      rw [← mul_sub, Real.norm_eq_abs, abs_mul]
      unfold kerE
      by_cases hu1 : u ≤ s
      · have h1 : 0 ≤ t - u := by linarith
        have h2 : 0 ≤ s - u := by linarith
        simp only [h1, h2, if_true, Set.indicator, Set.mem_Ioc]
        rw [if_neg (by intro h; linarith [h.1])]
        have : Real.exp (-(t - u)) = Real.exp (-(t - s)) * Real.exp (-(s - u)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this, abs_of_nonpos (a := Real.exp (-(t - s)) * Real.exp (-(s - u)) - Real.exp (-(s - u)))
          (by nlinarith [Real.exp_pos (-(s - u))])]
        apply le_of_eq; ring
      · by_cases hu2 : u ≤ t
        · have h1 : 0 ≤ t - u := by linarith
          have h2 : ¬ (0 ≤ s - u) := by intro h; exact hu1 (by linarith)
          simp only [h1, h2, if_true, if_false, sub_zero, Set.indicator, Set.mem_Ioc, mul_zero, zero_add]
          rw [if_pos ⟨not_le.1 hu1, hu2⟩, abs_of_pos (Real.exp_pos _)]
          have : Real.exp (-(t - u)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
          exact mul_le_of_le_one_right (abs_nonneg _) this
        · have h1 : ¬ (0 ≤ t - u) := by intro h; exact hu2 (by linarith)
          have h2 : ¬ (0 ≤ s - u) := by intro h; exact hu1 (by linarith)
          simp only [h1, h2, if_false, sub_zero, abs_zero, mul_zero, Set.indicator, Set.mem_Ioc,
            zero_add]
          split_ifs <;> simp [abs_nonneg]
    calc ‖∫ u, (f u * kerE (t - u) - f u * kerE (s - u))‖ ≤ ∫ u, g u :=
          norm_integral_le_of_norm_le hg_int (Filter.Eventually.of_forall hbound)
      _ = (1 - Real.exp (-(t - s))) * S s + ∫ u in Set.Ioc s t, |f u| := by
        rw [hg, integral_add ((hint s).const_mul _) (hfa.indicator measurableSet_Ioc),
          integral_const_mul, integral_indicator measurableSet_Ioc]
  -- the two finite totals
  set If : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal |f x| with hIf
  have hIf_fin : If < ∞ := by
    have := hf.hasFiniteIntegral
    refine lt_of_eq_of_lt ?_ this
    apply lintegral_congr; intro x
    rw [Real.enorm_eq_ofReal_abs]
  set IS : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (S x) with hIS
  have hIS_fin : IS < ∞ := by
    have := hS_int.hasFiniteIntegral
    refine lt_of_eq_of_lt ?_ this
    apply lintegral_congr; intro x
    rw [Real.enorm_eq_ofReal (hS_nonneg x)]
  constructor
  · intro h hh
    exact lt_of_le_of_lt (ENNReal.tsum_le_tsum (hsupS h)) (hSdri.1 h hh)
  · -- main bound for h > 0
    have hmain : ∀ h : ℝ, 0 < h →
        ENNReal.ofReal h * ∑' n : ℤ, cellOsc (smooth f) h n ≤
          ENNReal.ofReal (1 - Real.exp (-h)) * (ENNReal.ofReal h * ∑' n : ℤ, cellOsc S h n + IS) +
            ENNReal.ofReal h * If := by
      intro h hh
      -- J n
      set J : ℤ → ℝ := fun n => ∫ u in cell h n, |f u| with hJ
      have hJsum : ∑' n : ℤ, ENNReal.ofReal (J n) = If := by
        rw [hIf, ← tsum_cellIco' (fun x => ENNReal.ofReal |f x|) h hh]
        congr 1; ext n
        rw [hJ]; simp only
        rw [ofReal_integral_eq_lintegral_ofReal hfa.integrableOn
          (Filter.Eventually.of_forall (fun u => abs_nonneg _))]
        unfold cell
        rw [Measure.restrict_congr_set Ico_ae_eq_Icc]
      -- osc bound per cell
      have hexph : Real.exp (-h) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      have hosc : ∀ n : ℤ, cellOsc (smooth f) h n ≤
          ENNReal.ofReal (1 - Real.exp (-h)) * cellSupAbs S h n + ENNReal.ofReal (J n) := by
        intro n
        unfold cellOsc
        refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
        -- generic claim for s ≤ t both in the cell
        have key : ∀ s t : ℝ, s ∈ cell h n → t ∈ cell h n → s ≤ t →
            ENNReal.ofReal |smooth f t - smooth f s| ≤
              ENNReal.ofReal (1 - Real.exp (-h)) * cellSupAbs S h n + ENNReal.ofReal (J n) := by
          intro s t hs ht hst
          have e1 := hosc_est s t hst
          have hts : t - s ≤ h := by
            simp only [cell, Set.mem_Icc] at hs ht; linarith
          have e2 : Real.exp (-h) ≤ Real.exp (-(t - s)) := Real.exp_le_exp.2 (by linarith)
          have e3 : (1 - Real.exp (-(t - s))) * S s ≤ (1 - Real.exp (-h)) * S s :=
            mul_le_mul_of_nonneg_right (by linarith) (hS_nonneg s)
          have e4 : ∫ u in Set.Ioc s t, |f u| ≤ J n := by
            rw [hJ]; simp only
            apply setIntegral_mono_set hfa.integrableOn
              (Filter.Eventually.of_forall (fun u => abs_nonneg _))
            refine Filter.Eventually.of_forall ?_
            intro u hu
            simp only [cell, Set.mem_Icc] at hs ht ⊢
            exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
          calc ENNReal.ofReal |smooth f t - smooth f s|
              ≤ ENNReal.ofReal ((1 - Real.exp (-h)) * S s + J n) :=
                ENNReal.ofReal_le_ofReal (by linarith)
            _ ≤ ENNReal.ofReal ((1 - Real.exp (-h)) * S s) + ENNReal.ofReal (J n) :=
                ENNReal.ofReal_add_le
            _ ≤ ENNReal.ofReal (1 - Real.exp (-h)) * cellSupAbs S h n + ENNReal.ofReal (J n) := by
                gcongr
                rw [ENNReal.ofReal_mul (by linarith)]
                gcongr
                unfold cellSupAbs
                rw [← abs_of_nonneg (hS_nonneg s)]
                exact le_iSup₂ (f := fun (x : ℝ) (_ : x ∈ cell h n) => ENNReal.ofReal |S x|) s hs
        rcases le_total x y with hxy | hxy
        · calc ENNReal.ofReal (smooth f x - smooth f y)
              ≤ ENNReal.ofReal |smooth f y - smooth f x| :=
                ENNReal.ofReal_le_ofReal (by rw [abs_sub_comm]; exact le_abs_self _)
            _ ≤ _ := key x y hx hy hxy
        · calc ENNReal.ofReal (smooth f x - smooth f y)
              ≤ ENNReal.ofReal |smooth f x - smooth f y| :=
                ENNReal.ofReal_le_ofReal (le_abs_self _)
            _ ≤ _ := key y x hy hx hxy
      -- sup of S bounded by osc of S plus integral
      have hsupbound : (∑' n : ℤ, cellSupAbs S h n) * ENNReal.ofReal h ≤
          (∑' n : ℤ, cellOsc S h n) * ENNReal.ofReal h + IS := by
        rw [hIS, ← tsum_cellIco' (fun x => ENNReal.ofReal (S x)) h hh, ← ENNReal.tsum_mul_right,
          ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
        apply ENNReal.tsum_le_tsum
        intro n
        have hh' : ENNReal.ofReal h ≠ 0 := (ENNReal.ofReal_pos.2 hh).ne'
        rw [← ENNReal.le_div_iff_mul_le (Or.inl hh') (Or.inl ENNReal.ofReal_ne_top)]
        unfold cellSupAbs
        refine iSup₂_le fun x hx => ?_
        rw [ENNReal.le_div_iff_mul_le (Or.inl hh') (Or.inl ENNReal.ofReal_ne_top)]
        have hvol : volume (Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h)) = ENNReal.ofReal h := by
          rw [Real.volume_Ico]; congr 1; ring
        have e1 : ENNReal.ofReal |S x| * ENNReal.ofReal h =
            ∫⁻ y in Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h), ENNReal.ofReal |S x| := by
          rw [setLIntegral_const, hvol]
        have e2 : ∫⁻ y in Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h), ENNReal.ofReal |S x| ≤
            ∫⁻ y in Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h), (cellOsc S h n + ENNReal.ofReal (S y)) := by
          apply setLIntegral_mono' measurableSet_Ico
          intro y hy
          have hy' : y ∈ cell h n := Set.Ico_subset_Icc_self hy
          rw [abs_of_nonneg (hS_nonneg x)]
          calc ENNReal.ofReal (S x) = ENNReal.ofReal ((S x - S y) + S y) := by ring_nf
            _ ≤ ENNReal.ofReal (S x - S y) + ENNReal.ofReal (S y) := ENNReal.ofReal_add_le
            _ ≤ cellOsc S h n + ENNReal.ofReal (S y) := by
                gcongr
                unfold cellOsc
                calc ENNReal.ofReal (S x - S y)
                    ≤ ⨆ y ∈ cell h n, ENNReal.ofReal (S x - S y) :=
                      le_iSup₂ (f := fun (y : ℝ) (_ : y ∈ cell h n) => ENNReal.ofReal (S x - S y)) y hy'
                  _ ≤ ⨆ x ∈ cell h n, ⨆ y ∈ cell h n, ENNReal.ofReal (S x - S y) :=
                      le_iSup₂ (f := fun (x : ℝ) (_ : x ∈ cell h n) =>
                        ⨆ y ∈ cell h n, ENNReal.ofReal (S x - S y)) x hx
        have e3 : ∫⁻ y in Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h), (cellOsc S h n + ENNReal.ofReal (S y)) =
            cellOsc S h n * ENNReal.ofReal h + ∫⁻ y in Set.Ico ((n:ℝ) * h) (((n:ℝ) + 1) * h), ENNReal.ofReal (S y) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, hvol]
        rw [e1]; exact e2.trans (le_of_eq e3)
      calc ENNReal.ofReal h * ∑' n : ℤ, cellOsc (smooth f) h n
          ≤ ENNReal.ofReal h * ∑' n : ℤ, (ENNReal.ofReal (1 - Real.exp (-h)) * cellSupAbs S h n +
              ENNReal.ofReal (J n)) := by gcongr with n; exact hosc n
        _ = ENNReal.ofReal (1 - Real.exp (-h)) * ((∑' n : ℤ, cellSupAbs S h n) * ENNReal.ofReal h) +
              ENNReal.ofReal h * If := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hJsum]; ring
        _ ≤ ENNReal.ofReal (1 - Real.exp (-h)) * ((∑' n : ℤ, cellOsc S h n) * ENNReal.ofReal h + IS) +
              ENNReal.ofReal h * If := by gcongr
        _ = _ := by ring
    -- limit of the bound
    have hT1 : Tendsto (fun h : ℝ => ENNReal.ofReal h * ∑' n : ℤ, cellOsc S h n + IS) (𝓝[>] 0)
        (𝓝 (0 + IS)) := hSdri.2.add tendsto_const_nhds
    have hT2 : Tendsto (fun h : ℝ => ENNReal.ofReal (1 - Real.exp (-h))) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun h : ℝ => 1 - Real.exp (-h)) (𝓝 0) (𝓝 (1 - Real.exp (-0))) :=
        (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).tendsto 0
      rw [neg_zero, Real.exp_zero, sub_self] at this
      have := ENNReal.tendsto_ofReal (this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)) (a := 0)))
      rwa [ENNReal.ofReal_zero] at this
    have hT3 : Tendsto (fun h : ℝ => ENNReal.ofReal h * If) (𝓝[>] 0) (𝓝 (0 * If)) := by
      apply ENNReal.Tendsto.mul_const _ (Or.inr hIf_fin.ne)
      have := ENNReal.tendsto_ofReal (tendsto_id.mono_left (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0)))
      rwa [ENNReal.ofReal_zero] at this
    have hB : Tendsto (fun h : ℝ =>
        ENNReal.ofReal (1 - Real.exp (-h)) * (ENNReal.ofReal h * ∑' n : ℤ, cellOsc S h n + IS) +
          ENNReal.ofReal h * If) (𝓝[>] 0) (𝓝 (0 * (0 + IS) + 0 * If)) := by
      apply Tendsto.add _ hT3
      exact ENNReal.Tendsto.mul hT2 (Or.inr (by finiteness)) hT1 (Or.inr ENNReal.zero_ne_top)
    simp only [zero_mul, zero_add] at hB
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
      (Filter.Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact hmain h hh

end GoldieRenewal.Implicit

open GoldieRenewal.Implicit


theorem solution (f : ℝ → ℝ) (hf : Integrable f) : IsDRi (smooth f) := by
  exact lemma_9_2_core f hf
