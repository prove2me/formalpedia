-- Prove2me | solution 1 for MartOT.Abs.stay_part_eq_inf
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:04:58.643793+00:00
-- url     : https://prove2.me/submissions/4f054bae-ef46-4796-9f37-3dd5d5258228

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_HN_lemma_1_11
import Theorems.Thm_MartOT_Abs_lemma_7_5
import Theorems.Thm_MartOT_Opt_reroute_competitor

open MeasureTheory

private lemma cost_abs_eq_lintegral (m : Measure (ℝ × ℝ)) :
    MartOT.Var.cost (fun x y => |y - x|) m =
      ((∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂m : ENNReal) : EReal) := by
  unfold MartOT.Var.cost MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have hpos : ∀ p : ℝ × ℝ, ((|p.2 - p.1| : ℝ) : EReal).toENNReal = ENNReal.ofReal |p.2 - p.1| := by
    intro p
    have h1 : ((ENNReal.ofReal |p.2 - p.1| : ENNReal) : EReal) = ((|p.2 - p.1| : ℝ) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left (abs_nonneg _)]
    rw [← h1, EReal.toENNReal_coe]
  have hneg : ∀ p : ℝ × ℝ, (-((|p.2 - p.1| : ℝ) : EReal)).toENNReal = 0 := by
    intro p
    exact EReal.toENNReal_of_nonpos (by
      rw [← EReal.coe_neg]
      exact_mod_cast neg_nonpos.mpr (abs_nonneg (p.2 - p.1)))
  simp_rw [hpos, hneg]
  simp

private lemma cost_abs_three_dirac (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (p₁ p₂ p₃ : ℝ × ℝ) :
    MartOT.Var.cost (fun x y => |y - x|)
        (ENNReal.ofReal a • Measure.dirac p₁ + ENNReal.ofReal b • Measure.dirac p₂ +
          Measure.dirac p₃) =
      ((a * |p₁.2 - p₁.1| + b * |p₂.2 - p₂.1| + |p₃.2 - p₃.1| : ℝ) : EReal) := by
  rw [cost_abs_eq_lintegral]
  have hg : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal |p.2 - p.1|) :=
    ((continuous_snd.sub continuous_fst).abs.measurable).ennreal_ofReal
  rw [lintegral_add_measure, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac' _ hg, lintegral_dirac' _ hg, lintegral_dirac' _ hg]
  simp only [smul_eq_mul]
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_add (mul_nonneg ha (abs_nonneg _)) (mul_nonneg hb (abs_nonneg _)),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg ha (abs_nonneg _)) (mul_nonneg hb (abs_nonneg _)))
      (abs_nonneg _)]
  rw [EReal.coe_ennreal_ofReal, max_eq_left]
  positivity

private lemma exists_measurable_subset_image_null
    (m : Measure (ℝ × ℝ)) [IsFiniteMeasure m]
    (E : Set (ℝ × ℝ)) (hE : MeasurableSet E) (hEc : m Eᶜ = 0)
    (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    ∃ B : Set ℝ, MeasurableSet B ∧ B ⊆ f '' E ∧ (m.map f) Bᶜ = 0 := by
  have hK : ∀ n : ℕ, ∃ K : Set (ℝ × ℝ), K ⊆ E ∧ IsCompact K ∧
      m (E \ K) < (((n + 1 : ℕ) : ENNReal)⁻¹) := by
    intro n
    have hε : (((n + 1 : ℕ) : ENNReal)⁻¹) ≠ 0 :=
      ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top (n + 1))
    exact hE.exists_isCompact_sdiff_lt (measure_ne_top m E) hε
  choose K hKE hKc hKm using hK
  let F : Set (ℝ × ℝ) := ⋃ n : ℕ, K n
  let B : Set ℝ := f '' F
  have hB_meas : MeasurableSet B := by
    have hBeq : B = ⋃ n : ℕ, f '' K n := Set.image_iUnion
    rw [hBeq]
    exact MeasurableSet.iUnion (fun n => ((hKc n).image hf).isClosed.measurableSet)
  have hB_sub : B ⊆ f '' E := Set.image_mono (Set.iUnion_subset hKE)
  have hEF_zero : m (E \ F) = 0 := by
    by_contra hne
    rcases ENNReal.exists_inv_nat_lt hne with ⟨n, hn⟩
    have hn0 : n ≠ 0 := by
      intro h0
      subst h0
      simp only [Nat.cast_zero, ENNReal.inv_zero] at hn
      exact not_lt_of_ge (le_top : m (E \ F) ≤ ⊤) hn
    have hle : m (E \ F) ≤ m (E \ K (n - 1)) :=
      measure_mono (Set.sdiff_subset_sdiff_right (Set.subset_iUnion K (n - 1)))
    have hlt : m (E \ K (n - 1)) < (n : ENNReal)⁻¹ := by
      have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)
      simpa [hsub] using hKm (n - 1)
    exact lt_irrefl _ (lt_of_lt_of_le hn (hle.trans_lt hlt).le)
  have hFc_zero : m Fᶜ = 0 := by
    have hsub : Fᶜ ⊆ (E \ F) ∪ Eᶜ := by
      intro p hp
      by_cases hpE : p ∈ E
      · exact Or.inl ⟨hpE, hp⟩
      · exact Or.inr hpE
    have hle : m Fᶜ ≤ m (E \ F) + m Eᶜ :=
      (measure_mono hsub).trans (measure_union_le _ _)
    rw [hEF_zero, hEc, add_zero] at hle
    exact nonpos_iff_eq_zero.mp hle
  refine ⟨B, hB_meas, hB_sub, ?_⟩
  rw [Measure.map_apply hf.measurable hB_meas.compl]
  have hsub : f ⁻¹' Bᶜ ⊆ Fᶜ := by
    intro p hp hpF
    exact hp ⟨p, hpF, rfl⟩
  exact measure_mono_null hsub hFc_zero

private lemma martingale_off_diag {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (hπ : MartOT.Var.IsMartingalePlan μ ν π)
    (ρ : ℝ → ℝ) (hρm : Measurable ρ) (hρb : ∃ C, ∀ x, |ρ x| ≤ C) :
    ∫ p, ρ p.1 * (p.2 - p.1) ∂(π.restrict {p : ℝ × ℝ | p.1 = p.2}ᶜ) = 0 := by
  let Δ : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 = p.2}
  have hΔ : MeasurableSet Δ := (isClosed_eq continuous_fst continuous_snd).measurableSet
  rw [← integral_indicator hΔ.compl]
  have hfun : Δᶜ.indicator (fun p : ℝ × ℝ => ρ p.1 * (p.2 - p.1)) =
      fun p : ℝ × ℝ => ρ p.1 * (p.2 - p.1) := by
    funext p
    by_cases hp : p ∈ Δᶜ
    · exact Set.indicator_of_mem hp _
    · rw [Set.indicator_of_notMem hp]
      have heq : p.1 = p.2 := by simpa [Δ] using hp
      simp [heq]
  rw [hfun]
  exact hπ.2.2 ρ hρm hρb

private lemma null_of_pos_or_neg_null {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (hπ : MartOT.Var.IsMartingalePlan μ ν π)
    {S : Set ℝ} (hS : MeasurableSet S) (sign : Bool)
    (hnull : ((π.restrict {p : ℝ × ℝ | p.1 = p.2}ᶜ).restrict
      (if sign then {p : ℝ × ℝ | p.1 < p.2} else {p : ℝ × ℝ | p.2 < p.1})).map Prod.fst S = 0) :
    ((π.restrict {p : ℝ × ℝ | p.1 = p.2}ᶜ).map Prod.fst) S = 0 := by
  let Δ : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 = p.2}
  have hΔ : MeasurableSet Δ := (isClosed_eq continuous_fst continuous_snd).measurableSet
  let πb : Measure (ℝ × ℝ) := π.restrict Δᶜ
  have hπb_Δ : πb Δ = 0 := by
    simp [πb, Measure.restrict_apply hΔ]
  let U : Set (ℝ × ℝ) := if sign then {p : ℝ × ℝ | p.1 < p.2} else {p : ℝ × ℝ | p.2 < p.1}
  have hU : MeasurableSet U := by
    cases sign <;> dsimp [U]
    · exact (isOpen_lt continuous_snd continuous_fst).measurableSet
    · exact (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hπb_SU : πb (Prod.fst ⁻¹' S ∩ U) = 0 := by
    have h1 : (πb.restrict U).map Prod.fst S = 0 := hnull
    rw [Measure.map_apply measurable_fst hS, Measure.restrict_apply (measurable_fst hS)] at h1
    exact h1
  let indS : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hindS_m : Measurable indS := measurable_const.indicator hS
  have hindS_b : ∃ C, ∀ x, |indS x| ≤ C := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ S <;> simp [indS, hx]
  have hint_diff : Integrable (fun p : ℝ × ℝ => p.2 - p.1) πb := hπ.2.1.restrict
  have hint_prod : Integrable (fun p : ℝ × ℝ => indS p.1 * (p.2 - p.1)) πb := by
    refine hint_diff.mono ?_ ?_
    · exact (hindS_m.comp measurable_fst).mul (measurable_snd.sub measurable_fst) |>.aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      have h1 : |indS p.1| ≤ 1 := by
        by_cases hx : p.1 ∈ S <;> simp [indS, hx]
      calc |indS p.1| * |p.2 - p.1| ≤ 1 * |p.2 - p.1| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |p.2 - p.1| := one_mul _
  have hint0 : ∫ p, indS p.1 * (p.2 - p.1) ∂πb = 0 :=
    martingale_off_diag hπ indS hindS_m hindS_b
  let g : ℝ × ℝ → ℝ := fun p =>
    if sign then indS p.1 * (p.1 - p.2) else indS p.1 * (p.2 - p.1)
  have hg_int : Integrable g πb := by
    cases sign
    · exact hint_prod
    · have hge : g = fun p => -(indS p.1 * (p.2 - p.1)) := by
        funext p; dsimp [g]; ring
      rw [hge]
      exact hint_prod.neg
  have hg_int0 : ∫ p, g p ∂πb = 0 := by
    cases sign
    · exact hint0
    · have hge : g = fun p => -(indS p.1 * (p.2 - p.1)) := by
        funext p; simp [g]; ring
      rw [hge, integral_neg, hint0, neg_zero]
  have hg_nonneg : 0 ≤ᵐ[πb] g := by
    have hbad : πb (Δ ∪ (Prod.fst ⁻¹' S ∩ U)) = 0 := by
      have hle : πb (Δ ∪ (Prod.fst ⁻¹' S ∩ U)) ≤ πb Δ + πb (Prod.fst ⁻¹' S ∩ U) :=
        measure_union_le _ _
      rw [hπb_Δ, hπb_SU, add_zero] at hle
      exact nonpos_iff_eq_zero.mp hle
    have hae : ∀ᵐ p ∂πb, p ∉ Δ ∪ (Prod.fst ⁻¹' S ∩ U) :=
      compl_mem_ae_iff.mpr (by simpa using hbad)
    filter_upwards [hae] with p hp
    have hpSU : ¬ (p.1 ∈ S ∧ p ∈ U) := fun h => hp (Or.inr h)
    change (0 : ℝ) ≤ g p
    by_cases hpS : p.1 ∈ S
    · have hpU : p ∉ U := fun h => hpSU ⟨hpS, h⟩
      cases sign <;> simp only [g, U, indS, Set.indicator_of_mem hpS, one_mul, Bool.false_eq_true,
        ↓reduceIte, Set.mem_ofPred_eq] at hpU ⊢
      · linarith
      · linarith
    · cases sign <;> simp [g, indS, Set.indicator_of_notMem hpS]
  have hg_zero : g =ᵐ[πb] 0 := (integral_eq_zero_iff_of_nonneg_ae hg_nonneg hg_int).mp hg_int0
  have hS_inter_zero : πb (Prod.fst ⁻¹' S ∩ Δᶜ) = 0 := by
    have hsub : Prod.fst ⁻¹' S ∩ Δᶜ ⊆ {p : ℝ × ℝ | g p ≠ 0} := by
      intro p ⟨hpS, hpΔ⟩
      have hpS' : p.1 ∈ S := hpS
      have hne : p.1 ≠ p.2 := hpΔ
      change g p ≠ 0
      cases sign <;> simp only [g, indS, Set.indicator_of_mem hpS', one_mul, Bool.false_eq_true,
        ↓reduceIte, ne_eq, sub_eq_zero]
      · exact hne.symm
      · exact hne
    have hnull_g : πb {p : ℝ × ℝ | g p ≠ 0} = 0 := by
      simpa [Filter.EventuallyEq, ae_iff] using hg_zero
    exact measure_mono_null hsub hnull_g
  rw [Measure.map_apply measurable_fst hS]
  have hsub : Prod.fst ⁻¹' S ⊆ (Prod.fst ⁻¹' S ∩ Δᶜ) ∪ Δ := by
    intro p hp
    by_cases hpΔ : p ∈ Δ
    · exact Or.inr hpΔ
    · exact Or.inl ⟨hp, hpΔ⟩
  have hle : πb (Prod.fst ⁻¹' S) ≤ πb (Prod.fst ⁻¹' S ∩ Δᶜ) + πb Δ :=
    (measure_mono hsub).trans (measure_union_le _ _)
  rw [hS_inter_zero, hπb_Δ, add_zero] at hle
  exact nonpos_iff_eq_zero.mp hle

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π) :
    π.restrict {p : ℝ × ℝ | p.1 = p.2} = (μ ⊓ ν).map (fun x : ℝ => (x, x)) := by
  have : IsProbabilityMeasure π := by
    refine ⟨?_⟩
    have h1 : (π.map Prod.fst) Set.univ = 1 := by rw [hπ.1.1.1, measure_univ]
    rwa [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h1
  -- Step 1: Apply Lemma 1.11 to get Borel Γ with π(Γᶜ) = 0 and finite-support optimality.
  have hc_meas : Measurable (Function.uncurry (fun x y : ℝ => |y - x|)) :=
    (continuous_snd.sub continuous_fst).abs.measurable
  have hint : MartOT.Var.SuffIntegrable μ ν (fun x y => |y - x|) :=
    ⟨fun _ => 0, fun _ => 0, integrable_zero _ _ _, integrable_zero _ _ _,
      fun x y => by simp [abs_nonneg]⟩
  have hfin : MartOT.Var.cost (fun x y => |y - x|) π < ⊤ := by
    rw [cost_abs_eq_lintegral]
    have hlt : ∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂π < ⊤ := by
      have hfi := hπ.1.2.1.2
      simpa [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using hfi
    exact lt_top_iff_ne_top.mpr (EReal.coe_ennreal_eq_top_iff.not.mpr hlt.ne)
  rcases MartOT.HN.lemma_1_11 μ ν hμν (fun x y => |y - x|) hc_meas hint π hπ hfin with
    ⟨Γ, hΓ_meas, hΓ_null, hΓ_opt⟩
  -- Step 2: Decompose π = π₀ + π̄ along the diagonal Δ.
  let Δ : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 = p.2}
  have hΔ : MeasurableSet Δ := (isClosed_eq continuous_fst continuous_snd).measurableSet
  let π₀ : Measure (ℝ × ℝ) := π.restrict Δ
  let πb : Measure (ℝ × ℝ) := π.restrict Δᶜ
  have hπ_split : π₀ + πb = π := Measure.restrict_add_restrict_compl hΔ
  let ρ : Measure ℝ := π₀.map Prod.fst
  let μb : Measure ℝ := πb.map Prod.fst
  let νb : Measure ℝ := πb.map Prod.snd
  have hdiag_meas : Measurable (fun x : ℝ => (x, x)) := measurable_id.prodMk measurable_id
  have hπ₀_diag : π₀ = ρ.map (fun x : ℝ => (x, x)) := by
    rw [Measure.map_map hdiag_meas measurable_fst]
    have hae : (fun x : ℝ => (x, x)) ∘ Prod.fst =ᵐ[π₀] id := by
      have hmem : ∀ᵐ p ∂π₀, p ∈ Δ := ae_restrict_mem hΔ
      filter_upwards [hmem] with p hp
      change (p.1, p.1) = p
      exact Prod.ext rfl hp
    rw [Measure.map_congr hae, Measure.map_id]
  have hπ₀_snd : π₀.map Prod.snd = ρ := by
    have hae : Prod.snd =ᵐ[π₀] Prod.fst := by
      have hmem : ∀ᵐ p ∂π₀, p ∈ Δ := ae_restrict_mem hΔ
      filter_upwards [hmem] with p hp
      exact hp.symm
    exact Measure.map_congr hae
  have hρ_add_μb : ρ + μb = μ := by
    calc ρ + μb = (π₀ + πb).map Prod.fst := (Measure.map_add _ _ measurable_fst).symm
      _ = π.map Prod.fst := by rw [hπ_split]
      _ = μ := hπ.1.1.1
  have hρ_add_νb : ρ + νb = ν := by
    calc ρ + νb = π₀.map Prod.snd + πb.map Prod.snd := by rw [hπ₀_snd]
      _ = (π₀ + πb).map Prod.snd := (Measure.map_add _ _ measurable_snd).symm
      _ = π.map Prod.snd := by rw [hπ_split]
      _ = ν := hπ.1.1.2
  have hρ_le_μ : ρ ≤ μ := hρ_add_μb ▸ Measure.le_add_right le_rfl
  have hρ_le_ν : ρ ≤ ν := hρ_add_νb ▸ Measure.le_add_right le_rfl
  have hρ_le_inf : ρ ≤ μ ⊓ ν := le_inf hρ_le_μ hρ_le_ν
  have : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ hρ_le_μ
  have : IsFiniteMeasure (μ ⊓ ν) := isFiniteMeasure_of_le μ inf_le_left
  let κ : Measure ℝ := (μ ⊓ ν) - ρ
  have hκ_add_ρ : κ + ρ = μ ⊓ ν := Measure.sub_add_cancel_of_le hρ_le_inf
  have hκ_le_μb : κ ≤ μb := by
    refine Measure.le_iff.mpr fun s _ => ?_
    have h1 : (κ + ρ) s ≤ (μb + ρ) s := by
      rw [hκ_add_ρ, add_comm μb ρ, hρ_add_μb]
      exact (inf_le_left : μ ⊓ ν ≤ μ) s
    simp only [Measure.add_apply] at h1
    exact ENNReal.le_of_add_le_add_right (measure_ne_top ρ s) h1
  have hκ_le_νb : κ ≤ νb := by
    refine Measure.le_iff.mpr fun s _ => ?_
    have h1 : (κ + ρ) s ≤ (νb + ρ) s := by
      rw [hκ_add_ρ, add_comm νb ρ, hρ_add_νb]
      exact (inf_le_right : μ ⊓ ν ≤ ν) s
    simp only [Measure.add_apply] at h1
    exact ENNReal.le_of_add_le_add_right (measure_ne_top ρ s) h1
  -- Step 3: Show κ = 0 by contradiction.
  have hκ_zero : κ Set.univ = 0 := by
    by_contra hκ_ne
    let Γb : Set (ℝ × ℝ) := Γ \ Δ
    have hΓb_meas : MeasurableSet Γb := hΓ_meas.diff hΔ
    have hπb_Γb : πb Γbᶜ = 0 := by
      have hsub : Γbᶜ ⊆ Γᶜ ∪ Δ := by
        intro p hp
        by_cases hpΔ : p ∈ Δ
        · exact Or.inr hpΔ
        · exact Or.inl (fun hpΓ => hp ⟨hpΓ, hpΔ⟩)
      have hπb_Δ : πb Δ = 0 := by simp [πb, Measure.restrict_apply hΔ]
      have hπb_Γc : πb Γᶜ = 0 := nonpos_iff_eq_zero.mp
        ((Measure.restrict_le_self Γᶜ).trans_eq hΓ_null)
      have hle : πb Γbᶜ ≤ πb Γᶜ + πb Δ := (measure_mono hsub).trans (measure_union_le _ _)
      rw [hπb_Γc, hπb_Δ, add_zero] at hle
      exact nonpos_iff_eq_zero.mp hle
    let Upos : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < p.2}
    let Uneg : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 < p.1}
    have hUpos : MeasurableSet Upos := (isOpen_lt continuous_fst continuous_snd).measurableSet
    have hUneg : MeasurableSet Uneg := (isOpen_lt continuous_snd continuous_fst).measurableSet
    -- Construct Borel sets B₊, B₋, B₂ from inner regularity of finite measures on ℝ × ℝ.
    have hπb_pos_null : (πb.restrict Upos) (Γb ∩ Upos)ᶜ = 0 := by
      rw [Measure.restrict_apply (hΓb_meas.inter hUpos).compl]
      have hsub : (Γb ∩ Upos)ᶜ ∩ Upos ⊆ Γbᶜ := fun p ⟨h1, h2⟩ h3 => h1 ⟨h3, h2⟩
      exact measure_mono_null hsub hπb_Γb
    have hπb_neg_null : (πb.restrict Uneg) (Γb ∩ Uneg)ᶜ = 0 := by
      rw [Measure.restrict_apply (hΓb_meas.inter hUneg).compl]
      have hsub : (Γb ∩ Uneg)ᶜ ∩ Uneg ⊆ Γbᶜ := fun p ⟨h1, h2⟩ h3 => h1 ⟨h3, h2⟩
      exact measure_mono_null hsub hπb_Γb
    rcases exists_measurable_subset_image_null (πb.restrict Upos) (Γb ∩ Upos)
        (hΓb_meas.inter hUpos) hπb_pos_null Prod.fst continuous_fst with
      ⟨Bpos, hBpos_m, hBpos_sub, hBpos_null⟩
    rcases exists_measurable_subset_image_null (πb.restrict Uneg) (Γb ∩ Uneg)
        (hΓb_meas.inter hUneg) hπb_neg_null Prod.fst continuous_fst with
      ⟨Bneg, hBneg_m, hBneg_sub, hBneg_null⟩
    rcases exists_measurable_subset_image_null πb Γb
        hΓb_meas hπb_Γb Prod.snd continuous_snd with
      ⟨B2, hB2_m, hB2_sub, hB2_null⟩
    -- Transfer nullness to μ̄, ν̄, and κ.
    have hμb_Bpos : μb Bposᶜ = 0 :=
      null_of_pos_or_neg_null hπ.1 hBpos_m.compl true hBpos_null
    have hμb_Bneg : μb Bnegᶜ = 0 :=
      null_of_pos_or_neg_null hπ.1 hBneg_m.compl false hBneg_null
    have hκ_Bpos : κ Bposᶜ = 0 := nonpos_iff_eq_zero.mp ((hκ_le_μb Bposᶜ).trans_eq hμb_Bpos)
    have hκ_Bneg : κ Bnegᶜ = 0 := nonpos_iff_eq_zero.mp ((hκ_le_μb Bnegᶜ).trans_eq hμb_Bneg)
    have hκ_B2 : κ B2ᶜ = 0 := nonpos_iff_eq_zero.mp ((hκ_le_νb B2ᶜ).trans_eq hB2_null)
    have hκ_inter_c : κ (Bpos ∩ Bneg ∩ B2)ᶜ = 0 := by
      have hsub : (Bpos ∩ Bneg ∩ B2)ᶜ ⊆ Bposᶜ ∪ Bnegᶜ ∪ B2ᶜ := by
        intro x hx
        by_cases h1 : x ∈ Bpos
        · by_cases h2 : x ∈ Bneg
          · exact Or.inr (fun h3 => hx ⟨⟨h1, h2⟩, h3⟩)
          · exact Or.inl (Or.inr h2)
        · exact Or.inl (Or.inl h1)
      have hle : κ (Bpos ∩ Bneg ∩ B2)ᶜ ≤ κ Bposᶜ + κ Bnegᶜ + κ B2ᶜ :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl))
      rw [hκ_Bpos, hκ_Bneg, hκ_B2, add_zero, add_zero] at hle
      exact nonpos_iff_eq_zero.mp hle
    have hne : (Bpos ∩ Bneg ∩ B2).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Set.compl_empty] at hκ_inter_c
      exact hκ_ne hκ_inter_c
    -- Pick x ∈ B₊ ∩ B₋ ∩ B₂ and extract forbidden configuration in Γ.
    rcases hne with ⟨x, ⟨hx_pos, hx_neg⟩, hx_2⟩
    rcases hBpos_sub hx_pos with ⟨⟨x1, yp⟩, ⟨⟨h1Γ, _⟩, h1lt⟩, hx1⟩
    dsimp only at hx1; rw [hx1] at h1Γ h1lt
    rcases hBneg_sub hx_neg with ⟨⟨x2, ym⟩, ⟨⟨h2Γ, _⟩, h2lt⟩, hx2⟩
    dsimp only at hx2; rw [hx2] at h2Γ h2lt
    rcases hB2_sub hx_2 with ⟨⟨x', y'⟩, ⟨h3Γ, h3nΔ⟩, hy'⟩
    dsimp only at hy'; rw [hy'] at h3Γ h3nΔ
    have hlt_m : ym < x := h2lt
    have hlt_p : x < yp := h1lt
    have hne_x' : x' ≠ x := h3nΔ
    -- Construct the barycentre-preserving competitor and apply Lemma 1.11 + Lemma 7.5(3).
    let l : ℝ := (x - ym) / (yp - ym)
    have hden : 0 < yp - ym := by linarith
    have hl0 : 0 < l := div_pos (by linarith) hden
    have hl1 : l < 1 := (div_lt_one hden).mpr (by linarith)
    have hcomb : l * yp + (1 - l) * ym = x := by
      dsimp [l]
      field_simp [hden.ne']
      ring
    let p₁ : ℝ × ℝ := (x, yp)
    let p₂ : ℝ × ℝ := (x, ym)
    let p₃ : ℝ × ℝ := (x', x)
    have hp12 : p₁ ≠ p₂ := by intro h; have := congrArg Prod.snd h; dsimp [p₁, p₂] at this; linarith
    have hp13 : p₁ ≠ p₃ := by intro h; have := congrArg Prod.fst h; exact hne_x'.symm this
    have hp23 : p₂ ≠ p₃ := by intro h; have := congrArg Prod.fst h; exact hne_x'.symm this
    let S : Finset (ℝ × ℝ) := {p₁, p₂, p₃}
    let w : ℝ × ℝ → NNReal := fun p =>
      if p = p₁ then Real.toNNReal l
      else if p = p₂ then Real.toNNReal (1 - l)
      else if p = p₃ then 1 else 0
    have hS_sub : (↑S : Set (ℝ × ℝ)) ⊆ Γ := by
      intro p hp
      simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact h1Γ
      · exact h2Γ
      · exact h3Γ
    let α : Measure (ℝ × ℝ) :=
      ENNReal.ofReal l • Measure.dirac p₁ + ENNReal.ofReal (1 - l) • Measure.dirac p₂ +
        Measure.dirac p₃
    let α' : Measure (ℝ × ℝ) :=
      ENNReal.ofReal (1 - l) • Measure.dirac (x', ym) + ENNReal.ofReal l • Measure.dirac (x', yp) +
        Measure.dirac (x, x)
    have hα_eq : ∑ p ∈ S, (w p : ENNReal) • Measure.dirac p = α := by
      have h1not : p₁ ∉ ({p₂, p₃} : Finset (ℝ × ℝ)) := by simp [hp12, hp13]
      have h2not : p₂ ∉ ({p₃} : Finset (ℝ × ℝ)) := by simp [hp23]
      simp only [S, Finset.sum_insert h1not, Finset.sum_insert h2not, Finset.sum_singleton]
      simp only [w, ↓reduceIte, hp12.symm, hp13.symm, hp23.symm]
      change ENNReal.ofReal l • Measure.dirac p₁ +
        (ENNReal.ofReal (1 - l) • Measure.dirac p₂ + (1 : ENNReal) • Measure.dirac p₃) = α
      rw [one_smul, ← add_assoc]
    have hcomp : MartOT.Var.IsCompetitor α α' :=
      MartOT.Opt.reroute_competitor x x' ym yp x l hl0 hl1 hcomb
    have hle_cost : MartOT.Var.cost (fun x y => |y - x|) α ≤
        MartOT.Var.cost (fun x y => |y - x|) α' := by
      rw [← hα_eq]
      exact hΓ_opt S w hS_sub α' (hα_eq.symm ▸ hcomp)
    let A : ℝ → ℝ := fun t => l * |x - yp| + (1 - l) * |x - ym| + |t - x|
    let B : ℝ → ℝ := fun t => l * |t - yp| + (1 - l) * |t - ym| + |x - x|
    have hcost_α : MartOT.Var.cost (fun x y => |y - x|) α = ((A x' : ℝ) : EReal) := by
      rw [cost_abs_three_dirac l (1 - l) hl0.le (by linarith) p₁ p₂ p₃]
      congr 1
      dsimp [A, p₁, p₂, p₃]
      rw [abs_sub_comm yp x, abs_sub_comm ym x, abs_sub_comm x x']
    have hcost_α' : MartOT.Var.cost (fun x y => |y - x|) α' = ((B x' : ℝ) : EReal) := by
      rw [cost_abs_three_dirac (1 - l) l (by linarith) hl0.le (x', ym) (x', yp) (x, x)]
      congr 1
      dsimp [B]
      rw [abs_sub_comm ym x', abs_sub_comm yp x']
      ring
    have h75 := (MartOT.Abs.lemma_7_5 x ym yp x l ⟨hlt_m, hlt_p⟩ ⟨hlt_m, hlt_p⟩ hcomb
      A B (fun _ => rfl) (fun _ => rfl)).2.2 rfl
    have hge0 : 0 ≤ A x' - B x' := h75.1 x'
    have hne0 : A x' - B x' ≠ 0 := fun h0 => hne_x' ((h75.2 x').mp h0)
    have hlt_AB : B x' < A x' := by
      have : 0 < A x' - B x' := lt_of_le_of_ne hge0 hne0.symm
      linarith
    rw [hcost_α, hcost_α'] at hle_cost
    have hle_real : A x' ≤ B x' := EReal.coe_le_coe_iff.mp hle_cost
    linarith
  -- Step 4: Conclude ρ = μ ⊓ ν and hence π₀ = (μ ⊓ ν).map (fun x => (x, x)).
  have hκ_eq_zero : κ = 0 := Measure.measure_univ_eq_zero.mp hκ_zero
  have hρ_eq_inf : ρ = μ ⊓ ν := by
    rw [← hκ_add_ρ, hκ_eq_zero, zero_add]
  change π₀ = (μ ⊓ ν).map (fun x : ℝ => (x, x))
  rw [hπ₀_diag, hρ_eq_inf]
