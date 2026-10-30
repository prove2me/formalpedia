-- Prove2me | solution 1 for MaxSpectralRisk.Duality.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:05:08.349721+00:00
-- url     : https://prove2.me/submissions/251075c7-0238-4f92-a542-e6b44f65e6ab

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting
import Theorems.Thm_MaxSpectralRisk_Duality_lemma_1
import Theorems.Thm_MaxSpectralRisk_Duality_es_representation
import Theorems.Thm_MaxSpectralRisk_Duality_eq_2

open MeasureTheory Filter Topology MaxSpectralRisk.Duality

namespace MSRP2Usc

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- Lower-semicontinuous version of
`lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`. -/
lemma lintegral_le_liminf_of_lsc {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ}
    (f_lsc : LowerSemicontinuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn)
    f_lsc.measurable.aemeasurable]
  calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a}) :=
        lintegral_mono (fun t ↦ h_opens _ (f_lsc.isOpen_preimage t))
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a}) :=
        lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
          measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))

variable [HasOuterApproxClosed Ω]

/-- Bounded usc functions: for every `t > ∫ h dμ`, eventually `∫ h dμₙ < t`. -/
lemma eventually_integral_lt_of_usc_bdd {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω}
    (hlim : Tendsto μs atTop (𝓝 μ)) {h : Ω → ℝ} (h_usc : UpperSemicontinuous h) {M k : ℝ}
    (hM : ∀ x, h x ≤ M) (hk : ∀ x, -k ≤ h x) {t : ℝ} (ht : ∫ x, h x ∂(μ : Measure Ω) < t) :
    ∀ᶠ n in atTop, ∫ x, h x ∂(μs n : Measure Ω) < t := by
  set u : Ω → ℝ := fun x => M - h x with hu
  have hu_lsc : LowerSemicontinuous u := by
    have : LowerSemicontinuous (fun x => -h x) :=
      continuous_neg.comp_upperSemicontinuous_antitone h_usc (fun a b hab => neg_le_neg hab)
    simpa [hu, sub_eq_add_neg] using
      (lowerSemicontinuous_const (z := M)).add this
  have hu_nn : 0 ≤ u := fun x => by simp [hu, hM x]
  have hu_le : ∀ x, u x ≤ M + k := fun x => by simp only [hu]; linarith [hk x]
  have hhm : Measurable h := h_usc.measurable
  have hbdd : ∀ ν : Measure Ω, [IsProbabilityMeasure ν] → Integrable h ν := by
    intro ν _
    refine Integrable.of_bound (C := |M| + |k|) hhm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [hk x, le_abs_self k, abs_nonneg M]
    · linarith [hM x, le_abs_self M, abs_nonneg k]
  have hint_u : ∀ ν : Measure Ω, [IsProbabilityMeasure ν] →
      ∫ x, u x ∂ν = (∫⁻ x, ENNReal.ofReal (u x) ∂ν).toReal := by
    intro ν _
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hu_nn)
      hu_lsc.measurable.aestronglyMeasurable
  have hu_int : ∀ ν : Measure Ω, [IsProbabilityMeasure ν] →
      ∫ x, h x ∂ν = M - ∫ x, u x ∂ν := by
    intro ν _
    simp only [hu]
    rw [integral_sub (integrable_const M) (hbdd ν), integral_const]
    simp
  have hlin_fin : ∀ ν : Measure Ω, [IsProbabilityMeasure ν] →
      ∫⁻ x, ENNReal.ofReal (u x) ∂ν ≠ ⊤ := by
    intro ν _
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal
      (hu_le x))) ?_)
    simp
  have h_opens : ∀ G, IsOpen G → (μ : Measure Ω) G ≤
      atTop.liminf (fun i ↦ (μs i : Measure Ω) G) := fun G hG =>
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG
  have hmain := lintegral_le_liminf_of_lsc hu_lsc hu_nn h_opens
  -- `∫ u dμ > M - t`
  have hgt : M - t < ∫ x, u x ∂(μ : Measure Ω) := by
    rw [hu_int (μ : Measure Ω)] at ht; linarith
  rcases lt_or_ge (M - t) 0 with hneg | hnn
  · refine Eventually.of_forall fun n => ?_
    rw [hu_int (μs n : Measure Ω)]
    have : 0 ≤ ∫ x, u x ∂(μs n : Measure Ω) := integral_nonneg hu_nn
    linarith
  · have hlt : ENNReal.ofReal (M - t) < ∫⁻ x, ENNReal.ofReal (u x) ∂(μ : Measure Ω) := by
      rw [hint_u (μ : Measure Ω)] at hgt
      rw [← ENNReal.ofReal_toReal (hlin_fin (μ : Measure Ω))]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn).2 hgt
    have hev := eventually_lt_of_lt_liminf (lt_of_lt_of_le hlt hmain)
    filter_upwards [hev] with n hn
    rw [hu_int (μs n : Measure Ω), hint_u (μs n : Measure Ω)]
    have := (ENNReal.ofReal_lt_iff_lt_toReal hnn (hlin_fin (μs n : Measure Ω))).1 hn
    linarith

/-- Usc functions bounded above (integrable along the sequence): for every `t > ∫ f dμ`,
eventually `∫ f dμₙ < t`. -/
lemma eventually_integral_lt_of_usc {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω}
    (hlim : Tendsto μs atTop (𝓝 μ)) {f : Ω → ℝ} (f_usc : UpperSemicontinuous f) {M : ℝ}
    (hM : ∀ x, f x ≤ M) (hfi : Integrable f (μ : Measure Ω))
    (hfis : ∀ n, Integrable f (μs n : Measure Ω)) {t : ℝ}
    (ht : ∫ x, f x ∂(μ : Measure Ω) < t) :
    ∀ᶠ n in atTop, ∫ x, f x ∂(μs n : Measure Ω) < t := by
  have hfm : Measurable f := f_usc.measurable
  set hk : ℕ → Ω → ℝ := fun k x => max (f x) (-(k : ℝ)) with hhk
  have hkint : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (k : ℕ), Integrable (hk k) ν := by
    intro ν _ k
    refine Integrable.of_bound (C := |M| + k) (hfm.max measurable_const).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    constructor
    · have := le_max_right (f x) (-(k : ℝ)); linarith [abs_nonneg M]
    · exact max_le (by linarith [hM x, le_abs_self M]) (by linarith [abs_nonneg M])
  -- `∫ max(f, -k) dμ → ∫ f dμ`
  have hconv : Tendsto (fun k : ℕ => ∫ x, hk k x ∂(μ : Measure Ω)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |f x| + |M|)
      (fun k => (hfm.max measurable_const).aestronglyMeasurable) (hfi.abs.add (integrable_const _))
      (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, abs_le]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      constructor
      · have := le_max_left (f x) (-(k : ℝ)); linarith [neg_abs_le (f x), abs_nonneg M]
      · exact max_le (by linarith [hM x, le_abs_self M, abs_nonneg (f x)])
          (by linarith [abs_nonneg M, abs_nonneg (f x)])
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (-f x)] with k hk'
      simp only [hhk]
      rw [max_eq_left (by linarith)]
  obtain ⟨k, hk1⟩ := ((tendsto_order.1 hconv).2 t ht).exists
  have hk_usc : UpperSemicontinuous (hk k) := by
    have := (continuous_id.max continuous_const :
      Continuous fun y : ℝ => max y (-(k : ℝ))).comp_upperSemicontinuous f_usc
      (fun a b hab => max_le_max hab le_rfl)
    exact this
  have hev := eventually_integral_lt_of_usc_bdd hlim hk_usc (M := max M (-(k : ℝ))) (k := k)
    (fun x => max_le_max (hM x) le_rfl) (fun x => le_max_right _ _) hk1
  filter_upwards [hev] with n hn
  exact lt_of_le_of_lt (integral_mono (hfis n) (hkint _ k) fun x => le_max_left _ _) hn

end MSRP2Usc


namespace MSRProp2Aux

lemma coe_add_iInf (a : ℝ) {ι : Sort*} (f : ι → EReal) :
    (a : EReal) + ⨅ i, f i = ⨅ i, ((a : EReal) + f i) := by
  apply le_antisymm
  · exact le_iInf fun i => add_le_add le_rfl (iInf_le f i)
  · have h : ((-a : ℝ) : EReal) + ⨅ i, ((a : EReal) + f i) ≤ ⨅ i, f i := by
      refine le_iInf fun i => ?_
      calc ((-a : ℝ) : EReal) + ⨅ i, ((a : EReal) + f i)
          ≤ ((-a : ℝ) : EReal) + ((a : EReal) + f i) := add_le_add le_rfl (iInf_le _ i)
        _ = f i := by rw [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
    calc ⨅ i, ((a : EReal) + f i)
        = (a : EReal) + (((-a : ℝ) : EReal) + ⨅ i, ((a : EReal) + f i)) := by
          rw [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add]
      _ ≤ (a : EReal) + ⨅ i, f i := add_le_add le_rfl h

lemma coe_add_iSup (a : ℝ) {ι : Sort*} (f : ι → EReal) :
    (a : EReal) + ⨆ i, f i = ⨆ i, ((a : EReal) + f i) := by
  apply le_antisymm
  · have h : ⨆ i, f i ≤ ((-a : ℝ) : EReal) + ⨆ i, ((a : EReal) + f i) := by
      refine iSup_le fun i => ?_
      calc f i = ((-a : ℝ) : EReal) + ((a : EReal) + f i) := by
            rw [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
        _ ≤ ((-a : ℝ) : EReal) + ⨆ i, ((a : EReal) + f i) :=
            add_le_add le_rfl (le_iSup (fun i => (a : EReal) + f i) i)
    calc (a : EReal) + ⨆ i, f i
        ≤ (a : EReal) + (((-a : ℝ) : EReal) + ⨆ i, ((a : EReal) + f i)) := add_le_add le_rfl h
      _ = ⨆ i, ((a : EReal) + f i) := by
          rw [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add]
  · exact iSup_le fun i => add_le_add le_rfl (le_iSup f i)

instance gam_finite (sig : SpectralFunction) : IsFiniteMeasure (gam sig) := by
  refine ⟨?_⟩
  unfold gam
  rw [Measure.restrict_apply_univ]
  exact measure_Ico_lt_top

lemma gam_ae_Ico (sig : SpectralFunction) : ∀ᵐ u ∂(gam sig), u ∈ Set.Ico (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Ico

lemma Gam_ac_gam (sig : SpectralFunction) : Gam sig ≪ gam sig :=
  withDensity_absolutelyContinuous _ _

lemma gam_ac_Gam (sig : SpectralFunction) : gam sig ≪ Gam sig := by
  unfold Gam
  refine withDensity_absolutelyContinuous' (by fun_prop) ?_
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  linarith [hu.2]

lemma Gam_ae_Ico (sig : SpectralFunction) : ∀ᵐ u ∂(Gam sig), u ∈ Set.Ico (0 : ℝ) 1 :=
  (Gam_ac_gam sig).ae_le (gam_ae_Ico sig)

lemma int_Gam_iff (sig : SpectralFunction) (f : ℝ → ℝ) :
    Integrable f (Gam sig) ↔ Integrable (fun u => (1 - u) * f u) (gam sig) := by
  unfold Gam
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [hu.2])]

lemma integral_Gam (sig : SpectralFunction) (f : ℝ → ℝ) :
    ∫ u, f u ∂(Gam sig) = ∫ u, (1 - u) * f u ∂(gam sig) := by
  unfold Gam
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [hu.2])]

lemma int_Gam_of_int_gam (sig : SpectralFunction) {f : ℝ → ℝ} (hf : Integrable f (gam sig)) :
    Integrable f (Gam sig) := by
  rw [int_Gam_iff]
  refine Integrable.mono' hf.norm (by fun_prop) ?_
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [Real.norm_eq_abs]
  rw [abs_mul, abs_of_nonneg (by linarith [hu.2] : (0 : ℝ) ≤ 1 - u)]
  have : 1 - u ≤ 1 := by linarith [hu.1]
  have h0 : 0 ≤ |f u| := abs_nonneg _
  nlinarith

section Coupling

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma aerect_ae {μ : Measure X} {ν : Measure Y} {P : X → Y → Prop}
    (h : AERect μ ν P) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) :
    ∀ᵐ p ∂π, P p.1 p.2 := by
  obtain ⟨N, hN, N', hN', hP⟩ := h
  have h1 : π (Prod.fst ⁻¹' toMeasurable μ N) = 0 := by
    rw [← Measure.map_apply measurable_fst (measurableSet_toMeasurable _ _), hπ.2.1,
      measure_toMeasurable, hN]
  have h2 : π (Prod.snd ⁻¹' toMeasurable ν N') = 0 := by
    rw [← Measure.map_apply measurable_snd (measurableSet_toMeasurable _ _), hπ.2.2,
      measure_toMeasurable, hN']
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1, measure_eq_zero_iff_ae_notMem.1 h2]
    with p hp1 hp2
  exact hP p.1 (fun h => hp1 (subset_toMeasurable _ _ h)) p.2
    (fun h => hp2 (subset_toMeasurable _ _ h))

lemma int_fst {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun p : X × Y => f p.1) π := by
  have : Integrable f (π.map Prod.fst) := by rw [hπ.2.1]; exact hf
  exact (integrable_map_measure this.1 measurable_fst.aemeasurable).1 this

lemma int_snd {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) {f : Y → ℝ} (hf : Integrable f ν) :
    Integrable (fun p : X × Y => f p.2) π := by
  have : Integrable f (π.map Prod.snd) := by rw [hπ.2.2]; exact hf
  exact (integrable_map_measure this.1 measurable_snd.aemeasurable).1 this

end Coupling

section Main

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {sig : SpectralFunction} {L : X × Y → ℝ}

lemma L_meas (hA : Assumptions L μ ν) : Measurable L := hA.usc.measurable

lemma L_int (hA : Assumptions L μ ν) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) : Integrable L π := by
  obtain ⟨A, B, -, hAi, -, hBi, hub⟩ := hA.upper_bound
  obtain ⟨a, b, -, hai, -, hbi, hlb⟩ := hA.lower_bound
  refine Integrable.mono' (((int_fst hπ hai).add (int_snd hπ hbi)).abs.add
    ((int_fst hπ hAi).add (int_snd hπ hBi)).abs) (L_meas hA).aestronglyMeasurable ?_
  filter_upwards [aerect_ae hub hπ, aerect_ae hlb hπ] with p h1 h2
  simp only [Prod.mk.eta] at h1 h2
  rw [Real.norm_eq_abs]
  exact (abs_le_max_abs_abs h2 h1).trans (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))

lemma C_int (hA : Assumptions L μ ν) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) (β : ℝ → ℝ)
    (hβ : Integrable β (gam sig)) :
    Integrable (fun p : X × Y => Cbeta sig L β p.1 p.2) π := by
  haveI : IsProbabilityMeasure π := hπ.1
  have hL := L_int hA hπ
  set f : (X × Y) → ℝ → ℝ := fun p u => max (L p - β u) 0 with hfdef
  have hf : Integrable (Function.uncurry f) (π.prod (gam sig)) := by
    refine Integrable.mono' ((hL.comp_fst (gam sig)).norm.add ((hβ.comp_snd π).norm)) ?_ ?_
    · exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
        ((hL.comp_fst (gam sig)).1.sub (hβ.comp_snd π).1)
    · refine ae_of_all _ fun q => ?_
      show ‖max (L q.1 - β q.2) 0‖ ≤ ‖L q.1‖ + ‖β q.2‖
      rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (by linarith [le_abs_self (L q.1), neg_abs_le (β q.2)])
        (by positivity)
  have hC : ∀ p : X × Y, Cbeta sig L β p.1 p.2 = ∫ u, f p u ∂(gam sig) := fun p => by
    simp only [Cbeta, Prod.mk.eta, hfdef]
  simp_rw [hC]
  exact hf.integral_prod_left

/-- Step (7) of the proof of Theorem 1 (Tonelli): for a coupling `π` and `β ∈ L¹(γσ)`,
`H(π, β) = ∫ β dΓσ + E_π[C^β]`. -/
lemma H_eq (hA : Assumptions L μ ν) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) (β : ℝ → ℝ)
    (hβ : Integrable β (gam sig)) :
    H sig L π β = (((∫ u, β u ∂(Gam sig)) + ∫ p, Cbeta sig L β p.1 p.2 ∂π : ℝ) : EReal) := by
  haveI : IsProbabilityMeasure π := hπ.1
  have hL := L_int hA hπ
  set f : (X × Y) → ℝ → ℝ := fun p u => max (L p - β u) 0 with hfdef
  have hf : Integrable (Function.uncurry f) (π.prod (gam sig)) := by
    refine Integrable.mono' ((hL.comp_fst (gam sig)).norm.add ((hβ.comp_snd π).norm)) ?_ ?_
    · exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
        ((hL.comp_fst (gam sig)).1.sub (hβ.comp_snd π).1)
    · refine ae_of_all _ fun q => ?_
      show ‖max (L q.1 - β q.2) 0‖ ≤ ‖L q.1‖ + ‖β q.2‖
      rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (by linarith [le_abs_self (L q.1), neg_abs_le (β q.2)])
        (by positivity)
  have hG : Integrable (fun u => ∫ p, f p u ∂π) (gam sig) := hf.integral_prod_right
  have hswap : ∫ p, ∫ u, f p u ∂(gam sig) ∂π = ∫ u, ∫ p, f p u ∂π ∂(gam sig) :=
    integral_integral_swap hf
  have hC : ∀ p : X × Y, Cbeta sig L β p.1 p.2 = ∫ u, f p u ∂(gam sig) := fun p => by
    simp only [Cbeta, Prod.mk.eta, hfdef]
  have hG' : Integrable (fun u => (1 - u)⁻¹ * ∫ p, f p u ∂π) (Gam sig) := by
    rw [int_Gam_iff]
    refine hG.congr ?_
    filter_upwards [gam_ae_Ico sig] with u hu
    have : (1 - u) ≠ 0 := by linarith [hu.2]
    field_simp
  have hGint : ∫ u, (1 - u)⁻¹ * ∫ p, f p u ∂π ∂(Gam sig) = ∫ u, ∫ p, f p u ∂π ∂(gam sig) := by
    rw [integral_Gam]
    apply integral_congr_ae
    filter_upwards [gam_ae_Ico sig] with u hu
    have : (1 - u) ≠ 0 := by linarith [hu.2]
    field_simp
  have hF : Integrable (fun u => β u + (1 - u)⁻¹ * ∫ p, f p u ∂π) (Gam sig) :=
    (int_Gam_of_int_gam sig hβ).add hG'
  unfold H extIntegral
  rw [if_pos hF]
  congr 1
  rw [integral_add (int_Gam_of_int_gam sig hβ) hG', hGint, ← hswap]
  simp only [hC]

end Main


lemma int_pos {W : Type*} [MeasurableSpace W] {π : Measure W} [IsFiniteMeasure π] {L : W → ℝ}
    (hL : Integrable L π)
    (b : ℝ) : Integrable (fun p => max (L p - b) 0) π :=
  (hL.sub (integrable_const b)).pos_part

lemma g_convex {W : Type*} [MeasurableSpace W] {π : Measure W} [IsFiniteMeasure π] {L : W → ℝ} (hL : Integrable L π)
    {α : ℝ} (hα : α < 1) : ConvexOn ℝ Set.univ (fun b => g α b π L) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hc : 0 ≤ (1 - α)⁻¹ := inv_nonneg.2 (by linarith)
  have key : ∫ p, max (L p - (a * x + b * y)) 0 ∂π ≤
      a * ∫ p, max (L p - x) 0 ∂π + b * ∫ p, max (L p - y) 0 ∂π := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((int_pos hL x).const_mul a) ((int_pos hL y).const_mul b)]
    refine integral_mono (int_pos hL _) (((int_pos hL x).const_mul a).add
      ((int_pos hL y).const_mul b)) fun p => ?_
    have e : L p - (a * x + b * y) = a * (L p - x) + b * (L p - y) := by
      linear_combination (-(L p)) * hab
    show max (L p - (a * x + b * y)) 0 ≤ a * max (L p - x) 0 + b * max (L p - y) 0
    rw [e]
    exact max_le (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb))
      (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))
  simp only [g, smul_eq_mul]
  have := mul_le_mul_of_nonneg_left key hc
  nlinarith

lemma Φcont {W : Type*} [MeasurableSpace W] {π : Measure W} [IsProbabilityMeasure π]
    {L : W → ℝ} (hL : Integrable L π) : Continuous (fun b => ∫ p, max (L p - b) 0 ∂π) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun s t => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, ← integral_sub (int_pos hL s) (int_pos hL t)]
  have := norm_integral_le_of_norm_le_const (μ := π)
    (f := fun p => max (L p - s) 0 - max (L p - t) 0) (C := |s - t|)
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      have := abs_max_sub_max_le_abs (L p - s) (L p - t) 0
      rwa [show L p - s - (L p - t) = -(s - t) by ring, abs_neg] at this)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
  simpa using this

end MSRProp2Aux

open MSRP2Usc MSRProp2Aux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) :
    (∀ β ∈ DH sig L μ ν, ∀ π₀ ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ π₁ ∈ MongeKantorovichYao.transferencePlans μ ν,
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        H sig L (ENNReal.ofReal t • π₁ + ENNReal.ofReal (1 - t) • π₀) β =
          ((t : ℝ) : EReal) * H sig L π₁ β + ((1 - t : ℝ) : EReal) * H sig L π₀ β) ∧
    (∀ β : ℝ → ℝ, Integrable β (gam sig) →
      ∀ (πs : ℕ → ProbabilityMeasure (X × Y)) (π : ProbabilityMeasure (X × Y)),
        (∀ n, (πs n : Measure (X × Y)) ∈ MongeKantorovichYao.transferencePlans μ ν) →
        (π : Measure (X × Y)) ∈ MongeKantorovichYao.transferencePlans μ ν →
        Tendsto πs atTop (𝓝 π) →
        limsup (fun n => H sig L (πs n : Measure (X × Y)) β) atTop ≤
          H sig L (π : Measure (X × Y)) β) ∧
    (∀ π ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ β₀ β₁ : ℝ → ℝ,
      Integrable β₀ (Gam sig) → Integrable β₁ (Gam sig) → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        H sig L π (t • β₁ + (1 - t) • β₀) ≤
          ((t : ℝ) : EReal) * H sig L π β₁ + ((1 - t : ℝ) : EReal) * H sig L π β₀) ∧
    Convex ℝ (DH sig L μ ν) := by
  -- `H` unfolded
  have hHdef : ∀ (π : Measure (X × Y)) (β : ℝ → ℝ), H sig L π β =
      extIntegral (fun u => β u + (1 - u)⁻¹ * ∫ p, max (L p - β u) 0 ∂π) (Gam sig) :=
    fun _ _ => rfl
  have hext : ∀ f : ℝ → ℝ, Integrable f (Gam sig) →
      extIntegral f (Gam sig) = ((∫ u, f u ∂(Gam sig) : ℝ) : EReal) := fun f hf => by
    unfold extIntegral; rw [if_pos hf]
  have hext' : ∀ f : ℝ → ℝ, ¬ Integrable f (Gam sig) → extIntegral f (Gam sig) = ⊤ :=
    fun f hf => by unfold extIntegral; rw [if_neg hf]
  have hext_ne_bot : ∀ f : ℝ → ℝ, extIntegral f (Gam sig) ≠ ⊥ := fun f => by
    unfold extIntegral; split_ifs
    · exact EReal.coe_ne_bot _
    · exact top_ne_bot
  -- (iii) convexity in `β`
  have hiii : ∀ π ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ β₀ β₁ : ℝ → ℝ,
      Integrable β₀ (Gam sig) → Integrable β₁ (Gam sig) → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        H sig L π (t • β₁ + (1 - t) • β₀) ≤
          ((t : ℝ) : EReal) * H sig L π β₁ + ((1 - t : ℝ) : EReal) * H sig L π β₀ := by
    intro π hπ β₀ β₁ h0 h1 t ht
    haveI : IsProbabilityMeasure π := hπ.1
    have hL := L_int hA hπ
    have hLm := L_meas hA
    obtain ⟨hmin, hES0, hglb, -⟩ := eq_2 π L hLm hL
    obtain ⟨hESi, -⟩ := es_representation sig π L hLm hL
    have hlow : ∀ u ∈ Set.Ico (0 : ℝ) 1, ∀ b, ES u π L ≤ g u b π L := by
      intro u hu b
      rcases eq_or_lt_of_le hu.1 with h0 | hpos
      · subst h0
        rw [hES0]; exact hglb.1 ⟨b, rfl⟩
      · exact (hmin u ⟨hpos, hu.2⟩).2 ⟨b, rfl⟩
    set F : (ℝ → ℝ) → ℝ → ℝ := fun β u => β u + (1 - u)⁻¹ * ∫ p, max (L p - β u) 0 ∂π
      with hF
    rw [hHdef, hHdef, hHdef]
    by_cases hi1 : Integrable (F β₁) (Gam sig)
    · by_cases hi0 : Integrable (F β₀) (Gam sig)
      · have hβt : AEStronglyMeasurable (t • β₁ + (1 - t) • β₀) (Gam sig) :=
          (h1.1.const_smul t).add (h0.1.const_smul (1 - t))
        have hmeas : AEStronglyMeasurable (F (t • β₁ + (1 - t) • β₀)) (Gam sig) :=
          hβt.add ((((measurable_const.sub measurable_id).inv).aestronglyMeasurable).mul
            ((Φcont hL).comp_aestronglyMeasurable hβt))
        have hR : Integrable (fun u => t * F β₁ u + (1 - t) * F β₀ u) (Gam sig) :=
          (hi1.const_mul t).add (hi0.const_mul (1 - t))
        have hle : ∀ᵐ u ∂(Gam sig), ES u π L ≤ F (t • β₁ + (1 - t) • β₀) u ∧
            F (t • β₁ + (1 - t) • β₀) u ≤ t * F β₁ u + (1 - t) * F β₀ u := by
          filter_upwards [Gam_ae_Ico sig] with u hu
          refine ⟨hlow u hu _, ?_⟩
          have hc := (g_convex hL (α := u) hu.2).2 (Set.mem_univ (β₁ u)) (Set.mem_univ (β₀ u))
            ht.1.le (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) (by ring)
          simp only [smul_eq_mul] at hc
          simpa [F, g, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hc
        have hint : Integrable (F (t • β₁ + (1 - t) • β₀)) (Gam sig) := by
          refine Integrable.mono' (hESi.abs.add hR.abs) hmeas ?_
          filter_upwards [hle] with u hu
          obtain ⟨hu1, hu2⟩ := hu
          simp only [Pi.add_apply]
          rw [Real.norm_eq_abs, abs_le]
          constructor
          · linarith [neg_abs_le (ES u π L), abs_nonneg (t * F β₁ u + (1 - t) * F β₀ u)]
          · linarith [le_abs_self (t * F β₁ u + (1 - t) * F β₀ u), abs_nonneg (ES u π L)]
        rw [hext _ hint, hext _ hi1, hext _ hi0, ← EReal.coe_mul, ← EReal.coe_mul,
          ← EReal.coe_add, EReal.coe_le_coe_iff]
        calc ∫ u, F (t • β₁ + (1 - t) • β₀) u ∂(Gam sig)
            ≤ ∫ u, (t * F β₁ u + (1 - t) * F β₀ u) ∂(Gam sig) :=
              integral_mono_ae hint hR (by filter_upwards [hle] with u hu using hu.2)
          _ = t * ∫ u, F β₁ u ∂(Gam sig) + (1 - t) * ∫ u, F β₀ u ∂(Gam sig) := by
              rw [integral_add (hi1.const_mul t) (hi0.const_mul (1 - t)), integral_const_mul,
                integral_const_mul]
      · rw [hext' _ hi0, EReal.coe_mul_top_of_pos (by linarith [ht.2]),
          EReal.add_top_of_ne_bot]
        · exact le_top
        · rw [hext _ hi1, ← EReal.coe_mul]; exact EReal.coe_ne_bot _
    · rw [hext' _ hi1, EReal.coe_mul_top_of_pos ht.1, EReal.top_add_of_ne_bot]
      · exact le_top
      · by_cases hi0 : Integrable (F β₀) (Gam sig)
        · rw [hext _ hi0, ← EReal.coe_mul]; exact EReal.coe_ne_bot _
        · rw [hext' _ hi0, EReal.coe_mul_top_of_pos (by linarith [ht.2])]
          exact top_ne_bot
  refine ⟨?_, ?_, hiii, ?_⟩
  · -- (i) affinity in `π`
    intro β hβ π₀ h0 π₁ h1 t ht
    haveI : IsProbabilityMeasure π₀ := h0.1
    haveI : IsProbabilityMeasure π₁ := h1.1
    have hfin : ∀ π ∈ MongeKantorovichYao.transferencePlans μ ν,
        Integrable (fun u => β u + (1 - u)⁻¹ * ∫ p, max (L p - β u) 0 ∂π) (Gam sig) := by
      intro π hπ
      have := hβ.2 π hπ
      rw [hHdef] at this
      by_contra hc
      rw [hext' _ hc] at this
      exact lt_irrefl _ this
    have ht0 : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
    have hmix : ∀ u, ∫ p, max (L p - β u) 0 ∂(ENNReal.ofReal t • π₁ + ENNReal.ofReal (1 - t) • π₀)
        = t * ∫ p, max (L p - β u) 0 ∂π₁ + (1 - t) * ∫ p, max (L p - β u) 0 ∂π₀ := by
      intro u
      have i1 := int_pos (L_int hA h1) (β u)
      have i0 := int_pos (L_int hA h0) (β u)
      rw [integral_add_measure (i1.smul_measure ENNReal.ofReal_ne_top)
        (i0.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
        ENNReal.toReal_ofReal ht.1.le, ENNReal.toReal_ofReal ht0, smul_eq_mul, smul_eq_mul]
    have hF : (fun u => β u + (1 - u)⁻¹ * ∫ p, max (L p - β u) 0 ∂(ENNReal.ofReal t • π₁ +
        ENNReal.ofReal (1 - t) • π₀)) = fun u =>
        t * (β u + (1 - u)⁻¹ * ∫ p, max (L p - β u) 0 ∂π₁) +
        (1 - t) * (β u + (1 - u)⁻¹ * ∫ p, max (L p - β u) 0 ∂π₀) := by
      funext u; rw [hmix]; ring
    have hI : Integrable (fun u => t * (β u + (1 - u)⁻¹ * ∫ p, max (L p - β u) 0 ∂π₁) +
        (1 - t) * (β u + (1 - u)⁻¹ * ∫ p, max (L p - β u) 0 ∂π₀)) (Gam sig) :=
      ((hfin _ h1).const_mul t).add ((hfin _ h0).const_mul _)
    rw [hHdef, hHdef, hHdef, hF, hext _ hI,
      hext _ (hfin _ h1), hext _ (hfin _ h0),
      integral_add ((hfin _ h1).const_mul t) ((hfin _ h0).const_mul _), integral_const_mul,
      integral_const_mul, EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
  · -- (ii) upper semicontinuity in `π`
    intro β hβ πs π hπs hπ hlim
    have hLm := L_meas hA
    obtain ⟨hCusc, hCint_u, -, -⟩ := lemma_1 μ ν sig L hA β hβ
    obtain ⟨A, B, hAlsc, hAi, hBlsc, hBi, hub⟩ := hA.upper_bound
    set m := (gam sig).real Set.univ with hm
    have hm0 : 0 ≤ m := measureReal_nonneg
    set k0 := ∫ u, max (-β u) 0 ∂(gam sig) with hk0
    set Ap : X → ℝ := fun x => max (A x) 0
    set Bp : Y → ℝ := fun y => max (B y) 0
    have hApl : LowerSemicontinuous Ap := hAlsc.sup lowerSemicontinuous_const
    have hBpl : LowerSemicontinuous Bp := hBlsc.sup lowerSemicontinuous_const
    set Cf : X × Y → ℝ := fun p => Cbeta sig L β p.1 p.2 with hCf
    set f : X × Y → ℝ := fun p => min (Cf p + (-(m * Ap p.1)) + (-(m * Bp p.2)) + (-k0)) 0
      with hfdef
    have hmul_lsc : ∀ {h : X × Y → ℝ}, LowerSemicontinuous h →
        UpperSemicontinuous (fun z => -(m * h z)) := by
      intro h hh
      have h1 : LowerSemicontinuous (fun z => m * h z) :=
        (continuous_const.mul continuous_id :
          Continuous fun y : ℝ => m * y).comp_lowerSemicontinuous hh
          (fun a b hab => mul_le_mul_of_nonneg_left hab hm0)
      exact continuous_neg.comp_lowerSemicontinuous_antitone h1 (fun a b hab => neg_le_neg hab)
    have hf_usc : UpperSemicontinuous f := by
      have h1 : UpperSemicontinuous (fun p : X × Y => -(m * Ap p.1)) :=
        hmul_lsc (h := fun p => Ap p.1) (hApl.comp continuous_fst)
      have h2 : UpperSemicontinuous (fun p : X × Y => -(m * Bp p.2)) :=
        hmul_lsc (h := fun p => Bp p.2) (hBpl.comp continuous_snd)
      have h3 := ((hCusc.add h1).add h2).add (upperSemicontinuous_const (z := -k0))
      exact (continuous_id.min continuous_const :
        Continuous fun y : ℝ => min y 0).comp_upperSemicontinuous h3
        (fun a b hab => min_le_min hab le_rfl)
    have hf_le : ∀ p, f p ≤ 0 := fun p => min_le_right _ _
    -- the bound `C^β ≤ m A₊ + m B₊ + k₀` off a null rectangle
    have hCbd : AERect μ ν (fun x y => Cbeta sig L β x y ≤ m * Ap x + m * Bp y + k0) := by
      obtain ⟨N, hN, N', hN', hP⟩ := hub
      refine ⟨N, hN, N', hN', fun x hx y hy => ?_⟩
      have hxy := hP x hx y hy
      have hneg : Integrable (fun u => max (-β u) 0) (gam sig) := hβ.neg.pos_part
      calc Cbeta sig L β x y ≤ ∫ u, (max (A x + B y) 0 + max (-β u) 0) ∂(gam sig) :=
            integral_mono (hCint_u x y) ((integrable_const _).add hneg) fun u =>
              max_le (by linarith [le_max_left (A x + B y) 0, le_max_left (-β u) 0])
                (add_nonneg (le_max_right _ _) (le_max_right _ _))
        _ = m * max (A x + B y) 0 + k0 := by
            rw [integral_add (integrable_const _) hneg, integral_const, smul_eq_mul]
        _ ≤ m * Ap x + m * Bp y + k0 := by
            have : max (A x + B y) 0 ≤ Ap x + Bp y :=
              max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
                (add_nonneg (le_max_right _ _) (le_max_right _ _))
            nlinarith
    have hApi : Integrable Ap μ := hAi.pos_part
    have hBpi : Integrable Bp ν := hBi.pos_part
    set Kc := m * ∫ x, Ap x ∂μ + m * ∫ y, Bp y ∂ν + k0 with hKc
    -- on every coupling, `f = C - (m A₊ + m B₊ + k₀)` a.e.
    have hf_ae : ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν,
        f =ᵐ[π'] fun p => Cf p - m * Ap p.1 - m * Bp p.2 - k0 := by
      intro π' hπ'
      filter_upwards [aerect_ae hCbd hπ'] with p hp
      simp only [hfdef]
      rw [min_eq_left (by simp only [hCf]; linarith)]
      ring
    have hgi : ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν,
        Integrable (fun p => Cf p - m * Ap p.1 - m * Bp p.2 - k0) π' := by
      intro π' hπ'
      haveI : IsProbabilityMeasure π' := hπ'.1
      exact (((C_int hA hπ' β hβ).sub ((int_fst hπ' hApi).const_mul m)).sub
        ((int_snd hπ' hBpi).const_mul m)).sub (integrable_const k0)
    have hfi : ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν, Integrable f π' :=
      fun π' hπ' => (hgi π' hπ').congr (hf_ae π' hπ').symm
    have hfint : ∀ π' ∈ MongeKantorovichYao.transferencePlans μ ν,
        ∫ p, f p ∂π' = ∫ p, Cf p ∂π' - Kc := by
      intro π' hπ'
      haveI : IsProbabilityMeasure π' := hπ'.1
      rw [integral_congr_ae (hf_ae π' hπ'), integral_sub _ (integrable_const k0),
        integral_sub _ ((int_snd hπ' hBpi).const_mul m),
        integral_sub (C_int hA hπ' β hβ) ((int_fst hπ' hApi).const_mul m),
        integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul]
      · have e1 : ∫ p, Ap p.1 ∂π' = ∫ x, Ap x ∂μ := by
          rw [← hπ'.2.1, integral_map measurable_fst.aemeasurable
            (by rw [hπ'.2.1]; exact hApi.1)]
        have e2 : ∫ p, Bp p.2 ∂π' = ∫ y, Bp y ∂ν := by
          rw [← hπ'.2.2, integral_map measurable_snd.aemeasurable
            (by rw [hπ'.2.2]; exact hBpi.1)]
        rw [e1, e2, hKc]; ring
      · exact (C_int hA hπ' β hβ).sub ((int_fst hπ' hApi).const_mul m)
      · exact ((C_int hA hπ' β hβ).sub ((int_fst hπ' hApi).const_mul m)).sub
          ((int_snd hπ' hBpi).const_mul m)
    -- the key eventual bound
    have hkey : ∀ r : ℝ, ∫ p, Cf p ∂(π : Measure (X × Y)) < r →
        ∀ᶠ n in atTop, ∫ p, Cf p ∂(πs n : Measure (X × Y)) < r := by
      intro r hr
      have ht : ∫ p, f p ∂(π : Measure (X × Y)) < r - Kc := by rw [hfint _ hπ]; linarith
      have hev := eventually_integral_lt_of_usc hlim hf_usc hf_le (hfi _ hπ)
        (fun n => hfi _ (hπs n)) ht
      filter_upwards [hev] with n hn
      rw [hfint _ (hπs n)] at hn
      linarith
    set a := ∫ u, β u ∂(Gam sig)
    have hHn : ∀ n, H sig L (πs n : Measure (X × Y)) β =
        ((a + ∫ p, Cf p ∂(πs n : Measure (X × Y)) : ℝ) : EReal) := fun n =>
      H_eq hA (hπs n) β hβ
    rw [H_eq hA hπ β hβ]
    by_contra hcon
    push Not at hcon
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hr1' : ∫ p, Cf p ∂(π : Measure (X × Y)) < r - a := by
      have := EReal.coe_lt_coe_iff.1 hr1; linarith
    have hev := hkey (r - a) hr1'
    have hle : limsup (fun n => H sig L (πs n : Measure (X × Y)) β) atTop ≤ (r : EReal) := by
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [hev] with n hn
      rw [hHn n, EReal.coe_le_coe_iff]
      linarith
    exact absurd (lt_of_lt_of_le hr2 hle) (lt_irrefl _)
  · -- (iv) convexity of `D_H`
    intro x hx y hy a b ha hb hab
    rcases ha.eq_or_lt with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1, zero_smul, zero_add, one_smul]
      exact hy
    rcases hb.eq_or_lt with hb0 | hb0
    · have ha1 : a = 1 := by linarith
      rw [← hb0, ha1, zero_smul, add_zero, one_smul]
      exact hx
    have hb' : b = 1 - a := by linarith
    refine ⟨(hx.1.smul a).add (hy.1.smul b), fun π hπ => ?_⟩
    have h := hiii π hπ y x hy.1 hx.1 a ⟨ha0, by linarith⟩
    rw [← hb'] at h
    refine lt_of_le_of_lt h ?_
    have hfx := hx.2 π hπ
    have hfy := hy.2 π hπ
    have hxb : H sig L π x ≠ ⊥ := by rw [hHdef]; exact hext_ne_bot _
    have hyb : H sig L π y ≠ ⊥ := by rw [hHdef]; exact hext_ne_bot _
    rw [← EReal.coe_toReal hfx.ne hxb, ← EReal.coe_toReal hfy.ne hyb, ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_lt_top _
