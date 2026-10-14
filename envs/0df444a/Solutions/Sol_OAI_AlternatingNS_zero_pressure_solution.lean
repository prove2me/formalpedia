-- Prove2me | solution 1 for OAI.AlternatingNS.zero_pressure_solution
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T02:23:13.200164+00:00
-- url     : https://prove2.me/submissions/a97d1188-b62c-431b-8b3d-f95de984428e

import Mathlib
import Definitions.Def_NavierStokesAlternating

set_option autoImplicit false

open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory OAI OAI.AlternatingNS

namespace AN_R

noncomputable section

/-- The closed half-space `[0, ∞) × ℝ³`. -/
abbrev HS : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set Space)

lemma uniqueDiffOn_HS : UniqueDiffOn ℝ HS := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

lemma mem_HS {t : ℝ} (ht : 0 ≤ t) (x : Space) : ((t, x) : ℝ × Space) ∈ HS := by
  simp [HS, ht]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The within-derivative of the uncurried field on the half-space. -/
abbrev DD (F : AlternatingNS.Field E) : ℝ × Space → (ℝ × Space →L[ℝ] E) :=
  fderivWithin ℝ (Function.uncurry F) HS

lemma hasFDerivWithinAt_DD {F : AlternatingNS.Field E} (hF : Smooth F) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    HasFDerivWithinAt (Function.uncurry F) (DD F (t, x)) HS (t, x) := by
  have h1 : DifferentiableOn ℝ (Function.uncurry F) HS :=
    hF.differentiableOn (by simp)
  exact (h1 _ (mem_HS ht x)).hasFDerivWithinAt

lemma contDiffOn_DD {F : AlternatingNS.Field E} (hF : Smooth F) : ContDiffOn ℝ ∞ (DD F) HS :=
  ContDiffOn.fderivWithin hF uniqueDiffOn_HS (by simp)

lemma hasFDerivAt_space {F : AlternatingNS.Field E} (hF : Smooth F) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    HasFDerivAt (F t) ((DD F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
  have h1 := hasFDerivWithinAt_DD hF ht x
  have h2 : HasFDerivWithinAt (fun y : Space => ((t, y) : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) Set.univ x :=
    (hasFDerivAt_prodMk_right t x).hasFDerivWithinAt
  have h3 := h1.comp x h2 (fun y _ => mem_HS ht y)
  exact hasFDerivWithinAt_univ.mp h3

lemma hasFDerivWithinAt_time {F : AlternatingNS.Field E} (hF : Smooth F) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    HasFDerivWithinAt (fun s => F s x) ((DD F (t, x)).comp (ContinuousLinearMap.inl ℝ ℝ Space))
      (Set.Ici 0) t := by
  have h1 := hasFDerivWithinAt_DD hF ht x
  have h2 : HasFDerivWithinAt (fun s : ℝ => ((s, x) : ℝ × Space))
      (ContinuousLinearMap.inl ℝ ℝ Space) (Set.Ici 0) t :=
    (hasFDerivAt_prodMk_left t x).hasFDerivWithinAt
  exact h1.comp t h2 (fun s hs => mem_HS hs x)

lemma dx_eq {F : AlternatingNS.Field E} (hF : Smooth F) (i : Fin 3) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    dx i F t x = DD F (t, x) (0, e i) := by
  simp only [dx]
  rw [(hasFDerivAt_space hF ht x).fderiv]
  rfl

lemma dt_eq {F : AlternatingNS.Field E} (hF : Smooth F) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    dt F t x = DD F (t, x) (1, 0) := by
  simp only [dt]
  rw [(hasFDerivWithinAt_time hF ht x).fderivWithin (uniqueDiffOn_Ici 0 t ht)]
  rfl

lemma smooth_dx {F : AlternatingNS.Field E} (hF : Smooth F) (i : Fin 3) : Smooth (dx i F) := by
  have h : ContDiffOn ℝ ∞ (fun z => DD F z (0, e i)) HS :=
    (contDiffOn_DD hF).clm_apply contDiffOn_const
  refine h.congr ?_
  rintro ⟨t, x⟩ hz
  exact dx_eq hF i hz.1 x

lemma smooth_dt {F : AlternatingNS.Field E} (hF : Smooth F) : Smooth (dt F) := by
  have h : ContDiffOn ℝ ∞ (fun z => DD F z (1, 0)) HS :=
    (contDiffOn_DD hF).clm_apply contDiffOn_const
  refine h.congr ?_
  rintro ⟨t, x⟩ hz
  exact dt_eq hF hz.1 x

lemma smooth_iterate_dx {F : AlternatingNS.Field E} (hF : Smooth F) (i : Fin 3) (n : ℕ) :
    Smooth ((dx i)^[n] F) := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact smooth_dx ih i

lemma smooth_spatial {F : AlternatingNS.Field E} (hF : Smooth F) (α : MultiIndex) : Smooth (spatial α F) :=
  smooth_iterate_dx (smooth_iterate_dx (smooth_iterate_dx hF 2 _) 1 _) 0 _

/-- Vanishing outside a closed set is preserved by spatial derivatives. -/
lemma vanish_dx {F : AlternatingNS.Field E} {K : Set Space} (hK : IsClosed K)
    (hF : ∀ t, 0 ≤ t → ∀ x, x ∉ K → F t x = 0) (i : Fin 3) :
    ∀ t, 0 ≤ t → ∀ x, x ∉ K → dx i F t x = 0 := by
  intro t ht x hx
  have hev : F t =ᶠ[𝓝 x] fun _ => (0 : E) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact hF t ht y hy
  simp only [dx]
  rw [hev.fderiv_eq]
  simp

lemma vanish_iterate_dx {F : AlternatingNS.Field E} {K : Set Space} (hK : IsClosed K)
    (hF : ∀ t, 0 ≤ t → ∀ x, x ∉ K → F t x = 0) (i : Fin 3) (n : ℕ) :
    ∀ t, 0 ≤ t → ∀ x, x ∉ K → (dx i)^[n] F t x = 0 := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact vanish_dx hK ih i

lemma vanish_spatial {F : AlternatingNS.Field E} {K : Set Space} (hK : IsClosed K)
    (hF : ∀ t, 0 ≤ t → ∀ x, x ∉ K → F t x = 0) (α : MultiIndex) :
    ∀ t, 0 ≤ t → ∀ x, x ∉ K → spatial α F t x = 0 :=
  vanish_iterate_dx hK (vanish_iterate_dx hK (vanish_iterate_dx hK hF 2 _) 1 _) 0 _

lemma vanish_dt {F : AlternatingNS.Field E} {K : Set Space}
    (hF : ∀ t, 0 ≤ t → ∀ x, x ∉ K → F t x = 0) :
    ∀ t, 0 ≤ t → ∀ x, x ∉ K → dt F t x = 0 := by
  intro t ht x hx
  simp only [dt]
  have : fderivWithin ℝ (fun s => F s x) (Set.Ici 0) t
      = fderivWithin ℝ (fun _ => (0 : E)) (Set.Ici 0) t :=
    fderivWithin_congr (fun s hs => hF s hs x hx) (hF t ht x hx)
  rw [this]
  simp




omit [NormedSpace ℝ E] in
lemma unif_close {F : ℝ → Space → E} (hF : Continuous (Function.uncurry F)) {K : Set Space}
    (hK : IsCompact K) (h0 : ∀ s x, x ∉ K → F s x = 0) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, dist s t < δ → ∀ x, ‖F s x - F t x‖ ≤ ε := by
  have hc : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ K) := isCompact_Icc.prod hK
  have hu := hc.uniformContinuousOn_of_continuous hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδ'⟩ := hu ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun s hs x => ?_⟩
  by_cases hx : x ∈ K
  · have hs1 : dist s t < δ := lt_of_lt_of_le hs (min_le_left _ _)
    have hs2 : dist s t < 1 := lt_of_lt_of_le hs (min_le_right _ _)
    rw [Real.dist_eq, abs_lt] at hs2
    have := hδ' (s, x) ⟨⟨by linarith, by linarith⟩, hx⟩ (t, x) ⟨⟨by linarith, by linarith⟩, hx⟩
      (by simpa [Prod.dist_eq] using hs1)
    rw [dist_eq_norm] at this
    exact this.le
  · simp [h0 s x hx, h0 t x hx, hε.le]

omit [NormedSpace ℝ E] in
lemma norm_toLp_le {f : Space → E} (hf : MemLp f 2 volume) {K : Set Space} (hK : IsCompact K)
    (h0 : ∀ x, x ∉ K → f x = 0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    ‖hf.toLp f‖ ≤ C * (volume K ^ (1 / (2 : ℝ))).toReal := by
  rw [Lp.norm_toLp]
  have h1 : eLpNorm f 2 volume ≤ eLpNorm (K.indicator fun _ => C) 2 volume := by
    apply eLpNorm_mono
    intro x
    by_cases hx : x ∈ K
    · simp [hx, abs_of_nonneg hC, hb x]
    · simp [hx, h0 x hx]
  rw [eLpNorm_indicator_const hK.measurableSet two_ne_zero ENNReal.ofNat_ne_top] at h1
  have hfin : ‖C‖ₑ * volume K ^ (1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hK.measure_lt_top.ne)
  calc (eLpNorm f 2 volume).toReal
      ≤ (‖C‖ₑ * volume K ^ (1 / (2 : ℝ≥0∞).toReal)).toReal := ENNReal.toReal_mono hfin h1
    _ = C * (volume K ^ (1 / (2 : ℝ))).toReal := by
      rw [ENNReal.toReal_mul]
      simp [abs_of_nonneg hC]

omit [NormedSpace ℝ E] in
lemma continuous_toL2 {F : ℝ → Space → E} (hF : Continuous (Function.uncurry F)) {K : Set Space}
    (hK : IsCompact K) (h0 : ∀ s x, x ∉ K → F s x = 0) (hm : ∀ s, MemLp (F s) 2 volume) :
    Continuous (fun s => (hm s).toLp (F s)) := by
  rw [Metric.continuous_iff]
  intro t ε hε
  set M := (volume K ^ (1 / (2 : ℝ))).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  obtain ⟨δ, hδ, hδ'⟩ := unif_close hF hK h0 t (ε := ε / (M + 1)) (by positivity)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  rw [dist_eq_norm, ← MemLp.toLp_sub]
  calc _ ≤ ε / (M + 1) * M :=
        norm_toLp_le _ hK (fun x hx => by simp [h0 s x hx, h0 t x hx]) (by positivity)
          (fun x => hδ' s hs x)
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

lemma hasDerivWithinAt_toL2 {F F' : ℝ → Space → E} (hF' : Continuous (Function.uncurry F'))
    {K : Set Space} (hK : IsCompact K) (h0 : ∀ s x, x ∉ K → F s x = 0)
    (h0' : ∀ s x, x ∉ K → F' s x = 0)
    (hm : ∀ s, MemLp (F s) 2 volume) (hm' : ∀ s, MemLp (F' s) 2 volume)
    (hd : ∀ x, ∀ τ, 0 ≤ τ → HasDerivWithinAt (fun s => F s x) (F' τ x) (Set.Ici 0) τ)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => (hm s).toLp (F s)) ((hm' t).toLp (F' t)) (Set.Ici 0) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set M := (volume K ^ (1 / (2 : ℝ))).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  obtain ⟨δ, hδ, hδ'⟩ := unif_close hF' hK h0' t (ε := ε / (M + 1)) (by positivity)
  refine ⟨δ, hδ, fun s hs hst => ?_⟩
  have hsne : s ≠ t := hs.2
  have hs0 : 0 ≤ s := hs.1
  have hpt : ∀ x, ‖(s - t)⁻¹ • (F s x - F t x) - F' t x‖ ≤ ε / (M + 1) := by
    intro x
    set D := Set.Ici (0 : ℝ) ∩ Metric.ball t δ
    have hDc : Convex ℝ D := (convex_Ici 0).inter (convex_ball t δ)
    let φ : ℝ → E := fun τ => F τ x - (τ - t) • F' t x
    have hφ : ∀ τ ∈ D, HasDerivWithinAt φ (F' τ x - F' t x) D τ := by
      intro τ hτ
      have h1 := (hd x τ hτ.1).mono (Set.inter_subset_left : D ⊆ Set.Ici 0)
      have h2 : HasDerivWithinAt (fun τ : ℝ => (τ - t) • F' t x) ((1 : ℝ) • F' t x) D τ :=
        (((hasDerivAt_id τ).sub_const t).smul_const (F' t x)).hasDerivWithinAt
      have h3 := h1.sub h2
      simp only [one_smul] at h3
      exact h3
    have hb : ∀ τ ∈ D, ‖F' τ x - F' t x‖ ≤ ε / (M + 1) :=
      fun τ hτ => hδ' τ (Metric.mem_ball.mp hτ.2) x
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hb hDc
      ⟨ht, Metric.mem_ball_self hδ⟩ ⟨hs0, Metric.mem_ball.mpr hst⟩
    have hne : s - t ≠ 0 := sub_ne_zero.mpr hsne
    have hrw : (s - t)⁻¹ • (F s x - F t x) - F' t x = (s - t)⁻¹ • (φ s - φ t) := by
      simp only [φ, sub_self, zero_smul, sub_zero, smul_sub, smul_smul, inv_mul_cancel₀ hne,
        one_smul]
      abel
    rw [hrw, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [Real.norm_eq_abs] at hmvt
    rw [inv_mul_le_iff₀ (abs_pos.mpr hne)]
    linarith [hmvt]
  rw [slope_def_module, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_const_smul,
    ← MemLp.toLp_sub]
  calc _ ≤ ε / (M + 1) * M :=
        norm_toLp_le _ hK (fun x hx => by simp [h0 s x hx, h0 t x hx, h0' t x hx])
          (by positivity) (fun x => by simpa using hpt x)
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith


/-! ### Extension in time and `L²` realisations -/

/-- Extension of a field to negative times by its value at time `0`. -/
def ext (F : AlternatingNS.Field E) : AlternatingNS.Field E := fun s x => F (max s 0) x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma ext_of_nonneg (F : AlternatingNS.Field E) {t : ℝ} (ht : 0 ≤ t) : ext F t = F t := by
  funext x
  simp [ext, max_eq_left ht]

omit [NormedSpace ℝ E] in
lemma continuous_ext {F : AlternatingNS.Field E} (hF : ContinuousOn (Function.uncurry F) HS) :
    Continuous (Function.uncurry (ext F)) := by
  have hc : Continuous (fun z : ℝ × Space => ((max z.1 0, z.2) : ℝ × Space)) := by
    fun_prop
  exact hF.comp_continuous hc (fun z => mem_HS (le_max_right _ _) _)

omit [NormedSpace ℝ E] in
lemma vanish_ext {F : AlternatingNS.Field E} {K : Set Space}
    (h0 : ∀ t, 0 ≤ t → ∀ x, x ∉ K → F t x = 0) : ∀ s x, x ∉ K → ext F s x = 0 :=
  fun s x hx => h0 (max s 0) (le_max_right _ _) x hx

omit [NormedSpace ℝ E] in
lemma memLp_ext {F : AlternatingNS.Field E} (hF : ContinuousOn (Function.uncurry F) HS)
    {K : Set Space} (hK : IsCompact K) (h0 : ∀ t, 0 ≤ t → ∀ x, x ∉ K → F t x = 0) (s : ℝ) :
    MemLp (ext F s) 2 volume := by
  have hc : Continuous (ext F s) := (continuous_ext hF).uncurry_left s
  have hcs : HasCompactSupport (ext F s) := HasCompactSupport.intro hK (vanish_ext h0 s)
  exact hc.memLp_of_hasCompactSupport hcs

omit [NormedSpace ℝ E] in
lemma L2_of_continuousOn {F : AlternatingNS.Field E} (hF : ContinuousOn (Function.uncurry F) HS)
    {K : Set Space} (hK : IsCompact K) (h0 : ∀ t, 0 ≤ t → ∀ x, x ∉ K → F t x = 0) :
    ∃ g : ℝ → Lp E 2 (volume : Measure Space), Continuous g ∧
      ∀ t, 0 ≤ t → ∀ᵐ x ∂(volume : Measure Space), (g t) x = F t x := by
  refine ⟨fun s => (memLp_ext hF hK h0 s).toLp (ext F s),
    continuous_toL2 (continuous_ext hF) hK (vanish_ext h0) _, fun t ht => ?_⟩
  filter_upwards [(memLp_ext hF hK h0 t).coeFn_toLp] with x hx
  exact hx.trans (congrFun (ext_of_nonneg F ht) x)

lemma continuousInH_of {F : AlternatingNS.Field E} (hF : Smooth F) {K : Set Space}
    (hK : IsCompact K) (h0 : ∀ t, 0 ≤ t → ∀ x, x ∉ K → F t x = 0) (k : ℕ) (T : ℝ) :
    ContinuousInH k F T := by
  intro α _
  obtain ⟨g, hg, hgt⟩ := L2_of_continuousOn (smooth_spatial hF α).continuousOn hK
    (vanish_spatial hK.isClosed h0 α)
  exact ⟨g, hg.continuousOn, fun t ht => hgt t ht.1⟩

lemma hasDerivWithinAt_ext_time {F : AlternatingNS.Field E} (hF : Smooth F) (x : Space) (τ : ℝ)
    (hτ : 0 ≤ τ) :
    HasDerivWithinAt (fun s => ext F s x) (ext (dt F) τ x) (Set.Ici 0) τ := by
  have h1 := (hasFDerivWithinAt_time hF hτ x).hasDerivWithinAt
  have h2 : ext (dt F) τ x = DD F (τ, x) (1, 0) := by
    rw [ext_of_nonneg _ hτ, dt_eq hF hτ x]
  rw [h2]
  refine h1.congr (fun s hs => ?_) ?_
  · simp only [ext, max_eq_left (show (0 : ℝ) ≤ s from hs)]
  · simp only [ext, max_eq_left hτ]

lemma c1InL2_of {U : Velocity} (hU : Smooth U) {K : Set Space} (hK : IsCompact K)
    (h0 : ∀ t, 0 ≤ t → ∀ x, x ∉ K → U t x = 0) (T : ℝ) : C1InL2 U T := by
  have hc := hU.continuousOn
  have hc' := (smooth_dt hU).continuousOn
  have h0' := vanish_dt h0
  have hm := memLp_ext hc hK h0
  have hm' := memLp_ext hc' hK h0'
  refine ⟨fun s => (hm s).toLp (ext U s), fun s => (hm' s).toLp (ext (dt U) s),
    (continuous_toL2 (continuous_ext hc) hK (vanish_ext h0) hm).continuousOn,
    (continuous_toL2 (continuous_ext hc') hK (vanish_ext h0') hm').continuousOn,
    fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · exact (hasDerivWithinAt_toL2 (continuous_ext hc') hK (vanish_ext h0) (vanish_ext h0') hm hm'
      (hasDerivWithinAt_ext_time hU) ht.1).mono Set.Icc_subset_Ici_self
  · filter_upwards [(hm t).coeFn_toLp] with x hx
    exact hx.trans (congrFun (ext_of_nonneg U ht.1) x)
  · filter_upwards [(hm' t).coeFn_toLp] with x hx
    exact hx.trans (congrFun (ext_of_nonneg (dt U) ht.1) x)

lemma bound_of {U : Velocity} (hU : Smooth U) {K : Set Space} (hK : IsCompact K)
    (h0 : ∀ t, 0 ≤ t → ∀ x, x ∉ K → U t x = 0) (T : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x, ‖U t x‖ + ‖fderiv ℝ (U t) x‖ ≤ C := by
  let H : ℝ × Space → ℝ := fun z =>
    ‖Function.uncurry U z‖ + ‖(DD U z).comp (ContinuousLinearMap.inr ℝ ℝ Space)‖
  have hH : ContinuousOn H HS :=
    hU.continuousOn.norm.add
      (((contDiffOn_DD hU).continuousOn.clm_comp continuousOn_const).norm)
  have hsub : Set.Icc 0 T ×ˢ K ⊆ HS := Set.prod_mono Set.Icc_subset_Ici_self (Set.subset_univ _)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hH.mono hsub)
  refine ⟨max C 0, fun t ht x => ?_⟩
  by_cases hx : x ∈ K
  · have h1 : fderiv ℝ (U t) x = (DD U (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
      (hasFDerivAt_space hU ht.1 x).fderiv
    have h2 := hC (t, x) ⟨ht, hx⟩
    have h3 : ‖U t x‖ + ‖fderiv ℝ (U t) x‖ = H (t, x) := by
      simp only [H, h1, Function.uncurry_apply_pair]
    rw [h3]
    exact le_trans (le_abs_self _) (le_trans (by simpa using h2) (le_max_left _ _))
  · have hev : U t =ᶠ[𝓝 x] fun _ => (0 : Space) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact h0 t ht.1 y hy
    rw [hev.fderiv_eq, h0 t ht.1 x hx]
    simp

lemma zero_field_eq : ∀ i : Fin 3, dx i (fun _ _ => (0 : ℝ)) = fun _ _ => 0 := by
  intro i
  funext t x
  simp [dx]

lemma grad_zero (t : ℝ) (x : Space) : grad (fun _ _ => (0 : ℝ)) t x = 0 := by
  simp only [grad, zero_field_eq]
  ext i
  simp

lemma smooth_zero : Smooth (fun _ _ => (0 : ℝ)) := contDiffOn_const

end

end AN_R

open AN_R in
theorem solution (ν : ℝ) (U : Velocity) (K : Set Space) (hK : IsCompact K)
    (hU : Smooth U) (hs : SupportedIn U K) (hr : Rapid U) (h0 : ∀ x, U 0 x = 0)
    (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    NavierStokes ν (residual ν U) U (fun _ _ => 0) ∧ EnergyClass U (fun _ _ => 0) := by
  have hU0 : ∀ t, 0 ≤ t → ∀ x, x ∉ K → U t x = 0 := by
    intro t ht x hx
    by_contra hne
    exact hx (hs t ht hne)
  have hsub : ∀ T, timeCylinder T ⊆ HS := fun T =>
    Set.prod_mono Set.Icc_subset_Ici_self (Set.subset_univ _)
  refine ⟨⟨⟨fun x t ht => (hasFDerivWithinAt_time hU ht x).differentiableWithinAt,
      fun t ht x => (hasFDerivAt_space hU ht x).differentiableAt,
      fun t ht i x => (hasFDerivAt_space (smooth_dx hU i) ht x).differentiableAt,
      fun t _ => differentiable_const 0,
      fun T _ => ⟨hU.continuousOn.mono (hsub T), (smooth_dt hU).continuousOn.mono (hsub T),
        fun i => (smooth_dx hU i).continuousOn.mono (hsub T),
        fun i j => (smooth_dx (smooth_dx hU j) i).continuousOn.mono (hsub T),
        continuousOn_const, fun i => (smooth_dx smooth_zero i).continuousOn.mono (hsub T)⟩⟩,
      h0, fun t ht x => ⟨hdiv t ht x, ?_⟩⟩, ?_⟩
  · rw [grad_zero]
    simp only [AlternatingNS.residual, neg_zero, zero_add]
    abel
  · have hb := bound_of hU hK hU0
    refine ⟨fun T _ => ⟨continuousInH_of hU hK hU0 2 T, c1InL2_of hU hK hU0 T,
      continuousInH_of smooth_zero hK (fun _ _ _ _ => rfl) 1 T, ?_⟩, fun T _ => hb T⟩
    obtain ⟨C, hC⟩ := hb T
    exact ⟨C, fun t ht x => le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hC t ht x)⟩
