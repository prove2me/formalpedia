-- Prove2me | solution 1 for HedgePSNV.lemma_ec_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T23:24:09.915802+00:00
-- url     : https://prove2.me/submissions/fe34a75e-3e76-43b0-b8f4-28a755e50fe7

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Theorems.Thm_HedgePSNV_theorem_1_ii
import Theorems.Thm_HedgePSNV_hedging_residual_pos
import Theorems.Thm_HedgePSNV_riskneutral_section_maximizers
import Theorems.Thm_HedgePSNV_theorem_1_ii_degenerate

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace HedgePSNVC4

open HedgePSNV

/-- The expected overage `G(R) = E[(R - A)^+]`. -/
noncomputable def G (ν : Measure ℝ) (R : ℝ) : ℝ := ∫ a, max (R - a) 0 ∂ν

lemma int_pos (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (R : ℝ) :
    Integrable (fun a : ℝ => max (R - a) 0) ν := by
  refine ((integrable_const |R|).add hint).mono' (by fun_prop) (Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have h1 := le_abs_self R
  have h2 := le_max_left (-a) 0
  have h3 : (0 : ℝ) ≤ max (-a) 0 := le_max_right _ _
  have h4 := abs_nonneg R
  show max (R - a) 0 ≤ |R| + max (-a) 0
  exact max_le (by linarith) (by linarith)

lemma V_eq (p : Params) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (P R : ℝ) :
    nvValue p ν id P R = (P - p.c) * (R - p.b * P) - (P - p.s) * G ν R := by
  unfold nvValue payoff G
  simp only [id]
  rw [integral_sub (integrable_const _) ((int_pos ν hint R).const_mul _), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  congr 1
  exact integral_const_mul (P - p.s) (fun a : ℝ => max (R - a) 0)

lemma G_diff (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (R1 R2 : ℝ) (h : R1 ≤ R2) :
    cdf ν R1 * (R2 - R1) ≤ G ν R2 - G ν R1 ∧ G ν R2 - G ν R1 ≤ cdf ν R2 * (R2 - R1) := by
  have hsub : G ν R2 - G ν R1 = ∫ a, (max (R2 - a) 0 - max (R1 - a) 0) ∂ν := by
    unfold G; rw [integral_sub (int_pos ν hint R2) (int_pos ν hint R1)]
  have hind : ∀ x : ℝ, ∫ a, (Set.Iic x).indicator (fun _ => (R2 - R1)) a ∂ν =
      cdf ν x * (R2 - R1) := by
    intro x
    rw [integral_indicator measurableSet_Iic, setIntegral_const, cdf_eq_real, smul_eq_mul]
  have hii : ∀ x : ℝ, Integrable ((Set.Iic x).indicator (fun _ => (R2 - R1))) ν :=
    fun x => (integrable_const _).indicator measurableSet_Iic
  have hdi : Integrable (fun a => max (R2 - a) 0 - max (R1 - a) 0) ν :=
    (int_pos ν hint R2).sub (int_pos ν hint R1)
  refine ⟨?_, ?_⟩
  · rw [hsub, ← hind]
    refine integral_mono (hii R1) hdi fun a => ?_
    simp only [Set.indicator, Set.mem_Iic]
    split_ifs with ha
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · have := max_le_max_right 0 (show R1 - a ≤ R2 - a by linarith)
      linarith
  · rw [hsub, ← hind]
    refine integral_mono hdi (hii R2) fun a => ?_
    simp only [Set.indicator, Set.mem_Iic]
    split_ifs with ha
    · rcases le_total a R1 with h1 | h1
      · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; simp

lemma G_lip (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) : LipschitzWith 1 (G ν) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total x y with h | h
  · obtain ⟨h1, h2⟩ := G_diff ν hint x y h
    have := cdf_nonneg ν x; have := cdf_le_one ν y
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    nlinarith
  · obtain ⟨h1, h2⟩ := G_diff ν hint y x h
    have := cdf_nonneg ν y; have := cdf_le_one ν x
    rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by linarith)]
    nlinarith

lemma cdf_strictMono (ν : Measure ℝ) [IsProbabilityMeasure ν] (h1 : Assumption1 ν) :
    StrictMono (cdf ν) := by
  obtain ⟨f, r, r', hf, hr, hr', hpos, -, -⟩ := h1
  refine (monotone_cdf ν).strictMono_of_injective fun x y hxy => ?_
  by_contra hne
  wlog hlt : x < y generalizing x y
  · exact this y x hxy.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  have hconst : ∀ z ∈ Set.Ioo x y, cdf ν z = cdf ν x := fun z hz =>
    le_antisymm (hxy ▸ monotone_cdf ν hz.2.le) (monotone_cdf ν hz.1.le)
  have hf0 : ∀ z ∈ Set.Ioo x y, f z = 0 := by
    intro z hz
    have hev : (fun _ : ℝ => cdf ν x) =ᶠ[𝓝 z] fun w => cdf ν w :=
      Filter.mem_of_superset (Ioo_mem_nhds hz.1 hz.2) fun w hw => (hconst w hw).symm
    exact (hf z).unique ((hasDerivAt_const z (cdf ν x)).congr_of_eventuallyEq hev.symm)
  have hr0 : ∀ z ∈ Set.Ioo x y, r z = 0 := fun z hz => by rw [hr z, hf0 z hz, zero_div]
  set a := (x + y) / 2
  have ha : a ∈ Set.Ioo x y := ⟨by simp only [a]; linarith, by simp only [a]; linarith⟩
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 a] r :=
    Filter.mem_of_superset (Ioo_mem_nhds ha.1 ha.2) fun w hw => (hr0 w hw).symm
  have hr'0 : r' a = 0 := (hr' a).unique ((hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq hev.symm)
  have := hpos a
  rw [hr0 a ha, hr'0] at this
  norm_num at this

lemma G_strict (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (h1 : Assumption1 ν) (R1 R2 : ℝ)
    (h : R2 < R1) : 2 * G ν ((R1 + R2) / 2) < G ν R1 + G ν R2 := by
  set m := (R1 + R2) / 2 with hm
  set q := (R2 + m) / 2 with hq
  obtain ⟨-, a1⟩ := G_diff ν hint R2 q (by linarith)
  obtain ⟨-, a2⟩ := G_diff ν hint q m (by linarith)
  obtain ⟨a3, -⟩ := G_diff ν hint m R1 (by linarith)
  have hs : cdf ν q < cdf ν m := cdf_strictMono ν h1 (by linarith)
  have hpos : 0 < (cdf ν m - cdf ν q) * (R1 - R2) := mul_pos (by linarith) (by linarith)
  have e1 : q - R2 = (R1 - R2) / 4 := by rw [hq, hm]; ring
  have e2 : m - q = (R1 - R2) / 4 := by rw [hq, hm]; ring
  have e3 : R1 - m = (R1 - R2) / 2 := by rw [hm]; ring
  rw [e1] at a1; rw [e2] at a2; rw [e3] at a3
  nlinarith

end HedgePSNVC4

namespace HedgePSNVEC7

open HedgePSNV

/-- Dominance exclusion with a general mean-penalty `A`: a strictly larger price (and no smaller
`R`) cannot do better, because the residual risk scales by `((P - s)/(P1 - s))^2 > 1`. -/
lemma no_dominance (s : ℝ) (B Ψ A : ℝ → ℝ → ℝ≥0∞)
    (hB : ∀ P R, B P R = A P R + Ψ P R)
    (hscale : ∀ P1 P2 R, s < P1 → P1 ≤ P2 →
      Ψ P2 R = ENNReal.ofReal (((P2 - s) / (P1 - s)) ^ 2) * Ψ P1 R)
    (P1 R1 P R : ℝ) (hs : s < P1) (hP : P1 < P) (hR : R1 ≤ R)
    (hmono : Ψ P R1 ≤ Ψ P R) (hpos : 0 < Ψ P1 R1)
    (ha : A P1 R1 ≤ A P R) (hle : B P R ≤ B P1 R1) (hfin : B P R < ⊤) : False := by
  set k : ℝ := ((P - s) / (P1 - s)) ^ 2 with hk
  have hk1 : 1 < k := by
    have h1 : 1 < (P - s) / (P1 - s) := by
      rw [lt_div_iff₀ (by linarith)]; linarith
    nlinarith
  have hsc := hscale P1 P R1 hs hP.le
  have hΨh : ENNReal.ofReal k * Ψ P1 R1 ≤ Ψ P R := hsc ▸ hmono
  have hA1 : A P1 R1 ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin.ne (ha.trans ?_)
    rw [hB P R]; exact le_self_add
  have h1 : A P1 R1 + ENNReal.ofReal k * Ψ P1 R1 ≤ A P1 R1 + Ψ P1 R1 := by
    calc A P1 R1 + ENNReal.ofReal k * Ψ P1 R1
        ≤ A P R + Ψ P R := add_le_add ha hΨh
      _ = B P R := (hB P R).symm
      _ ≤ B P1 R1 := hle
      _ = _ := hB P1 R1
  have h2 : ENNReal.ofReal k * Ψ P1 R1 ≤ Ψ P1 R1 :=
    (ENNReal.add_le_add_iff_left hA1).1 h1
  have hfin1 : Ψ P1 R1 ≠ ⊤ := by
    have : Ψ P1 R1 ≤ B P R := by
      calc Ψ P1 R1 = 1 * Ψ P1 R1 := (one_mul _).symm
        _ ≤ ENNReal.ofReal k * Ψ P1 R1 := by
            gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hk1.le
        _ ≤ Ψ P R := hΨh
        _ ≤ A P R + Ψ P R := le_add_self
        _ = B P R := (hB P R).symm
    exact ne_top_of_le_ne_top hfin.ne this
  have h3 : ENNReal.ofReal k * Ψ P1 R1 ≤ 1 * Ψ P1 R1 := by rwa [one_mul]
  have h4 := (ENNReal.mul_le_mul_iff_left hpos.ne' hfin1).1 h3
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at h4
  linarith

lemma I_zero_ae {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) : M.I 0 =ᵐ[M.P] fun _ => (0 : ℝ) := by
  obtain ⟨a, -, -, -, hlim⟩ := hM.I_ito.2 0
  have hsum : ∀ n, EthierKurtz.itoStepSum M.B 0 n (a n) = fun _ => (0 : ℝ) := by
    intro n
    funext ω
    unfold EthierKurtz.itoStepSum
    simp
  have h0 : TendstoInMeasure M.P (fun n => EthierKurtz.itoStepSum M.B 0 n (a n)) Filter.atTop
      (fun _ => (0 : ℝ)) := by
    intro ε hε
    simp [hsum, not_le.mpr hε]
  exact tendstoInMeasure_ae_unique hlim h0

lemma PM_prob {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) : IsProbabilityMeasure M.PM := by
  have := hM.prob
  have hZ0 : M.Z 0 =ᵐ[M.P] fun _ => (1 : ℝ) := by
    filter_upwards [I_zero_ae M hM] with ω hω
    simp [Model.Z, hω]
  have hint : Integrable (M.Z p.T) M.P := (h5.1.2.1 p.T le_rfl)
  have hce := h5.1.2.2 0 p.T zero_le le_rfl
  have hE : ∫ ω, M.Z p.T ω ∂M.P = 1 := by
    rw [← integral_condExp (M.F.le 0)]
    rw [integral_congr_ae (hce.trans hZ0)]
    simp
  constructor
  unfold Model.PM
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le), hE, ENNReal.ofReal_one]

lemma AT_aemeas {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) : AEMeasurable M.AT M.P := by
  have hCm : Measurable (M.C p.T) := ((hM.C_adapted p.T).mono (M.G.le p.T)).measurable
  have hBm : AEMeasurable (M.Bt p.T) M.P :=
    (hM.brownBt.toIsPreBrownianReal.hasLaw_eval p.T).aemeasurable
  show AEMeasurable (fun ω => M.C p.T ω + p.σt * M.Bt p.T ω) M.P
  fun_prop

lemma PM_ac {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) : M.PM ≪ M.P :=
  withDensity_absolutelyContinuous _ _

lemma nvValue_map (p : Params) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (A : Ω → ℝ)
    (hA : AEMeasurable A Q) (P R : ℝ) :
    nvValue p (Q.map A) id P R = nvValue p Q A P R := by
  unfold nvValue
  rw [integral_map hA]
  · rfl
  · have : Continuous (fun a => payoff p P R (id a)) := by
      unfold payoff; fun_prop
    exact this.aestronglyMeasurable

lemma negPart_AT_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hintM : M.NegPartIntegrable M.PM) (h5 : M.Assumption5) :
    Integrable (fun ω => max (-(M.AT ω)) 0) M.PM := by
  have := hM.prob
  have hBlaw : HasLaw (M.Bt p.T) (gaussianReal 0 p.T) M.P :=
    hM.brownBt.toIsPreBrownianReal.hasLaw_eval p.T
  have hBm : AEMeasurable (M.Bt p.T) M.P := hBlaw.aemeasurable
  have hB2 : MemLp (M.Bt p.T) 2 M.P := by
    have h := memLp_id_gaussianReal' (μ := 0) (v := p.T) 2 (by simp)
    rw [← hBlaw.map_eq] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id hBm).1 h
  have hBPM : Integrable (fun ω => |M.Bt p.T ω|) M.PM := by
    unfold Model.PM
    have hZm : StronglyMeasurable (M.Z p.T) := (h5.1.1 p.T le_rfl).mono (M.F.le p.T)
    rw [integrable_withDensity_iff_integrable_smul' hZm.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hZpos : ∀ ω, 0 ≤ M.Z p.T ω := fun ω => by
      simp only [Model.Z]; exact (Real.exp_pos _).le
    simp_rw [ENNReal.toReal_ofReal (hZpos _), smul_eq_mul]
    exact (h5.2 p.T le_rfl).integrable_mul hB2.abs
  have hg : Integrable (fun ω => max (-(M.C p.T ω)) 0 + |p.σt| * |M.Bt p.T ω|) M.PM :=
    hintM.add (hBPM.const_mul |p.σt|)
  have hmeas : AEStronglyMeasurable (fun ω => max (-(M.AT ω)) 0) M.PM := by
    have h := (AT_aemeas M hM).mono_ac (PM_ac M)
    exact (by fun_prop : AEMeasurable (fun ω => max (-(M.AT ω)) 0) M.PM).aestronglyMeasurable
  refine hg.mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
  have h1 : -(p.σt * M.Bt p.T ω) ≤ |p.σt| * |M.Bt p.T ω| :=
    (neg_le_abs _).trans_eq (abs_mul _ _)
  have h3 := le_max_left (-(M.C p.T ω)) 0
  have h4 : (0 : ℝ) ≤ max (-(M.C p.T ω)) 0 := le_max_right _ _
  have h5' : (0 : ℝ) ≤ |p.σt| * |M.Bt p.T ω| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  show max (-(M.C p.T ω + p.σt * M.Bt p.T ω)) 0 ≤ _
  exact max_le (by linarith) (by linarith)

lemma negPart_int_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hL2 : M.NegPartL2) (h5 : M.Assumption5) : M.NegPartIntegrable M.PM := by
  unfold Model.NegPartIntegrable Model.PM
  have hZm : StronglyMeasurable (M.Z p.T) := (h5.1.1 p.T le_rfl).mono (M.F.le p.T)
  rw [integrable_withDensity_iff_integrable_smul' hZm.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hZpos : ∀ ω, 0 ≤ M.Z p.T ω := fun ω => by
    simp only [Model.Z]; exact (Real.exp_pos _).le
  simp_rw [ENNReal.toReal_ofReal (hZpos _), smul_eq_mul]
  exact (h5.2 p.T le_rfl).integrable_mul hL2


/-- The residual (unhedgeable) risk term of Theorem 1(ii). -/
noncomputable def Psi {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (P R : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
    ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2) ∂M.P

lemma Psi_scale {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (P1 P2 R : ℝ) (hs : p.s < P1) :
    Psi M P2 R = ENNReal.ofReal (((P2 - p.s) / (P1 - p.s)) ^ 2) * Psi M P1 R := by
  have hd : ∀ t ω, M.delta P2 R t ω = (P2 - p.s) / (P1 - p.s) * M.delta P1 R t ω := by
    intro t ω
    unfold Model.delta
    have : P1 - p.s ≠ 0 := by linarith
    field_simp
  unfold Psi
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun u => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _), hd]
  congr 1
  ring

lemma P_ac_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) : M.P ≪ M.PM := by
  have hm : Measurable (M.Z p.T) := ((h5.1.1 p.T le_rfl).mono (M.F.le p.T)).measurable
  exact withDensity_absolutelyContinuous' hm.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun ω => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _)

lemma Psi_monoR {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) [IsFiniteMeasure M.PM] (hA : AEMeasurable M.AT M.PM)
    (hZ : ∀ t : ℝ≥0, t ≤ p.T → ∀ᵐ ω ∂M.P, 0 ≤ M.Z t ω / M.ZM t ω)
    (P R1 R2 : ℝ) (hP : p.s ≤ P) (hR : R1 ≤ R2) : Psi M P R1 ≤ Psi M P R2 := by
  have hind : ∀ R : ℝ, Integrable (Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ))) M.PM := by
    intro R
    have : Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) =
        (Set.indicator (Set.Iic R) (fun _ => (1 : ℝ))) ∘ M.AT := by
      funext x; simp [Set.indicator]
    rw [this]
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((measurable_const.indicator measurableSet_Iic).comp_aemeasurable hA).aestronglyMeasurable
    · simp only [Function.comp_apply, Set.indicator]; split_ifs <;> simp
  unfold Psi
  refine setLIntegral_mono' measurableSet_Icc fun u hu => ?_
  have hu' : u.toNNReal ≤ p.T := by
    rw [Real.toNNReal_le_iff_le_coe]; exact hu.2
  refine lintegral_mono_ae ?_
  have hle : (M.PM)[Set.indicator {x | M.AT x ≤ R1} (fun _ => (1 : ℝ)) | M.F u.toNNReal] ≤ᵐ[M.PM]
      (M.PM)[Set.indicator {x | M.AT x ≤ R2} (fun _ => (1 : ℝ)) | M.F u.toNNReal] := by
    refine condExp_mono (hind R1) (hind R2) (Filter.Eventually.of_forall fun x => ?_)
    simp only [Set.indicator, Set.mem_ofPred_eq]
    split_ifs with h1 h2 <;> first | exact le_rfl | (exfalso; linarith) | norm_num
  have hnn : 0 ≤ᵐ[M.PM] (M.PM)[Set.indicator {x | M.AT x ≤ R1} (fun _ => (1 : ℝ)) | M.F u.toNNReal] :=
    condExp_nonneg (μ := M.PM) (m := M.F u.toNNReal)
      (f := Set.indicator {x | M.AT x ≤ R1} (fun _ => (1 : ℝ)))
      (Filter.Eventually.of_forall fun x => by
        show (0 : ℝ) ≤ Set.indicator {x | M.AT x ≤ R1} (fun _ => (1 : ℝ)) x
        simp only [Set.indicator]; split_ifs <;> norm_num)
  filter_upwards [P_ac_PM M h5 hle, P_ac_PM M h5 hnn, hZ _ hu'] with ω h1 h2 h3
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ h3)
  unfold Model.delta
  have hk : 0 ≤ p.σt * (P - p.s) := mul_nonneg p.hσt.le (by linarith)
  exact pow_le_pow_left₀ (mul_nonneg hk h2) (mul_le_mul_of_nonneg_left h1 hk) 2

lemma V0_c_nonpos {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) :
    M.V0 p.c (p.b * p.c) ≤ 0 := by
  unfold Model.V0 nvValue
  refine integral_nonpos fun ω => ?_
  unfold payoff
  have := p.hsc
  have h0 : (0 : ℝ) ≤ max (p.b * p.c - M.AT ω) 0 := le_max_right _ _
  have h1 := mul_nonneg (sub_nonneg.2 this.le) h0
  show (p.c - p.c) * (p.b * p.c - p.b * p.c) - (p.c - p.s) * max (p.b * p.c - M.AT ω) 0 ≤ 0
  nlinarith [h1]

lemma PM_eq_P_of_deg {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) : M.PM = M.P := by
  unfold Model.PM
  rw [withDensity_congr_ae (g := fun _ => (1 : ℝ≥0∞))]
  · exact withDensity_one
  · filter_upwards [hdeg] with ω h
    simp [h]

lemma Z_div_ZM_nonneg {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) (t : ℝ≥0) : ∀ᵐ ω ∂M.P, 0 ≤ M.Z t ω / M.ZM t ω := by
  have h : 0 ≤ᵐ[M.PM] M.ZM t := by
    unfold Model.ZM
    exact condExp_nonneg (Filter.Eventually.of_forall fun ω => by
      show (0 : ℝ) ≤ M.Z p.T ω
      simp only [Model.Z]; exact (Real.exp_pos _).le)
  filter_upwards [P_ac_PM M h5 h] with ω hω
  refine div_nonneg ?_ hω
  simp only [Model.Z]; exact (Real.exp_pos _).le

lemma hint_map {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (h5 : M.Assumption5) :
    Integrable (fun a : ℝ => max (-a) 0) (M.PM.map M.AT) := by
  have hAm : AEMeasurable M.AT M.PM := (AT_aemeas M hM).mono_ac (PM_ac M)
  rw [integrable_map_measure (continuous_neg.max continuous_const).aestronglyMeasurable hAm]
  exact negPart_AT_PM M hM (negPart_int_PM M hL2 h5) h5


/-- The abstract argument of Lemma EC.7 (paper EC.8.2, constrained sections), for
`B = A + Ψ` with a mean penalty `A` vanishing on `{V = m}`. -/
lemma core7 (b c s : ℝ) (hb : 0 < b) (hsc : s < c) (V : ℝ → ℝ → ℝ)
    (B Ψ A : ℝ → ℝ → ℝ≥0∞) (m : ℝ) (hm : 0 ≤ m)
    (hB : ∀ P R, B P R = A P R + Ψ P R)
    (hscale : ∀ P1 P2 R, s < P1 → P1 ≤ P2 →
      Ψ P2 R = ENNReal.ofReal (((P2 - s) / (P1 - s)) ^ 2) * Ψ P1 R)
    (hmonoR : ∀ P R1 R2, c ≤ P → R1 ≤ R2 → Ψ P R1 ≤ Ψ P R2)
    (hpos : ∀ P R, c ≤ P → 0 < Ψ P R)
    (hcont : Continuous fun q : ℝ × ℝ => V q.1 q.2)
    (hVc : ∀ R, V c R ≤ 0)
    (hVb : ∀ P, c ≤ P → V P (b * P) ≤ 0)
    (hA0 : ∀ P1 R1, V P1 R1 = m → A P1 R1 = 0)
    (P R : ℝ) (hc : c ≤ P) (hbPR : b * P ≤ R)
    (hmin : ∀ P'' R'', c ≤ P'' → b * P'' ≤ R'' → B P R ≤ B P'' R'')
    (hfin : B P R < ⊤)
    (hAmono : ∀ P1 R1, V P R ≤ V P1 R1 → V P1 R1 ≤ m → A P1 R1 ≤ A P R)
    (hAstrict : ∀ P1 R1, V P R < V P1 R1 → V P1 R1 ≤ m → A P1 R1 < A P R)
    (hRconc : ∀ R1 R2, b * P ≤ R1 → R1 < R2 →
      (∀ R'', b * P ≤ R'' → V P R'' ≤ V P R1) → V P R2 < V P R1) :
    (∀ P', c ≤ P' → b * P' ≤ R →
      (∀ P'', c ≤ P'' → b * P'' ≤ R → V P'' R ≤ V P' R) → P ≤ P') ∧
    (∀ R', b * P ≤ R' → (∀ R'', b * P ≤ R'' → V P R'' ≤ V P R') → R ≤ R') := by
  have dom : ∀ P1 R1, c ≤ P1 → b * P1 ≤ R1 → P1 < P → R1 ≤ R → A P1 R1 ≤ A P R → False :=
    fun P1 R1 hc1 hb1 hP1 hR1 ha1 =>
      no_dominance s B Ψ A hB hscale P1 R1 P R (by linarith) hP1 hR1
        (hmonoR P R1 R hc hR1) (hpos P1 R1 hc1) ha1 (hmin P1 R1 hc1 hb1) hfin
  have hVm : V P R ≤ m := by
    by_contra hgt
    push Not at hgt
    have hPc : c < P := by
      rcases eq_or_lt_of_le hc with h | h
      · exfalso; have := hVc R; rw [h] at this; linarith
      · exact h
    set φ : ℝ → ℝ := fun l => V ((1 - l) * c + l * P) ((1 - l) * (b * c) + l * R) with hφ
    have hφc : Continuous φ := by
      have : Continuous fun l : ℝ => (((1 - l) * c + l * P), ((1 - l) * (b * c) + l * R)) := by
        fun_prop
      exact hcont.comp this
    have h0 : φ 0 = V c (b * c) := by simp [hφ]
    have h1 : φ 1 = V P R := by simp [hφ]
    have hVbc := hVb c le_rfl
    have hmem : m ∈ Set.Icc (φ 0) (φ 1) := ⟨by linarith, by linarith⟩
    obtain ⟨l, hl, hlm⟩ := intermediate_value_Icc zero_le_one hφc.continuousOn hmem
    have hl1 : l < 1 := by
      rcases eq_or_lt_of_le hl.2 with h | h
      · exfalso; rw [h, h1] at hlm; linarith
      · exact h
    have hbc : b * c ≤ b * P := by nlinarith
    refine dom ((1 - l) * c + l * P) ((1 - l) * (b * c) + l * R) ?_ ?_ ?_ ?_ ?_
    · nlinarith [hl.1, hl.2]
    · nlinarith [hl.1, hl.2]
    · nlinarith [hl.1, hl.2]
    · nlinarith [hl.1, hl.2]
    · rw [hA0 _ _ hlm]; exact zero_le
  have hΨfin : Ψ P R ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin.ne ?_
    rw [hB P R]; exact le_add_self
  refine ⟨fun P' hc' hb' hmax => ?_, fun R' hb' hmax => ?_⟩
  · by_contra hlt
    push Not at hlt
    have hV' : V P R ≤ V P' R := hmax P hc hbPR
    by_cases hVm' : V P' R ≤ m
    · exact dom P' R hc' hb' hlt le_rfl (hAmono P' R hV' hVm')
    · push Not at hVm'
      have hψc : Continuous fun r : ℝ => V P' r :=
        hcont.comp (by fun_prop : Continuous fun r : ℝ => ((P', r) : ℝ × ℝ))
      have hb0 := hVb P' hc'
      have hmem : m ∈ Set.Icc (V P' (b * P')) (V P' R) := ⟨by linarith, by linarith⟩
      obtain ⟨r, hr, hrm⟩ := intermediate_value_Icc hb' hψc.continuousOn hmem
      exact dom P' r hc' hr.1 hlt hr.2 (by rw [hA0 _ _ hrm]; exact zero_le)
  · by_contra hlt
    push Not at hlt
    have hstrict : V P R < V P R' := hRconc R' R hb' hlt hmax
    by_cases hVm' : V P R' ≤ m
    · have hA := hAstrict P R' hstrict hVm'
      have hle := hmin P R' hc hb'
      have hlt2 : B P R' < B P R := by
        rw [hB P R', hB P R]
        calc A P R' + Ψ P R' ≤ A P R' + Ψ P R := add_le_add le_rfl (hmonoR P R' R hc hlt.le)
          _ < A P R + Ψ P R := (ENNReal.add_lt_add_iff_right hΨfin).2 hA
      exact absurd hle (not_le.2 hlt2)
    · push Not at hVm'
      have hψc : Continuous fun q : ℝ => V q R' :=
        hcont.comp (by fun_prop : Continuous fun q : ℝ => ((q, R') : ℝ × ℝ))
      have hc0 := hVc R'
      have hmem : m ∈ Set.Icc (V c R') (V P R') := ⟨by linarith, by linarith⟩
      obtain ⟨q, hq, hqm⟩ := intermediate_value_Icc hc hψc.continuousOn hmem
      have hqP : q < P := by
        rcases eq_or_lt_of_le hq.2 with h | h
        · exfalso; rw [h] at hqm; linarith
        · exact h
      have hbq : b * q ≤ R' := le_trans (by nlinarith [hq.2]) hb'
      exact dom q R' hq.1 hbq hqP hlt.le (by rw [hA0 _ _ hqm]; exact zero_le)

lemma V0_nonpos_of {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (P R : ℝ) (hz : (P - p.c) * (R - p.b * P) = 0) (hs : p.s ≤ P) : M.V0 P R ≤ 0 := by
  unfold Model.V0 nvValue
  refine integral_nonpos fun ω => ?_
  show payoff p P R (M.AT ω) ≤ 0
  unfold payoff
  rw [hz]
  have := mul_nonneg (sub_nonneg.2 hs) (le_max_right (R - M.AT ω) 0)
  linarith

set_option maxHeartbeats 1000000 in
/-- Lemma EC.7 from its children (Theorem 1(ii) in both cases, positivity of the residual
risk, and the section maximizers of `V_0`). -/
theorem ec7_of_children (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (h5 : M.Assumption5)
    (h1M : Assumption1 (M.PM.map M.AT))
    (m : ℝ) (hm : 0 ≤ m) (P R : ℝ) (hPR : (P, R) ∈ decisionDomain p)
    (hmin : ∀ P' R' : ℝ, (P', R') ∈ decisionDomain p → M.Bval m P R ≤ M.Bval m P' R')
    (hfin : M.Bval m P R < ⊤)
    (hT1 : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) →
      (∀ m P R : ℝ, M.Bval m P R =
        ENNReal.ofReal ((m - M.V0 P R) ^ 2 / (M.ZM0 - 1)) + Psi M P R) ∧ 1 < M.ZM0)
    (hdegB : (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) →
      ∀ m P R : ℝ, M.Bval m P R = (if M.V0 P R = m then 0 else ⊤) + Psi M P R)
    (hC3 : ∀ P R : ℝ, p.s < P → 0 < Psi M P R)
    (hcont0 : Continuous (fun q : ℝ × ℝ => nvValue p (M.PM.map M.AT) id q.1 q.2)) :
    (∀ P' : ℝ, (P', R) ∈ decisionDomain p →
      (∀ P'' : ℝ, (P'', R) ∈ decisionDomain p → M.V0 P'' R ≤ M.V0 P' R) → P ≤ P') ∧
    (∀ R' : ℝ, (P, R') ∈ decisionDomain p →
      (∀ R'' : ℝ, (P, R'') ∈ decisionDomain p → M.V0 P R'' ≤ M.V0 P R') → R ≤ R') := by
  have : IsProbabilityMeasure M.PM := PM_prob M hM h5
  have hAm : AEMeasurable M.AT M.PM := (AT_aemeas M hM).mono_ac (PM_ac M)
  have hν : IsProbabilityMeasure (M.PM.map M.AT) := Measure.isProbabilityMeasure_map hAm
  have hint := hint_map M hM hL2 h5
  have hV : ∀ P R, nvValue p (M.PM.map M.AT) id P R = M.V0 P R :=
    fun P R => nvValue_map p M.PM M.AT hAm P R
  have hcont : Continuous (fun q : ℝ × ℝ => M.V0 q.1 q.2) := by
    simp only [hV] at hcont0; exact hcont0
  have hVeq : ∀ P R, M.V0 P R = (P - p.c) * (R - p.b * P) -
      (P - p.s) * HedgePSNVC4.G (M.PM.map M.AT) R := by
    intro P R; rw [← hV]; exact HedgePSNVC4.V_eq p _ hint P R
  have hsc := p.hsc
  have hmonoR : ∀ P R1 R2, p.c ≤ P → R1 ≤ R2 → Psi M P R1 ≤ Psi M P R2 :=
    fun P R1 R2 hc hR => Psi_monoR M h5 hAm (fun t _ => Z_div_ZM_nonneg M h5 t) P R1 R2
      (by linarith) hR
  have hpos : ∀ P R, p.c ≤ P → 0 < Psi M P R := fun P R hc => hC3 P R (by linarith)
  have hscale : ∀ P1 P2 R, p.s < P1 → P1 ≤ P2 →
      Psi M P2 R = ENNReal.ofReal (((P2 - p.s) / (P1 - p.s)) ^ 2) * Psi M P1 R :=
    fun P1 P2 R hs _ => Psi_scale M P1 P2 R hs
  have hVc : ∀ R, M.V0 p.c R ≤ 0 := fun R => V0_nonpos_of M p.c R (by ring) hsc.le
  have hVb : ∀ P, p.c ≤ P → M.V0 P (p.b * P) ≤ 0 :=
    fun P hc => V0_nonpos_of M P (p.b * P) (by ring) (by linarith)
  have hmin' : ∀ P'' R'', p.c ≤ P'' → p.b * P'' ≤ R'' → M.Bval m P R ≤ M.Bval m P'' R'' :=
    fun P'' R'' h1 h2 => hmin P'' R'' ⟨h1, h2⟩
  have hRconc : ∀ R1 R2, p.b * P ≤ R1 → R1 < R2 →
      (∀ R'', p.b * P ≤ R'' → M.V0 P R'' ≤ M.V0 P R1) → M.V0 P R2 < M.V0 P R1 := by
    intro R1 R2 hb1 h12 hmax
    have hmid := hmax ((R2 + R1) / 2) (by linarith)
    have hG := HedgePSNVC4.G_strict (M.PM.map M.AT) hint h1M R2 R1 h12
    have hPs : 0 < P - p.s := by linarith [hPR.1]
    have hk := mul_lt_mul_of_pos_left hG hPs
    rw [hVeq, hVeq] at hmid
    rw [hVeq, hVeq]
    nlinarith [hk, hmid]
  have key : ∀ A : ℝ → ℝ → ℝ≥0∞, (∀ P R, M.Bval m P R = A P R + Psi M P R) →
      (∀ P1 R1, M.V0 P1 R1 = m → A P1 R1 = 0) →
      (∀ P1 R1, M.V0 P R ≤ M.V0 P1 R1 → M.V0 P1 R1 ≤ m → A P1 R1 ≤ A P R) →
      (∀ P1 R1, M.V0 P R < M.V0 P1 R1 → M.V0 P1 R1 ≤ m → A P1 R1 < A P R) →
      (∀ P' : ℝ, (P', R) ∈ decisionDomain p →
        (∀ P'' : ℝ, (P'', R) ∈ decisionDomain p → M.V0 P'' R ≤ M.V0 P' R) → P ≤ P') ∧
      (∀ R' : ℝ, (P, R') ∈ decisionDomain p →
        (∀ R'' : ℝ, (P, R'') ∈ decisionDomain p → M.V0 P R'' ≤ M.V0 P R') → R ≤ R') := by
    intro A hB hA0 hAmono hAstrict
    obtain ⟨k1, k2⟩ := core7 p.b p.c p.s p.hb hsc M.V0 (fun P R => M.Bval m P R) (Psi M) A m hm
      hB hscale hmonoR hpos hcont hVc hVb hA0 P R hPR.1 hPR.2 hmin' hfin hAmono hAstrict hRconc
    refine ⟨fun P' hP' hmax => k1 P' hP'.1 hP'.2 (fun P'' h1 h2 => hmax P'' ⟨h1, h2⟩),
      fun R' hR' hmax => k2 R' hR'.2 (fun R'' h => hmax R'' ⟨hPR.1, h⟩)⟩
  by_cases hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)
  · have hB := hdegB hdeg m
    have hVPR : M.V0 P R = m := by
      by_contra hne
      have := hB P R
      rw [if_neg hne, top_add] at this
      rw [this] at hfin
      exact lt_irrefl _ hfin
    refine key (fun P R => if M.V0 P R = m then 0 else ⊤) hB (fun P1 R1 h => if_pos h)
      (fun P1 R1 h1 h2 => ?_) (fun P1 R1 h1 h2 => ?_)
    · have : M.V0 P1 R1 = m := le_antisymm h2 (hVPR ▸ h1)
      simp [this]
    · exfalso; linarith
  · obtain ⟨hB, hZM⟩ := hT1 hdeg
    refine key (fun P R => ENNReal.ofReal ((m - M.V0 P R) ^ 2 / (M.ZM0 - 1))) (hB m)
      (fun P1 R1 h => by simp [h]) (fun P1 R1 h1 h2 => ?_) (fun P1 R1 h1 h2 => ?_)
    · refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by linarith))
      nlinarith
    · have hZ : 0 < M.ZM0 - 1 := by linarith
      have hsq : (m - M.V0 P1 R1) ^ 2 < (m - M.V0 P R) ^ 2 := by nlinarith
      have hlt : (m - M.V0 P1 R1) ^ 2 / (M.ZM0 - 1) < (m - M.V0 P R) ^ 2 / (M.ZM0 - 1) :=
        div_lt_div_of_pos_right hsq hZ
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hlt)).2 hlt

end HedgePSNVEC7

open HedgePSNVEC7 in
open HedgePSNV in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (h1P : Assumption1 (M.P.map M.AT)) (h1M : Assumption1 (M.PM.map M.AT))
    (PNV RNV : ℝ) (hNV : IsNVMaximizer p M.P M.AT PNV RNV)
    (h2 : Assumption2 p M.P M.AT PNV RNV) (h3 : Assumption3 p M.P M.AT PNV RNV)
    (m : ℝ) (hm : 0 ≤ m) (P R : ℝ) (hPR : (P, R) ∈ decisionDomain p)
    (hmin : ∀ P' R' : ℝ, (P', R') ∈ decisionDomain p → M.Bval m P R ≤ M.Bval m P' R')
    (hfin : M.Bval m P R < ⊤) :
    (∀ P' : ℝ, (P', R) ∈ decisionDomain p →
      (∀ P'' : ℝ, (P'', R) ∈ decisionDomain p → M.V0 P'' R ≤ M.V0 P' R) → P ≤ P') ∧
    (∀ R' : ℝ, (P, R') ∈ decisionDomain p →
      (∀ R'' : ℝ, (P, R'') ∈ decisionDomain p → M.V0 P R'' ≤ M.V0 P R') → R ≤ R') := by
  have hPM : IsProbabilityMeasure M.PM := PM_prob M hM h5
  have hAM : AEMeasurable M.AT M.PM := (AT_aemeas M hM).mono_ac (PM_ac M)
  have hν : IsProbabilityMeasure (M.PM.map M.AT) := Measure.isProbabilityMeasure_map hAM
  exact ec7_of_children p M hM hL2 h5 h1M m hm P R hPR hmin hfin
    (fun hne => ⟨(HedgePSNV.theorem_1_ii p M hM hL2 h4 h5 hne).1,
      (HedgePSNV.theorem_1_ii p M hM hL2 h4 h5 hne).2.2.1⟩)
    (HedgePSNV.theorem_1_ii_degenerate p M hM hL2 h4 h5)
    (fun P R hP => HedgePSNV.hedging_residual_pos p M hM h5 h1M P R hP)
    (HedgePSNV.riskneutral_section_maximizers p (M.PM.map M.AT) (hint_map M hM hL2 h5) h1M).1
