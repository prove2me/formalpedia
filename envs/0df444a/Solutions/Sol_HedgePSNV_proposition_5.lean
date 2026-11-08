-- Prove2me | solution 1 for HedgePSNV.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T23:53:29.016583+00:00
-- url     : https://prove2.me/submissions/2e37ddeb-252c-4977-880d-9da343300162

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Theorems.Thm_HedgePSNV_theorem_1_ii
import Theorems.Thm_HedgePSNV_lemma_ec_7
import Theorems.Thm_HedgePSNV_hedging_residual_pos
import Theorems.Thm_HedgePSNV_riskneutral_section_maximizers
import Theorems.Thm_HedgePSNV_theorem_1_ii_degenerate

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNVProp5

open HedgePSNV


/-- `R` maximizes the `R`-section of `V` at `P` over `{R : b P ≤ R}`. -/
def IsRMax (b : ℝ) (V : ℝ → ℝ → ℝ) (P R : ℝ) : Prop :=
  b * P ≤ R ∧ ∀ R'' : ℝ, b * P ≤ R'' → V P R'' ≤ V P R

/-- `P` maximizes the `P`-section of `V` at `R` over `{P : c ≤ P, b P ≤ R}`. -/
def IsPMax (b c : ℝ) (V : ℝ → ℝ → ℝ) (R P : ℝ) : Prop :=
  c ≤ P ∧ b * P ≤ R ∧ ∀ P'' : ℝ, c ≤ P'' → b * P'' ≤ R → V P'' R ≤ V P R

/-- Final step: once the minimizer is below the maximizer in one coordinate, the
post-fixed-point property (Lemma EC.7) and monotone section maximizers give both. -/
lemma finish (b c : ℝ) (hb : 0 < b) (V : ℝ → ℝ → ℝ)
    (hRex : ∀ P, c ≤ P → ∃ R, IsRMax b V P R)
    (hPex : ∀ R, b * c ≤ R → ∃ P, IsPMax b c V R P)
    (hRord : ∀ P1 P2 R1 R2, c ≤ P1 → P1 ≤ P2 → IsRMax b V P1 R1 → IsRMax b V P2 R2 → R1 ≤ R2)
    (hPord : ∀ R1 R2 P1 P2, R1 ≤ R2 → IsPMax b c V R1 P1 → IsPMax b c V R2 P2 → P1 ≤ P2)
    (P R : ℝ) (hc : c ≤ P) (hbPR : b * P ≤ R)
    (hec1 : ∀ P', IsPMax b c V R P' → P ≤ P')
    (hec2 : ∀ R', IsRMax b V P R' → R ≤ R')
    (P' R' : ℝ) (hc' : c ≤ P') (hbPR' : b * P' ≤ R')
    (hmax : ∀ P'' R'', c ≤ P'' → b * P'' ≤ R'' → V P'' R'' ≤ V P' R')
    (hor : P ≤ P' ∨ R ≤ R') : P ≤ P' ∧ R ≤ R' := by
  have hR' : IsRMax b V P' R' := ⟨hbPR', fun R'' h => hmax P' R'' hc' h⟩
  have hP' : IsPMax b c V R' P' := ⟨hc', hbPR', fun P'' h1 h2 => hmax P'' R' h1 h2⟩
  rcases hor with h | h
  · obtain ⟨R2, hR2⟩ := hRex P hc
    exact ⟨h, (hec2 R2 hR2).trans (hRord P P' R2 R' hc h hR2 hR')⟩
  · have hbc : b * c ≤ R := le_trans (by nlinarith) hbPR
    obtain ⟨P2, hP2⟩ := hPex R hbc
    exact ⟨(hec1 P2 hP2).trans (hPord R R' P2 P' h hP2 hP'), h⟩

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

/-- The abstract argument of Proposition 5 (paper EC.8.2, constrained sections), for
`B = A + Ψ` with a mean penalty `A` vanishing on `{V = m}`. -/
lemma core_gen (b c s : ℝ) (hb : 0 < b) (hsc : s < c) (V : ℝ → ℝ → ℝ)
    (B Ψ A : ℝ → ℝ → ℝ≥0∞) (m : ℝ)
    (hB : ∀ P R, B P R = A P R + Ψ P R)
    (hscale : ∀ P1 P2 R, s < P1 → P1 ≤ P2 →
      Ψ P2 R = ENNReal.ofReal (((P2 - s) / (P1 - s)) ^ 2) * Ψ P1 R)
    (hmonoR : ∀ P R1 R2, c ≤ P → R1 ≤ R2 → Ψ P R1 ≤ Ψ P R2)
    (hpos : ∀ P R, c ≤ P → 0 < Ψ P R)
    (hcont : Continuous fun q : ℝ × ℝ => V q.1 q.2)
    (hV0 : V c (b * c) ≤ m)
    (hA0 : ∀ P1 R1, V P1 R1 = m → A P1 R1 = 0)
    (hRex : ∀ P, c ≤ P → ∃ R, IsRMax b V P R)
    (hPex : ∀ R, b * c ≤ R → ∃ P, IsPMax b c V R P)
    (hRord : ∀ P1 P2 R1 R2, c ≤ P1 → P1 ≤ P2 → IsRMax b V P1 R1 → IsRMax b V P2 R2 → R1 ≤ R2)
    (hPord : ∀ R1 R2 P1 P2, R1 ≤ R2 → IsPMax b c V R1 P1 → IsPMax b c V R2 P2 → P1 ≤ P2)
    (P R : ℝ) (hc : c ≤ P) (hbPR : b * P ≤ R)
    (hmin : ∀ P'' R'', c ≤ P'' → b * P'' ≤ R'' → B P R ≤ B P'' R'')
    (hfin : B P R < ⊤)
    (hec1 : ∀ P', IsPMax b c V R P' → P ≤ P')
    (hec2 : ∀ R', IsRMax b V P R' → R ≤ R')
    (P' R' : ℝ) (hc' : c ≤ P') (hbPR' : b * P' ≤ R')
    (hmax : ∀ P'' R'', c ≤ P'' → b * P'' ≤ R'' → V P'' R'' ≤ V P' R')
    (hAcmp : V P' R' ≤ m → A P' R' ≤ A P R) :
    P ≤ P' ∧ R ≤ R' := by
  obtain ⟨P1, R1, hc1, hb1, hP1, hR1, ha1⟩ : ∃ P1 R1, c ≤ P1 ∧ b * P1 ≤ R1 ∧ P1 ≤ P' ∧ R1 ≤ R' ∧
      A P1 R1 ≤ A P R := by
    rcases le_or_gt (V P' R') m with hV | hV
    · exact ⟨P', R', hc', hbPR', le_rfl, le_rfl, hAcmp hV⟩
    · set φ : ℝ → ℝ := fun l => V ((1 - l) * c + l * P') ((1 - l) * (b * c) + l * R') with hφ
      have hφc : Continuous φ := by
        have : Continuous fun l : ℝ => (((1 - l) * c + l * P'), ((1 - l) * (b * c) + l * R')) := by
          fun_prop
        exact hcont.comp this
      have h0 : φ 0 = V c (b * c) := by simp [hφ]
      have h1 : φ 1 = V P' R' := by simp [hφ]
      have hmem : m ∈ Set.Icc (φ 0) (φ 1) := ⟨by linarith, by linarith⟩
      obtain ⟨l, hl, hlm⟩ := intermediate_value_Icc zero_le_one hφc.continuousOn hmem
      have hbc' : b * c ≤ b * P' := by nlinarith
      refine ⟨(1 - l) * c + l * P', (1 - l) * (b * c) + l * R', ?_, ?_, ?_, ?_, ?_⟩
      · nlinarith [hl.1, hl.2]
      · nlinarith [hl.1, hl.2]
      · nlinarith [hl.1, hl.2]
      · nlinarith [hl.1, hl.2]
      · rw [hA0 _ _ hlm]; exact bot_le
  have hor : P ≤ P1 ∨ R1 > R := by
    by_contra hcon
    push Not at hcon
    exact no_dominance s B Ψ A hB hscale P1 R1 P R
      (by linarith) hcon.1 hcon.2 (hmonoR P R1 R (hc1.trans hcon.1.le) hcon.2) (hpos P1 R1 hc1)
      ha1 (hmin P1 R1 hc1 hb1) hfin
  refine finish b c hb V hRex hPex hRord hPord P R hc hbPR hec1 hec2 P' R' hc' hbPR' hmax ?_
  rcases hor with h | h
  · exact Or.inl (h.trans hP1)
  · exact Or.inr (h.le.trans hR1)


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

/-- The conclusion of the child `riskneutral_section_maximizers` for a law `ν`. -/
def C4concl (p : Params) (ν : Measure ℝ) : Prop :=
  Continuous (fun q : ℝ × ℝ => nvValue p ν id q.1 q.2) ∧
    (∀ P, p.c ≤ P → ∃ R, p.b * P ≤ R ∧
      ∀ R', p.b * P ≤ R' → nvValue p ν id P R' ≤ nvValue p ν id P R) ∧
    (∀ R, p.b * p.c ≤ R → ∃ P, p.c ≤ P ∧ p.b * P ≤ R ∧
      ∀ P', p.c ≤ P' → p.b * P' ≤ R → nvValue p ν id P' R ≤ nvValue p ν id P R) ∧
    (∀ P1 P2 R1 R2, p.c ≤ P1 → P1 ≤ P2 →
      (p.b * P1 ≤ R1 ∧ ∀ R', p.b * P1 ≤ R' → nvValue p ν id P1 R' ≤ nvValue p ν id P1 R1) →
      (p.b * P2 ≤ R2 ∧ ∀ R', p.b * P2 ≤ R' → nvValue p ν id P2 R' ≤ nvValue p ν id P2 R2) →
      R1 ≤ R2) ∧
    (∀ R1 R2 P1 P2, R1 ≤ R2 →
      (p.c ≤ P1 ∧ p.b * P1 ≤ R1 ∧
        ∀ P', p.c ≤ P' → p.b * P' ≤ R1 → nvValue p ν id P' R1 ≤ nvValue p ν id P1 R1) →
      (p.c ≤ P2 ∧ p.b * P2 ≤ R2 ∧
        ∀ P', p.c ≤ P' → p.b * P' ≤ R2 → nvValue p ν id P' R2 ≤ nvValue p ν id P2 R2) →
      P1 ≤ P2)

set_option maxHeartbeats 1000000 in
/-- Proposition 5 from its children (Theorem 1(ii) in both cases, Lemma EC.7, positivity of the
residual risk, and the section maximizers of `V_0`). -/
theorem prop5_of_children (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5)
    (m : ℝ) (hm : 0 ≤ m) (P R : ℝ) (hPR : (P, R) ∈ decisionDomain p)
    (hmin : ∀ P' R' : ℝ, (P', R') ∈ decisionDomain p → M.Bval m P R ≤ M.Bval m P' R')
    (hfin : M.Bval m P R < ⊤)
    (hT1 : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) →
      (∀ m P R : ℝ, M.Bval m P R =
        ENNReal.ofReal ((m - M.V0 P R) ^ 2 / (M.ZM0 - 1)) + Psi M P R) ∧ 1 < M.ZM0)
    (hdegB : (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) →
      ∀ m P R : ℝ, M.Bval m P R = (if M.V0 P R = m then 0 else ⊤) + Psi M P R)
    (hEC7 : (∀ P' : ℝ, (P', R) ∈ decisionDomain p →
      (∀ P'' : ℝ, (P'', R) ∈ decisionDomain p → M.V0 P'' R ≤ M.V0 P' R) → P ≤ P') ∧
      (∀ R' : ℝ, (P, R') ∈ decisionDomain p →
      (∀ R'' : ℝ, (P, R'') ∈ decisionDomain p → M.V0 P R'' ≤ M.V0 P R') → R ≤ R'))
    (hC3 : ∀ P R : ℝ, p.s < P → 0 < Psi M P R)
    (hC4 : C4concl p (M.PM.map M.AT)) :
    ∀ P' R' : ℝ, IsNVMaximizer p M.PM M.AT P' R' → P ≤ P' ∧ R ≤ R' := by
  intro P' R' hNV'
  have : IsProbabilityMeasure M.PM := PM_prob M hM h5
  have hAm : AEMeasurable M.AT M.PM := (AT_aemeas M hM).mono_ac (PM_ac M)
  have hV : ∀ P R, nvValue p (M.PM.map M.AT) id P R = M.V0 P R :=
    fun P R => nvValue_map p M.PM M.AT hAm P R
  obtain ⟨hcont, hRex, hPex, hRord, hPord⟩ := hC4
  simp only [hV] at hcont hRex hPex hRord hPord
  have hsc := p.hsc
  have hmonoR : ∀ P R1 R2, p.c ≤ P → R1 ≤ R2 → Psi M P R1 ≤ Psi M P R2 :=
    fun P R1 R2 hc hR => Psi_monoR M h5 hAm (fun t _ => Z_div_ZM_nonneg M h5 t) P R1 R2
      (by linarith) hR
  have hpos : ∀ P R, p.c ≤ P → 0 < Psi M P R := fun P R hc => hC3 P R (by linarith)
  have hscale : ∀ P1 P2 R, p.s < P1 → P1 ≤ P2 →
      Psi M P2 R = ENNReal.ofReal (((P2 - p.s) / (P1 - p.s)) ^ 2) * Psi M P1 R :=
    fun P1 P2 R hs _ => Psi_scale M P1 P2 R hs
  have hV0 : M.V0 p.c (p.b * p.c) ≤ m := (V0_c_nonpos M).trans hm
  have hmin' : ∀ P'' R'', p.c ≤ P'' → p.b * P'' ≤ R'' → M.Bval m P R ≤ M.Bval m P'' R'' :=
    fun P'' R'' h1 h2 => hmin P'' R'' ⟨h1, h2⟩
  have hec1 : ∀ P1, IsPMax p.b p.c M.V0 R P1 → P ≤ P1 :=
    fun P1 h => hEC7.1 P1 ⟨h.1, h.2.1⟩ (fun P'' hP'' => h.2.2 P'' hP''.1 hP''.2)
  have hec2 : ∀ R1, IsRMax p.b M.V0 P R1 → R ≤ R1 :=
    fun R1 h => hEC7.2 R1 ⟨hPR.1, h.1⟩ (fun R'' hR'' => h.2 R'' hR''.2)
  have hmax : ∀ P'' R'', p.c ≤ P'' → p.b * P'' ≤ R'' → M.V0 P'' R'' ≤ M.V0 P' R' :=
    fun P'' R'' h1 h2 => hNV'.2 P'' R'' ⟨h1, h2⟩
  have hVPR : M.V0 P R ≤ M.V0 P' R' := hmax P R hPR.1 hPR.2
  by_cases hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)
  · refine core_gen p.b p.c p.s p.hb hsc M.V0 (fun P R => M.Bval m P R) (Psi M)
      (fun P R => if M.V0 P R = m then 0 else ⊤) m (hdegB hdeg m) hscale hmonoR hpos hcont hV0
      (fun P1 R1 h => if_pos h) hRex hPex hRord hPord P R hPR.1 hPR.2 hmin' hfin hec1 hec2
      P' R' hNV'.1.1 hNV'.1.2 hmax ?_
    intro hle
    by_cases h : M.V0 P R = m
    · have : M.V0 P' R' = m := le_antisymm hle (h ▸ hVPR)
      simp [this]
    · simp [h]
  · obtain ⟨hB, hZM⟩ := hT1 hdeg
    refine core_gen p.b p.c p.s p.hb hsc M.V0 (fun P R => M.Bval m P R) (Psi M)
      (fun P R => ENNReal.ofReal ((m - M.V0 P R) ^ 2 / (M.ZM0 - 1))) m (hB m) hscale hmonoR
      hpos hcont hV0 (fun P1 R1 h => by simp [h]) hRex hPex hRord hPord P R hPR.1 hPR.2 hmin'
      hfin hec1 hec2 P' R' hNV'.1.1 hNV'.1.2 hmax ?_
    intro hle
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by linarith))
    nlinarith

end HedgePSNVProp5

open HedgePSNVProp5 in
open HedgePSNV in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (h1P : Assumption1 (M.P.map M.AT)) (h1M : Assumption1 (M.PM.map M.AT))
    (PNV RNV : ℝ) (hNV : IsNVMaximizer p M.P M.AT PNV RNV)
    (h2 : Assumption2 p M.P M.AT PNV RNV) (h3 : Assumption3 p M.P M.AT PNV RNV)
    (m : ℝ) (hm : 0 ≤ m) (P R : ℝ) (hPR : (P, R) ∈ decisionDomain p)
    (hmin : ∀ P' R' : ℝ, (P', R') ∈ decisionDomain p → M.Bval m P R ≤ M.Bval m P' R')
    (hfin : M.Bval m P R < ⊤) :
    ∀ P' R' : ℝ, IsNVMaximizer p M.PM M.AT P' R' → P ≤ P' ∧ R ≤ R' := by
  have hPM : IsProbabilityMeasure M.PM := PM_prob M hM h5
  have hAM : AEMeasurable M.AT M.PM := (AT_aemeas M hM).mono_ac (PM_ac M)
  have hν : IsProbabilityMeasure (M.PM.map M.AT) := Measure.isProbabilityMeasure_map hAM
  exact prop5_of_children p M hM h5 m hm P R hPR hmin hfin
    (fun hne => ⟨(HedgePSNV.theorem_1_ii p M hM hL2 h4 h5 hne).1,
      (HedgePSNV.theorem_1_ii p M hM hL2 h4 h5 hne).2.2.1⟩)
    (HedgePSNV.theorem_1_ii_degenerate p M hM hL2 h4 h5)
    (HedgePSNV.lemma_ec_7 p M hM hL2 h4 h5 h1P h1M PNV RNV hNV h2 h3 m hm P R hPR hmin hfin)
    (fun P R hP => HedgePSNV.hedging_residual_pos p M hM h5 h1M P R hP)
    (HedgePSNV.riskneutral_section_maximizers p (M.PM.map M.AT) (hint_map M hM hL2 h5) h1M)
