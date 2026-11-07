-- Prove2me | solution 1 for HedgePSNV.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T23:53:39.281087+00:00
-- url     : https://prove2.me/submissions/09c668ed-9379-45ad-a894-fe565b046dd1

import Mathlib
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Theorems.Thm_HedgePSNV_remark_1
import Theorems.Thm_HedgePSNV_lemma_ec_6
import Theorems.Thm_HedgePSNV_proposition_1

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNVProp4

open HedgePSNV

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

lemma isNVMax_map (p : Params) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (A : Ω → ℝ)
    (hA : AEMeasurable A Q) (P R : ℝ) :
    IsNVMaximizer p (Q.map A) id P R ↔ IsNVMaximizer p Q A P R := by
  unfold IsNVMaximizer
  simp only [nvValue_map p Q A hA]

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

lemma usualOrder_map {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) (X : Ω → ℝ)
    (hμ : AEMeasurable X μ) (hν : AEMeasurable X ν)
    (h : StochasticOrders.Usual.UsualOrder μ ν X X) :
    StochasticOrders.Usual.UsualOrder (μ.map X) (ν.map X) id id := by
  intro x
  have hs : MeasurableSet {a : ℝ | x < id a} := measurableSet_Ioi
  rw [Measure.map_apply_of_aemeasurable hμ hs, Measure.map_apply_of_aemeasurable hν hs]
  exact h x

end HedgePSNVProp4

open HedgePSNVProp4 in
open HedgePSNV in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hintM : M.NegPartIntegrable M.PM) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (h1P : Assumption1 (M.P.map M.AT)) (h1M : Assumption1 (M.PM.map M.AT))
    (PNV RNV : ℝ) (hNV : IsNVMaximizer p M.P M.AT PNV RNV)
    (h2 : Assumption2 p M.P M.AT PNV RNV) (h3 : Assumption3 p M.P M.AT PNV RNV)
    (hpos : StochasticOrders.Usual.UsualOrder M.PM M.P (M.C p.T) (M.C p.T)) :
    (∀ P' R' : ℝ, IsNVMaximizer p M.PM M.AT P' R' → P' ≤ PNV ∧ R' ≤ RNV) ∧
    ∀ P R : ℝ, p.s ≤ P → M.V0 P R ≤ nvValue p M.P M.AT P R := by
  have hP := hM.prob
  have hPM := PM_prob M hM h5
  have hAP : AEMeasurable M.AT M.P := AT_aemeas M hM
  have hAM : AEMeasurable M.AT M.PM := hAP.mono_ac (PM_ac M)
  have hν₁ : IsProbabilityMeasure (M.PM.map M.AT) := Measure.isProbabilityMeasure_map hAM
  have hν₂ : IsProbabilityMeasure (M.P.map M.AT) := Measure.isProbabilityMeasure_map hAP
  have hordA := (HedgePSNV.remark_1 p M hM hPM).1 hpos
  have hord := usualOrder_map M.PM M.P M.AT hAM hAP hordA
  have hint₁ : Integrable (fun a : ℝ => max (-a) 0) (M.PM.map M.AT) := by
    rw [integrable_map_measure (by fun_prop : AEMeasurable (fun a : ℝ => max (-a) 0)
      (M.PM.map M.AT)).aestronglyMeasurable hAM]
    exact negPart_AT_PM M hM hintM h5
  have hNV' : IsNVMaximizer p (M.P.map M.AT) id PNV RNV := (isNVMax_map p M.P M.AT hAP _ _).2 hNV
  have h2' : Assumption2 p (M.P.map M.AT) id PNV RNV := by
    unfold Assumption2
    rw [nvValue_map p M.P M.AT hAP]
    exact h2
  have huniq := (HedgePSNV.proposition_1 p (M.P.map M.AT) h1P PNV RNV hNV' h2').1
  have hec := HedgePSNV.lemma_ec_6 p (M.PM.map M.AT) (M.P.map M.AT) hint₁ h1M h1P hord
    PNV RNV hNV' huniq
  refine ⟨fun P' R' hmax => hec.1 P' R' ((isNVMax_map p M.PM M.AT hAM _ _).2 hmax),
    fun P R hPs => ?_⟩
  have := hec.2 P R hPs
  rw [nvValue_map p M.PM M.AT hAM, nvValue_map p M.P M.AT hAP] at this
  exact this
