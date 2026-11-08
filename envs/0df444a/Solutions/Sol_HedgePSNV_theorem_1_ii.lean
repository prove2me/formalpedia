-- Prove2me | solution 1 for HedgePSNV.theorem_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T20:44:48.730952+00:00
-- url     : https://prove2.me/submissions/978933e5-1109-4f35-85df-f01210059c2f

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Theorems.Thm_HedgePSNV_asset_price_riskneutral_martingale
import Theorems.Thm_HedgePSNV_theorem_1_ii_lower_bound
import Theorems.Thm_HedgePSNV_theorem_1_ii_upper_bound

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedge

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

/-- `E[Z_T] = 1` (Assumption 5 martingale property and `Z_0 = 1` a.s.). -/
lemma integral_Z_T {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) : ∫ ω, M.Z p.T ω ∂M.P = 1 := by
  have := hM.prob
  have hZ0 : M.Z 0 =ᵐ[M.P] fun _ => (1 : ℝ) := by
    filter_upwards [I_zero_ae M hM] with ω hω
    simp [Model.Z, hω]
  have hce := h5.1.2.2 0 p.T zero_le le_rfl
  rw [← integral_condExp (M.F.le 0)]
  rw [integral_congr_ae (hce.trans hZ0)]
  simp

lemma Z_pos {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) (t : ℝ≥0) (ω : Ω) :
    0 < M.Z t ω := Real.exp_pos _

lemma Z_T_measurable {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) : Measurable (M.Z p.T) :=
  ((h5.1.1 p.T le_rfl).mono (M.F.le p.T)).measurable

/-- `Z^M_0 = E^M[Z_T] = E[Z_T^2]` (Theorem 1(ii), p.15). -/
lemma ZM0_eq {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) : M.ZM0 = ∫ ω, M.Z p.T ω ^ 2 ∂M.P := by
  have hm : Measurable (fun ω => (M.Z p.T ω).toNNReal) :=
    (Z_T_measurable M h5).real_toNNReal
  unfold Model.ZM0 Model.PM
  have hden : (fun ω => ENNReal.ofReal (M.Z p.T ω)) =
      (fun ω => (((M.Z p.T ω).toNNReal : ℝ≥0) : ℝ≥0∞)) := rfl
  rw [hden, integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Z_pos M p.T ω).le]
  ring

/-- `Z^M_0 > 1` when `Z_T` is not a.s. `1` (strict Jensen). -/
lemma one_lt_ZM0 {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5)
    (hne : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))) : 1 < M.ZM0 := by
  have := hM.prob
  rw [ZM0_eq M h5]
  have hL2 : MemLp (M.Z p.T) 2 M.P := h5.2 p.T le_rfl
  have hint : Integrable (M.Z p.T) M.P := h5.1.2.1 p.T le_rfl
  have hsq : Integrable (fun ω => M.Z p.T ω ^ 2) M.P := hL2.integrable_sq
  have hE := integral_Z_T M hM h5
  have hvar_int : Integrable (fun ω => (M.Z p.T ω - 1) ^ 2) M.P := by
    have : (fun ω => (M.Z p.T ω - 1) ^ 2) =
        fun ω => M.Z p.T ω ^ 2 - 2 * M.Z p.T ω + 1 := by
      funext ω; ring
    rw [this]
    exact (hsq.sub (hint.const_mul 2)).add (integrable_const 1)
  have hvar : ∫ ω, (M.Z p.T ω - 1) ^ 2 ∂M.P = ∫ ω, M.Z p.T ω ^ 2 ∂M.P - 1 := by
    have : (fun ω => (M.Z p.T ω - 1) ^ 2) =
        fun ω => M.Z p.T ω ^ 2 - 2 * M.Z p.T ω + 1 := by
      funext ω; ring
    rw [this]
    have h1 : ∫ ω, (M.Z p.T ω ^ 2 - 2 * M.Z p.T ω + 1) ∂M.P =
        ∫ ω, (M.Z p.T ω ^ 2 - 2 * M.Z p.T ω) ∂M.P + ∫ _ω, (1 : ℝ) ∂M.P :=
      integral_add (hsq.sub (hint.const_mul 2)) (integrable_const 1)
    have h2 : ∫ ω, (M.Z p.T ω ^ 2 - 2 * M.Z p.T ω) ∂M.P =
        ∫ ω, M.Z p.T ω ^ 2 ∂M.P - ∫ ω, 2 * M.Z p.T ω ∂M.P :=
      integral_sub hsq (hint.const_mul 2)
    rw [h1, h2, integral_const_mul, hE]
    simp
    ring
  have hnn : 0 ≤ᵐ[M.P] fun ω => (M.Z p.T ω - 1) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hpos : 0 < ∫ ω, (M.Z p.T ω - 1) ^ 2 ∂M.P := by
    rcases (integral_nonneg_of_ae hnn).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hne
      have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hvar_int).1 h.symm
      filter_upwards [h0] with ω hω
      have : (M.Z p.T ω - 1) ^ 2 = 0 := hω
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      simpa using (sub_eq_zero.1 this)
  linarith

end StochCalcHedge

/-! S8 tail (8c066573 relay 1, 2026-11-06): `0 ≤ Z_t/Z^M_t ≤ 1` a.s. and the three elementary
conjuncts of theorem_1_ii (everything except the value formula (21)).
Appended after S8.lean (namespace StochCalcHedge provides I_zero_ae, Z_pos, Z_T_measurable,
ZM0_eq, one_lt_ZM0). -/

namespace StochCalcS8b

open HedgePSNV StochCalcHedge

lemma PM_prob {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) : IsProbabilityMeasure M.PM := by
  have := hM.prob
  have hint : Integrable (M.Z p.T) M.P := (h5.1.2.1 p.T le_rfl)
  constructor
  unfold Model.PM
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le), integral_Z_T M hM h5,
    ENNReal.ofReal_one]

lemma P_ac_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) : M.P ≪ M.PM := by
  exact withDensity_absolutelyContinuous' (Z_T_measurable M h5).ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun ω => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _)

/-- `∫ Z_T g dP = ∫ g dP^M` (density `Z_T`). -/
lemma integral_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) (g : Ω → ℝ) :
    ∫ ω, M.Z p.T ω * g ω ∂M.P = ∫ ω, g ω ∂M.PM := by
  have hm : Measurable (fun ω => (M.Z p.T ω).toNNReal) :=
    (Z_T_measurable M h5).real_toNNReal
  unfold Model.PM
  have hden : (fun ω => ENNReal.ofReal (M.Z p.T ω)) =
      (fun ω => (((M.Z p.T ω).toNNReal : ℝ≥0) : ℝ≥0∞)) := rfl
  rw [hden, integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Z_pos M p.T ω).le]

/-- `g` is `P^M`-integrable when `Z_T g` is `P`-integrable. -/
lemma int_PM_of {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) (g : Ω → ℝ) (hg : Integrable (fun ω => M.Z p.T ω * g ω) M.P) :
    Integrable g M.PM := by
  have hm : Measurable (fun ω => (M.Z p.T ω).toNNReal) :=
    (Z_T_measurable M h5).real_toNNReal
  unfold Model.PM
  have hden : (fun ω => ENNReal.ofReal (M.Z p.T ω)) =
      (fun ω => (((M.Z p.T ω).toNNReal : ℝ≥0) : ℝ≥0∞)) := rfl
  rw [hden, integrable_withDensity_iff_integrable_smul hm]
  refine hg.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Z_pos M p.T ω).le]

/-- `Z_t ≤ Z^M_t` `P^M`-a.s. for `t ≤ T`: for `s ∈ F_t`,
`∫_s Z^M_t dP^M = ∫_s Z_T² dP ≥ ∫_s Z_t² dP = ∫_s Z_t Z_T dP = ∫_s Z_t dP^M`. -/
lemma Z_le_ZM_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) (t : ℝ≥0) (ht : t ≤ p.T) :
    ∀ᵐ ω ∂M.PM, M.Z t ω ≤ M.ZM t ω := by
  have := hM.prob
  haveI := PM_prob M hM h5
  have hT2 : MemLp (M.Z p.T) 2 M.P := h5.2 p.T le_rfl
  have ht2 : MemLp (M.Z t) 2 M.P := h5.2 t ht
  have hTT : Integrable (fun ω => M.Z p.T ω * M.Z p.T ω) M.P := hT2.integrable_mul hT2
  have hTt : Integrable (fun ω => M.Z p.T ω * M.Z t ω) M.P := hT2.integrable_mul ht2
  have htt : Integrable (fun ω => M.Z t ω * M.Z t ω) M.P := ht2.integrable_mul ht2
  have hZTPM : Integrable (M.Z p.T) M.PM := int_PM_of M h5 _ hTT
  have hZtPM : Integrable (M.Z t) M.PM := int_PM_of M h5 _ hTt
  have hZMPM : Integrable (M.ZM t) M.PM := integrable_condExp
  have hmt : StronglyMeasurable[M.F t] (M.Z t) := h5.1.1 t ht
  have hmart : condExp (M.F t) M.P (M.Z p.T) =ᵐ[M.P] M.Z t := h5.1.2.2 t p.T ht le_rfl
  set f : Ω → ℝ := fun ω => M.ZM t ω - M.Z t ω with hf
  have hfm : StronglyMeasurable[M.F t] f :=
    (stronglyMeasurable_condExp (m := M.F t) (μ := M.PM) (f := M.Z p.T)).sub hmt
  have hfi : Integrable f M.PM := hZMPM.sub hZtPM
  have key : ∀ s, MeasurableSet[M.F t] s → 0 ≤ ∫ ω in s, f ω ∂M.PM := by
    intro s hs
    have hs' : MeasurableSet s := M.F.le t s hs
    -- set integrals under P^M as P-integrals
    have e1 : ∫ ω in s, M.ZM t ω ∂M.PM = ∫ ω in s, M.Z p.T ω * M.Z p.T ω ∂M.P := by
      unfold Model.ZM
      rw [setIntegral_condExp (M.F.le t) hZTPM hs, ← integral_indicator hs',
        ← integral_indicator hs', ← integral_PM M h5]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      by_cases h : ω ∈ s <;> simp [h]
    have e2 : ∫ ω in s, M.Z t ω ∂M.PM = ∫ ω in s, M.Z p.T ω * M.Z t ω ∂M.P := by
      rw [← integral_indicator hs', ← integral_indicator hs', ← integral_PM M h5]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      by_cases h : ω ∈ s <;> simp [h]
    -- pull-out: ∫_s Z_T Z_t dP = ∫_s Z_t Z_t dP
    have e3 : ∫ ω in s, M.Z p.T ω * M.Z t ω ∂M.P = ∫ ω in s, M.Z t ω * M.Z t ω ∂M.P := by
      rw [← integral_indicator hs', ← integral_indicator hs']
      have q1 : s.indicator (fun ω => M.Z p.T ω * M.Z t ω) =
          (s.indicator (M.Z t)) * (M.Z p.T) := by
        funext ω; by_cases h : ω ∈ s <;> simp [h, mul_comm]
      have q2 : s.indicator (fun ω => M.Z t ω * M.Z t ω) =
          (s.indicator (M.Z t)) * (M.Z t) := by
        funext ω; by_cases h : ω ∈ s <;> simp [h]
      have hsm : StronglyMeasurable[M.F t] (s.indicator (M.Z t)) := hmt.indicator hs
      have hint : Integrable ((s.indicator (M.Z t)) * (M.Z p.T)) M.P := by
        rw [← q1]; exact hTt.indicator hs' |>.congr (Filter.Eventually.of_forall fun ω => by
          by_cases h : ω ∈ s <;> simp [h, mul_comm])
      rw [q1, q2, ← integral_condExp (M.F.le t)]
      refine integral_congr_ae ?_
      filter_upwards [condExp_mul_of_stronglyMeasurable_left hsm hint (h5.1.2.1 p.T le_rfl),
        hmart] with ω h1 h2
      rw [h1]; simp only [Pi.mul_apply, h2]
    have hsq : 0 ≤ ∫ ω in s, (M.Z p.T ω - M.Z t ω) ^ 2 ∂M.P :=
      setIntegral_nonneg hs' (fun ω _ => sq_nonneg _)
    have hexp : ∫ ω in s, (M.Z p.T ω - M.Z t ω) ^ 2 ∂M.P =
        ∫ ω in s, M.Z p.T ω * M.Z p.T ω ∂M.P - 2 * ∫ ω in s, M.Z p.T ω * M.Z t ω ∂M.P +
          ∫ ω in s, M.Z t ω * M.Z t ω ∂M.P := by
      have i1 : Integrable (fun ω => M.Z p.T ω * M.Z p.T ω - 2 * (M.Z p.T ω * M.Z t ω))
          (M.P.restrict s) := (hTT.sub (hTt.const_mul 2)).restrict
      have a1 : ∫ ω in s, (M.Z p.T ω - M.Z t ω) ^ 2 ∂M.P =
          ∫ ω in s, ((M.Z p.T ω * M.Z p.T ω - 2 * (M.Z p.T ω * M.Z t ω)) +
            M.Z t ω * M.Z t ω) ∂M.P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only; ring
      have a2 : ∫ ω in s, ((M.Z p.T ω * M.Z p.T ω - 2 * (M.Z p.T ω * M.Z t ω)) +
            M.Z t ω * M.Z t ω) ∂M.P =
          ∫ ω in s, (M.Z p.T ω * M.Z p.T ω - 2 * (M.Z p.T ω * M.Z t ω)) ∂M.P +
            ∫ ω in s, M.Z t ω * M.Z t ω ∂M.P := integral_add i1 htt.restrict
      have a3 : ∫ ω in s, (M.Z p.T ω * M.Z p.T ω - 2 * (M.Z p.T ω * M.Z t ω)) ∂M.P =
          ∫ ω in s, M.Z p.T ω * M.Z p.T ω ∂M.P - ∫ ω in s, 2 * (M.Z p.T ω * M.Z t ω) ∂M.P :=
        integral_sub hTT.restrict (hTt.const_mul 2).restrict
      rw [a1, a2, a3, integral_const_mul]
    have hsub : ∫ ω in s, f ω ∂M.PM =
        ∫ ω in s, M.ZM t ω ∂M.PM - ∫ ω in s, M.Z t ω ∂M.PM :=
      integral_sub hZMPM.restrict hZtPM.restrict
    rw [hsub, e1, e2]
    linarith
  have htr : 0 ≤ᵐ[M.PM.trim (M.F.le t)] f := by
    refine ae_nonneg_of_forall_setIntegral_nonneg (hfi.trim (M.F.le t) hfm) ?_
    intro s hs _
    rw [← setIntegral_trim (M.F.le t) hfm hs]
    exact key s hs
  filter_upwards [ae_of_ae_trim (M.F.le t) htr] with ω hω
  have : 0 ≤ M.ZM t ω - M.Z t ω := hω
  linarith

lemma Z_div_ZM_nonneg {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) (t : ℝ≥0) : ∀ᵐ ω ∂M.P, 0 ≤ M.Z t ω / M.ZM t ω := by
  have h : 0 ≤ᵐ[M.PM] M.ZM t := by
    unfold Model.ZM
    exact condExp_nonneg (Filter.Eventually.of_forall fun ω => by
      show (0 : ℝ) ≤ M.Z p.T ω
      simp only [Model.Z]; exact (Real.exp_pos _).le)
  filter_upwards [P_ac_PM M h5 h] with ω hω
  exact div_nonneg (Z_pos M t ω).le hω

lemma Z_div_ZM_le_one {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) (t : ℝ≥0) (ht : t ≤ p.T) :
    ∀ᵐ ω ∂M.P, M.Z t ω / M.ZM t ω ≤ 1 := by
  filter_upwards [P_ac_PM M h5 (Z_le_ZM_PM M hM h5 t ht)] with ω hω
  rcases le_or_gt (M.ZM t ω) 0 with h0 | h0
  · exact (div_nonpos_of_nonneg_of_nonpos (Z_pos M t ω).le h0).trans zero_le_one
  · exact (div_le_one h0).2 hω

/-- The three elementary conjuncts of theorem_1_ii (all but the value formula (21)). -/
theorem t1ii_elem {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5)
    (hne : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))) :
    M.ZM0 = ∫ ω, M.Z p.T ω ^ 2 ∂M.P ∧ 1 < M.ZM0 ∧
    ∀ t : ℝ≥0, t ≤ p.T → ∀ᵐ ω ∂M.P, 0 ≤ M.Z t ω / M.ZM t ω ∧ M.Z t ω / M.ZM t ω ≤ 1 :=
  ⟨ZM0_eq M h5, one_lt_ZM0 M hM h5 hne, fun t ht => by
    filter_upwards [Z_div_ZM_nonneg M h5 t, Z_div_ZM_le_one M hM h5 t ht] with ω h1 h2
    exact ⟨h1, h2⟩⟩

end StochCalcS8b


open HedgePSNV MeasureTheory ProbabilityTheory in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hne : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))) :
    (∀ m P R : ℝ, M.Bval m P R =
      ENNReal.ofReal ((m - M.V0 P R) ^ 2 / (M.ZM0 - 1)) +
        ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
          ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2)
            ∂M.P) ∧
    M.ZM0 = ∫ ω, M.Z p.T ω ^ 2 ∂M.P ∧ 1 < M.ZM0 ∧
    ∀ t : ℝ≥0, t ≤ p.T → ∀ᵐ ω ∂M.P, 0 ≤ M.Z t ω / M.ZM t ω ∧ M.Z t ω / M.ZM t ω ≤ 1 := by
  have hXM := HedgePSNV.asset_price_riskneutral_martingale p M hM h4 h5
  exact ⟨fun m P R => le_antisymm
      (HedgePSNV.theorem_1_ii_upper_bound p M hM hL2 h4 h5 hne hXM m P R)
      (HedgePSNV.theorem_1_ii_lower_bound p M hM hL2 h4 h5 hne hXM m P R),
    StochCalcS8b.t1ii_elem M hM h5 hne⟩
