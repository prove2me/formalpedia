-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.integrable_om_eMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:39:37.176649+00:00
-- url     : https://prove2.me/submissions/a98dc167-59b6-4124-8a62-4cd16b14b693

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableZetaIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrable
import Theorems.Thm_GlobalTheory_GodementJacquet_eMat_leftInv
import Theorems.Thm_GlobalTheory_GodementJacquet_isLocallyConstant_char_det
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_measurableEmbedding_val
import Theorems.Thm_GlobalTheory_SplitWeil_continuous_density_volGL
import Theorems.Thm_GlobalTheory_SplitWeil_isLocallyConstant_nabs
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_ZetaConvergence_exists_nabs_le
import Theorems.Thm_P2M_GlobalTheory_SplitWeil_nabs_pos__162ed63212bf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet Matrix
open GlobalTheory GlobalTheory.GodementJacquet
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.GodementJacquet
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (r t : ℕ) (μ : kˣ →* ℂˣ),
    r ≤ t → IsSmoothChar μ → IsUnitaryChar μ → ∀ (h : GL (Fin (r + t)) k)
      (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ), Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) (volGL ν (Fin r)) := by
  intro k _ _ _ _ _ _ ν _ r t μ hrt hμs hμu h Φ hΦ
  have hu : ∀ x : kˣ, ‖((μ x : ℂˣ) : ℂ)‖ = 1 := hμu
  set Φ' : Matrix (Fin r) (Fin r) k → ℂ := fun x => Φ ((h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * x)
    with hΦ'
  set P : Matrix (Fin r) (Fin (r + t)) k := Matrix.of fun i j => if (j : ℕ) = i then 1 else 0 with hP
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have hcont : Continuous fun x : Matrix (Fin r) (Fin r) k =>
      (h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * x :=
    continuous_const.matrix_mul continuous_id
  have hl' : IsLocallyConstant Φ' := hl.comp_continuous hcont
  have hK' : HasCompactSupport Φ' := by
    refine HasCompactSupport.intro (hK.image (f := fun y => P * h.val * y)
      (continuous_const.matrix_mul continuous_id)) fun x hx => ?_
    by_contra h0
    apply hx
    refine ⟨_, subset_tsupport _ h0, ?_⟩
    show P * h.val * ((h⁻¹ : GL _ k).val * eMat k r t * x) = x
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc P, Units.mul_inv, Matrix.mul_one, hP, eMat_leftInv, Matrix.one_mul]
  obtain ⟨B, hB⟩ := GlobalTheory.ZetaConvergence.exists_nabs_le (IsCompact.image hK'
    (f := fun x : Matrix (Fin r) (Fin r) k => x.det) continuous_id.matrix_det)
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have : BorelSpace (Matrix (Fin r) (Fin r) k) := inferInstanceAs (BorelSpace (Fin r → Fin r → k))
  have : (volM ν (Fin r) (Fin r)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : BorelSpace (GL (Fin r) k) := SplitFlip.borel_GL
  have : SecondCountableTopology (GL (Fin r) k) := SplitFlip.secondCountable_GL
  have hE := GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) (Fin r)
  have hd := continuous_density_volGL (k := k) (n := Fin r)
  have hn : IsLocallyConstant fun g : GL (Fin r) k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hI : Integrable (fun g : GL (Fin r) k => Φ' g.val)
      ((volM ν (Fin r) (Fin r)).comap fun g : GL (Fin r) k => g.val) := by
    have h1 : Integrable Φ' (volM ν (Fin r) (Fin r)) := hl'.continuous.integrable_of_hasCompactSupport hK'
    refine (hE.integrable_map_iff (g := Φ')).1 ?_
    rw [hE.map_comap]
    exact h1.restrict
  have hloc : IsLocallyConstant fun g : GL (Fin r) k => om μ g h Φ (eMat k r t) := by
    unfold om
    refine ((((isLocallyConstant_char_det hμs).mul (IsLocallyConstant.const _)).mul
      (hn.comp fun a => ((a ^ ((Fintype.card (Fin (r + t)) : ℝ) / 2) : ℝ) : ℂ))).mul
      (IsLocallyConstant.const _)).mul ?_
    exact hl'.comp_continuous Units.continuous_val
  set c : ℝ := nabs k (GeneralLinearGroup.det h) ^ (-(Fintype.card (Fin r) : ℝ) / 2) with hc
  unfold volGL
  rw [integrable_withDensity_iff_integrable_smul' hd.measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hI.norm.mul_const (c * B ^ (((t : ℝ) - r) / 2))).mono'
    (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hloc.continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos' k (GeneralLinearGroup.det g)
  have hq := nabs_pos' k (GeneralLinearGroup.det h)
  by_cases h0 : Φ' g.val = 0
  · have : om μ g h Φ (eMat k r t) = 0 := by
      simp only [om]
      rw [show Φ ((h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * g.val) = 0 from h0, mul_zero]
    simp [this, h0]
  have h1 : nabs k (GeneralLinearGroup.det g) ≤ B := hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩
  set a := nabs k (GeneralLinearGroup.det g) with ha
  have e1 : ‖om μ g h Φ (eMat k r t)‖ = a ^ (((r : ℝ) + t) / 2) * c * ‖Φ' g.val‖ := by
    simp only [om, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hq.le _),
      Fintype.card_fin, Nat.cast_add, hc, ha, hΦ']
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k _).le _)]
    ring
  rw [norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hp.le _),
    e1, Fintype.card_fin]
  have hc0 : 0 ≤ c := Real.rpow_nonneg hq.le _
  have h2 : a ^ (((t : ℝ) - r) / 2) ≤ B ^ (((t : ℝ) - r) / 2) :=
    Real.rpow_le_rpow hp.le h1 (div_nonneg (sub_nonneg.2 (by exact_mod_cast hrt)) (by norm_num))
  calc a ^ (-(r : ℝ)) * (a ^ (((r : ℝ) + t) / 2) * c * ‖Φ' g.val‖)
      = ‖Φ' g.val‖ * (c * a ^ (((t : ℝ) - r) / 2)) := by
        rw [show ((t : ℝ) - r) / 2 = -(r : ℝ) + ((r : ℝ) + t) / 2 by ring, Real.rpow_add hp]; ring
    _ ≤ ‖Φ' g.val‖ * (c * B ^ (((t : ℝ) - r) / 2)) := by gcongr
end GlobalTheory.GodementJacquet
