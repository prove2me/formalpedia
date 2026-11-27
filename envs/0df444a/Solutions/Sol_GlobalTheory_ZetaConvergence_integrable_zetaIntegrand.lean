-- Prove2me | solution 1 for GlobalTheory.ZetaConvergence.integrable_zetaIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:04.337633+00:00
-- url     : https://prove2.me/submissions/ffc795b0-1284-4ed1-a3b7-d66b8fd31abd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableZetaIntegrand
import Theorems.Thm_GlobalTheory_ZetaConvergence_exists_nabs_le
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_SBUniform_exists_bound_period
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_measurableEmbedding_val
import Theorems.Thm_GlobalTheory_SplitWeil_continuous_density_volGL
import Theorems.Thm_GlobalTheory_SplitWeil_isLocallyConstant_nabs
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_P2M_GlobalTheory_SplitWeil_nabs_pos__162ed63212bf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open GlobalTheory GlobalTheory.ZetaConvergence
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.ZetaConvergence
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : GL n k → ℂ) (α : ℝ), Continuous c → (∀ N : ℕ, ∃ C : ℝ, ∀ g : GL n k, (∀ i j, Deep (-(N : ℤ)) (g.val i j)) → ‖c g‖ ≤ C * nabs k (GeneralLinearGroup.det g) ^ (-α)) → ∀ Φ ∈ SB (Matrix n n k), ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (zetaIntegrand Φ c s) (volGL ν n) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c α hc hb Φ hΦ
  obtain ⟨N, -, hN, -⟩ := GlobalTheory.SBUniform.exists_bound_period k n Φ hΦ
  obtain ⟨C, hC⟩ := hb N
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨B, hB⟩ := exists_nabs_le (IsCompact.image hK (f := fun x : Matrix n n k => x.det)
    continuous_id.matrix_det)
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : BorelSpace (GL n k) := SplitFlip.borel_GL
  have : SecondCountableTopology (GL n k) := SplitFlip.secondCountable_GL
  have hE := GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) n
  have hd := continuous_density_volGL (k := k) (n := n)
  have hn : IsLocallyConstant fun g : GL n k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hI : Integrable (fun g : GL n k => Φ g.val) ((volM ν n n).comap fun g : GL n k => g.val) := by
    have h1 : Integrable Φ (volM ν n n) := hl.continuous.integrable_of_hasCompactSupport hK
    refine hE.integrable_map_iff.1 ?_
    rw [hE.map_comap]
    exact h1.restrict
  refine ⟨α + Fintype.card n - ((Fintype.card n : ℝ) - 1) / 2, fun s hs => ?_⟩
  set t : ℂ := s + ((Fintype.card n : ℂ) - 1) / 2 with ht
  have htr : t.re = s.re + ((Fintype.card n : ℝ) - 1) / 2 := by
    have : ((Fintype.card n : ℂ) - 1) / 2 = ((((Fintype.card n : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [ht, this, Complex.add_re, Complex.ofReal_re]
  have he : 0 ≤ -(Fintype.card n : ℝ) + -α + t.re := by linarith
  have hz : Continuous (zetaIntegrand Φ c s) :=
    ((hl.continuous.comp Units.continuous_val).mul hc).mul (hn.comp fun r : ℝ => (r : ℂ) ^ t).continuous
  unfold volGL
  rw [integrable_withDensity_iff_integrable_smul' hd.measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hI.norm.mul_const (|C| * B ^ (-(Fintype.card n : ℝ) + -α + t.re))).mono'
    (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hz.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos' k (GeneralLinearGroup.det g)
  by_cases h0 : Φ g.val = 0
  · simp [zetaIntegrand, h0]
  have h1 : nabs k (GeneralLinearGroup.det g) ≤ B := hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩
  have h2 := (hC g (hN _ h0)).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hp.le _))
  rw [norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), zetaIntegrand, norm_mul, norm_mul,
    val_absPow, Complex.norm_cpow_eq_rpow_re_of_pos hp, ← ht, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
  set a := nabs k (GeneralLinearGroup.det g)
  calc _ ≤ a ^ (-(Fintype.card n : ℝ)) * (‖Φ g.val‖ * (|C| * a ^ (-α)) * a ^ t.re) := by gcongr
    _ = ‖Φ g.val‖ * (|C| * a ^ (-(Fintype.card n : ℝ) + -α + t.re)) := by
      rw [Real.rpow_add hp, Real.rpow_add hp]; ring
    _ ≤ _ := by gcongr
end GlobalTheory.ZetaConvergence
