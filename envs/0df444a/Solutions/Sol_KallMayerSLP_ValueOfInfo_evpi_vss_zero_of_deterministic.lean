-- Prove2me | solution 1 for KallMayerSLP.ValueOfInfo.evpi_vss_zero_of_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:32:52.106256+00:00
-- url     : https://prove2.me/submissions/bc0d8424-8d07-4832-91dc-fd1c8e0fc637

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_EVPI
import Definitions.Def_KallMayerSLP_ValueOfInfo_VSS
import Definitions.Def_KallMayerSLP_ValueOfInfo_IsEVOptimal

set_option autoImplicit false

open MeasureTheory Matrix KallMayerSLP.ValueOfInfo
open scoped ENNReal

namespace KallMayerSLP.ValueOfInfo.DetProof

theorem eq_dirac_of_prob_singleton {r : ℕ} (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ]
    (ξhat : Fin r → ℝ) (hdet : μ {ξhat} = 1) :
    μ = Measure.dirac ξhat := by
  have hcompl0 : μ ({ξhat}ᶜ) = 0 := by
    rw [prob_compl_eq_zero_iff (MeasurableSet.singleton ξhat)]
    exact hdet
  ext S hS
  by_cases hmem : ξhat ∈ S
  · have hge : (1 : ℝ≥0∞) ≤ μ S := by
      rw [← hdet]
      exact measure_mono (Set.singleton_subset_iff.mpr hmem)
    rw [le_antisymm prob_le_one hge, Measure.dirac_apply' _ hS, Set.indicator_of_mem hmem,
      Pi.one_apply]
  · have hsub : S ⊆ {ξhat}ᶜ := fun x hx h => hmem ((Set.mem_singleton_iff.mp h) ▸ hx)
    rw [measure_mono_null hsub hcompl0, Measure.dirac_apply' _ hS, Set.indicator_of_notMem hmem]

theorem eExp_dirac {r : ℕ} (ξhat : Fin r → ℝ) (g : (Fin r → ℝ) → EReal) :
    eExp (Measure.dirac ξhat) g = g ξhat := by
  unfold eExp
  rw [lintegral_dirac, lintegral_dirac]
  cases hg : g ξhat using EReal.rec with
  | top =>
    simp
  | bot =>
    have h1 : (⊥ : EReal).toENNReal = 0 := by simp
    have h2 : (-(⊥ : EReal)).toENNReal = ∞ := by simp
    rw [h1, if_neg ENNReal.zero_ne_top, h2]
    rfl
  | coe a =>
    have h1 : (a : EReal).toENNReal = ENNReal.ofReal a := by simp [EReal.toENNReal]
    have h2 : (-(a : EReal)).toENNReal = ENNReal.ofReal (-a) := by
      rw [show -(a : EReal) = ((-a : ℝ) : EReal) from rfl]
      simp [EReal.toENNReal]
    rw [h1, if_neg ENNReal.ofReal_ne_top, h2, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
      ← EReal.coe_sub]
    congr 1
    rcases le_total 0 a with ha | ha
    · rw [max_eq_left ha, max_eq_right (by linarith)]; ring
    · rw [max_eq_right ha, max_eq_left (by linarith)]; ring

theorem ereal_le_coe_add_iff (B w : EReal) (a : ℝ) :
    B ≤ (a : EReal) + w ↔ B + ((-a : ℝ) : EReal) ≤ w := by
  cases B using EReal.rec <;> cases w using EReal.rec
  · simp
  · simp
  · simp
  · simp
  · rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith
  · simp
  · simp
  · rw [← EReal.coe_add, EReal.top_add_coe]
    exact ⟨fun h => absurd (top_le_iff.mp h) (EReal.coe_ne_top _),
      fun h => absurd (top_le_iff.mp h) (EReal.coe_ne_top _)⟩
  · rw [EReal.top_add_coe]
    simp

theorem rs_eq_gamma_dirac {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂)
    (ξhat : Fin r → ℝ) :
    RS P (Measure.dirac ξhat) = gamma P ξhat := by
  unfold RS gamma
  simp_rw [eExp_dirac]
  apply le_antisymm
  · refine le_sInf ?_
    rintro _ ⟨⟨x, y⟩, ⟨hAx, hTW, hx0, hy0⟩, rfl⟩
    have hx_mem : x ∈ firstStageSet P := ⟨hAx, hx0⟩
    have hy_mem : y ∈ {y | 0 ≤ y ∧ P.W ξhat *ᵥ y = P.h ξhat - P.T ξhat *ᵥ x} :=
      ⟨hy0, eq_sub_of_add_eq' hTW⟩
    have hrec : recourse P x ξhat ≤ ((P.q ξhat ⬝ᵥ y : ℝ) : EReal) :=
      sInf_le ⟨y, hy_mem, rfl⟩
    refine (iInf₂_le x hx_mem).trans ?_
    dsimp only
    rw [EReal.coe_add]
    exact add_le_add_right hrec _
  · refine le_iInf₂ fun x ⟨hAx, hx0⟩ => ?_
    rw [ereal_le_coe_add_iff]
    unfold recourse StochasticProg.RecourseKKT.secondStageValue
    refine le_sInf ?_
    rintro _ ⟨y, ⟨hy0, hWy⟩, rfl⟩
    rw [← ereal_le_coe_add_iff, ← EReal.coe_add]
    refine sInf_le ⟨(x, y), ⟨hAx, ?_, hx0, hy0⟩, rfl⟩
    rw [hWy]
    abel

end KallMayerSLP.ValueOfInfo.DetProof

open KallMayerSLP.ValueOfInfo.DetProof in
theorem solution {r n₁ m₁ n₂ m₂ : ℕ} (μ : Measure (Fin r → ℝ))
    [IsProbabilityMeasure μ] (ξhat : Fin r → ℝ) (hdet : μ {ξhat} = 1)
    (P : TwoStageSLP r n₁ m₁ n₂ m₂) :
    ((¬ (RS P μ = ⊤ ∧ WS P μ = ⊤) ∧ ¬ (RS P μ = ⊥ ∧ WS P μ = ⊥)) → EVPI P μ = 0) ∧
    (∀ xhat, IsEVOptimal P μ xhat → VSS P μ xhat = 0) := by
  have hμ : μ = Measure.dirac ξhat := eq_dirac_of_prob_singleton μ ξhat hdet
  have hxi : xiBar μ = ξhat := by
    ext j
    simp [xiBar, hμ, integral_dirac]
  have hWS : WS P μ = gamma P ξhat := by
    unfold WS; rw [hμ, eExp_dirac]
  have hRS : RS P μ = gamma P ξhat := by
    rw [hμ]; exact rs_eq_gamma_dirac P ξhat
  constructor
  · rintro ⟨hnot_top, hnot_bot⟩
    unfold EVPI
    rw [hRS, hWS] at hnot_top hnot_bot ⊢
    cases hg : gamma P ξhat using EReal.rec with
    | bot => exact absurd ⟨hg, hg⟩ hnot_bot
    | top => exact absurd ⟨hg, hg⟩ hnot_top
    | coe v => simp
  · intro xhat ⟨yhat, hAx, hTW, hx0, hy0, hEV⟩
    rw [hxi] at hTW hEV
    unfold EV at hEV
    rw [hxi] at hEV
    unfold VSS EEV
    rw [hμ, eExp_dirac, ← hμ, hRS, ← hEV]
    set v : ℝ := P.c ⬝ᵥ xhat + P.q ξhat ⬝ᵥ yhat
    have hEEV_le : ((P.c ⬝ᵥ xhat : ℝ) : EReal) + recourse P xhat ξhat ≤ (v : EReal) := by
      have hy_mem : yhat ∈ {y | 0 ≤ y ∧ P.W ξhat *ᵥ y = P.h ξhat - P.T ξhat *ᵥ xhat} :=
        ⟨hy0, eq_sub_of_add_eq' hTW⟩
      have hrec : recourse P xhat ξhat ≤ ((P.q ξhat ⬝ᵥ yhat : ℝ) : EReal) :=
        sInf_le ⟨yhat, hy_mem, rfl⟩
      simp only [v, EReal.coe_add]
      exact add_le_add_right hrec _
    have hEEV_ge : (v : EReal) ≤ ((P.c ⬝ᵥ xhat : ℝ) : EReal) + recourse P xhat ξhat := by
      rw [hEV, ← hRS, hμ]
      unfold RS
      simp_rw [eExp_dirac]
      exact iInf₂_le xhat ⟨hAx, hx0⟩
    rw [le_antisymm hEEV_le hEEV_ge]
    simp
