-- Prove2me | solution 1 for GlobalTheory.QuotIntFJ.weil_formula_FJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:03.079877+00:00
-- url     : https://prove2.me/submissions/45d97cba-8bbc-4a53-bfb6-2f610d7f65e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProperTripleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicQuotient
import Theorems.Thm_GlobalTheory_QuotIntFJ_integral_rotate_three
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_QuotInt_continuous_embX
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_continuous_colE
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_colE
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_embX
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_VolN_continuous_co
import Theorems.Thm_GlobalTheory_RootEx_VolN_volN_eq
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_volGL_haar
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_T_exists_compact_preimage_embX_mul_colE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.QuotIntFJ
namespace GlobalTheory.QuotIntFJ
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) f z → (∀ h, Integrable (fun β : n → k => f (colE c (ρ + 1) β * h)) (Measure.pi fun _ => ν)) ∧ IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k, f (colE c (ρ + 1) β * h) ∂(Measure.pi fun _ => ν)) z := by
  intro k _ _ _ _ _ _ n _ _ c ρ hρ hρc ν _ μX _ μG f z hq
  obtain ⟨F, hF, hfF, hz⟩ := hq
  have hF' : IsLocallyConstant F ∧ HasCompactSupport F := hF
  obtain ⟨hsck, ht2k⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have := hsck
  have := ht2k
  obtain ⟨hB1, hL1, hS1, -⟩ := volGL_haar k n ν
  obtain ⟨hB2, hL2, hS2, -⟩ := volGL_haar k (n ⊕ Fin c) ν
  have := hB1
  have := hL1
  have := hS1
  have := hB2
  have := hL2
  have := hS2

  have hV : volN ν n c (ρ + 1) =
      (Measure.pi fun _ => ν).map (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)) :=
    GlobalTheory.RootEx.VolN.volN_eq (n := n) (c := c) ν (ρ + 1)
  have : SigmaFinite (volN ν n c (ρ + 1)) := by
    rw [hV]
    exact (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)).sigmaFinite_map
  have : IsFiniteMeasureOnCompacts (volN ν n c (ρ + 1)) := by
    rw [hV]
    refine ⟨fun K hK => ?_⟩
    rw [MeasurableEquiv.map_apply]
    have hpre : (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)) ⁻¹' K =
        GlobalTheory.RootEx.VolN.co (ρ + 1) '' K := by
      ext e
      constructor
      · intro he
        exact ⟨_, he, GlobalTheory.RootEx.VolN.co_mkNel _ e⟩
      · rintro ⟨g, hg, rfl⟩
        show GlobalTheory.RootEx.Model.mkNel _ (GlobalTheory.RootEx.VolN.co _ g) ∈ K
        rw [GlobalTheory.RootEx.VolN.mkNel_co]
        exact hg
    rw [hpre]
    exact (hK.image (GlobalTheory.RootEx.VolN.continuous_co _)).measure_lt_top

  have hint : ∀ h : GL (n ⊕ Fin c) k, Integrable
      (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h))
      ((Measure.pi fun _ => ν).prod (μX.prod (volN ν n c (ρ + 1)))) := by
    intro h
    have hcont : Continuous (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h)) := by
      refine hF'.1.continuous.comp (Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) ?_) continuous_const)
      · exact GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_fst.comp continuous_snd)
      · exact continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
      · exact (GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp continuous_fst
    obtain ⟨D, hD, hDC⟩ := GlobalTheory.T.exists_compact_preimage_embX_mul_colE k n c ρ hρ hρc ((fun g => g * h⁻¹) '' tsupport F)
      (hF'.2.image (continuous_mul_const h⁻¹))
    have hsupp : HasCompactSupport (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h)) := by
      refine HasCompactSupport.intro
        (hD.image (f := fun t : GL n k × N k n c (ρ + 1) × (n → k) => (t.2.2, (t.1, t.2.1)))
          (by fun_prop)) ?_
      intro w hw
      by_contra hne
      apply hw
      refine ⟨(w.2.1, w.2.2, w.1), hDC _ ⟨_, subset_tsupport _ hne, ?_⟩, rfl⟩
      simp [mul_assoc]
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hfeq : ∀ (h : GL (n ⊕ Fin c) k) (b : n → k), f (colE c (ρ + 1) b * h) =
      ∫ x, ∫ u : N k n c (ρ + 1), F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h)
        ∂(volN ν n c (ρ + 1)) ∂μX := by
    intro h b
    rw [hfF]
    simp only [mul_assoc]
  have key := fun h : GL (n ⊕ Fin c) k => integral_rotate_three (Measure.pi fun _ : n => ν) μX
    (volN ν n c (ρ + 1))
    (fun b x (u : N k n c (ρ + 1)) => F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h))
    (hint h)
  refine ⟨fun h => (key h).1.congr (Filter.Eventually.of_forall fun b => (hfeq h b).symm), ?_⟩
  unfold IsQuotIntFJ
  refine ⟨F, hF, fun h => ?_, hz⟩
  calc ∫ b : n → k, f (colE c (ρ + 1) b * h) ∂(Measure.pi fun _ => ν)
      = ∫ b : n → k, ∫ x, ∫ u : N k n c (ρ + 1),
          F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h)
            ∂(volN ν n c (ρ + 1)) ∂μX ∂(Measure.pi fun _ => ν) :=
        integral_congr_ae (Filter.Eventually.of_forall (hfeq h))
    _ = _ := (key h).2
end GlobalTheory.QuotIntFJ
