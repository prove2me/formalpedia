-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.fOp_nOp_fOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:42:37.950816+00:00
-- url     : https://prove2.me/submissions/50cb9450-3f89-420f-8586-f4a4fda5c6af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGauss
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_continuous_std
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_exists_big
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_setIntegral_add_left_mem
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_NL_add
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_NL_smul
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_tr_symm
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_tr_smul_right
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_tr_add_right
import Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_psiK_add
import Theorems.Thm_GlobalTheory_JR_EtMeas_continuous_NL
import Theorems.Thm_GlobalTheory_JR_EtMeas_eq_zero_of_trace
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_formL_apply
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure
import Theorems.Thm_GlobalTheory_JR_SelfDualUniq_selfDual_exists_unique_isTest


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad
open Fnf
namespace GlobalTheory.JR.WeilQuad
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ)
    (hH : Hyp A ψ x μ ω) (u : A.Kˣ) (G : ℂ) (hG : IsStableGauss A ψ x μ u G) (φ : A.L → ℂ) (hφ : IsTest φ)
    (z : A.L) :
    fOp A ψ x μ (nOp A ψ x u (fOp A ψ x μ φ)) z = G * A.psiK ψ (-((u⁻¹ : A.Kˣ) : A.K) * x * A.NL z) *
      fOp A ψ x μ (nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) φ) ((-((u⁻¹ : A.Kˣ) : A.K)) • z) := by
  obtain ⟨-, -, hψ, hsd, -⟩ := hH
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  have hμ : μ.IsAddHaarMeasure := hsd.1
  obtain ⟨-, hinj, -, htr, hnd0⟩ := Et.quadratic_structure F E A

  have hψc := continuous_std ψ hψ
  have htrKc : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have htrLc : Continuous (Algebra.trace A.K A.L) :=
    IsModuleTopology.continuous_of_linearMap ((Algebra.trace A.K A.L).restrictScalars F)
  have hec : Continuous (A.psiK ψ) := by
    show Continuous fun t => ψ (Algebra.trace F A.K t)
    exact hψc.comp htrKc
  have hNc := EtMeas.continuous_NL A
  have hk2 : Continuous (fun p : A.L × A.L => A.kerL ψ x p.1 p.2) := by
    show Continuous fun p : A.L × A.L => A.psiK ψ ((x : A.K) * Algebra.trace A.K A.L (star p.1 * p.2))
    exact hec.comp (continuous_const.mul (htrLc.comp ((continuous_star.comp continuous_fst).mul continuous_snd)))
  have hφc : Continuous φ := hφ.1.continuous
  have hsmc : ∀ c : A.K, Continuous (fun v : A.L => c • v) := fun c => by
    simp_rw [Algebra.smul_def]; exact continuous_const.mul continuous_id

  have hs : (EtMeas.formL A x).IsSymm := ⟨fun y y' => by
    rw [EtMeas.formL_apply, EtMeas.formL_apply]
    congr 2
    apply hinj
    rw [htr, htr]; simp [add_comm, mul_comm]⟩
  have hl : ∀ y', (∀ y, EtMeas.formL A x y' y = 0) → y' = 0 := fun y' h => hnd0 y' fun y => by
    have h1 : (x : A.K) * Algebra.trace A.K A.L (star y' * y) = 0 := EtMeas.eq_zero_of_trace F A.K _ fun k => by
      have := h (k • y)
      rw [EtMeas.formL_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    simpa using h1
  have hfφ : IsTest (fOp A ψ x μ φ) :=
    (SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ A.L (EtMeas.formL A x) hs
      ⟨hl, fun y h => hl y fun y' => by rw [hs.eq]; exact h y'⟩).2 μ hμ φ hφ

  set ui : A.K := ((u⁻¹ : A.Kˣ) : A.K) with hui
  have huui : (u : A.K) * ui = 1 := by simp [hui]
  obtain ⟨Λ₀, hΛ₀o, hΛ₀c, hΛ₀⟩ := hG
  set S := tsupport φ with hSdef
  have hSc : IsCompact S := hφ.2
  have hSm : MeasurableSet S := (isClosed_tsupport φ).measurableSet
  have hCc : IsCompact (tsupport (fOp A ψ x μ φ) ∪ (fun y => ui • (y + z)) '' S) :=
    hfφ.2.union (hSc.image ((hsmc ui).comp (continuous_id.add continuous_const)))
  obtain ⟨Λ, hΛo, hΛc, hΛ₀Λ, hCΛ⟩ := exists_big (F := F) Λ₀ hΛ₀o hΛ₀c _ hCc
  have hGΛ : gaussInt A ψ x μ u Λ = G := hΛ₀ Λ hΛo hΛc hΛ₀Λ
  have hΛm : MeasurableSet (Λ : Set A.L) := hΛo.measurableSet
  have hφ0 : ∀ y ∉ S, φ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hf0 : ∀ y' ∉ (Λ : Set A.L), fOp A ψ x μ φ y' = 0 := fun y' hy' =>
    image_eq_zero_of_notMem_tsupport fun h => hy' (hCΛ (Or.inl h))
  have hfS : ∀ y', fOp A ψ x μ φ y' = ∫ y in S, φ y * A.kerL ψ x y y' ∂μ := fun y' =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hφ0 y hy, zero_mul]).symm

  have e1 : fOp A ψ x μ (nOp A ψ x u (fOp A ψ x μ φ)) z =
      ∫ y' in (Λ : Set A.L), ∫ y in S, φ y * (A.psiK ψ ((u : A.K) * x * A.NL y') * A.kerL ψ x y y' *
        A.kerL ψ x y' z) ∂μ ∂μ := by
    show ∫ y', nOp A ψ (x : A.K) (u : A.K) (fOp A ψ x μ φ) y' * A.kerL ψ x y' z ∂μ = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Λ : Set A.L))]
    · refine setIntegral_congr_fun hΛm fun y' _ => ?_
      simp only [nOp, hfS y']
      rw [← integral_const_mul, ← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      ring
    · intro y' hy'
      simp only [nOp, hf0 y' hy', mul_zero, zero_mul]

  have hint : Integrable (Function.uncurry fun y' y => φ y * (A.psiK ψ ((u : A.K) * x * A.NL y') *
      A.kerL ψ x y y' * A.kerL ψ x y' z)) ((μ.restrict Λ).prod (μ.restrict S)) := by
    rw [Measure.prod_restrict]
    have hc : Continuous fun p : A.L × A.L => φ p.2 * (A.psiK ψ ((u : A.K) * x * A.NL p.1) *
        A.kerL ψ x p.2 p.1 * A.kerL ψ x p.1 z) :=
      (hφc.comp continuous_snd).mul (((hec.comp (continuous_const.mul (hNc.comp continuous_fst))).mul
        (hk2.comp continuous_swap)).mul (hk2.comp (continuous_fst.prodMk continuous_const)))
    exact hc.continuousOn.integrableOn_compact (hΛc.prod hSc)
  have e2 := integral_integral_swap hint

  have e3 : ∀ y ∈ S, ∫ y' in (Λ : Set A.L), φ y * (A.psiK ψ ((u : A.K) * x * A.NL y') * A.kerL ψ x y y' *
      A.kerL ψ x y' z) ∂μ = φ y * (G * A.psiK ψ (-(ui * x * A.NL (y + z)))) := by
    intro y hy
    have hw : ui • (y + z) ∈ Λ := hCΛ (Or.inr ⟨y, hy, rfl⟩)
    have hpt : (fun y' => φ y * (A.psiK ψ ((u : A.K) * x * A.NL y') * A.kerL ψ x y y' * A.kerL ψ x y' z)) =
        fun y' => (φ y * A.psiK ψ (-(ui * x * A.NL (y + z)))) * A.psiK ψ ((u : A.K) * x * A.NL (ui • (y + z) + y')) := by
      funext y'
      have h3 : A.psiK ψ ((u : A.K) * x * A.NL y') * A.kerL ψ x y y' * A.kerL ψ x y' z =
          A.psiK ψ (-(ui * x * A.NL (y + z))) * A.psiK ψ ((u : A.K) * x * A.NL (ui • (y + z) + y')) := by
        simp only [Et.kerL]
        rw [← psiK_add, ← psiK_add, ← psiK_add]
        congr 1
        rw [NL_add A (ui • (y + z)) y', NL_smul, tr_symm A (ui • (y + z)) y', tr_smul_right, tr_add_right,
          tr_symm A y y']
        linear_combination (-(ui * x * A.NL (y + z)) - (x : A.K) * (Algebra.trace A.K A.L (star y' * y) +
          Algebra.trace A.K A.L (star y' * z))) * huui
      rw [h3]; ring
    have hT : ∫ y' in (Λ : Set A.L), A.psiK ψ ((u : A.K) * x * A.NL (ui • (y + z) + y')) ∂μ = G := by
      rw [← hGΛ]
      exact setIntegral_add_left_mem μ Λ hΛm (fun t => A.psiK ψ ((u : A.K) * x * A.NL t)) _ hw
    rw [hpt, integral_const_mul, hT]
    ring

  rw [e1, e2, setIntegral_congr_fun hSm e3]
  show _ = G * A.psiK ψ (-ui * x * A.NL z) *
    ∫ y, nOp A ψ (x : A.K) (-ui) φ y * A.kerL ψ x y (-ui • z) ∂μ
  have hR : ∫ y, nOp A ψ (x : A.K) (-ui) φ y * A.kerL ψ x y (-ui • z) ∂μ =
      ∫ y in S, nOp A ψ (x : A.K) (-ui) φ y * A.kerL ψ x y (-ui • z) ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp only [nOp, hφ0 y hy, mul_zero, zero_mul]).symm
  rw [hR, ← integral_const_mul]
  refine setIntegral_congr_fun hSm fun y _ => ?_
  simp only [nOp, Et.kerL]
  have h4 : -(ui * x * A.NL (y + z)) = -ui * x * A.NL z +
      (-ui * x * A.NL y + (x : A.K) * Algebra.trace A.K A.L (star y * (-ui • z))) := by
    rw [NL_add, tr_smul_right]; ring
  rw [h4, psiK_add, psiK_add]
  ring
end GlobalTheory.JR.WeilQuad
