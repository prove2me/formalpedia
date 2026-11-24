-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.isUnitarisable_parInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:00:13.114806+00:00
-- url     : https://prove2.me/submissions/0060dc1e-2db1-40b9-8c0e-6d64e4152b3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_exists_iwasawa
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_lintegral_KO_mul_right
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_form_eq_of_diag
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isLocallyConstant_indSp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_modulus_pos
import Theorems.Thm_GlobalTheory_SmGL_parInd_law
import Theorems.Thm_GlobalTheory_SmGL_unipRad_le_parab
import Theorems.Thm_GlobalTheory_SmGL_val_deltaHalf
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (h : IsUnitarisable ρ) :
    IsUnitarisable (parInd e ρ) := by
  obtain ⟨B, hs, hp, hi⟩ := h
  borelize k
  let μ : Measure (GL n k) := (Measure.haar : Measure (GL n k)).restrict (KO k n)
  have hK : MeasurableSet (KO k n : Set (GL n k)) := isOpen_KO.measurableSet
  have hc : ∀ f f' : IndSp e ρ, Continuous fun x => B (f.1.1 x) (f'.1.1 x) := fun f f' =>
    ((isLocallyConstant_indSp f).comp₂ (isLocallyConstant_indSp f') fun v w => B v w).continuous
  have hI : ∀ f f' : IndSp e ρ, Integrable (fun x => B (f.1.1 x) (f'.1.1 x)) μ := fun f f' =>
    (hc f f').continuousOn.integrableOn_compact isCompact_KO
  let C : IndSp e ρ →ₗ[ℂ] IndSp e ρ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f f' => ∫ x, B (f.1.1 x) (f'.1.1 x) ∂μ)
    (fun f g f' => by rw [← integral_add (hI _ _) (hI _ _)]; simp)
    (fun c f f' => by rw [← integral_smul]; simp)
    (fun f g f' => by rw [← integral_add (hI _ _) (hI _ _)]; simp)
    (fun c f f' => by rw [← integral_smul]; simp)
  have hC : ∀ f f', C f f' = ∫ x, B (f.1.1 x) (f'.1.1 x) ∂μ := fun _ _ => rfl
  have hn : ∀ v, 0 ≤ (B v v).re := fun v => by
    by_cases h : v = 0
    · simp [h]
    · exact (hp v h).le
  have hre : ∀ v, B v v = ((B v v).re : ℂ) := fun v => (Complex.conj_eq_iff_re.1 (hs v v).symm).symm
  have hcr : ∀ f : IndSp e ρ, Continuous fun x => (B (f.1.1 x) (f.1.1 x)).re := fun f =>
    Complex.continuous_re.comp (hc f f)
  have hdiag : ∀ f, C f f = ((∫ x, (B (f.1.1 x) (f.1.1 x)).re ∂μ : ℝ) : ℂ) := fun f => by
    rw [hC, ← integral_complex_ofReal]
    exact integral_congr_ae (.of_forall fun x => hre _)
  refine ⟨C, fun f f' => ?_, fun f hf => ?_, fun g => ?_⟩
  · rw [hC, hC, ← integral_conj]
    exact integral_congr_ae (.of_forall fun x => hs _ _)
  · rw [hdiag, Complex.ofReal_re, integral_pos_iff_support_of_nonneg (fun x => hn _) (hI f f).re,
      Measure.restrict_apply' hK]
    refine ((hcr f).isOpen_support.inter isOpen_KO).measure_pos _ ?_
    obtain ⟨x, hx⟩ : ∃ x, f.1.1 x ≠ 0 := by
      by_contra! h0
      exact hf (Subtype.ext (Subtype.ext (funext h0)))
    obtain ⟨u, t, w, hw, rfl⟩ := exists_iwasawa e x
    refine ⟨w, (hp _ fun h0 => hx ?_).ne', hw⟩
    have := parInd_law e ρ f (⟨u, unipRad_le_parab k e u.2⟩ * ⟨_, leviEmb_mem_parab k e t⟩) w
    rw [h0, map_zero, smul_zero] at this
    exact this
  · refine form_eq_of_diag ((C.comp (parInd e ρ g)).compl₂ (parInd e ρ g)) C fun f => ?_
    rw [LinearMap.compl₂_apply, LinearMap.comp_apply, hdiag, hdiag,
      integral_eq_lintegral_of_nonneg_ae (.of_forall fun x => hn _) (hcr _).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (.of_forall fun x => hn _) (hcr _).aestronglyMeasurable]
    congr 2
    refine lintegral_KO_mul_right e Measure.haar (φ := fun x => ENNReal.ofReal (B (f.1.1 x) (f.1.1 x)).re)
      (hcr f).measurable.ennreal_ofReal (fun p x => ?_) g
    have h0 := (modulus_pos k (leviProj k e p)).le
    rw [← ENNReal.ofReal_mul h0, parInd_law, val_deltaHalf]
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, hi, Complex.conj_ofReal, smul_eq_mul,
      Complex.re_ofReal_mul, RingHom.id_apply]
    rw [← mul_assoc, Real.mul_self_sqrt h0]
end GlobalTheory.SmGL.UnitInd
