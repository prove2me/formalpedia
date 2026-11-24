-- Prove2me | solution 1 for GlobalTheory.HeisUnit.exists_unitary_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:08.642323+00:00
-- url     : https://prove2.me/submissions/8fba3f4b-5999-43b7-9694-1dd34143a342

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatLintegralSqNeTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCharacterUnitEqOneHeisenbergStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergCosetRepTranslatesOrthogonalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqUniformizerCharacterMulResidueCardPowEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMulNormalisedAbsPowHalfEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsWeilCharacterDetEqAbsDetPow
import Theorems.Thm_GlobalTheory_HeisUnit_intInd_mem_SB
import Theorems.Thm_GlobalTheory_HeisUnit_intInd_zero
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SplitFlip_apow_add
import Theorems.Thm_GlobalTheory_SplitFlip_apow_ne_zero
import Theorems.Thm_GlobalTheory_SplitFlip_exists_isUnif
import Theorems.Thm_GlobalTheory_T_heisenbergCosetRepTranslates_orthogonal
import Theorems.Thm_GlobalTheory_T_normSq_uniformizer_character_mul_residueCard_pow_eq_one
import Theorems.Thm_GlobalTheory_T_norm_character_unit_eq_one_heisenberg
import Theorems.Thm_GlobalTheory_T_norm_mul_normalisedAbsPow_half_eq_one
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_lintegral_sq_ne_top
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.HeisUnit
namespace GlobalTheory.HeisUnit
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
      (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∃ ν : kˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧ ∀ g : GL (Fin n) k,
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = ν (Matrix.GeneralLinearGroup.det g) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) ((d : ℂ) / 2) := by
  intro k _ _ _ _ n d ψ0 hψc hψ1 ι hι Tr Mu hTr hMu hTrI hMuI S hS hSI χ hχ
  let ν : kˣ →* ℂˣ := χ *
    { toFun := fun x => Units.mk0 (GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))) (GlobalTheory.SplitFlip.apow_ne_zero _ _)
      map_one' := Units.ext (GlobalTheory.SplitFlip.apow_one _)
      map_mul' := fun x y => Units.ext (GlobalTheory.SplitFlip.apow_mul x y _) }
  have hν : ∀ x : kˣ, (ν x : ℂ) = (χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := fun x => rfl
  have hfac : ∀ x : kˣ, (χ x : ℂ) = ν x * GlobalTheory.SplitFlip.apow x ((d : ℂ) / 2) := fun x => by
    rw [hν, mul_assoc, ← GlobalTheory.SplitFlip.apow_add, neg_add_cancel, GlobalTheory.SplitFlip.apow_zero, mul_one]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, fun x => by simp, fun g => ?_⟩
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp
  · refine ⟨ν, fun x => ?_, fun g => hfac _⟩
    let i0 : Fin n := ⟨0, hn⟩
    obtain ⟨φ0, hφ0, hιφ0⟩ := hι.surjOn (GlobalTheory.HeisUnit.intInd_mem_SB (k := k) n d)
    have hne : φ0 ≠ 0 := by
      rintro rfl
      have h := congrFun hιφ0 0
      rw [map_zero, GlobalTheory.HeisUnit.intInd_zero] at h
      exact zero_ne_one h
    have hN : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤ := fun μ hμ =>
      ⟨(GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0).2.2.1 hne, (GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0).1⟩
    have hU := GlobalTheory.T.norm_character_unit_eq_one_heisenberg ι hι.injOn S hS hSI χ hχ φ0 hφ0 hιφ0 hN i0
    obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := k)
    have hP := GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one ι hι.injOn Tr hTr hTrI S hS hSI χ hχ φ0 hφ0 hιφ0 hne ϖ hϖ i0
      (fun μ hμ T T' h => GlobalTheory.T.heisenbergCosetRepTranslates_orthogonal ψ0 hψc hψ1 ι hι.injOn Tr hTr Mu hMu hMuI φ0 hφ0 hιφ0 ϖ hϖ i0 T T' h μ hμ)
    rw [hν]
    exact GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one d χ hU ϖ hϖ hP x
end GlobalTheory.HeisUnit
