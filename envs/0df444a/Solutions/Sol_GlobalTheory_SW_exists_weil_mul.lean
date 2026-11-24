-- Prove2me | solution 1 for GlobalTheory.SW.exists_weil_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:08:29.428537+00:00
-- url     : https://prove2.me/submissions/81c0ee8b-a903-4e25-8f7b-c39bfccd214d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandarStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplectic
import Theorems.Thm_GlobalTheory_T_siegelThetaTransformationLaw_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (h : ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ')
    (h' : ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS σ' φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ') :
    ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧
      TransS (σ * σ') φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  obtain ⟨ω, hω⟩ := h
  obtain ⟨ω', hω'⟩ := h'
  refine ⟨fun φ => ω (ω' φ), fun φ hφ => ?_⟩
  obtain ⟨hs', ht', hi'⟩ := hω' φ hφ
  obtain ⟨hs, ht, hi⟩ := hω (ω' φ) hs'
  refine ⟨hs, GlobalTheory.T.siegelThetaTransformationLaw_mul κ ι σ' σ hσ' hσ φ (ω' φ) (ω (ω' φ)) ht' ht, fun φ' hφ' => ?_⟩
  rw [hi _ (hω' φ' hφ').1, hi' φ' hφ']
end GlobalTheory.SW
