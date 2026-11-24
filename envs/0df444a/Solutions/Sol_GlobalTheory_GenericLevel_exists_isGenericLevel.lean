-- Prove2me | solution 1 for GlobalTheory.GenericLevel.exists_isGenericLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:24:36.80627+00:00
-- url     : https://prove2.me/submissions/ba334840-0926-4b2d-8cec-54b84fdb2dd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrame
import Theorems.Thm_GlobalTheory_GenericLevel_exists_residueChar
import Theorems.Thm_GlobalTheory_GenericLevel_superSum_map
import Theorems.Thm_GlobalTheory_GenericLevel_genChar_apply
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_ofResidue_lam


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.GenericLevel
namespace GlobalTheory.GenericLevel
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ κ l : ℕ,
      ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsGenericLevel ψ ϖ P := by
  intro k _ _ _ _ ψ hψ ϖ hϖ κ l
  obtain ⟨φ, hφ⟩ := exists_residueChar hψ hϖ
  refine ⟨TypeDatum.ofResidue (upperUnip 𝓀[k] (framePos κ l)) (genChar φ (framePos κ l)), ?_, ?_⟩
  · intro g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨u, rfl, rfl⟩, hu⟩
    · rintro ⟨gb, ⟨u, rfl, rfl⟩, hu⟩
      exact ⟨u, hu, rfl⟩
  · rintro ⟨g, u, hu, rfl⟩
    have h := TypeDatum.ofResidue_lam (upperUnip 𝓀[k] (framePos κ l)) (genChar φ (framePos κ l)) u hu
    rw [h, genChar_apply]
    have e1 := superSum_map (IsLocalRing.residue 𝒪[k]) (framePos κ l) (u : Matrix _ _ 𝒪[k])
    have e2 := superSum_map (algebraMap 𝒪[k] k) (framePos κ l) (u : Matrix _ _ 𝒪[k])
    have e3 := hφ (∑ r, ∑ s, if framePos κ l s = framePos κ l r + 1
      then (u : Matrix _ _ 𝒪[k]) r s else 0)
    rw [← e1] at e3
    have e4 : φ (superSum (framePos κ l) ((u : Matrix _ _ 𝒪[k]).map (IsLocalRing.residue 𝒪[k])))
        = ψ (((ϖ⁻¹ : kˣ) : k) *
          superSum (framePos κ l) ((u : Matrix _ _ 𝒪[k]).map (algebraMap 𝒪[k] k))) := by
      rw [e3, e2]
      rfl
    exact congrArg (fun z : Circle => (z : ℂ)) e4
end GlobalTheory.GenericLevel
