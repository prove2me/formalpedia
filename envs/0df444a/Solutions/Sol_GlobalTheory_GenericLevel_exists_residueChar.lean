-- Prove2me | solution 1 for GlobalTheory.GenericLevel.exists_residueChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:21.232796+00:00
-- url     : https://prove2.me/submissions/28d8c683-4603-4180-b3ba-91afaff171f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrame
import Theorems.Thm_GlobalTheory_StepData_residue_eq_iff_lt


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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.GenericLevel
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ φ : AddChar 𝓀[k] Circle, ∀ x : 𝒪[k],
      φ (IsLocalRing.residue 𝒪[k] x) = ψ (((ϖ⁻¹ : kˣ) : k) * (x : k)) := by
  have hsurj : Function.Surjective (IsLocalRing.residue 𝒪[k]) := IsLocalRing.residue_surjective
  have h1 : ∀ y : k, valuation k y ≤ 1 → ψ y = 1 := by
    intro y hy
    exact (hψ 1).2 (by simp) y (by simpa using hy)
  have key : ∀ x y : 𝒪[k], IsLocalRing.residue 𝒪[k] x = IsLocalRing.residue 𝒪[k] y →
      ψ (((ϖ⁻¹ : kˣ) : k) * (x : k)) = ψ (((ϖ⁻¹ : kˣ) : k) * (y : k)) := by
    intro x y hxy
    have h2 := (hϖ _).1 ((residue_eq_iff_lt x y).1 hxy)
    have h0 : valuation k (ϖ : k) ≠ 0 := by simp
    have h3 : valuation k (((ϖ⁻¹ : kˣ) : k) * ((x : k) - (y : k))) ≤ 1 := by
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact (inv_mul_le_one₀ (zero_lt_iff.2 h0)).2 h2
    have h4 : ((ϖ⁻¹ : kˣ) : k) * (x : k)
        = ((ϖ⁻¹ : kˣ) : k) * (y : k) + ((ϖ⁻¹ : kˣ) : k) * ((x : k) - (y : k)) := by ring
    rw [h4, AddChar.map_add_eq_mul, h1 _ h3, mul_one]
  let f : 𝓀[k] → Circle := fun t => ψ (((ϖ⁻¹ : kˣ) : k) * ((Function.surjInv hsurj t : 𝒪[k]) : k))
  have hf : ∀ x : 𝒪[k], f (IsLocalRing.residue 𝒪[k] x) = ψ (((ϖ⁻¹ : kˣ) : k) * (x : k)) :=
    fun x => key _ _ (Function.surjInv_eq hsurj _)
  refine ⟨⟨f, ?_, ?_⟩, hf⟩
  · have := hf 0
    simpa using this
  · intro s t
    obtain ⟨x, rfl⟩ := hsurj s
    obtain ⟨y, rfl⟩ := hsurj t
    rw [← map_add, hf, hf, hf, ← AddChar.map_add_eq_mul]
    congr 1
    push_cast
    ring
end GlobalTheory.GenericLevel
