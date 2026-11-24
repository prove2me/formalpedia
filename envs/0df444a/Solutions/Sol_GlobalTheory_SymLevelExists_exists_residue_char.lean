-- Prove2me | solution 1 for GlobalTheory.SymLevelExists.exists_residue_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:28.675968+00:00
-- url     : https://prove2.me/submissions/9a8e9e9a-08f2-4b76-a9fc-4de215726abf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
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
noncomputable section
open GlobalTheory GlobalTheory.SymLevelExists
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SymLevelExists
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ χ : 𝓀[k] → Circle, (∀ y z, χ (y + z) = χ y * χ z) ∧
      ∀ y : 𝒪[k], χ (IsLocalRing.residue 𝒪[k] y) = ψ ((ϖ⁻¹ : kˣ) * (y : k)) := by
  have hs : Function.Surjective (IsLocalRing.residue 𝒪[k]) := IsLocalRing.residue_surjective
  have key : ∀ y z : 𝒪[k], IsLocalRing.residue 𝒪[k] y = IsLocalRing.residue 𝒪[k] z →
      ψ ((ϖ⁻¹ : kˣ) * (y : k)) = ψ ((ϖ⁻¹ : kˣ) * (z : k)) := by
    intro y z h
    have h1 : valuation k ((y : k) - z) < 1 := (residue_eq_iff_lt y z).1 h
    have h2 := (hϖ _).1 h1
    have h3 : ψ ((ϖ⁻¹ : kˣ) * ((y : k) - z)) = 1 := by
      refine hψ.eq_one ?_
      have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
      simp only [cball, Set.mem_setOf_eq, Units.val_one, map_one, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      rwa [inv_mul_le_one₀ h0]
    rw [show ((ϖ⁻¹ : kˣ) : k) * (y : k) = (ϖ⁻¹ : kˣ) * ((y : k) - z) + (ϖ⁻¹ : kˣ) * (z : k) by ring,
      AddChar.map_add_eq_mul, h3, one_mul]
  have h2 : ∀ y : 𝒪[k], ψ ((ϖ⁻¹ : kˣ) * ((Function.surjInv hs (IsLocalRing.residue 𝒪[k] y) : 𝒪[k]) : k)) =
      ψ ((ϖ⁻¹ : kˣ) * (y : k)) := fun y => key _ _ (Function.surjInv_eq hs _)
  refine ⟨fun y => ψ ((ϖ⁻¹ : kˣ) * ((Function.surjInv hs y : 𝒪[k]) : k)), fun y z => ?_, h2⟩
  obtain ⟨y, rfl⟩ := hs y
  obtain ⟨z, rfl⟩ := hs z
  beta_reduce
  rw [← map_add, h2, h2, h2, ← AddChar.map_add_eq_mul, ← mul_add]
  rfl
end GlobalTheory.SymLevelExists
