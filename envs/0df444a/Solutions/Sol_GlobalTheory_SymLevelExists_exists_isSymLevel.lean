-- Prove2me | solution 1 for GlobalTheory.SymLevelExists.exists_isSymLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:06.337021+00:00
-- url     : https://prove2.me/submissions/94fdf833-c447-4c19-9400-2c8cc39af6ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
import Theorems.Thm_GlobalTheory_SymLevelExists_symSum_mul
import Theorems.Thm_GlobalTheory_SymLevelExists_exists_residue_char
import Theorems.Thm_GlobalTheory_SymLevelExists_map_symSumInt
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
noncomputable section
open GlobalTheory GlobalTheory.SymLevelExists
namespace GlobalTheory.SymLevelExists
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ ρ κ l : ℕ, ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsSymLevel ψ ϖ ρ P := by
  intro k _ _ _ _ ψ hψ ϖ hϖ ρ κ l
  obtain ⟨χ, hadd, hres⟩ := exists_residue_char hψ hϖ
  let χ' : symGroup 𝓀[k] κ l (ρ + 1) →* ℂˣ :=
    MonoidHom.mk' (fun x => Circle.toUnits (χ (symSum (x : GL (Fin κ ⊕ Fin l) 𝓀[k])))) fun x y => by
      rw [Subgroup.coe_mul, symSum_mul x.2 y.2, hadd, map_mul]
  refine ⟨TypeDatum.ofResidue _ χ', fun g => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨g₀, ⟨u, hu, γ, hγ, e⟩, rfl⟩
    exact ⟨u, hu, γ, hγ, g₀, rfl, e⟩
  · rintro ⟨u, hu, γ, hγ, g₀, rfl, e⟩
    exact ⟨g₀, ⟨u, hu, γ, hγ, e⟩, rfl⟩
  · rintro ⟨_, g₀, hg, rfl⟩
    rw [TypeDatum.ofResidue_lam _ χ' g₀ hg]
    change ((χ (symSum (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀)) : Circle) : ℂ) = _
    rw [← map_symSumInt, hres, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← mul_add]
    exact congrArg (fun z : k => ((ψ ((ϖ⁻¹ : kˣ) * z) : Circle) : ℂ)) (map_symSumInt (algebraMap 𝒪[k] k) g₀)
end GlobalTheory.SymLevelExists
