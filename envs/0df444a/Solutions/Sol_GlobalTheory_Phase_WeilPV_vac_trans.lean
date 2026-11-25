-- Prove2me | solution 1 for GlobalTheory.Phase.WeilPV.vac_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:18:46.100217+00:00
-- url     : https://prove2.me/submissions/0cd655c6-2cb3-4c5f-a7ee-0aa0a6c1f297

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplectic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeisenbergOperatorRationalPointLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralGaussianShapeRootOfUnityPhStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSIntertwines
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelParabolicTransformPhaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RootOfUnityPhaseVacuumSiegelThetaTransform
import Theorems.Thm_GlobalTheory_Phase_WeilPV_trans_unique
import Theorems.Thm_GlobalTheory_Phase_WeilPV_trans_smul
import Theorems.Thm_GlobalTheory_Phase_WeilPV_sb_smul
import Theorems.Thm_GlobalTheory_Phase_ParabValues_trans_unique
import Theorems.Thm_GlobalTheory_Phase_transS_intertwines
import Theorems.Thm_GlobalTheory_SW_heisS_laws


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.WeilPV
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.Phase.WeilPV
theorem _root_.solution {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS σ φ ψ) (h : ∃ A ε, VacS A ε φ) :
    ∃ A ε, VacS A ε ψ := by
  obtain ⟨A, ε, h⟩ := h
  obtain ⟨T, hom, hT⟩ := GlobalTheory.Phase.transS_intertwines κ ι σ hσ
  have mem : ∀ y, y ∈ A.map T.toAddMonoidHom ↔ T.symm y ∈ A := fun y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa using hz, fun hy => ⟨_, hy, by simp⟩⟩
  have hom' : ∀ y y', om (T.symm y) (T.symm y') = om y y' := fun y y' => by
    rw [← hom]; simp
  refine ⟨A.map T.toAddMonoidHom, fun y => ε (T.symm y), ?_, ?_, ?_, ?_, ?_, hψ, ?_⟩
  · obtain ⟨S, hS⟩ := h.fg
    classical
    exact ⟨S.image T, by rw [← hS, AddMonoidHom.map_closure]; simp⟩
  · intro y
    rw [mem, h.dual]
    constructor
    · intro H y' hy'
      rw [← hom']; exact H _ ((mem _).1 hy')
    · intro H y' hy'
      have := H (T y') ((mem _).2 (by simpa using hy'))
      rw [← hom'] at this
      simpa using this
  · intro y hy; exact h.norm _ ((mem _).1 hy)
  · intro y hy y' hy'
    rw [map_add, h.semi _ ((mem _).1 hy) _ ((mem _).1 hy'), hom']
  · obtain ⟨m, hm, H⟩ := h.ord
    exact ⟨m, hm, fun y hy => by rw [map_nsmul]; exact H _ ((mem _).1 hy)⟩
  · intro y hy
    have t1 := trans_smul (ε (T.symm y)) (hT φ ψ h.sb hψ t (T.symm y))
    rw [h.fix _ ((mem _).1 hy), T.apply_symm_apply] at t1
    exact trans_unique hσ (sb_smul _ (GlobalTheory.SW.heisS_laws _ _ _ _ ψ hψ).1) hψ t1 t
end GlobalTheory.Phase.WeilPV
